//! Map fuzzer, ops 20–29: whole-map lattice ops.  Mirrors `MapFuzz/Lattice.lean`,
//! which has the op table and the rendering rules for `AlgebraicResult`.

use super::*;
use super::core_ops::{full_dump, is_empty_map, pairs, values_only, SKIP_MAP_IDENT};
use pathmap::ring::{AlgebraicResult, AlgebraicStatus, DistributiveLattice, Lattice};

/// Render an `AlgebraicResult<PathMap>` as `class/dump` and return the map it
/// resolves to.  `args` are the operands (bit `i` of an identity mask names
/// `args[i]`); `k` picks the accessor that resolves it; `meet` compares by
/// values and drops dangling paths (see Lattice.lean).
fn render(
    res: AlgebraicResult<PathMap<u64>>,
    args: &[&PathMap<u64>],
    k: usize,
    meet: bool,
) -> (String, PathMap<u64>) {
    let (is_none, is_ident, is_elem, mask) = match &res {
        AlgebraicResult::None => (true, false, false, None),
        AlgebraicResult::Identity(m) => (false, true, false, Some(*m)),
        AlgebraicResult::Element(_) => (false, false, true, None),
    };
    let accessors_agree = res.is_none() == is_none
        && res.is_identity() == is_ident
        && res.is_element() == is_elem
        && res.identity_mask() == mask;
    let status = res.status();
    let r = match k {
        0 => {
            if res.is_none() {
                PathMap::new()
            } else {
                res.unwrap(args)
            }
        }
        1 => res.unwrap_or_else(|i| args[i].clone(), PathMap::new),
        2 => res.unwrap_or(args, PathMap::new()),
        _ => res.into_option(args).unwrap_or_default(),
    };
    let same = |x: &PathMap<u64>, y: &PathMap<u64>| {
        if meet { pairs(x) == pairs(y) } else { full_dump(x) == full_dump(y) }
    };
    let mask = mask.unwrap_or(0);
    let sound = (0..64)
        .filter(|j| mask & (1u64 << j) != 0)
        .all(|j| j < args.len() && same(&r, args[j]));
    let r = if meet { values_only(&r) } else { r };
    let class = if !accessors_agree {
        "ACCESSOR-MISMATCH"
    } else if !sound {
        "UNSOUND-MASK"
    } else if is_empty_map(&r) {
        "None"
    } else if meet {
        if pairs(&r) == pairs(args[0]) { "Identity" } else { "Element" }
    } else if full_dump(&r) == full_dump(args[0]) {
        // `skip:map-ident`: the class of a result equal to `self` is not
        // compared (MapFuzz/Lattice.lean, `map_alg_ident_closures`).
        SKIP_MAP_IDENT
    } else {
        show_status(status)
    };
    (format!("{}/{}", class, dump(&mut r.read_zipper())), r)
}

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        20..=23 => {
            let (a, b, c) = (map_ix(d)?, map_ix(d)?, map_ix(d)?);
            let (x, y) = (&st.maps[a], &st.maps[b]);
            let (name, r) = match op {
                20 => ("join", x.join(y)),
                // Dangling paths after a meet are unspecified: compare values.
                21 => ("meet", values_only(&x.meet(y))),
                22 => ("subtract", x.subtract(y)),
                _ => ("restrict", x.restrict(y)),
            };
            let s = dump(&mut r.read_zipper());
            st.maps[c] = r;
            (name, s)
        }
        24..=26 => {
            let (a, b, c, k) = (map_ix(d)?, map_ix(d)?, map_ix(d)?, d.modn(4)?);
            let (x, y) = (&st.maps[a], &st.maps[b]);
            let (name, res, meet) = match op {
                24 => ("pjoin", x.pjoin(y), false),
                25 => ("pmeet", x.pmeet(y), true),
                _ => ("psubtract", x.psubtract(y), false),
            };
            let (s, r) = render(res, &[x, y], k, meet);
            st.maps[c] = r;
            (name, s)
        }
        27 => {
            let (a, b) = (map_ix(d)?, map_ix(d)?);
            let other = st.maps[b].clone();
            let before = full_dump(&st.maps[a]);
            let status = st.maps[a].join_into(other);
            let m = &st.maps[a];
            let class = if is_empty_map(m) {
                "None"
            } else if status == AlgebraicStatus::Element && full_dump(m) == before {
                // `Element` for an unchanged map: tagged so that the KNOWN entry
                // for it (`map_join_into_layout_status`) matches nothing else.
                "Element=SELF"
            } else {
                show_status(status)
            };
            ("join_into", format!("{}/{}", class, dump(&mut m.read_zipper())))
        }
        28 => {
            let n = d.modn(4)?;
            let mut ix = Vec::new();
            for _ in 0..n {
                ix.push(map_ix(d)?);
            }
            let c = map_ix(d)?;
            // `join_all` wants `S: AsRef<PathMap>`, which `Box` provides.
            let boxes: Vec<Box<PathMap<u64>>> = ix.iter().map(|&i| Box::new(st.maps[i].clone())).collect();
            let res = PathMap::join_all(&boxes);
            let args: Vec<&PathMap<u64>> = boxes.iter().map(|b| &**b).collect();
            let (s, r) = if args.is_empty() {
                // No operands: `None`, and nothing to resolve an identity against.
                let s = match res {
                    AlgebraicResult::None => "None/_:-".to_string(),
                    _ => "UNSOUND-MASK/_:-".to_string(),
                };
                (s, PathMap::new())
            } else {
                render(res, &args, 3, false)
            };
            st.maps[c] = r;
            ("join_all", s)
        }
        _ => ("nop", "-".to_string()),
    })
}
