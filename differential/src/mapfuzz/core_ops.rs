//! Map fuzzer, ops 0–19: the `PathMap` surface.  Mirrors `MapFuzz/Core.lean`,
//! which has the op table and the semantic decisions.

use super::*;
use pathmap::zipper::*;

/// Skip reasons, the same tokens as `MapFuzz/Core.lean` (which documents them).
pub const SKIP_DEBUG_ROOT_VAL: &str = "skip:debug-root-val";
pub const SKIP_MAP_IDENT: &str = "skip:map-ident";

/// What op 1 appends to a path when its map byte asks for a long one
/// (`longTail` in `Core.lean`): 48 bytes, so the key outgrows a
/// `LineListNode` key buffer (`KEY_BYTES_CNT`: 42 with the default
/// `slim_ptrs`, 14 without) and continuation nodes are made
/// (`set_child_0` / `set_child_1`).
pub const LONG_TAIL: [u8; 48] = [
    1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0,
    1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0,
];

/// Every location of `m`, depth-first, uncapped (for comparing whole maps).
pub fn full_dump(m: &PathMap<u64>) -> String {
    let mut z = m.read_zipper();
    let mut lines = vec![format!("{}:{}", hex_path(z.path()), show_val(z.val()))];
    while z.to_next_step() {
        lines.push(format!("{}:{}", hex_path(z.path()), show_val(z.val())));
    }
    lines.join(",")
}

/// The key/value pairs of `m`, root value first, read with a zipper (not with
/// `iter`, which is under test).
pub fn pairs(m: &PathMap<u64>) -> Vec<(Vec<u8>, u64)> {
    let mut z = m.read_zipper();
    let mut out = Vec::new();
    if let Some(v) = z.val() {
        out.push((vec![], *v));
    }
    while z.to_next_val() {
        out.push((z.path().to_vec(), *z.val().unwrap()));
    }
    out
}

/// `m` rebuilt from its values alone: no dangling paths.
pub fn values_only(m: &PathMap<u64>) -> PathMap<u64> {
    let mut fresh = PathMap::new();
    for (p, v) in pairs(m) {
        fresh.set_val_at(&p, v);
    }
    fresh
}

/// A path operand for map `m`: `Dec.mpath` in Core.lean, which documents it.
pub fn mpath(d: &mut Dec, m: &PathMap<u64>) -> Option<Vec<u8>> {
    let sel = d.u8()? as usize;
    if sel < 128 {
        let mut z = m.read_zipper();
        let (mut all, mut valued, mut tips) = (vec![], vec![], vec![]);
        loop {
            let p = z.path().to_vec();
            if z.val().is_some() {
                valued.push(p.clone());
            } else if z.child_count() == 0 {
                tips.push(p.clone());
            }
            all.push(p);
            if !z.to_next_step() {
                break;
            }
        }
        let ps = if sel < 48 { valued } else if sel < 80 { tips } else { all.clone() };
        let ps = if ps.is_empty() { all } else { ps };
        let k = d.u8()? as usize;
        Some(ps[k % ps.len()].clone())
    } else {
        d.path_n(sel % 6)
    }
}

/// No value and no path besides the root.
pub fn is_empty_map(m: &PathMap<u64>) -> bool {
    full_dump(m) == "_:-"
}

/// `ZipperConcrete::shared_node_id` documents that equal ids mean the same
/// node; for a `PathMap` (which reports `None` when it has a root value) that
/// means the same contents.  `1` if every pair of maps reporting the same id
/// holds the same contents.
fn shared_ids_sound(maps: &[PathMap<u64>; 3]) -> &'static str {
    for x in 0..3 {
        for y in x + 1..3 {
            if let (Some(a), Some(b)) = (maps[x].shared_node_id(), maps[y].shared_node_id()) {
                if a == b && full_dump(&maps[x]) != full_dump(&maps[y]) {
                    return "0";
                }
            }
        }
    }
    "1"
}

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        0 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            ("get", show_val(st.maps[i].get(&p)))
        }
        1 => {
            // The map byte's spare bits (`Core.lean`, op 1): `/3 % 2` picks
            // `insert` over `set_val_at` (an alias), `/6 % 4 == 3` stretches the
            // path by `LONG_TAIL`, past a `LineListNode`'s key buffer (only a
            // quarter of the time: a long path is 48 locations of the final
            // dumps' 64).
            let raw = d.u8()? as usize;
            let i = raw % 3;
            let mut p = mpath(d, &st.maps[i])?;
            let (v,) = (val(d)?,);
            if (raw / 6) % 4 == 3 {
                p.extend_from_slice(&LONG_TAIL);
            }
            let m = &mut st.maps[i];
            let old = if (raw / 3) % 2 == 1 { m.insert(&p, v) } else { m.set_val_at(&p, v) };
            ("insert", show_val(old.as_ref()))
        }
        2 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            ("remove", show_val(st.maps[i].remove(&p).as_ref()))
        }
        3 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            ("contains", show_bool(st.maps[i].contains(&p)).to_string())
        }
        4 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            let m = &st.maps[i];
            #[allow(deprecated)]
            let (cp, gv) = (m.contains_path(&p), m.get_val_at(&p));
            let s = format!(
                "{}|{}|{}|{}|{}",
                show_bool(m.path_exists_at(&p)),
                show_bool(cp),
                show_val(m.val_at(&p)),
                show_val(gv),
                show_val(ZipperValues::val(m)),
            );
            ("exists", s)
        }
        5 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            let (pr,) = (d.boolean()?,);
            ("remove_val_at", show_val(st.maps[i].remove_val_at(&p, pr).as_ref()))
        }
        6 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            let (k, v) = (d.boolean()?, val(d)?);
            let m = &mut st.maps[i];
            let r = if k { m.get_mut(&p) } else { m.get_val_mut_at(&p) };
            let old = r.map(|r| {
                let old = *r;
                *r = v;
                old
            });
            ("get_val_mut_at", show_val(old.as_ref()))
        }
        7 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            let (dv,) = (val(d)?,);
            let r = st.maps[i].get_val_or_set_mut_at(&p, dv);
            let seen = *r;
            *r = seen.wrapping_add(1);
            ("get_val_or_set_mut_at", show_val(Some(&seen)))
        }
        8 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            let (dv,) = (val(d)?,);
            let mut ran = false;
            let r = st.maps[i].get_val_or_set_mut_with_at(&p, || {
                ran = true;
                dv
            });
            let seen = *r;
            *r = seen.wrapping_add(1);
            ("get_val_or_set_mut_with_at", format!("{}:{}", seen, show_bool(ran)))
        }
        9 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            let (pr,) = (d.boolean()?,);
            ("remove_branches_at", show_bool(st.maps[i].remove_branches_at(&p, pr)).to_string())
        }
        10 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            ("prune_path", st.maps[i].prune_path(&p).to_string())
        }
        11 => {
            let i = map_ix(d)?;
            let p = mpath(d, &st.maps[i])?;
            ("create_path", show_bool(st.maps[i].create_path(&p)).to_string())
        }
        12 => {
            let (i, merk) = (map_ix(d)?, d.boolean()?);
            let m = &mut st.maps[i];
            if merk {
                let _ = m.merkleize();
            }
            let s = format!("{},{},{}", m.val_count(), m.goat_val_count(), show_bool(m.is_empty()));
            ("counts", s)
        }
        13 => {
            let (i, k) = (map_ix(d)?, d.boolean()?);
            let m = &st.maps[i];
            if k {
                // `skip:debug-root-val`: Debug omits the root value; see Core.lean.
                let s = if m.val_at::<&[u8]>(&[]).is_some() { SKIP_DEBUG_ROOT_VAL.to_string() } else { format!("{m:?}") };
                ("debug-fmt", s)
            } else {
                ("iter", show_pairs(m.iter().take(64).map(|(p, v)| (p, *v))))
            }
        }
        14 => {
            let (i, j, k) = (map_ix(d)?, map_ix(d)?, d.modn(3)?);
            let src = &st.maps[j];
            match k {
                0 => {
                    let t: PathMap<u64> = src.iter().map(|(p, v)| (p, *v)).collect();
                    let s = dump(&mut t.read_zipper());
                    st.maps[i] = t;
                    ("from_iter", s)
                }
                1 => {
                    let ps: Vec<(Vec<u8>, u64)> = src.iter().map(|(p, v)| (p, *v)).collect();
                    let t: PathMap<u64> = ps.iter().collect();
                    let s = dump(&mut t.read_zipper());
                    st.maps[i] = t;
                    ("from_iter", s)
                }
                _ => {
                    let keys: Vec<Vec<u8>> = src.iter().map(|(p, _)| p).collect();
                    let u: PathMap<()> = keys.iter().map(|k| k.as_slice()).collect();
                    ("from_iter", show_paths(u.iter().take(64).map(|(p, _)| p)))
                }
            }
        }
        15 => {
            let (i, k) = (map_ix(d)?, d.boolean()?);
            if k {
                let m = std::mem::take(&mut st.maps[i]);
                let ps: Vec<(Vec<u8>, u64)> = m.into_iter().collect();
                st.maps[i] = ps.iter().cloned().collect();
                ("into_iter", show_pairs(ps.into_iter().take(64)))
            } else {
                // Consuming a clone must leave the original alone (copy-on-write).
                let ps: Vec<(Vec<u8>, u64)> = st.maps[i].clone().into_iter().take(64).collect();
                ("into_iter", show_pairs(ps))
            }
        }
        16 => {
            let (i, j) = (map_ix(d)?, map_ix(d)?);
            st.maps[i] = st.maps[j].clone();
            ("clone", shared_ids_sound(&st.maps).to_string())
        }
        17 => {
            // `kraw / 5 % 2` builds kinds 0-2 through an owned write zipper
            // instead (`WriteZipperOwned::new` / `new_in`, `descend_to`,
            // `set_val`, `into_map`): the same map (`Core.lean`, op 17).
            let (i, kraw, p, v) = (map_ix(d)?, d.u8()? as usize, d.path(6)?, val(d)?);
            let k = kraw % 5;
            let t: PathMap<u64> = match k {
                0..=2 if (kraw / 5) % 2 == 1 => {
                    let mut wz = if k == 2 { WriteZipperOwned::new_in(pathmap::alloc::global_alloc()) } else { WriteZipperOwned::new() };
                    wz.descend_to(&p);
                    wz.set_val(v);
                    wz.into_map()
                }
                0 => PathMap::single(&p, v),
                1 => PathMap::from((&p, v)),
                2 => PathMap::single_in(&p, v, pathmap::alloc::global_alloc()),
                3 => PathMap::new(),
                _ => PathMap::default(),
            };
            let s = dump(&mut t.read_zipper());
            st.maps[i] = t;
            ("single", s)
        }
        18 => {
            // `kraw / 3 % 2` reads kinds 0 and 1 through `PathMap::trie_ref_at_path`
            // instead (`&Vec` and `&[u8]` keys), dumping its `fork_read_zipper`
            // (`_:-` where the path is missing, as `dump` prints a missing root).
            let (i, kraw) = (map_ix(d)?, d.u8()? as usize);
            let (k, tref) = (kraw % 3, (kraw / 3) % 2 == 1);
            let p = mpath(d, &st.maps[i])?;
            let s = match k {
                0 if tref => dump_fork(&st.maps[i].trie_ref_at_path(&p)),
                1 if tref => dump_fork(&st.maps[i].trie_ref_at_path(p.as_slice())),
                0 => dump(&mut st.maps[i].read_zipper_at_borrowed_path(&p)),
                1 => dump(&mut st.maps[i].read_zipper_at_path(&p)),
                _ => {
                    let m = std::mem::take(&mut st.maps[i]);
                    let mut rz = m.into_read_zipper(&p);
                    let s = dump(&mut rz);
                    st.maps[i] = rz.into_map();
                    s
                }
            };
            ("read_zipper_at", s)
        }
        19 => {
            let (i, p, q, v) = (map_ix(d)?, d.path(4)?, d.path(4)?, val(d)?);
            let m = std::mem::take(&mut st.maps[i]);
            let mut wz = m.into_write_zipper(&p);
            wz.descend_to(&q);
            let old = wz.set_val(v);
            st.maps[i] = wz.into_map();
            let s = format!("{}|{}", show_val(old.as_ref()), dump(&mut st.maps[i].read_zipper_at_path(&p)));
            ("into_write_zipper", s)
        }
        _ => ("nop", "-".to_string()),
    })
}
