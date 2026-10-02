//! A developer tool for finding *avoidable loss of sharing across algebraic
//! pipelines*. It explores many related input shapes and combinations of ops,
//! checks each intermediate result, and reports the step at which sharing was
//! lost. The question is how much sharing an algebraic result could retain or
//! create from its known inputs, and how much the implementation actually keeps.
//!
//! Each case constructs a small family of related maps from reusable fragments.
//! Grafts usually line up at the same schema positions in different operands;
//! record IDs and fragment contents provide variation. A pseudorandom program
//! then joins, meets, subtracts, and restricts those maps, often reusing earlier
//! results. After every step, an independent flat path-set model checks the
//! result's logical contents, and a sharing observer compares locations within
//! the result. A symbolic model also follows sharing opportunities through later
//! steps, so a gap introduced earlier remains visible in subsequent results.
//!
//! The observer measures two kinds of opportunity:
//!
//! * **Ordinary sharing:** one input fragment `S` occurs under many parents and
//!   survives unchanged. Even if an op rebuilds those parents, their result
//!   locations should still share one `S`.
//! * **Result-sharing:** the same shared pair `(S, T)` is combined at many
//!   locations. Those locations could share one computed result. The current
//!   implementation does not generally produce this sharing, so this category
//!   records a target for future implementations.
//!
//! A **split** means locations that could share one node instead occupy
//! multiple physical nodes. For ordinary sharing, this can be an unnecessary
//! make-unique; for result-sharing, it can be a computed result that was
//! recomputed instead of reused.
//!
//! An obligation requires known shared inputs and surviving or repeated work;
//! equal contents built independently do not qualify. Sharing comparisons use
//! live zippers within one map, without carrying physical IDs between steps.
//! Fixed tests supplement the sweep with 100 parents, varying fanout,
//! projection, boolean values, empty and root-valued operands, and an unvalued
//! path.
//!
//! ## Two ways to run the sweep
//!
//! **Report mode** is the default. It runs every selected seed and reports
//! totals, including all split sharing groups. To keep output short, it displays
//! only the first four split examples of each kind; those examples can come
//! from the same seed. They are not a list of all failures or distinct root
//! causes. Logical errors still stop the validator.
//!
//! **Strict mode** is enabled with `PATHMAP_SHARING_ENFORCE_ORDINARY=1` and/or
//! `PATHMAP_SHARING_ENFORCE_RESULTS=1`. It stops at the first enforced sharing
//! loss, minimizes that failure, saves a replay, and exits unsuccessfully.
//! `PATHMAP_SHARING_CASES` is only an upper bound here: seeds after the first
//! failure are not run. Result-sharing enforcement is off by default because
//! that optimization is not yet implemented.
//!
//! ## Running the validator
//!
//! Run from the repository root:
//!
//! ```sh
//! # Run the seeded sweep and print a full report.
//! cargo run -p algebra-sharing-validation
//!
//! # Report across seeds 100 through 149.
//! PATHMAP_SHARING_START=100 PATHMAP_SHARING_CASES=50 cargo run -p algebra-sharing-validation
//!
//! # Stop at the first ordinary-sharing loss.
//! PATHMAP_SHARING_ENFORCE_ORDINARY=1 cargo run -p algebra-sharing-validation
//!
//! # Fail on the first missing result-sharing opportunity in seed 0.
//! PATHMAP_SHARING_START=0 PATHMAP_SHARING_CASES=1 PATHMAP_SHARING_STEPS=1 PATHMAP_SHARING_SPOTS=2 PATHMAP_SHARING_ENFORCE_RESULTS=1 cargo run -p algebra-sharing-validation
//!
//! # Run the nine fixed calibration tests and the seeded sweep as separate tests.
//! cargo test -p algebra-sharing-validation
//! ```
//!
//! The optional environment variables mean:
//!
//! * `PATHMAP_SHARING_START`: first decimal `u64` seed; default `0`. One seed
//!   selects one deterministic construction and operation program.
//! * `PATHMAP_SHARING_CASES`: positive decimal number of consecutive seeds;
//!   default `24` (`1` under Miri). Increasing this explores more cases; it
//!   does not make each trie larger.
//! * `PATHMAP_SHARING_STEPS`: positive decimal number of algebra operations in
//!   each case; default `8`. A smaller number keeps an initial program prefix.
//! * `PATHMAP_SHARING_SPOTS`: decimal cap on graft locations per case; default
//!   is no cap. More spots can create higher sharing multiplicity; some cases
//!   generate 100. Values below `2` act as `2`. Reducing the cap retains the
//!   first graft locations, although a focused operation may choose a different
//!   location from that smaller set.
//! * `PATHMAP_SHARING_ENFORCE_ORDINARY`: defaults to `0`, so ordinary-sharing
//!   losses are counted and reported across all seeds. Set to `1` to stop at
//!   the first loss. Other values are rejected.
//! * `PATHMAP_SHARING_ENFORCE_RESULTS`: set to exactly `1` to fail on missing
//!   result-sharing; default is report only.
//!
//! The binary runs only the seeded sweep. `cargo test -p
//! algebra-sharing-validation` runs the nine fixed calibration tests and the
//! sweep independently. The calibrations exercise known sharing, independent
//! construction, and projection semantics without requiring current sharing
//! losses to persist. Invalid numeric text uses the default; `CASES=0` and
//! `STEPS=0` fail. Wrong logical results always fail the sweep.
//!
//! ## Reading the output
//!
//! Start with a report run to see which kinds of sharing are lost across a seed
//! range. If a split needs investigation, use strict mode and a narrow seed
//! range to save a minimized replay. Read a completed report from top to bottom:
//!
//! * `SHARING SWEEP — REPORT MODE` confirms that every selected seed ran.
//!   `Seeds checked` shows the half-open seed range: the end seed is excluded.
//!   `Operations` counts output maps checked; `focused` counts operations at a
//!   non-root path.
//! * `Split = missed sharing ...` defines the table's last column. Each table
//!   row counts *groups checked after operations*, not shared nodes at the
//!   beginning or end. A group contains multiple locations expected to share
//!   one node. `Checked` counts such group observations; `Split` is the subset
//!   that occupied multiple physical nodes. The same group can be observed at
//!   several steps, so these are not counts of distinct bugs or lost bytes.
//! * `Ordinary (surviving)` checks groups physically shared in an input whose
//!   contents survived unchanged at multiple locations in the output. Its
//!   `Checked - Split` difference is the number of checks that kept sharing.
//! * `Result (computed)` checks groups where the same pair of physically shared
//!   inputs underwent the same operation at multiple locations. A split means
//!   those locations did not reuse one computed result.
//! * `Symbolic model (overlaps the checks above)` follows possible sharing
//!   through later steps, including sharing a prior computation could have
//!   produced. `Groups expected to share` counts its group observations;
//!   `Physically split` counts the ones split in the current output. `Of those,
//!   first computed before this step` is a subset of `Physically split`: those
//!   groups' symbolic computed tokens originated on an earlier step. It does
//!   not establish that they were already split then. This model is a separate,
//!   overlapping view, so do not add its numbers to the table. Zero physical
//!   splits is its target if its symbolic expectations are all achievable;
//!   the aggregate count alone does not establish that for each group.
//! * The later `Operations` and `Routes` lines show which operations and
//!   implementations the selected seeds exercised. Each `... examples`
//!   section shows at most four split observations, not every split. An example
//!   gives the seed, one representative path in hexadecimal bytes, the number
//!   of physical groups, and the operation sequence leading to that result.
//!
//! In strict mode, the output says how many seeds ran before the first enforced
//! loss, then shows its minimized operation sequence. The saved file under
//! `target/pathmap-sharing-failures/` (or `CARGO_TARGET_DIR` when set) contains
//! the replay command, full trace, source keys, and graft paths. A seed is
//! stable for this generator version; changing the generator can change it.

//GOAT!  Why is there a special repro case in the docs if every case hits a failure?
//GOAT!  Can a specific failure be isolated back to a simple test, to validate the harness
//          Include an example of how to replay a failure / turn a failure into a specific test
//GOAT!  What are the other tests in this file??  Are they tests for the test?

use pathmap::PathMap;
use pathmap::ring::Lattice;
use pathmap::zipper::{ZipperConcrete, ZipperMoving, ZipperPath, ZipperWriting};
use std::collections::{BTreeMap, BTreeSet};

fn main() {
    const USAGE: &str = "Usage: algebra-sharing-validation\nSee validation/algebra_sharing/src/main.rs for environment variables and examples. Run cargo test -p algebra-sharing-validation for calibration tests.";
    match std::env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [] => seeded_algebra_sharing_sweep(),
        [flag] if flag == "--help" || flag == "-h" => println!("{USAGE}"),
        _ => {
            eprintln!("{USAGE}");
            std::process::exit(2);
        }
    }
}

type Keys = BTreeSet<Vec<u8>>;
const DISPLAY_LIMIT: usize = 4;

fn display_path(path: &[u8]) -> String {
    if path.is_empty() {
        return "(root)".to_owned();
    }
    path.iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<Vec<_>>()
        .join("/")
}

#[derive(Clone, Copy, Debug)]
enum Op {
    Join,
    Meet,
    Subtract,
    Restrict,
}

#[derive(Clone, Copy, Debug)]
enum Route {
    Whole,
    Zipper,
    JoinMap,
    JoinTake,
    JoinInto,
    Meet2,
    Restricting,
}

impl Op {
    fn apply(self, route: Route, focus: &[u8], a: &PathMap<()>, b: &PathMap<()>) -> PathMap<()> {
        match route {
            Route::Whole => match self {
                Self::Join => a.join(b),
                Self::Meet => a.meet(b),
                Self::Subtract => a.subtract(b),
                Self::Restrict => a.restrict(b),
            },
            Route::Zipper => {
                let mut result = a.clone();
                {
                    let mut dest = result.write_zipper_at_path(focus);
                    let src = b.read_zipper_at_path(focus);
                    match self {
                        Self::Join => {
                            dest.join_into(&src);
                        }
                        Self::Meet => {
                            dest.meet_into(&src, true);
                        }
                        Self::Subtract => {
                            dest.subtract_into(&src, true);
                        }
                        Self::Restrict => {
                            dest.restrict(&src);
                        }
                    }
                }
                result
            }
            Route::JoinMap => {
                let mut result = a.clone();
                result.write_zipper().join_map_into(b.clone());
                result
            }
            Route::JoinTake => {
                let mut result = a.clone();
                let mut source = b.clone();
                {
                    let mut dest = result.write_zipper();
                    let mut src = source.write_zipper();
                    dest.join_into_take(&mut src, true);
                }
                result
            }
            Route::JoinInto => {
                let mut result = a.clone();
                result.join_into(b.clone());
                result
            }
            Route::Meet2 => {
                let mut result = PathMap::new();
                result
                    .write_zipper()
                    .meet_2(&a.read_zipper(), &b.read_zipper());
                result
            }
            Route::Restricting => {
                let mut result = b.clone();
                result.write_zipper().restricting(&a.read_zipper());
                result
            }
        }
    }

    fn model(self, a: &Keys, b: &Keys) -> Keys {
        match self {
            Self::Join => a.union(b).cloned().collect(),
            Self::Meet => a.intersection(b).cloned().collect(),
            Self::Subtract => a.difference(b).cloned().collect(),
            Self::Restrict => a
                .iter()
                .filter(|path| (0..=path.len()).any(|n| b.contains(&path[..n].to_vec())))
                .cloned()
                .collect(),
        }
    }

    fn model_at(self, focus: &[u8], a: &Keys, b: &Keys) -> Keys {
        if focus.is_empty() {
            return self.model(a, b);
        }
        let mut result: Keys = a
            .iter()
            .filter(|path| !path.starts_with(focus))
            .cloned()
            .collect();
        for suffix in self.model(&subtree(a, focus), &subtree(b, focus)) {
            let mut path = focus.to_vec();
            path.extend(suffix);
            result.insert(path);
        }
        result
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        ((self.next() >> 32) as usize) % n
    }
}

struct State {
    map: PathMap<()>,
    keys: Keys,
    tokens: BTreeMap<Vec<u8>, u64>,
}

fn append_fragment(keys: &mut Keys, at: &[u8], fragment: &Keys) {
    for suffix in fragment {
        let mut path = at.to_vec();
        path.extend_from_slice(suffix);
        keys.insert(path);
    }
}

fn fragment(rng: &mut Rng, field: u8) -> State {
    let mut keys = Keys::new();
    // The fixed field marker is encoding glue; later bytes carry variance.
    let branch_count = match rng.below(16) {
        0 => 1,
        1 => 16,
        _ => 3 + rng.below(6),
    };
    for branch in 0..branch_count {
        let mut path = vec![field, branch as u8, 0xf0];
        let length = if rng.below(32) == 0 {
            16 + rng.below(16)
        } else {
            1 + rng.below(6)
        };
        for _ in 0..length {
            path.push(rng.below(9) as u8);
        }
        keys.insert(path.clone());
        if branch % 2 == 0 {
            keys.insert(path[..3].to_vec());
        }
        if branch % 3 == 0 {
            path.push(0x7f);
            keys.insert(path);
        }
    }
    let mut state = from_keys(keys);
    if rng.below(2) == 0 {
        let mut nested_keys = Keys::new();
        for index in 0..2 + rng.below(4) {
            nested_keys.insert(vec![0x70, index as u8, 0x71]);
        }
        let nested = from_keys(nested_keys);
        for at in [&[0xe0, 0][..], &[0xe0, 1][..]] {
            state
                .map
                .write_zipper_at_path(at)
                .graft_map(nested.map.clone());
            append_fragment(&mut state.keys, at, &nested.keys);
        }
    }
    state
}

fn from_keys(keys: Keys) -> State {
    let mut map = PathMap::new();
    for key in &keys {
        map.insert(key, ());
    }
    State {
        map,
        keys,
        tokens: BTreeMap::new(),
    }
}

fn record_spots(rng: &mut Rng) -> Vec<Vec<u8>> {
    let count = if rng.below(8) == 0 {
        100
    } else {
        4 + rng.below(9)
    };
    let tag = rng.below(4) as u8;
    (0..count)
        .map(|i| vec![0xa0, tag, (i >> 8) as u8, i as u8, 0x00, 0xb0])
        .collect()
}

fn grafted(fragment: &State, spots: &[Vec<u8>], rng: &mut Rng, flavor: u8) -> State {
    let mut map = PathMap::new();
    let mut keys = Keys::new();
    for (i, spot) in spots.iter().enumerate() {
        if flavor == 2 && i % 7 == 0 {
            continue; // Controlled occurrence removal.
        }
        map.write_zipper_at_path(spot)
            .graft_map(fragment.map.clone());
        append_fragment(&mut keys, spot, &fragment.keys);

        // Changes to the parent are common, while the grafted link is left alone.
        if flavor != 0 && (i + flavor as usize) % 3 == 0 {
            let mut sibling = spot[..spot.len() - 1].to_vec();
            sibling.extend_from_slice(&[0xc0, rng.below(16) as u8]);
            map.insert(&sibling, ());
            keys.insert(sibling);
        }
        if flavor == 1 && i % 5 == 0 {
            let parent = spot[..spot.len() - 1].to_vec();
            map.insert(&parent, ());
            keys.insert(parent);
        }
    }
    State {
        map,
        keys,
        tokens: BTreeMap::new(),
    }
}

fn actual_keys(map: &PathMap<()>) -> Keys {
    map.iter().map(|(key, ())| key).collect()
}

/// Compare two occurrences while both zipper observations are live. No node ID
/// escapes this function or is carried to another map/checkpoint.
fn same_node<V: Clone + Send + Sync + Unpin>(map: &PathMap<V>, a: &[u8], b: &[u8]) -> bool {
    let left = map.read_zipper_at_path(a);
    let right = map.read_zipper_at_path(b);
    matches!((left.shared_node_id(), right.shared_node_id()), (Some(x), Some(y)) if x == y)
}

#[test]
fn boolean_values_are_checked_independently_of_path_presence() {
    type Values = BTreeMap<Vec<u8>, bool>;
    let source_a: Values = [
        (vec![0x31, 0], false),
        (vec![0x31, 1], true),
        (vec![0x31, 2], false),
    ]
    .into();
    let source_b: Values = [
        (vec![0x31, 0], true),
        (vec![0x31, 1], false),
        (vec![0x32, 0], true),
    ]
    .into();
    let build = |values: &Values| -> PathMap<bool> {
        let mut map = PathMap::new();
        for (path, value) in values {
            map.insert(path, *value);
        }
        map
    };
    let spots: Vec<Vec<u8>> = (0..8).map(|i| vec![0xa0, i, 0xb0]).collect();
    let mut a = PathMap::new();
    let mut b = PathMap::new();
    let a_source = build(&source_a);
    let b_source = build(&source_b);
    let mut a_values = Values::new();
    let mut b_values = Values::new();
    for spot in &spots {
        a.write_zipper_at_path(spot).graft_map(a_source.clone());
        b.write_zipper_at_path(spot).graft_map(b_source.clone());
        for (path, value) in &source_a {
            a_values.insert([spot.as_slice(), path].concat(), *value);
        }
        for (path, value) in &source_b {
            b_values.insert([spot.as_slice(), path].concat(), *value);
        }
    }
    assert!(same_node(&a, &spots[0], &spots[7]));
    let actual = |map: &PathMap<bool>| -> Values {
        map.iter().map(|(path, value)| (path, *value)).collect()
    };
    let mut joined = a_values.clone();
    for (path, value) in &b_values {
        joined
            .entry(path.clone())
            .and_modify(|old| *old |= *value)
            .or_insert(*value);
    }
    let met: Values = a_values
        .iter()
        .filter_map(|(path, value)| {
            b_values
                .get(path)
                .map(|other| (path.clone(), *value && *other))
        })
        .collect();
    let subtracted: Values = a_values
        .iter()
        .filter(|(path, value)| b_values.get(*path).is_none_or(|other| other != *value))
        .map(|(path, value)| (path.clone(), *value))
        .collect();
    let restricted: Values = a_values
        .iter()
        .filter(|(path, _)| (0..=path.len()).any(|n| b_values.contains_key(&path[..n].to_vec())))
        .map(|(path, value)| (path.clone(), *value))
        .collect();
    assert_eq!(actual(&a.join(&b)), joined);
    assert_eq!(actual(&a.meet(&b)), met);
    assert_eq!(actual(&a.subtract(&b)), subtracted);
    assert_eq!(actual(&a.restrict(&b)), restricted);

    let mut parent_edits = PathMap::new();
    for spot in &spots {
        parent_edits.insert([&spot[..spot.len() - 1], &[0xc0]].concat(), true);
    }
    let output = a.join(&parent_edits);
    assert!(same_node(&output, &spots[0], &spots[7]));
}

fn boundary_paths(map: &PathMap<()>) -> Vec<Vec<u8>> {
    let mut z = map.read_zipper();
    let mut paths = Vec::new();
    if z.shared_node_id().is_some() {
        paths.push(Vec::new());
    }
    while z.to_next_step() {
        if z.shared_node_id().is_some() {
            paths.push(z.path().to_vec());
        }
    }
    paths
}

/// Physical sharing groups observed in one map. Paths are retained, never IDs.
fn shared_groups(map: &PathMap<()>) -> Vec<Vec<Vec<u8>>> {
    let mut groups: Vec<Vec<Vec<u8>>> = Vec::new();
    for path in boundary_paths(map) {
        if let Some(group) = groups
            .iter_mut()
            .find(|group| same_node(map, &group[0], &path))
        {
            group.push(path);
        } else {
            groups.push(vec![path]);
        }
    }
    groups.into_iter().filter(|group| group.len() > 1).collect()
}

fn subtree(keys: &Keys, prefix: &[u8]) -> Keys {
    keys.iter()
        .filter_map(|key| key.strip_prefix(prefix).map(|suffix| suffix.to_vec()))
        .collect()
}

fn partition(map: &PathMap<()>, paths: &[Vec<u8>]) -> Vec<Vec<Vec<u8>>> {
    let mut groups: Vec<Vec<Vec<u8>>> = Vec::new();
    for path in paths {
        if let Some(group) = groups
            .iter_mut()
            .find(|group| same_node(map, &group[0], path))
        {
            group.push(path.clone());
        } else {
            groups.push(vec![path.clone()]);
        }
    }
    groups
}

/// Symbolic IDs model *known* sharing. They never contain physical node IDs.
/// An output computation gets one token when its operation and both input
/// tokens repeat, even if the current implementation failed to share it.
#[derive(Default)]
struct Tokens {
    next: u64,
    computed: BTreeMap<(u8, u64, u64, bool), u64>,
    born: BTreeMap<u64, usize>,
}

impl Tokens {
    fn fresh(&mut self) -> u64 {
        self.next += 1;
        self.next
    }

    fn seed_map(&mut self, state: &mut State) {
        for path in boundary_paths(&state.map) {
            let prior = state
                .tokens
                .iter()
                .find(|(other, _)| same_node(&state.map, other, &path))
                .map(|(_, token)| *token);
            state
                .tokens
                .insert(path, prior.unwrap_or_else(|| self.fresh()));
        }
    }

    fn after(
        &mut self,
        op: Op,
        a: &State,
        b: &State,
        output: &Keys,
        step: usize,
    ) -> BTreeMap<Vec<u8>, u64> {
        let paths: BTreeSet<_> = a.tokens.keys().chain(b.tokens.keys()).cloned().collect();
        let mut result = BTreeMap::new();
        for path in paths {
            let out = subtree(output, &path);
            if out.is_empty() {
                continue;
            }
            let left = subtree(&a.keys, &path);
            let right = subtree(&b.keys, &path);
            let ltoken = a.tokens.get(&path).copied().unwrap_or(0);
            let rtoken = b.tokens.get(&path).copied().unwrap_or(0);
            let token = if out == left && ltoken != 0 {
                ltoken
            } else if matches!(op, Op::Join | Op::Meet) && out == right && rtoken != 0 {
                rtoken
            } else {
                let context = matches!(op, Op::Restrict)
                    && (0..path.len()).any(|n| b.keys.contains(&path[..n].to_vec()));
                let key = (op as u8, ltoken, rtoken, context);
                if let Some(&existing) = self.computed.get(&key) {
                    existing
                } else {
                    let new = self.fresh();
                    self.computed.insert(key, new);
                    self.born.insert(new, step);
                    new
                }
            };
            result.insert(path, token);
        }
        result
    }
}

#[derive(Default)]
struct Counts {
    ops: [usize; 4],
    routes: [usize; 7],
    focused: usize,
    ordinary_groups: usize,
    ordinary_split: usize,
    result_groups: usize,
    result_split: usize,
    ideal_groups: usize,
    ideal_split: usize,
    inherited_split: usize,
    ordinary_examples: Vec<Example>,
    result_examples: Vec<Example>,
}

struct Example {
    seed: u64,
    trace: Vec<String>,
    path: Vec<u8>,
    physical_groups: usize,
}

struct Failure {
    details: String,
    trace: Vec<String>,
}

impl Example {
    fn new(seed: u64, trace: &str, path: &[u8], physical_groups: usize) -> Self {
        Self {
            seed,
            trace: trace.split("; ").map(str::to_owned).collect(),
            path: path.to_vec(),
            physical_groups,
        }
    }
}

fn print_examples(label: &str, examples: &[Example], total: usize) {
    eprintln!(
        "\n{label} examples (showing {} of {total}):",
        examples.len()
    );
    if examples.is_empty() {
        eprintln!("  None");
    }
    for (index, example) in examples.iter().enumerate() {
        eprintln!(
            "  {}. Seed {}: {} physical groups at {}",
            index + 1,
            example.seed,
            example.physical_groups,
            display_path(&example.path)
        );
        for step in &example.trace {
            eprintln!("     {step}");
        }
    }
}

fn check_ideal(output: &State, tokens: &Tokens, step: usize, counts: &mut Counts) {
    let mut groups: BTreeMap<u64, Vec<Vec<u8>>> = BTreeMap::new();
    for (path, &token) in &output.tokens {
        groups.entry(token).or_default().push(path.clone());
    }
    for (token, paths) in groups {
        if paths.len() < 2 {
            continue;
        }
        counts.ideal_groups += 1;
        let actual = partition(&output.map, &paths);
        if actual.len() > 1 {
            counts.ideal_split += 1;
            if tokens.born.get(&token).is_some_and(|&birth| birth < step) {
                counts.inherited_split += 1;
            }
        }
    }
}

fn check_ordinary(
    input: &State,
    output: &State,
    seed: u64,
    trace: &str,
    enforce: bool,
    counts: &mut Counts,
) -> Option<String> {
    for group in shared_groups(&input.map) {
        let surviving: Vec<_> = group
            .into_iter()
            .filter(|path| {
                let before = subtree(&input.keys, path);
                !before.is_empty() && before == subtree(&output.keys, path)
            })
            .collect();
        if surviving.len() < 2 {
            continue;
        }
        counts.ordinary_groups += 1;
        let actual = partition(&output.map, &surviving);
        if actual.len() > 1 {
            counts.ordinary_split += 1;
            if counts.ordinary_examples.len() < DISPLAY_LIMIT {
                counts.ordinary_examples.push(Example::new(
                    seed,
                    trace,
                    &surviving[0],
                    actual.len(),
                ));
            }
            if enforce {
                return Some(format!(
                    "ordinary sharing lost: seed={seed}, {trace}, surviving={surviving:?}, physical_groups={actual:?}"
                ));
            }
        }
    }
    None
}

fn check_result(
    left: &State,
    right: &State,
    output: &State,
    seed: u64,
    trace: &str,
    enforce: bool,
    counts: &mut Counts,
) -> Option<String> {
    let right_boundaries: BTreeSet<_> = boundary_paths(&right.map).into_iter().collect();
    let common: Vec<_> = boundary_paths(&left.map)
        .into_iter()
        .filter(|path| right_boundaries.contains(path))
        .collect();

    // Group identical ordered pairs of *physical* inputs. This asks for memoization
    // only where both operands already have known sharing. Different content that
    // happens to compare equal never creates an obligation.
    let mut pairs: Vec<Vec<Vec<u8>>> = Vec::new();
    for path in common {
        if let Some(group) = pairs.iter_mut().find(|group| {
            same_node(&left.map, &group[0], &path) && same_node(&right.map, &group[0], &path)
        }) {
            group.push(path);
        } else {
            pairs.push(vec![path]);
        }
    }

    for pair in pairs {
        let produced: Vec<_> = pair
            .into_iter()
            .filter(|path| {
                let result = subtree(&output.keys, path);
                !result.is_empty()
                    && result != subtree(&left.keys, path)
                    && result != subtree(&right.keys, path)
            })
            .collect();
        if produced.len() < 2 {
            continue;
        }
        counts.result_groups += 1;
        let actual = partition(&output.map, &produced);
        if actual.len() > 1 {
            counts.result_split += 1;
            if counts.result_examples.len() < DISPLAY_LIMIT {
                counts
                    .result_examples
                    .push(Example::new(seed, trace, &produced[0], actual.len()));
            }
            if enforce {
                return Some(format!(
                    "result sharing absent: seed={seed}, {trace}, inputs={produced:?}, physical_groups={actual:?}"
                ));
            }
        }
    }
    None
}

fn run_case(
    seed: u64,
    steps: usize,
    spot_limit: usize,
    enforce_ordinary: bool,
    enforce_results: bool,
    counts: &mut Counts,
) -> Option<Failure> {
    let mut shape_rng = Rng(seed ^ 0x9e37_79b9_7f4a_7c15);
    let mut spots = record_spots(&mut shape_rng);
    let s = fragment(&mut shape_rng, 0x31);
    let t = fragment(&mut shape_rng, 0x32);
    spots.truncate(spot_limit.max(2));
    let mut program_rng = Rng(seed ^ 0x51ed_1dea_17ab_1e55);
    let maps = [
        grafted(&s, &spots, &mut Rng(seed ^ 0x1000), 0),
        grafted(&t, &spots, &mut Rng(seed ^ 0x1001), 0),
        grafted(&s, &spots, &mut Rng(seed ^ 0x1002), 1),
        grafted(&t, &spots, &mut Rng(seed ^ 0x1003), 2),
    ];
    let mut pool: Vec<State> = maps.into_iter().collect();
    let mut tokens = Tokens::default();
    for (i, state) in pool.iter().enumerate() {
        assert_eq!(
            actual_keys(&state.map),
            state.keys,
            "construction: seed={seed}, map={i}"
        );
    }
    for state in &mut pool {
        tokens.seed_map(state);
    }
    assert!(
        !shared_groups(&pool[0].map).is_empty(),
        "grafting failed to establish sharing: seed={seed}"
    );

    let mut trace = Vec::new();
    // The first step guarantees a substantial result-sharing opportunity.
    // Later steps draw from all prior results and force operation combinations.
    for step in 0..steps {
        let (op, ai, bi) = if step == 0 {
            (Op::Join, 0, 1)
        } else {
            let op = match program_rng.below(4) {
                0 => Op::Join,
                1 => Op::Meet,
                2 => Op::Subtract,
                _ => Op::Restrict,
            };
            let ai = if step % 2 == 0 {
                pool.len() - 1
            } else {
                program_rng.below(pool.len())
            };
            (op, ai, program_rng.below(pool.len()))
        };
        let left = &pool[ai];
        let right = &pool[bi];
        let route = if step == 0 {
            Route::Whole
        } else {
            match op {
                Op::Join => match program_rng.below(5) {
                    0 => Route::Whole,
                    1 => Route::Zipper,
                    2 => Route::JoinMap,
                    3 => Route::JoinTake,
                    _ => Route::JoinInto,
                },
                Op::Meet => match program_rng.below(3) {
                    0 => Route::Whole,
                    1 => Route::Zipper,
                    _ => Route::Meet2,
                },
                Op::Restrict => match program_rng.below(3) {
                    0 => Route::Whole,
                    1 => Route::Zipper,
                    _ => Route::Restricting,
                },
                Op::Subtract => {
                    if program_rng.below(2) == 0 {
                        Route::Whole
                    } else {
                        Route::Zipper
                    }
                }
            }
        };
        let focus = if matches!(route, Route::Zipper) && program_rng.below(3) == 0 {
            spots[program_rng.below(spots.len())].as_slice()
        } else {
            &[]
        };
        counts.ops[op as usize] += 1;
        counts.routes[route as usize] += 1;
        counts.focused += usize::from(!focus.is_empty());
        let mut step_description = format!("step {step}: m{ai} {op:?} m{bi} via {route:?}");
        if !focus.is_empty() {
            step_description.push_str(&format!(" at {}", display_path(focus)));
        }
        trace.push(step_description);
        let output_keys = op.model_at(focus, &left.keys, &right.keys);
        let output = State {
            map: op.apply(route, focus, &left.map, &right.map),
            tokens: tokens.after(op, left, right, &output_keys, step),
            keys: output_keys,
        };
        let context = trace.join("; ");
        assert_eq!(
            actual_keys(&output.map),
            output.keys,
            "semantics: seed={seed}, {context}, spots={spots:?}, s={:?}, t={:?}",
            s.keys,
            t.keys
        );
        let failure = check_ordinary(left, &output, seed, &context, enforce_ordinary, counts)
            .or_else(|| {
                (ai != bi)
                    .then(|| {
                        check_ordinary(right, &output, seed, &context, enforce_ordinary, counts)
                    })
                    .flatten()
            })
            .or_else(|| {
                check_result(
                    left,
                    right,
                    &output,
                    seed,
                    &context,
                    enforce_results,
                    counts,
                )
            });
        if let Some(failure) = failure {
            return Some(Failure {
                details: format!(
                    "{failure}\nspots={spots:?}\nsource_s={:?}\nsource_t={:?}",
                    s.keys, t.keys
                ),
                trace,
            });
        }
        check_ideal(&output, &tokens, step, counts);
        pool.push(output);
    }
    None
}

#[cfg(test)]
fn projection_model(keys: &Keys, width: usize, meet: bool) -> Keys {
    let mut columns: BTreeMap<Vec<u8>, Keys> = BTreeMap::new();
    for key in keys {
        if key.len() > width {
            columns
                .entry(key[..width].to_vec())
                .or_default()
                .insert(key[width..].to_vec());
        }
    }
    let mut columns = columns.into_values();
    let Some(mut result) = columns.next() else {
        return Keys::new();
    };
    for column in columns {
        if meet {
            result = result.intersection(&column).cloned().collect();
        } else {
            result.extend(column);
        }
    }
    result
}

#[test]
fn observer_separates_shared_and_independently_built_fragments() {
    let mut rng = Rng(0xbee5);
    let spots = record_spots(&mut rng);
    let source = fragment(&mut rng, 0x43);
    let shared = grafted(&source, &spots, &mut rng, 0);
    assert!(same_node(&shared.map, &spots[0], &spots[1]));

    let mut rebuilt = PathMap::new();
    for spot in &spots[..2] {
        for suffix in &source.keys {
            let mut path = spot.clone();
            path.extend_from_slice(suffix);
            rebuilt.insert(&path, ());
        }
    }
    assert!(!same_node(&rebuilt, &spots[0], &spots[1]));
}

#[test]
fn hundred_parent_edits_retain_one_shared_child() {
    let mut rng = Rng(0x5421);
    let source = fragment(&mut rng, 0x41);
    let spots: Vec<Vec<u8>> = (0..100)
        .map(|i| vec![0xa0, (i >> 8) as u8, i as u8, 0xb0])
        .collect();
    let input = grafted(&source, &spots, &mut rng, 0);
    let mut output = State {
        map: input.map.clone(),
        keys: input.keys.clone(),
        tokens: BTreeMap::new(),
    };
    for spot in &spots {
        let mut sibling = spot[..spot.len() - 1].to_vec();
        sibling.push(0xc0);
        output.map.insert(&sibling, ());
        output.keys.insert(sibling);
    }
    assert_eq!(actual_keys(&output.map), output.keys);
    assert!(same_node(&input.map, &spots[0], &spots[99]));
    assert!(same_node(&output.map, &spots[0], &spots[99]));
    let mut counts = Counts::default();
    assert!(
        check_ordinary(
            &input,
            &output,
            0x5421,
            "100 parent edits",
            true,
            &mut counts,
        )
        .is_none()
    );
    assert!(counts.ordinary_groups > 0);
}

#[test]
fn parent_edits_preserve_shared_children_across_fanouts() {
    for branches in [1, 2, 4, 8, 16, 64] {
        let keys: Keys = (0..branches).map(|i| vec![0x31, i as u8, 0x7f]).collect();
        let source = from_keys(keys);
        let spots = vec![
            vec![0xa0, 0, 0xb0],
            vec![0xa0, 1, 0xb0],
            vec![0xa0, 2, 0xb0],
        ];
        let input = grafted(&source, &spots, &mut Rng(0x42), 0);
        let mut output = State {
            map: input.map.clone(),
            keys: input.keys.clone(),
            tokens: BTreeMap::new(),
        };
        for spot in &spots {
            let sibling = vec![spot[0], spot[1], 0xc0];
            output.map.insert(&sibling, ());
            output.keys.insert(sibling);
        }
        assert_eq!(actual_keys(&output.map), output.keys);
        let mut counts = Counts::default();
        assert!(
            check_ordinary(
                &input,
                &output,
                branches as u64,
                "fanout parent edits",
                true,
                &mut counts,
            )
            .is_none(),
            "fanout={branches}"
        );
        assert!(counts.ordinary_groups > 0, "fanout={branches}");
    }
}

#[test]
fn empty_and_root_value_operands_keep_surviving_sharing() {
    let source = from_keys([vec![0x31, 0], vec![0x31, 1]].into());
    let spots = vec![
        vec![0xa0, 0, 0xb0],
        vec![0xa0, 1, 0xb0],
        vec![0xa0, 2, 0xb0],
    ];
    let input = grafted(&source, &spots, &mut Rng(0x22), 0);
    let empty = PathMap::new();
    let joined = input.map.join(&empty);
    let subtracted = input.map.subtract(&empty);
    assert_eq!(actual_keys(&joined), input.keys);
    assert_eq!(actual_keys(&subtracted), input.keys);
    assert!(same_node(&joined, &spots[0], &spots[2]));
    assert!(same_node(&subtracted, &spots[0], &spots[2]));
    assert!(actual_keys(&input.map.meet(&empty)).is_empty());
    assert!(actual_keys(&input.map.restrict(&empty)).is_empty());

    let mut root_value = PathMap::new();
    root_value.insert(&[], ());
    let restricted = input.map.restrict(&root_value);
    assert_eq!(actual_keys(&restricted), input.keys);
    assert!(same_node(&restricted, &spots[0], &spots[2]));
    let joined_root = input.map.join(&root_value);
    let mut expected = input.keys.clone();
    expected.insert(Vec::new());
    assert_eq!(actual_keys(&joined_root), expected);
    assert!(same_node(&joined_root, &spots[0], &spots[2]));
}

#[test]
fn unvalued_paths_do_not_force_shared_fragment_copies() {
    let mut source = from_keys([vec![0x31, 0], vec![0x31, 1]].into());
    source.map.create_path(&[0x40, 0x50, 0x60]);
    let spots = vec![
        vec![0xa0, 0, 0xb0],
        vec![0xa0, 1, 0xb0],
        vec![0xa0, 2, 0xb0],
    ];
    let input = grafted(&source, &spots, &mut Rng(0x23), 0);
    assert!(same_node(&input.map, &spots[0], &spots[2]));
    let mut additions = PathMap::new();
    for spot in &spots {
        additions.insert([&spot[..spot.len() - 1], &[0xc0]].concat(), ());
    }
    let output = input.map.join(&additions);
    assert!(same_node(&output, &spots[0], &spots[2]));
    assert_eq!(actual_keys(&output).len(), input.keys.len() + spots.len());
}

#[test]
fn repeated_projection_results_are_measured() {
    let s = from_keys([vec![0x31, 0], vec![0x31, 1], vec![0x33, 0]].into());
    let t = from_keys([vec![0x31, 1], vec![0x32, 0], vec![0x32, 1]].into());
    let spots: Vec<Vec<u8>> = (0..5).map(|i| vec![0xa0, i, 0xb0]).collect();
    for meet in [false, true] {
        let mut input = PathMap::new();
        let mut input_keys = Keys::new();
        for spot in &spots {
            for (branch, fragment) in [(0, &s), (1, &t)] {
                let at = [spot.as_slice(), &[branch]].concat();
                input
                    .write_zipper_at_path(&at)
                    .graft_map(fragment.map.clone());
                append_fragment(&mut input_keys, &at, &fragment.keys);
            }
        }
        assert_eq!(actual_keys(&input), input_keys);
        assert!(same_node(
            &input,
            &[spots[0].as_slice(), &[0]].concat(),
            &[spots[4].as_slice(), &[0]].concat()
        ));
        assert!(same_node(
            &input,
            &[spots[0].as_slice(), &[1]].concat(),
            &[spots[4].as_slice(), &[1]].concat()
        ));

        let mut output = input.clone();
        let mut expected = Keys::new();
        for spot in &spots {
            let local = projection_model(&subtree(&input_keys, spot), 1, meet);
            append_fragment(&mut expected, spot, &local);
            if meet {
                output.write_zipper_at_path(spot).meet_k_path_into(1, true);
            } else {
                output.write_zipper_at_path(spot).join_k_path_into(1, true);
            }
        }
        assert_eq!(
            actual_keys(&output),
            expected,
            "repeated projection meet={meet}"
        );
        let physical = partition(&output, &spots);
        assert_eq!(expected.len(), spots.len() * if meet { 1 } else { 5 });
        eprintln!(
            "  Result-sharing projection ({}): {} occurrences in {} physical groups",
            if meet { "meet" } else { "join" },
            spots.len(),
            physical.len()
        );
    }
}

#[test]
fn seeded_projection_semantics() {
    for seed in 0..12 {
        let mut rng = Rng(seed ^ 0xd1b5_4a32);
        let spots = record_spots(&mut rng);
        let s = fragment(&mut rng, 0x31);
        let mut t_keys: Keys = s.keys.iter().take(s.keys.len() / 2).cloned().collect();
        t_keys.extend(fragment(&mut rng, 0x32).keys);
        let t = from_keys(t_keys);
        let mut map = PathMap::new();
        let mut keys = Keys::new();
        for (i, spot) in spots.iter().enumerate() {
            let fragment = if i % 3 == 0 { &t } else { &s };
            map.write_zipper_at_path(spot)
                .graft_map(fragment.map.clone());
            append_fragment(&mut keys, spot, &fragment.keys);
        }
        assert_eq!(
            actual_keys(&map),
            keys,
            "projection construction seed={seed}"
        );
        let width = spots[0].len();
        for meet in [false, true] {
            let mut output = map.clone();
            if meet {
                output.write_zipper().meet_k_path_into(width, true);
            } else {
                output.write_zipper().join_k_path_into(width, true);
            }
            assert_eq!(
                actual_keys(&output),
                projection_model(&keys, width, meet),
                "projection seed={seed}, width={width}, meet={meet}"
            );
        }
    }
}

#[test]
fn focused_projections_keep_other_shared_occurrences() {
    let mut rng = Rng(0x3210_5544);
    let spots = record_spots(&mut rng);
    let source = fragment(&mut rng, 0x35);
    let input = grafted(&source, &spots, &mut rng, 0);
    for meet in [false, true] {
        let mut output = State {
            map: input.map.clone(),
            keys: input.keys.clone(),
            tokens: BTreeMap::new(),
        };
        let focus = &spots[0];
        let local = projection_model(&subtree(&input.keys, focus), 1, meet);
        output.keys.retain(|path| !path.starts_with(focus));
        append_fragment(&mut output.keys, focus, &local);
        if meet {
            output
                .map
                .write_zipper_at_path(focus)
                .meet_k_path_into(1, true);
        } else {
            output
                .map
                .write_zipper_at_path(focus)
                .join_k_path_into(1, true);
        }
        assert_eq!(
            actual_keys(&output.map),
            output.keys,
            "focused projection meet={meet}"
        );
        let mut counts = Counts::default();
        assert!(
            check_ordinary(
                &input,
                &output,
                0x3210_5544,
                "focused projection",
                true,
                &mut counts,
            )
            .is_none()
        );
        assert!(counts.ordinary_groups > 0);
    }
}

#[cfg_attr(test, test)]
fn seeded_algebra_sharing_sweep() {
    let start = std::env::var("PATHMAP_SHARING_START")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);
    let cases = std::env::var("PATHMAP_SHARING_CASES")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(if cfg!(miri) { 1 } else { 24 });
    assert!(cases > 0, "PATHMAP_SHARING_CASES must be positive");
    let steps = std::env::var("PATHMAP_SHARING_STEPS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(8);
    assert!(steps > 0, "PATHMAP_SHARING_STEPS must be positive");
    let spot_limit = std::env::var("PATHMAP_SHARING_SPOTS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(usize::MAX);
    let enforce_ordinary = match std::env::var("PATHMAP_SHARING_ENFORCE_ORDINARY").as_deref() {
        Ok("0") | Err(_) => false,
        Ok("1") => true,
        Ok(value) => panic!("PATHMAP_SHARING_ENFORCE_ORDINARY must be 0 or 1, got {value:?}"),
    };
    let enforce_results = std::env::var("PATHMAP_SHARING_ENFORCE_RESULTS").as_deref() == Ok("1");
    let mut counts = Counts::default();
    let end = start.saturating_add(cases);
    for seed in start..end {
        if let Some(_) = run_case(
            seed,
            steps,
            spot_limit,
            enforce_ordinary,
            enforce_results,
            &mut counts,
        ) {
            let mut minimal_steps = steps;
            for candidate in 1..=steps {
                if run_case(
                    seed,
                    candidate,
                    spot_limit,
                    enforce_ordinary,
                    enforce_results,
                    &mut Counts::default(),
                )
                .is_some()
                {
                    minimal_steps = candidate;
                    break;
                }
            }
            let mut shape_rng = Rng(seed ^ 0x9e37_79b9_7f4a_7c15);
            let available_spots = record_spots(&mut shape_rng).len();
            let mut minimal_spots = spot_limit.min(available_spots).max(2);
            for candidate in 2..=minimal_spots {
                if run_case(
                    seed,
                    minimal_steps,
                    candidate,
                    enforce_ordinary,
                    enforce_results,
                    &mut Counts::default(),
                )
                .is_some()
                {
                    minimal_spots = candidate;
                    break;
                }
            }
            let failure = run_case(
                seed,
                minimal_steps,
                minimal_spots,
                enforce_ordinary,
                enforce_results,
                &mut Counts::default(),
            )
            .expect("minimized failure must replay");
            let mode = if failure.details.starts_with("ordinary sharing lost:") {
                "ORDINARY"
            } else {
                "RESULTS"
            };
            let kind = if mode == "ORDINARY" {
                "ordinary sharing"
            } else {
                "result sharing"
            };
            let replay_enforcement = if mode == "ORDINARY" {
                "PATHMAP_SHARING_ENFORCE_ORDINARY=1"
            } else {
                "PATHMAP_SHARING_ENFORCE_ORDINARY=0 PATHMAP_SHARING_ENFORCE_RESULTS=1"
            };
            let target = std::env::var_os("CARGO_TARGET_DIR")
                .map(std::path::PathBuf::from)
                .unwrap_or_else(|| std::path::PathBuf::from("target"));
            let dir = target.join("pathmap-sharing-failures");
            std::fs::create_dir_all(&dir).expect("create sharing failure directory");
            let artifact = dir.join(format!("seed-{seed}-{mode}.txt"));
            let details = &failure.details;
            let body = format!(
                "generator_version=4\nseed={seed}\nsteps={minimal_steps}\nspots={minimal_spots}\nmode={mode}\nreplay=PATHMAP_SHARING_START={seed} PATHMAP_SHARING_CASES=1 PATHMAP_SHARING_STEPS={minimal_steps} PATHMAP_SHARING_SPOTS={minimal_spots} {replay_enforcement} cargo run -p algebra-sharing-validation\n\n{details}\n"
            );
            std::fs::write(&artifact, body).expect("write sharing failure artifact");
            eprintln!("\nSHARING SWEEP — STRICT MODE: STOPPED");
            eprintln!("  First enforced loss: {kind}, seed {seed}");
            eprintln!(
                "  Checked {} of {} selected seeds; later seeds were not run.",
                seed - start + 1,
                end - start
            );
            let step_unit = if minimal_steps == 1 { "step" } else { "steps" };
            eprintln!(
                "  Minimized to {minimal_steps} {step_unit} and {minimal_spots} graft spots."
            );
            eprintln!("  Operation sequence:");
            for step in &failure.trace {
                eprintln!("    {step}");
            }
            eprintln!("  Details and replay: {}", artifact.display());
            if cfg!(test) {
                panic!("strict sharing validation stopped at seed {seed}");
            }
            std::process::exit(1);
        }
    }
    if start == 0 && cases >= 24 && steps >= 8 && spot_limit >= 12 {
        assert!(
            counts.ordinary_groups > 0,
            "no ordinary-sharing obligations exercised"
        );
        assert!(
            counts.result_groups > 0,
            "no result-sharing opportunities exercised"
        );
        assert!(
            counts.ops.iter().all(|&n| n > 0),
            "operation coverage: {:?}",
            counts.ops
        );
        assert!(
            counts.routes.iter().all(|&n| n > 0),
            "route coverage: {:?}",
            counts.routes
        );
        assert!(counts.focused > 0, "no focused zipper operation exercised");
    }
    let completed_mode = if !enforce_ordinary && !enforce_results {
        "REPORT MODE"
    } else {
        "STRICT MODE: NO ENFORCED LOSS FOUND"
    };
    eprintln!("\nSHARING SWEEP — {completed_mode}");
    eprintln!("  Seeds checked: {start}..{end} ({} total)", end - start);
    eprintln!(
        "  Operations: {} total, {} focused",
        counts.ops.iter().sum::<usize>(),
        counts.focused
    );
    eprintln!(
        "\n  Split = missed sharing (ordinary: unnecessary make-unique; result: result not reused)."
    );
    eprintln!("  Counts below are group checks after operations, not start/end inventories.");
    eprintln!("\n  Sharing opportunities     Checked   Split");
    eprintln!(
        "  Ordinary (surviving)   {:>7} {:>7}",
        counts.ordinary_groups, counts.ordinary_split
    );
    eprintln!(
        "  Result (computed)      {:>7} {:>7}",
        counts.result_groups, counts.result_split
    );
    eprintln!("\n  Symbolic model (overlaps the checks above):");
    eprintln!("    Groups expected to share: {}", counts.ideal_groups);
    eprintln!("    Physically split: {}", counts.ideal_split);
    eprintln!(
        "    Of those, first computed before this step: {}",
        counts.inherited_split
    );
    eprintln!(
        "\n  Operations: join {}, meet {}, subtract {}, restrict {}",
        counts.ops[0], counts.ops[1], counts.ops[2], counts.ops[3]
    );
    eprintln!(
        "  Routes: whole {}, zipper {}, join_map {}, join_take {}, join_into {}, meet_2 {}, restricting {}",
        counts.routes[0],
        counts.routes[1],
        counts.routes[2],
        counts.routes[3],
        counts.routes[4],
        counts.routes[5],
        counts.routes[6]
    );
    eprintln!(
        "\n  Examples: first {DISPLAY_LIMIT} per kind at most. Totals above include every checked seed."
    );
    eprintln!("  Splits count observations, not distinct seeds or root causes.");
    print_examples(
        "Ordinary sharing loss",
        &counts.ordinary_examples,
        counts.ordinary_split,
    );
    print_examples(
        "Missing result sharing",
        &counts.result_examples,
        counts.result_split,
    );
}
