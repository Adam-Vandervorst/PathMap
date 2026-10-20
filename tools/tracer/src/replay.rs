//! Replays a trace against real [PathMap]s, producing a [Frame] after each event

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use pathmap::PathMap;
use pathmap::utils::ByteMask;
use pathmap::utils::debug::zipper_tracing::{TraceOp, TraceSrc};
use pathmap::zipper::*;

use crate::ReplayValue;

/// The most children shown below one node.  The rest are counted in [NodeView::hidden]
const MAX_CHILDREN: usize = 12;
/// How many levels below a zipper's focus are shown
const FOCUS_DEPTH: usize = 3;
/// Beyond the regions around the zippers, the rest of a map is shown until it has this many nodes
const MAP_NODE_BUDGET: usize = 400;

/// Settings for a replay
#[derive(Clone, Debug)]
pub struct ReplayConfig {
    /// Zippers whose `root_prefix_path`s share at least this many leading bytes are placed on the same map
    pub prefix_len: usize,
}

impl Default for ReplayConfig {
    fn default() -> Self {
        Self { prefix_len: 2 }
    }
}

/// The result of replaying a trace
pub struct Replay<V: ReplayValue> {
    /// The state of each map after the last event
    pub maps: Vec<PathMap<V>>,
    /// A description of each map
    pub map_labels: Vec<String>,
    /// The state before the first event, followed by the state after each event
    pub frames: Vec<Frame>,
    /// Problems encountered during the replay
    pub warnings: Vec<String>,
}

/// The visible state after one event
#[derive(Clone, Debug)]
pub struct Frame {
    pub caption: String,
    /// The zipper that performed the event
    pub actor: Option<u64>,
    /// Traced zippers the event read from
    pub sources: Vec<u64>,
    /// The maps that are seeded, or that have had a zipper
    pub maps: Vec<MapView>,
}

/// The visible part of one map: the regions around its live zippers, and as much of the rest as fits
#[derive(Clone, Debug)]
pub struct MapView {
    pub map: usize,
    /// Keyed by absolute path.  Every node's parent is present, up to the map root (the empty path)
    pub nodes: BTreeMap<Vec<u8>, NodeView>,
    pub zippers: Vec<ZipperView>,
}

#[derive(Clone, Debug, Default)]
pub struct NodeView {
    /// `false` for the part of a zipper's path that doesn't exist in the trie
    pub exists: bool,
    /// The node is at or below the root of a live zipper
    pub accessible: bool,
    pub val: Option<String>,
    /// The number of children the node has in the trie
    pub child_count: usize,
    /// The number of the node's children that aren't shown
    pub hidden: usize,
}

#[derive(Clone, Debug)]
pub struct ZipperView {
    pub id: u64,
    /// Absolute path of the zipper's root
    pub root: Vec<u8>,
    /// Absolute path of the zipper's focus
    pub focus: Vec<u8>,
    pub writer: bool,
}

fn is_write_op<V>(op: &TraceOp<V>) -> bool {
    use TraceOp::*;
    matches!(op, ValWritten { .. } | GetValMut | GetValOrSetMut { .. } | GetValOrSetMutWith | SetVal { .. } |
        SetValAt { .. } | RemoveVal { .. } | ZipperHead | Graft { .. } | GraftSrcAt { .. } | GraftMap { .. } |
        GraftChildMaps { .. } | GraftMaskedBranches { .. } | JoinInto { .. } | JoinMapInto { .. } | JoinIntoTake { .. } |
        JoinKPathInto { .. } | MeetKPathInto { .. } | InsertPrefix { .. } | RemovePrefix { .. } | MeetInto { .. } |
        Meet2 { .. } | SubtractInto { .. } | Restrict { .. } | Restricting { .. } | TakeMap { .. } | RemoveBranches { .. } |
        RemoveSubtrie { .. } | RemoveUnmaskedBranches { .. } | CreatePath | PrunePath | PruneAscend)
}

fn traced_sources<V>(op: &TraceOp<V>) -> Vec<u64> {
    use TraceOp::*;
    let srcs: Vec<&TraceSrc<V>> = match op {
        Graft { src } | GraftSrcAt { src, .. } | GraftMaskedBranches { src, .. } | JoinInto { src } |
        JoinIntoTake { src, .. } | MeetInto { src, .. } | SubtractInto { src, .. } | Restrict { src } |
        Restricting { src } => vec![src],
        Meet2 { src_a, src_b } => vec![src_a, src_b],
        _ => vec![],
    };
    srcs.into_iter().filter_map(|src| match src { TraceSrc::Traced(id) => Some(*id), TraceSrc::Unknown(_) => None }).collect()
}

fn overlaps(a: &[u8], b: &[u8]) -> bool {
    a.starts_with(b) || b.starts_with(a)
}

/// A map that zippers may be assigned to
struct MapSlot {
    /// For maps not seeded from a file, the leading bytes shared by the zippers on the map.  `None`
    /// for a map made for a zipper whose `root_prefix_path` is too short to share
    key: Option<Vec<u8>>,
    /// For maps seeded from a file, the index of the seed
    seed: Option<usize>,
    label: String,
    /// Live zippers, their `root_prefix_path`s, and whether they're writers
    live: Vec<(u64, Vec<u8>, bool)>,
}

/// Decides which map each zipper is on.  Returns the map index of each zipper id, and the labels of maps
/// added beyond the seeded ones
fn assign_maps<V: ReplayValue>(events: &[(u64, TraceOp<V>)], seeds: &[(String, PathMap<V>)], writers: &HashSet<usize>, cfg: &ReplayConfig, warnings: &mut Vec<String>) -> (HashMap<u64, usize>, Vec<String>) {
    let mut slots: Vec<MapSlot> = seeds.iter().enumerate().map(|(idx, (label, _))| MapSlot { key: None, seed: Some(idx), label: label.clone(), live: vec![] }).collect();
    let mut map_of: HashMap<u64, usize> = HashMap::new();
    for (idx, (id, op)) in events.iter().enumerate() {
        match op {
            TraceOp::Created { root_prefix_path: rpp, .. } => {
                let is_writer = writers.contains(&idx);
                //A reused id is the same zipper, so it stays on its map
                if let Some(&m) = map_of.get(id) {
                    slots[m].live.retain(|(live_id, _, _)| live_id != id);
                    slots[m].live.push((*id, rpp.clone(), is_writer));
                    continue
                }
                //Putting the zipper on a map where it would overlap a live writer would break exclusivity
                let fits = |slot: &MapSlot| !slot.live.iter().any(|(_, live_rpp, live_writer)| overlaps(live_rpp, rpp) && (is_writer || *live_writer));
                let key = (rpp.len() >= cfg.prefix_len).then(|| rpp[..cfg.prefix_len].to_vec());
                let seeded = slots.iter().position(|slot| {
                    slot.seed.is_some_and(|seed| {
                        let seed = &seeds[seed].1;
                        seed.path_exists_at(rpp) || key.as_ref().is_some_and(|key| seed.path_exists_at(key))
                    })
                });
                let shared = slots.iter().position(|slot| slot.seed.is_none() && key.is_some() && slot.key == key);
                let m = match seeded.or(shared) {
                    Some(m) if fits(&slots[m]) => m,
                    candidate => {
                        if let Some(m) = candidate {
                            warnings.push(format!("z{id} would overlap a live writer on {}, so it was given its own map", slots[m].label));
                        }
                        let label = match &key {
                            Some(key) => format!("map {} ({}…)", slots.len(), quote_path(key)),
                            None => format!("map {} (z{id})", slots.len()),
                        };
                        slots.push(MapSlot { key: key.clone(), seed: None, label, live: vec![] });
                        slots.len() - 1
                    }
                };
                slots[m].live.push((*id, rpp.clone(), is_writer));
                map_of.insert(*id, m);
            },
            TraceOp::Dropped => {
                if let Some(&m) = map_of.get(id) {
                    slots[m].live.retain(|(live_id, _, _)| live_id != id);
                }
            },
            _ => {}
        }
    }
    let labels = slots.into_iter().map(|slot| slot.label).collect();
    (map_of, labels)
}

/// A replay zipper.  Zippers that perform any write op are replayed as write zippers
enum Live<'h, V: ReplayValue> {
    Read(ReadZipperTracked<'h, 'static, V>),
    Write(WriteZipperTracked<'h, 'static, V>),
}

struct LiveZipper<'h, V: ReplayValue> {
    z: Live<'h, V>,
    map: usize,
    root: Vec<u8>,
}

macro_rules! with_z {
    ($live:expr, $z:ident => $body:expr) => {
        match $live {
            Live::Read($z) => $body,
            Live::Write($z) => $body,
        }
    };
}

/// The source argument of a write op, resolved to something that can be passed to the op
enum Src<'s, 'h, V: ReplayValue> {
    Read(&'s ReadZipperTracked<'h, 'static, V>),
    Write(&'s WriteZipperTracked<'h, 'static, V>),
    Map(PathMap<V>),
}

macro_rules! with_src {
    ($src:expr, $s:ident => $body:expr) => {
        match $src {
            Src::Read(z) => { let $s = z; $body },
            Src::Write(z) => { let $s = z; $body },
            Src::Map(map) => { let rz = map.read_zipper(); let $s = &rz; $body },
        }
    };
}

fn entries_map<V: ReplayValue>(entries: &[(Vec<u8>, V)]) -> PathMap<V> {
    entries.iter().cloned().collect()
}

fn resolve_src<'s, 'h, V: ReplayValue>(src: &TraceSrc<V>, live: &'s HashMap<u64, LiveZipper<'h, V>>) -> Result<Src<'s, 'h, V>, String> {
    match src {
        TraceSrc::Unknown(entries) => Ok(Src::Map(entries_map(entries))),
        TraceSrc::Traced(id) => match live.get(id).map(|lz| &lz.z) {
            Some(Live::Read(z)) => Ok(Src::Read(z)),
            Some(Live::Write(z)) => Ok(Src::Write(z)),
            None => Err(format!("source z{id} isn't live")),
        }
    }
}

/// Gives a write zipper the default [ZipperIteration] methods, which replay needs because the original
/// write zipper may have had them
struct IterAdapter<'a, Z>(&'a mut Z);

impl<Z: Zipper> Zipper for IterAdapter<'_, Z> {
    fn path_exists(&self) -> bool { self.0.path_exists() }
    fn is_val(&self) -> bool { self.0.is_val() }
    fn child_count(&self) -> usize { self.0.child_count() }
    fn child_mask(&self) -> ByteMask { self.0.child_mask() }
}

impl<Z: ZipperMoving> ZipperMoving for IterAdapter<'_, Z> {
    fn depth(&self) -> usize { self.0.depth() }
    fn focus_byte(&self) -> Option<u8> { self.0.focus_byte() }
    fn val_count(&self) -> usize { self.0.val_count() }
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) { self.0.descend_to(k) }
    fn ascend(&mut self, steps: usize) -> usize { self.0.ascend(steps) }
    fn ascend_until(&mut self) -> usize { self.0.ascend_until() }
    fn ascend_until_branch(&mut self) -> usize { self.0.ascend_until_branch() }
}

impl<Z: ZipperMoving> ZipperIteration for IterAdapter<'_, Z> {}

/// Applies an op that only moves the zipper.  Returns `false` if `op` isn't such an op
fn apply_move<V, Z: ZipperMoving + ZipperPath>(z: &mut Z, op: &TraceOp<V>) -> bool {
    use TraceOp::*;
    match op {
        Reset => z.reset(),
        DescendTo { path } => z.descend_to(path),
        DescendToCheck { path } => { z.descend_to_check(path); },
        DescendToExisting { path } => { z.descend_to_existing(path); },
        DescendToVal { path } => { z.descend_to_val(path); },
        DescendToByte { byte } => z.descend_to_byte(*byte),
        DescendToExistingByte { byte } => { z.descend_to_existing_byte(*byte); },
        DescendIndexedByte { idx } => { z.descend_indexed_byte(*idx); },
        DescendFirstByte => { z.descend_first_byte(); },
        DescendLastByte => { z.descend_last_byte(); },
        DescendUntil => { z.descend_until(); },
        DescendUntilMaxBytes { max_bytes } => { z.descend_until_max_bytes(*max_bytes); },
        Ascend { steps } => { z.ascend(*steps); },
        AscendByte => { z.ascend_byte(); },
        AscendUntil => { z.ascend_until(); },
        AscendUntilBranch => { z.ascend_until_branch(); },
        ToNextSiblingByte => { z.to_next_sibling_byte(); },
        ToPrevSiblingByte => { z.to_prev_sibling_byte(); },
        ToNextStep => { z.to_next_step(); },
        MoveToPath { path } => { z.move_to_path(path); },
        _ => return false,
    }
    true
}

/// Applies an iteration op.  Returns `false` if `op` isn't one
fn apply_iteration<V, Z: ZipperIteration>(z: &mut Z, op: &TraceOp<V>) -> bool {
    use TraceOp::*;
    match op {
        ToNextVal | ToNextGetVal => { z.to_next_val(); },
        DescendLastPath => { z.descend_last_path(); },
        DescendFirstKPath { k } => { z.descend_first_k_path(*k); },
        ToNextKPath { k } => { z.to_next_k_path(*k); },
        _ => return false,
    }
    true
}

/// Applies a write op to `w`.  `live` holds the other live zippers, which may be sources
fn apply_write<'h, V: ReplayValue>(w: &mut WriteZipperTracked<'h, 'static, V>, op: &TraceOp<V>, live: &mut HashMap<u64, LiveZipper<'h, V>>) -> Result<(), String> {
    use TraceOp::*;
    match op {
        GetValMut | GetValOrSetMutWith | ZipperHead => {},
        ValWritten { val } => { w.set_val(val.clone()); },
        GetValOrSetMut { default } => { w.get_val_or_set_mut(default.clone()); },
        SetVal { val } => { w.set_val(val.clone()); },
        SetValAt { path, val } => { w.set_val_at(path, val.clone()); },
        RemoveVal { prune } => { w.remove_val(*prune); },
        Graft { src } => with_src!(resolve_src(src, live)?, s => w.graft(s)),
        GraftSrcAt { src, path } => with_src!(resolve_src(src, live)?, s => w.graft_src_at(s, path)),
        GraftMap { map } => w.graft_map(entries_map(map)),
        GraftChildMaps { child_mask, maps, remove_unset } => w.graft_child_maps(*child_mask, maps.iter().map(|map| entries_map(map)), *remove_unset),
        GraftMaskedBranches { src, child_mask, remove_unset } => with_src!(resolve_src(src, live)?, s => w.graft_masked_branches(s, *child_mask, *remove_unset)),
        JoinInto { src } => { with_src!(resolve_src(src, live)?, s => w.join_into(s)); },
        JoinMapInto { map } => { w.join_map_into(entries_map(map)); },
        JoinIntoTake { src, prune } => {
            //The source must be taken from too, so it can't be shared
            if let TraceSrc::Traced(src_id) = src {
                if let Some(mut src_lz) = live.remove(src_id) {
                    let result = match &mut src_lz.z {
                        Live::Write(src_w) => { w.join_into_take(src_w, *prune); Ok(()) },
                        Live::Read(_) => Err(format!("join_into_take source z{src_id} isn't a write zipper")),
                    };
                    live.insert(*src_id, src_lz);
                    return result
                }
            }
            with_src!(resolve_src(src, live)?, s => w.join_into(s));
        },
        JoinKPathInto { byte_cnt, prune } => { w.join_k_path_into(*byte_cnt, *prune); },
        MeetKPathInto { byte_cnt, prune } => { w.meet_k_path_into(*byte_cnt, *prune); },
        InsertPrefix { prefix } => { w.insert_prefix(prefix); },
        RemovePrefix { n } => { w.remove_prefix(*n); },
        MeetInto { src, prune } => { with_src!(resolve_src(src, live)?, s => w.meet_into(s, *prune)); },
        Meet2 { src_a, src_b } => {
            let src_b = resolve_src(src_b, live)?;
            with_src!(resolve_src(src_a, live)?, a => with_src!(src_b, b => { w.meet_2(a, b); }));
        },
        SubtractInto { src, prune } => { with_src!(resolve_src(src, live)?, s => w.subtract_into(s, *prune)); },
        Restrict { src } => { with_src!(resolve_src(src, live)?, s => w.restrict(s)); },
        Restricting { src } => { with_src!(resolve_src(src, live)?, s => w.restricting(s)); },
        TakeMap { prune } => { w.take_map(*prune); },
        RemoveBranches { prune } => { w.remove_branches(*prune); },
        RemoveSubtrie { prune } => { w.remove_subtrie(*prune); },
        RemoveUnmaskedBranches { mask, prune } => w.remove_unmasked_branches(*mask, *prune),
        CreatePath => { w.create_path(); },
        PrunePath => { w.prune_path(); },
        PruneAscend => { w.prune_ascend(); },
        _ => {},
    }
    Ok(())
}

/// Returns the index of the `Created` event of each zipper lifetime that performs a write.  Write and read zippers
/// are replayed differently, and an id may be reused, so this is decided per lifetime rather than per id
fn writer_lifetimes<V>(events: &[(u64, TraceOp<V>)]) -> HashSet<usize> {
    let mut current: HashMap<u64, usize> = HashMap::new();
    let mut writers = HashSet::new();
    for (idx, (id, op)) in events.iter().enumerate() {
        if let TraceOp::Created { .. } = op {
            current.insert(*id, idx);
        }
        if is_write_op(op) {
            writers.extend(current.get(id));
        }
        //A join_into_take source has its focus taken, so it's a writer too
        if let TraceOp::JoinIntoTake { src: TraceSrc::Traced(src_id), .. } = op {
            writers.extend(current.get(src_id));
        }
    }
    writers
}

/// Replays `events` and records a frame after each one
///
/// `seeds` are the initial contents of maps loaded from files, in priority order.  When a zipper's
/// `root_prefix_path` is compatible with more than one seed, the first one wins
pub fn replay<V: ReplayValue>(events: &[(u64, TraceOp<V>)], seeds: Vec<(String, PathMap<V>)>, cfg: &ReplayConfig) -> Replay<V> {
    let mut warnings = Vec::new();
    let writers = writer_lifetimes(events);
    let (map_of, map_labels) = assign_maps(events, &seeds, &writers, cfg, &mut warnings);
    let map_count = map_labels.len();
    let mut shown: Vec<bool> = (0..map_count).map(|m| m < seeds.len()).collect();
    let mut maps: Vec<PathMap<V>> = seeds.into_iter().map(|(_, map)| map).collect();
    maps.resize_with(map_count, PathMap::new);
    //The real maps are only reachable through the replay zippers, which can't see outside their regions, so each
    // map is mirrored here.  Only writers change a map, so refreshing each live writer's region keeps the mirror exact
    let mut mirrors = maps.clone();

    let mut frames = Vec::with_capacity(events.len() + 1);
    {
        let heads: Vec<_> = maps.iter_mut().map(|map| map.zipper_head()).collect();
        let mut live: HashMap<u64, LiveZipper<'_, V>> = HashMap::new();
        frames.push(Frame { caption: "start".to_string(), actor: None, sources: vec![], maps: capture(&mut live, &mut mirrors, &shown) });
        for (idx, (id, op)) in events.iter().enumerate() {
            let mut caption = format!("z{id}.{}", call_text(op));
            let result = step(*id, op, &heads, &map_of, writers.contains(&idx), &mut live);
            if let Err(err) = result {
                caption.push_str(&format!("  ⚠ {err}"));
                warnings.push(format!("event {idx} (z{id}): {err}"));
            }
            if let Some(&m) = map_of.get(id) {
                shown[m] = true;
            }
            frames.push(Frame { caption, actor: Some(*id), sources: traced_sources(op), maps: capture(&mut live, &mut mirrors, &shown) });
        }
        //The zippers borrow the heads, so they must go first
        drop(live);
    }
    Replay { maps, map_labels, frames, warnings }
}

/// Applies one event.  `writer` says whether a zipper being created will write during its life
fn step<'h, V: ReplayValue>(id: u64, op: &TraceOp<V>, heads: &'h [ZipperHead<'_, '_, V>], map_of: &HashMap<u64, usize>, writer: bool, live: &mut HashMap<u64, LiveZipper<'h, V>>) -> Result<(), String> {
    match op {
        TraceOp::Created { root_prefix_path, path, .. } => {
            live.remove(&id);
            let map = map_of[&id];
            //SAFETY: The traced program obeyed PathMap's exclusivity rules, and map assignment never puts
            // a zipper where it would overlap a live writer, so these zippers can't conflict
            let mut z = if writer {
                Live::Write(unsafe { heads[map].write_zipper_at_exclusive_path_unchecked(root_prefix_path) })
            } else {
                Live::Read(unsafe { heads[map].read_zipper_at_path_unchecked(root_prefix_path) })
            };
            with_z!(&mut z, z => z.descend_to(path));
            live.insert(id, LiveZipper { z, map, root: root_prefix_path.clone() });
        },
        TraceOp::Dropped => { live.remove(&id); },
        _ => {
            let Some(mut lz) = live.remove(&id) else {
                return Err("zipper isn't live".to_string())
            };
            let result = match &mut lz.z {
                Live::Read(r) => {
                    if !apply_move(r, op) && !apply_iteration(r, op) && is_write_op(op) {
                        Err("write op on a read zipper".to_string())
                    } else {
                        Ok(())
                    }
                },
                Live::Write(w) => {
                    if apply_move(w, op) || apply_iteration(&mut IterAdapter(w), op) {
                        Ok(())
                    } else {
                        apply_write(w, op, live)
                    }
                }
            };
            live.insert(id, lz);
            result?;
        }
    }
    Ok(())
}

/// Builds the visible part of every shown map
fn capture<V: ReplayValue>(live: &mut HashMap<u64, LiveZipper<'_, V>>, mirrors: &mut [PathMap<V>], shown: &[bool]) -> Vec<MapView> {
    let mut views: Vec<MapView> = (0..mirrors.len()).map(|map| MapView { map, nodes: BTreeMap::new(), zippers: vec![] }).collect();
    let mut ids: Vec<u64> = live.keys().copied().collect();
    ids.sort();
    for id in ids {
        let lz = live.get_mut(&id).unwrap();
        let (root_exists, rel, snapshot) = with_z!(&mut lz.z, z => snapshot(z));
        let writer = matches!(lz.z, Live::Write(_));
        if writer {
            mirrors[lz.map].write_zipper_at_path(&lz.root).graft_map(snapshot.clone());
        }
        let view = &mut views[lz.map];
        add_zipper_region(&mut view.nodes, &lz.root, root_exists, &rel, &snapshot);
        let mut focus = lz.root.clone();
        focus.extend_from_slice(&rel);
        view.zippers.push(ZipperView { id, root: lz.root.clone(), focus, writer });
    }
    views.retain(|view| shown[view.map]);
    for view in &mut views {
        add_context(&mut view.nodes, &mirrors[view.map]);
        let mut shown_children: HashMap<Vec<u8>, usize> = HashMap::new();
        for path in view.nodes.keys().filter(|path| !path.is_empty()) {
            *shown_children.entry(path[..path.len() - 1].to_vec()).or_default() += 1;
        }
        for (path, node) in view.nodes.iter_mut() {
            node.hidden = node.child_count.saturating_sub(shown_children.get(path).copied().unwrap_or(0));
            node.accessible = view.zippers.iter().any(|z| path.starts_with(&z.root));
        }
    }
    views
}

/// Adds the rest of the map, nearest the nodes already shown first, until the map has [MAP_NODE_BUDGET] nodes
fn add_context<V: ReplayValue>(nodes: &mut BTreeMap<Vec<u8>, NodeView>, mirror: &PathMap<V>) {
    nodes.entry(vec![]).or_default().exists = true;
    let mut frontier: Vec<Vec<u8>> = nodes.iter().filter(|(_, node)| node.exists).map(|(path, _)| path.clone()).collect();
    frontier.sort_by_key(|path| path.len());
    let mut queue: VecDeque<Vec<u8>> = frontier.into();
    while let Some(path) = queue.pop_front() {
        let rz = mirror.read_zipper_at_path(&path);
        if !rz.path_exists() {
            continue
        }
        let node = nodes.get_mut(&path).unwrap();
        node.child_count = node.child_count.max(rz.child_count());
        if node.val.is_none() {
            node.val = rz.val().and_then(ReplayValue::display);
        }
        for byte in rz.child_mask().iter().take(MAX_CHILDREN) {
            let mut child = path.clone();
            child.push(byte);
            if nodes.contains_key(&child) {
                continue
            }
            if nodes.len() >= MAP_NODE_BUDGET {
                return
            }
            let child_rz = mirror.read_zipper_at_path(&child);
            nodes.insert(child.clone(), NodeView { exists: true, val: child_rz.val().and_then(ReplayValue::display), child_count: child_rz.child_count(), ..Default::default() });
            queue.push_back(child);
        }
    }
}

/// Captures the trie below a zipper's root, without disturbing the zipper.  Returns whether the root
/// exists, the focus relative to the root, and the trie
fn snapshot<V: ReplayValue, Z: ZipperMoving + ZipperPath + ZipperInfallibleSubtries<V>>(z: &mut Z) -> (bool, Vec<u8>, PathMap<V>) {
    let rel = z.path().to_vec();
    z.reset();
    let root_exists = z.path_exists();
    let snapshot = z.make_map();
    z.descend_to(&rel);
    (root_exists, rel, snapshot)
}

fn add_node(nodes: &mut BTreeMap<Vec<u8>, NodeView>, path: &[u8], exists: bool, val: Option<String>, child_count: usize) {
    let node = nodes.entry(path.to_vec()).or_default();
    node.exists |= exists;
    node.child_count = node.child_count.max(child_count);
    if node.val.is_none() {
        node.val = val;
    }
}

/// Adds the nodes on the zipper's path, their children, and the subtrie below the focus
fn add_zipper_region<V: ReplayValue>(nodes: &mut BTreeMap<Vec<u8>, NodeView>, root: &[u8], root_exists: bool, rel: &[u8], snapshot: &PathMap<V>) {
    for len in 0..root.len() {
        add_node(nodes, &root[..len], root_exists, None, 0);
    }
    let mut rz = snapshot.read_zipper();
    let mut path = root.to_vec();
    let mut existing = 0;
    while root_exists && rz.path_exists() {
        let at_focus = existing == rel.len();
        add_node(nodes, &path, true, rz.val().and_then(ReplayValue::display), rz.child_count());
        add_children(nodes, &mut rz, &mut path, if at_focus { FOCUS_DEPTH } else { 1 });
        if at_focus {
            return
        }
        rz.descend_to_byte(rel[existing]);
        path.push(rel[existing]);
        existing += 1;
    }
    //The rest of the path doesn't exist in the trie
    add_node(nodes, &path, false, None, 0);
    for &byte in &rel[existing..] {
        path.push(byte);
        add_node(nodes, &path, false, None, 0);
    }
}

fn add_children<V: ReplayValue, Z: ZipperMoving + ZipperValues<V>>(nodes: &mut BTreeMap<Vec<u8>, NodeView>, rz: &mut Z, path: &mut Vec<u8>, depth: usize) {
    let mask = rz.child_mask();
    for (idx, byte) in mask.iter().enumerate() {
        if idx == MAX_CHILDREN {
            break
        }
        rz.descend_to_byte(byte);
        path.push(byte);
        add_node(nodes, path, true, rz.val().and_then(ReplayValue::display), rz.child_count());
        if depth > 1 {
            add_children(nodes, rz, path, depth - 1);
        }
        path.pop();
        rz.ascend_byte();
    }
}

/// Renders a path as a quoted string, escaping bytes that aren't printable ascii
pub fn quote_path(path: &[u8]) -> String {
    let mut out = String::from("\"");
    for &byte in path {
        match byte {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            0x20..=0x7e => out.push(byte as char),
            _ => out.push_str(&format!("\\x{byte:02x}")),
        }
    }
    out.push('"');
    out
}

fn quote_byte(byte: u8) -> String {
    let quoted = quote_path(&[byte]);
    format!("'{}'", &quoted[1..quoted.len() - 1])
}

fn val_text<V: ReplayValue>(val: &V) -> String {
    val.display().unwrap_or_else(|| format!("{val:?}"))
}

fn mask_text(mask: &ByteMask) -> String {
    let bytes: Vec<String> = mask.iter().map(quote_byte).collect();
    format!("{{{}}}", bytes.join(", "))
}

fn src_text<V>(src: &TraceSrc<V>) -> String {
    match src {
        TraceSrc::Traced(id) => format!("z{id}"),
        TraceSrc::Unknown(entries) => format!("<untraced: {} values>", entries.len()),
    }
}

fn map_text<V>(entries: &[(Vec<u8>, V)]) -> String {
    format!("<map: {} values>", entries.len())
}

/// Renders an op as the method call it records
fn call_text<V: ReplayValue>(op: &TraceOp<V>) -> String {
    use TraceOp::*;
    match op {
        Created { type_name, root_prefix_path, path } => {
            let short_name = type_name.split('<').next().unwrap_or(type_name).rsplit("::").next().unwrap_or(type_name);
            let mut text = format!("created({short_name}, root: {}", quote_path(root_prefix_path));
            if !path.is_empty() {
                text.push_str(&format!(", focus: {}", quote_path(path)));
            }
            text.push(')');
            text
        },
        Dropped => "drop()".to_string(),
        ValWritten { val } => format!("<value written through &mut: {}>", val_text(val)),
        PathExists => "path_exists()".to_string(),
        IsVal => "is_val()".to_string(),
        ChildCount => "child_count()".to_string(),
        ChildMask => "child_mask()".to_string(),
        Val => "val()".to_string(),
        ValAt { path } => format!("val_at({})", quote_path(path)),
        NativeSubtries => "native_subtries()".to_string(),
        TryMakeMap => "try_make_map()".to_string(),
        TrieRef => "trie_ref()".to_string(),
        Depth => "depth()".to_string(),
        AtRoot => "at_root()".to_string(),
        FocusByte => "focus_byte()".to_string(),
        Reset => "reset()".to_string(),
        ValCount => "val_count()".to_string(),
        DescendTo { path } => format!("descend_to({})", quote_path(path)),
        DescendToCheck { path } => format!("descend_to_check({})", quote_path(path)),
        DescendToExisting { path } => format!("descend_to_existing({})", quote_path(path)),
        DescendToVal { path } => format!("descend_to_val({})", quote_path(path)),
        DescendToByte { byte } => format!("descend_to_byte({})", quote_byte(*byte)),
        DescendToExistingByte { byte } => format!("descend_to_existing_byte({})", quote_byte(*byte)),
        DescendIndexedByte { idx } => format!("descend_indexed_byte({idx})"),
        DescendFirstByte => "descend_first_byte()".to_string(),
        DescendLastByte => "descend_last_byte()".to_string(),
        DescendUntil => "descend_until()".to_string(),
        DescendUntilMaxBytes { max_bytes } => format!("descend_until_max_bytes({max_bytes})"),
        Ascend { steps } => format!("ascend({steps})"),
        AscendByte => "ascend_byte()".to_string(),
        AscendUntil => "ascend_until()".to_string(),
        AscendUntilBranch => "ascend_until_branch()".to_string(),
        ToNextSiblingByte => "to_next_sibling_byte()".to_string(),
        ToPrevSiblingByte => "to_prev_sibling_byte()".to_string(),
        ToNextStep => "to_next_step()".to_string(),
        ToNextVal => "to_next_val()".to_string(),
        DescendLastPath => "descend_last_path()".to_string(),
        DescendFirstKPath { k } => format!("descend_first_k_path({k})"),
        ToNextKPath { k } => format!("to_next_k_path({k})"),
        Path => "path()".to_string(),
        MoveToPath { path } => format!("move_to_path({})", quote_path(path)),
        OriginPath => "origin_path()".to_string(),
        RootPrefixPath => "root_prefix_path()".to_string(),
        GetVal => "get_val()".to_string(),
        GetValAt { path } => format!("get_val_at({})", quote_path(path)),
        ToNextGetVal => "to_next_get_val()".to_string(),
        MakeMap => "make_map()".to_string(),
        GetTrieRef => "get_trie_ref()".to_string(),
        FocusFactor => "focus_factor()".to_string(),
        FactorCount => "factor_count()".to_string(),
        PathIndices => "path_indices()".to_string(),
        GetValMut => "get_val_mut()".to_string(),
        GetValOrSetMut { default } => format!("get_val_or_set_mut({})", val_text(default)),
        GetValOrSetMutWith => "get_val_or_set_mut_with(<closure>)".to_string(),
        SetVal { val } => format!("set_val({})", val_text(val)),
        SetValAt { path, val } => format!("set_val_at({}, {})", quote_path(path), val_text(val)),
        RemoveVal { prune } => format!("remove_val({prune})"),
        ZipperHead => "zipper_head()".to_string(),
        Graft { src } => format!("graft({})", src_text(src)),
        GraftSrcAt { src, path } => format!("graft_src_at({}, {})", src_text(src), quote_path(path)),
        GraftMap { map } => format!("graft_map({})", map_text(map)),
        GraftChildMaps { child_mask, maps, remove_unset } => format!("graft_child_maps({}, <{} maps>, {remove_unset})", mask_text(child_mask), maps.len()),
        GraftMaskedBranches { src, child_mask, remove_unset } => format!("graft_masked_branches({}, {}, {remove_unset})", src_text(src), mask_text(child_mask)),
        JoinInto { src } => format!("join_into({})", src_text(src)),
        JoinMapInto { map } => format!("join_map_into({})", map_text(map)),
        JoinIntoTake { src, prune } => format!("join_into_take({}, {prune})", src_text(src)),
        JoinKPathInto { byte_cnt, prune } => format!("join_k_path_into({byte_cnt}, {prune})"),
        MeetKPathInto { byte_cnt, prune } => format!("meet_k_path_into({byte_cnt}, {prune})"),
        InsertPrefix { prefix } => format!("insert_prefix({})", quote_path(prefix)),
        RemovePrefix { n } => format!("remove_prefix({n})"),
        MeetInto { src, prune } => format!("meet_into({}, {prune})", src_text(src)),
        Meet2 { src_a, src_b } => format!("meet_2({}, {})", src_text(src_a), src_text(src_b)),
        SubtractInto { src, prune } => format!("subtract_into({}, {prune})", src_text(src)),
        Restrict { src } => format!("restrict({})", src_text(src)),
        Restricting { src } => format!("restricting({})", src_text(src)),
        TakeMap { prune } => format!("take_map({prune})"),
        RemoveBranches { prune } => format!("remove_branches({prune})"),
        RemoveSubtrie { prune } => format!("remove_subtrie({prune})"),
        RemoveUnmaskedBranches { mask, prune } => format!("remove_unmasked_branches({}, {prune})", mask_text(mask)),
        CreatePath => "create_path()".to_string(),
        PrunePath => "prune_path()".to_string(),
        PruneAscend => "prune_ascend()".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn created(id: u64, rpp: &[u8]) -> (u64, TraceOp<u64>) {
        (id, TraceOp::Created { type_name: "Z".to_string(), root_prefix_path: rpp.to_vec(), path: vec![] })
    }

    #[test]
    fn map_assignment() {
        let events = vec![
            created(1, b"ab/x"),
            created(2, b"ab/y"),
            //Shares "ab" but overlaps writer 1, so it can't be on 1's map
            created(3, b"ab/x/deep"),
            created(4, b"zz"),
            created(5, b"a"),
            created(6, b""),
            (1, TraceOp::SetVal { val: 1 }),
        ];
        //Zipper 1's lifetime begins at event 0
        let writers = HashSet::from([0]);
        let mut warnings = vec![];
        let (map_of, labels) = assign_maps(&events, &[], &writers, &ReplayConfig::default(), &mut warnings);
        assert_eq!(map_of[&1], map_of[&2]);
        assert_ne!(map_of[&3], map_of[&1]);
        assert_eq!(warnings.len(), 1);
        let distinct: HashSet<usize> = [1, 3, 4, 5, 6].iter().map(|id| map_of[id]).collect();
        assert_eq!(distinct.len(), 5);
        assert_eq!(labels.len(), 5);
    }

    #[test]
    fn call_text_matches_methods() {
        assert_eq!(call_text(&TraceOp::<u64>::DescendTo { path: b"hi\n".to_vec() }), "descend_to(\"hi\\x0a\")");
        assert_eq!(call_text(&TraceOp::<u64>::DescendToByte { byte: b'h' }), "descend_to_byte('h')");
        assert_eq!(call_text(&TraceOp::<u64>::SetValAt { path: b"x".to_vec(), val: 3 }), "set_val_at(\"x\", 3)");
        assert_eq!(call_text(&TraceOp::<u64>::Meet2 { src_a: TraceSrc::Traced(3), src_b: TraceSrc::Unknown(vec![]) }), "meet_2(z3, <untraced: 0 values>)");
    }
}
