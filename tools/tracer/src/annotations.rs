//! Annotations steer the playback of an animation: captions over ranges of events, playback speed, zooming
//! in on part of a map, labels on subtries, and chapter marks.  They're written as JSON, and refer to events
//! by their `seq`
//!
//! ```json
//! {
//!   "start": 0,
//!   "ranges": [
//!     { "events": [0, 86], "speed": 4, "caption": "Invert the \"parent\" paths to create the \"child\" subtrie" },
//!     { "events": 472, "zoom": { "path": "out/aunt/" }, "hold": 4, "caption": "Everyone's aunts" }
//!   ],
//!   "labels": [ { "path": "out/aunt/", "text": "aunts" } ],
//!   "marks": [ { "event": 340, "label": "aunts" } ]
//! }
//! ```
//!
//! Places in a map, as zoomed on or labeled, are given by `path`, or by `path_hex` for paths that aren't
//! text.  `map` is the map's index, and may be omitted to mean the first map showing the path.
//!
//! When ranges overlap, the later range wins for each setting it specifies.  Any object may also have a
//! `"comment"`, which is ignored.

use serde::Deserialize;
use serde_json::{json, Value};

use crate::{Replay, ReplayValue};

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Annotations {
    /// The event the page opens at.  Defaults to the state before the first event
    pub start: Option<u64>,
    #[serde(default)]
    pub ranges: Vec<RangeNote>,
    #[serde(default)]
    pub labels: Vec<Label>,
    #[serde(default)]
    pub marks: Vec<Mark>,
    #[serde(default)]
    pub comment: Option<String>,
}

/// A name shown on a subtrie, and around its extent, whenever it's on screen
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Label {
    pub map: Option<usize>,
    pub path: Option<String>,
    pub path_hex: Option<String>,
    pub text: String,
    /// Limits the label to a range of events
    pub events: Option<EventRange>,
    #[serde(default)]
    pub comment: Option<String>,
}

/// Settings for a range of events
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RangeNote {
    pub events: EventRange,
    /// Shown over the animation while playback is in the range
    pub caption: Option<String>,
    /// Multiplies the playback speed in the range
    pub speed: Option<f64>,
    /// Plays the range as a single transition, from the event before it to its last event
    #[serde(default)]
    pub collapse: bool,
    /// Points the camera at part of a map
    pub zoom: Option<Zoom>,
    /// Seconds to pause on each event in the range during playback
    pub hold: Option<f64>,
    #[serde(default)]
    pub comment: Option<String>,
}

/// An event `seq`, or an inclusive `[first, last]` range of them
#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(untagged)]
pub enum EventRange {
    One(u64),
    Span([u64; 2]),
}

impl EventRange {
    fn bounds(&self) -> (u64, u64) {
        match *self {
            EventRange::One(seq) => (seq, seq),
            EventRange::Span([first, last]) => (first, last),
        }
    }
}

/// The subtrie at a place in a map
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Zoom {
    pub map: Option<usize>,
    pub path: Option<String>,
    pub path_hex: Option<String>,
    /// The most the subtrie is magnified, which limits zooming in on a small subtrie.  Defaults to 4
    pub max_scale: Option<f64>,
}

/// A named point in the animation, which can be jumped to
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Mark {
    pub event: u64,
    pub label: String,
    #[serde(default)]
    pub comment: Option<String>,
}

impl Annotations {
    pub fn from_json(text: &str) -> Result<Self, String> {
        serde_json::from_str(text).map_err(|err| format!("annotations: {err}"))
    }
}

fn hex(path: &[u8]) -> String {
    path.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_hex(text: &str) -> Option<Vec<u8>> {
    if text.len() % 2 != 0 {
        return None
    }
    (0..text.len()).step_by(2).map(|idx| u8::from_str_radix(text.get(idx..idx + 2)?, 16).ok()).collect()
}

/// Finds the place named by `map`, `path`, and `path_hex`, which must be on screen in some frame of `frames`
fn resolve_place<V: ReplayValue>(replay: &Replay<V>, frames: (usize, usize), map: Option<usize>, path: &Option<String>, path_hex: &Option<String>, what: &str) -> Result<(usize, Vec<u8>), String> {
    let path = match (path, path_hex) {
        (Some(path), None) => path.as_bytes().to_vec(),
        (None, Some(path_hex)) => decode_hex(path_hex).ok_or_else(|| format!("annotations: {what} has an invalid path_hex"))?,
        _ => return Err(format!("annotations: {what} needs exactly one of path or path_hex")),
    };
    let shown_on = |map: usize| replay.frames[frames.0..=frames.1].iter().any(|frame| {
        frame.maps.iter().any(|view| view.map == map && view.nodes.contains_key(&path))
    });
    let map = match map {
        Some(map) if map < replay.map_labels.len() => map,
        Some(map) => return Err(format!("annotations: {what} refers to map {map}, but there are only {} maps", replay.map_labels.len())),
        None => (0..replay.map_labels.len()).find(|&map| shown_on(map))
            .ok_or_else(|| format!("annotations: {what} refers to {}, which isn't shown during its events", crate::quote_path(&path)))?,
    };
    if !shown_on(map) {
        return Err(format!("annotations: {what} refers to {} in map {map}, which isn't shown during its events", crate::quote_path(&path)))
    }
    Ok((map, path))
}

/// Checks the annotations against a replay, and converts them to the form the page uses, where events are
/// replaced by frame indices
pub(crate) fn resolve<V: ReplayValue>(ann: &Annotations, replay: &Replay<V>) -> Result<Value, String> {
    let frame_of = |seq: u64| replay.frames.iter().position(|frame| frame.event == Some(seq));
    let find = |seq: u64, what: &str| frame_of(seq).ok_or_else(|| format!("annotations: {what} refers to event {seq}, which isn't in the trace"));
    let find_range = |events: &EventRange, what: &str| -> Result<(usize, usize), String> {
        let (first, last) = events.bounds();
        if first > last {
            return Err(format!("annotations: {what} begins at event {first}, after it ends at {last}"))
        }
        Ok((find(first, what)?, find(last, what)?))
    };

    let start = match ann.start {
        Some(seq) => find(seq, "start")?,
        None => 0,
    };
    let mut ranges = Vec::new();
    for (idx, range) in ann.ranges.iter().enumerate() {
        let what = format!("ranges[{idx}]");
        let (from, to) = find_range(&range.events, &what)?;
        if let Some(speed) = range.speed {
            if !(speed > 0.0) {
                return Err(format!("annotations: {what} has speed {speed}, which isn't positive"))
            }
        }
        if let Some(hold) = range.hold {
            if !(hold >= 0.0) {
                return Err(format!("annotations: {what} has hold {hold}, which is negative"))
            }
        }
        let zoom = match &range.zoom {
            None => Value::Null,
            Some(zoom) => {
                let (map, path) = resolve_place(replay, (from, to), zoom.map, &zoom.path, &zoom.path_hex, &format!("{what}'s zoom"))?;
                if let Some(max_scale) = zoom.max_scale {
                    if !(max_scale > 0.0) {
                        return Err(format!("annotations: {what}'s zoom has max_scale {max_scale}, which isn't positive"))
                    }
                }
                json!({ "map": map, "path": hex(&path), "max_scale": zoom.max_scale })
            }
        };
        ranges.push(json!({
            "from": from,
            "to": to,
            "caption": range.caption,
            "speed": range.speed,
            "collapse": range.collapse,
            "hold": range.hold,
            "zoom": zoom,
        }));
    }
    let mut labels = Vec::new();
    for (idx, label) in ann.labels.iter().enumerate() {
        let what = format!("labels[{idx}]");
        let (from, to) = match &label.events {
            Some(events) => find_range(events, &what)?,
            None => (0, replay.frames.len() - 1),
        };
        let (map, path) = resolve_place(replay, (from, to), label.map, &label.path, &label.path_hex, &what)?;
        labels.push(json!({ "from": from, "to": to, "map": map, "path": hex(&path), "text": label.text }));
    }
    let mut marks = Vec::new();
    for (idx, mark) in ann.marks.iter().enumerate() {
        marks.push(json!({ "frame": find(mark.event, &format!("marks[{idx}]"))?, "label": mark.label }));
    }
    Ok(json!({ "start": start, "ranges": ranges, "labels": labels, "marks": marks }))
}

#[cfg(test)]
mod tests {
    use pathmap::utils::debug::zipper_tracing::TraceOp;

    use super::*;
    use crate::{replay, ReplayConfig};

    fn small_replay() -> Replay<u64> {
        let events = vec![
            (10, 1, TraceOp::Created { type_name: "Z".to_string(), root_prefix_path: b"ab/".to_vec(), path: vec![] }),
            (11, 1, TraceOp::SetValAt { path: b"cd".to_vec(), val: 1 }),
            (12, 1, TraceOp::Dropped),
        ];
        replay(&events, vec![], &ReplayConfig::default())
    }

    fn check(json: &str) -> Result<Value, String> {
        resolve(&Annotations::from_json(json)?, &small_replay())
    }

    #[test]
    fn events_become_frames() {
        let resolved = check(r#"{ "start": 11, "ranges": [{ "events": [10, 12], "speed": 2, "zoom": { "path": "ab/c" } }], "labels": [{ "path": "ab/", "text": "ab" }], "marks": [{ "event": 12, "label": "end" }] }"#).unwrap();
        assert_eq!(resolved["labels"][0], json!({ "from": 0, "to": 3, "map": 0, "path": "61622f", "text": "ab" }));
        //Frame 0 is the state before the first event
        assert_eq!(resolved["start"], 2);
        assert_eq!(resolved["ranges"][0]["from"], 1);
        assert_eq!(resolved["ranges"][0]["to"], 3);
        assert_eq!(resolved["ranges"][0]["zoom"], json!({ "map": 0, "path": "61622f63", "max_scale": null }));
        assert_eq!(resolved["marks"][0]["frame"], 3);
    }

    #[test]
    fn invalid_annotations() {
        assert!(check(r#"{ "start": 9 }"#).unwrap_err().contains("event 9"));
        assert!(check(r#"{ "ranges": [{ "events": [12, 10] }] }"#).unwrap_err().contains("after it ends"));
        assert!(check(r#"{ "ranges": [{ "events": 11, "speed": 0 }] }"#).unwrap_err().contains("isn't positive"));
        assert!(check(r#"{ "ranges": [{ "events": 11, "zoom": { "path": "zz" } }] }"#).unwrap_err().contains("isn't shown"));
        assert!(check(r#"{ "ranges": [{ "events": 11, "zoom": { "map": 3, "path": "ab" } }] }"#).unwrap_err().contains("only 1 maps"));
        assert!(check(r#"{ "labels": [{ "path": "ab/cd", "text": "x", "events": 10 }] }"#).unwrap_err().contains("isn't shown"));
        //Misspelled settings are caught rather than ignored
        assert!(check(r#"{ "ranges": [{ "events": 11, "sped": 2 }] }"#).unwrap_err().contains("unknown field"));
    }
}
