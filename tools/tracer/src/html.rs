//! Renders a [Replay] as a self-contained HTML page

use std::fmt::Write;

use crate::{Replay, ReplayValue};

const TEMPLATE: &str = include_str!("player.html");

/// Appends `s` as a JSON string.  `<` is escaped too, so the JSON can't end the enclosing `<script>`
fn push_json_str(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '<' => out.push_str("\\u003c"),
            c if (c as u32) < 0x20 => { let _ = write!(out, "\\u{:04x}", c as u32); },
            c => out.push(c),
        }
    }
    out.push('"');
}

fn push_hex(out: &mut String, path: &[u8]) {
    out.push('"');
    for byte in path {
        let _ = write!(out, "{byte:02x}");
    }
    out.push('"');
}

fn push_list<T>(out: &mut String, items: impl IntoIterator<Item = T>, mut push_item: impl FnMut(&mut String, T)) {
    out.push('[');
    for (idx, item) in items.into_iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        push_item(out, item);
    }
    out.push(']');
}

/// The frames as JSON.  Paths are hex strings.  Each node is `[path, exists, accessible, val, hidden]`, and
/// each zipper is `[id, root, focus, writer]`
fn frames_json<V: ReplayValue>(replay: &Replay<V>, title: &str) -> String {
    let mut out = String::from("{\"title\":");
    push_json_str(&mut out, title);
    out.push_str(",\"maps\":");
    push_list(&mut out, &replay.map_labels, |out, label| push_json_str(out, label));
    out.push_str(",\"frames\":");
    push_list(&mut out, &replay.frames, |out, frame| {
        out.push_str("{\"c\":");
        push_json_str(out, &frame.caption);
        match frame.actor {
            Some(id) => { let _ = write!(out, ",\"a\":{id}"); },
            None => out.push_str(",\"a\":null"),
        }
        out.push_str(",\"s\":");
        push_list(out, &frame.sources, |out, id| { let _ = write!(out, "{id}"); });
        out.push_str(",\"m\":");
        push_list(out, &frame.maps, |out, map| {
            let _ = write!(out, "{{\"i\":{},\"n\":", map.map);
            push_list(out, &map.nodes, |out, (path, node)| {
                out.push('[');
                push_hex(out, path);
                let _ = write!(out, ",{},{},", node.exists as u8, node.accessible as u8);
                match &node.val {
                    Some(val) => push_json_str(out, val),
                    None => out.push_str("null"),
                }
                let _ = write!(out, ",{}]", node.hidden);
            });
            out.push_str(",\"z\":");
            push_list(out, &map.zippers, |out, z| {
                let _ = write!(out, "[{},", z.id);
                push_hex(out, &z.root);
                out.push(',');
                push_hex(out, &z.focus);
                let _ = write!(out, ",{}]", z.writer as u8);
            });
            out.push('}');
        });
        out.push('}');
    });
    out.push('}');
    out
}

/// Renders the replay as a page that plays it back
pub fn render_html<V: ReplayValue>(replay: &Replay<V>, title: &str) -> String {
    let mut escaped_title = String::new();
    for c in title.chars() {
        match c {
            '<' => escaped_title.push_str("&lt;"),
            '>' => escaped_title.push_str("&gt;"),
            '&' => escaped_title.push_str("&amp;"),
            c => escaped_title.push(c),
        }
    }
    TEMPLATE
        .replace("__TITLE__", &escaped_title)
        .replace("/*__TRACE_DATA__*/null", &frames_json(replay, title))
}
