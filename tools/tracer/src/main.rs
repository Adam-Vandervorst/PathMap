use std::path::PathBuf;
use std::process::ExitCode;

use tracer::{render_trace, ReplayConfig};

const USAGE: &str = "\
Usage: tracer replay <trace-file> [--act <file.act>]... [--prefix-len <n>] [-o <out.html>]

Replays a trace written by pathmap's TraceZipper, and writes it as an animated HTML page

  --act <file>        Seeds a map with the contents of an ACT file.  May be given more than once; a zipper
                      goes on the first map its root_prefix_path is compatible with.  Without any, maps start empty
  --prefix-len <n>    Zippers whose root_prefix_paths share this many leading bytes share a map (default 2)
  -o <file>           Output file (default: the trace file with an .html extension)";

fn run(args: &[String]) -> Result<(), String> {
    let mut args = args.iter();
    match args.next().map(String::as_str) {
        Some("replay") => {},
        Some("-h") | Some("--help") => { println!("{USAGE}"); return Ok(()) },
        _ => return Err(USAGE.to_string()),
    }
    let mut trace = None;
    let mut acts = Vec::new();
    let mut out = None;
    let mut cfg = ReplayConfig::default();
    while let Some(arg) = args.next() {
        let mut value = || args.next().ok_or_else(|| format!("{arg} needs a value"));
        match arg.as_str() {
            "--act" => acts.push(PathBuf::from(value()?)),
            "--prefix-len" => cfg.prefix_len = value()?.parse().map_err(|_| "--prefix-len needs a number".to_string())?,
            "-o" => out = Some(PathBuf::from(value()?)),
            _ if trace.is_none() && !arg.starts_with('-') => trace = Some(PathBuf::from(arg)),
            _ => return Err(format!("unexpected argument {arg}\n\n{USAGE}")),
        }
    }
    let trace = trace.ok_or_else(|| USAGE.to_string())?;
    let out = out.unwrap_or_else(|| trace.with_extension("html"));
    let bytes = std::fs::read(&trace).map_err(|err| format!("{}: {err}", trace.display()))?;
    let title = trace.file_name().map_or_else(|| "trace".to_string(), |name| name.to_string_lossy().into_owned());
    let (html, warnings) = render_trace(&bytes, &acts, &cfg, &title).map_err(|err| format!("{}: {err}", trace.display()))?;
    for warning in warnings {
        eprintln!("warning: {warning}");
    }
    std::fs::write(&out, html).map_err(|err| format!("{}: {err}", out.display()))?;
    println!("wrote {}", out.display());
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("{err}");
            ExitCode::FAILURE
        }
    }
}
