import PathMapModel

/-!
The differential oracle.

    pathmap-oracle <input-file>       -- decode and run the file's bytes
    pathmap-oracle                    -- read the bytes from stdin
    pathmap-oracle --act <input-file> -- ArenaCompactTree mode: skip the
                                      -- operations an ACT read source cannot
                                      -- serve, matching differential/src/bin/act_trace.rs

Prints the trace produced by the model.  `differential/src/bin/pathmap_trace.rs` prints the
same trace from the real crate for the same input bytes, and
`differential/src/bin/act_trace.rs` does the same with an `ArenaCompactTree` as the read
source.
-/

open PathMapModel

def main (args : List String) : IO Unit := do
  let act := args.contains "--act"
  let files := args.filter (fun a => a != "--act")
  let bytes ← match files with
    | [] => (← IO.getStdin).readBinToEnd
    | path :: _ => IO.FS.readBinFile path
  for line in Fuzz.run bytes 256 act do
    IO.println line
