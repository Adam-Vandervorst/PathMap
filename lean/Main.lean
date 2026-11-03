import PathMapModel

/-!
The differential oracle.

One-shot:

    pathmap-oracle <input-file>       -- decode and run the file's bytes
    pathmap-oracle                    -- read the bytes from stdin
    pathmap-oracle --act <input-file> -- ArenaCompactTree mode: skip the
                                      -- operations an ACT read source cannot
                                      -- serve, matching differential/src/bin/act_trace.rs

Resident:

    pathmap-oracle --server [--act]   -- one process, many inputs

Spawning a fresh process per fuzzer input costs more than running the input
does, so `differential.py` keeps the oracle resident and feeds it work over
stdin.  The protocol matches `differential/src/server.rs`, one command per line:

    run-input <timeout-ms> <hex>    run the decoded bytes, print the trace
    quit                            exit 0

The reply is the trace lines, then exactly one terminator line, which is the
only line beginning with `!`:

    !DONE                           the trace above is complete
    !TIMEOUT                        exceeded <timeout-ms>
    !PANIC <one-line message>       malformed command

Prints the trace produced by the model.  `differential/src/bin/pathmap_trace.rs` prints the
same trace from the real crate for the same input bytes, and
`differential/src/bin/act_trace.rs` does the same with an `ArenaCompactTree` as the read
source; they are compared by `lean/differential.py`.
-/

open PathMapModel

/-! ## Why there is no in-process timeout here

`differential/src/server.rs` runs each input on a thread it can abandon, so a
hanging crate costs one input rather than the process.  The oracle does not, and
not for want of trying: `IO.asTask` plus `IO.sleep` under `IO.waitAny` blocks on
the work task in list order and never observes the timer, and polling with
`IO.hasFinished` blocks on the first call rather than reporting.  Both were
measured against a deliberately slow body: a 50 ms budget returned "finished"
after 99.5 s.

So the oracle parses the timeout argument and ignores it, and `differential.py`
enforces the deadline from outside — reading with a `select` timeout, then
killing and respawning the child.  The driver needs that path regardless, since
no in-process timeout can save a child that has died or wedged in the runtime.

This costs little in practice: the model is *total*, so it cannot hang, only be
slow, and a 4 kB input runs in about 6 ms.
-/

/-- Decode a lowercase/uppercase hex string. -/
def hexDecode (s : String) : Option ByteArray :=
  let cs := s.toList
  if cs.length % 2 != 0 then none
  else
    let rec go : List Char → ByteArray → Option ByteArray
      | [], acc => some acc
      | a :: b :: rest, acc => do
          let hi ← a.toString.toNat? |>.orElse fun _ =>
            "0123456789abcdef".toList.idxOf? a.toLower
          let lo ← b.toString.toNat? |>.orElse fun _ =>
            "0123456789abcdef".toList.idxOf? b.toLower
          go rest (acc.push (UInt8.ofNat (hi * 16 + lo)))
      | _, _ => none
    go cs ByteArray.empty

/-- The resident command loop. -/
partial def serve (act : Bool) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    -- `getLine` returns "" only at EOF; a blank line is "\n".
    if line.isEmpty then return
    let line := line.trimAscii.toString
    if line == "quit" then return
    let terminator ←
      match line.splitOn " " with
      | "run-input" :: ms :: rest =>
          -- The timeout is accepted for protocol compatibility and ignored; see
          -- "Why there is no in-process timeout here" above.
          match ms.toNat?, hexDecode (String.intercalate " " rest) with
          | some _, some bytes => do
              for line in Fuzz.run bytes 256 act do
                stdout.putStrLn line
              pure "!DONE"
          | _, _ => pure "!PANIC bad run-input arguments"
      | _ => pure s!"!PANIC unknown command: {line}"
    stdout.putStrLn terminator
    stdout.flush
    loop
  loop

def main (args : List String) : IO Unit := do
  let act := args.contains "--act"
  if args.contains "--server" then
    return ← serve act
  let files := args.filter (fun a => a != "--act" && a != "--server")
  let bytes ← match files with
    | [] => (← IO.getStdin).readBinToEnd
    | path :: _ => IO.FS.readBinFile path
  for line in Fuzz.run bytes 256 act do
    IO.println line
