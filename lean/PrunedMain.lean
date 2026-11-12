import PrunedModel

/-!
The oracle for the dangling-path-free model.

One-shot:

    pruned-oracle <input-file>       -- decode and run the file's bytes
    pruned-oracle                    -- read the bytes from stdin

Resident:

    pruned-oracle --server           -- one process, many inputs

Spawning a fresh process per fuzzer input costs more than running the input
does, so `pruned_differential.py` keeps the oracle resident and feeds it work
over stdin.  The protocol matches `differential/src/server.rs`, one command per
line:

    run-input <timeout-ms> <hex>    run the decoded bytes, print the trace
    quit                            exit 0

The reply is the trace lines, then exactly one terminator line, which is the
only line beginning with `!`:

    !DONE                           the trace above is complete
    !TIMEOUT                        exceeded <timeout-ms>
    !PANIC <one-line message>       malformed command

`differential/src/bin/pruned_trace.rs` prints the same trace from the real
crate for the same input bytes; `lean/pruned_differential.py` diffs them.

The timeout argument is parsed and ignored, as in `lean/Main.lean`: no
in-process timeout is reachable from Lean's `IO.asTask`/`IO.hasFinished`, and
the driver has to enforce the deadline from outside regardless, since no
in-process timeout can save a child that has died.  The model is total, so it
cannot hang, only be slow.
-/

open PrunedModel

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
partial def serve : IO Unit := do
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
          match ms.toNat?, hexDecode (String.intercalate " " rest) with
          | some _, some bytes => do
              for line in Fuzz.run bytes 256 do
                stdout.putStrLn line
              pure "!DONE"
          | _, _ => pure "!PANIC bad run-input arguments"
      | _ => pure s!"!PANIC unknown command: {line}"
    stdout.putStrLn terminator
    stdout.flush
    loop
  loop

def main (args : List String) : IO Unit := do
  if args.contains "--server" then
    return ← serve
  let files := args.filter (fun a => !a.startsWith "--")
  let bytes ← match files with
    | [] => (← IO.getStdin).readBinToEnd
    | path :: _ => IO.FS.readBinFile path
  for line in Fuzz.run bytes 256 do
    IO.println line
