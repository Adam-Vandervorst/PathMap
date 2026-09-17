# Regression corpus

Fuzzer inputs that reproduce a known divergence, kept because they are the
reproducer — each is a deterministic input to both trace producers, but not all
of them reduce to a snippet small enough to write out as a Rust example.

```bash
./lean/differential.py lean/corpus/*.bin        # all of them
./lean/shrink.py lean/corpus/<file>             # minimise one further
```

That exits non-zero, and is meant to: `dangling-residue-only-in-map0.bin` is here
precisely because `classify()` cannot recognise it, so it is reported as a new
divergence every time.  The exit code says "one entry is unclassified", not "the
crate regressed".

| file | what it shows |
| --- | --- |
| `status-imprecise-join_map_into.bin` | `join_map_into` reports `Element` where the trie is provably unchanged (FINDINGS.md #8) |
| `status-imprecise-restrict.bin` | `restrict` reports `Element` where the trie is provably unchanged (FINDINGS.md #8) |
| `dangling-residue-only-in-map0.bin` | a kept dangling child that no operation's fingerprint reveals: every one of the run's steps agrees, and the extra valueless path shows up only in the final `MAP0` dump. Same defect as `meet_keeps_dangling`, but `classify()` keys that one on `child_count`/`val_count` moving on the trace line, and a `MAP` line has neither — so this manifestation is reported as a new divergence |

Everything else in FINDINGS.md has a standalone reproducer instead; see
`cargo run -p differential --bin zipper_bug_repros -- --list`.
