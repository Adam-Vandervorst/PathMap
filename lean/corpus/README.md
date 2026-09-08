# Regression corpus

Fuzzer inputs that reproduce a known divergence, kept because they are the
reproducer — each is a deterministic input to both trace producers, but not all
of them reduce to a snippet small enough to write out as a Rust example.

```bash
./lean/differential.py lean/corpus/*.bin        # all of them
./lean/shrink.py lean/corpus/<file>             # minimise one further
```

| file | what it shows |
| --- | --- |
| `status-imprecise-join_map_into.bin` | `join_map_into` reports `Element` where the trie is provably unchanged (FINDINGS.md #8) |
| `status-imprecise-restrict.bin` | `restrict` reports `Element` where the trie is provably unchanged (FINDINGS.md #8) |

Everything else in FINDINGS.md has a standalone reproducer instead; see
`cargo run -p differential --bin zipper_bug_repros -- --list`.
