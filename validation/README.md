# Algebraic sharing validator

[`algebra_sharing/`](algebra_sharing/) generates related tries and sequences of
algebraic operations. It checks logical results and identifies steps that lose
ordinary sharing or miss an opportunity for result sharing. Run
`cargo run -p algebra-sharing-validation` from the repository root. Ordinary
and result-sharing losses are counted in the default **report** mode, which
checks every selected seed and prints aggregate counts. It shows only the first
four split examples of each kind, clearly labeled in the output. Set
`PATHMAP_SHARING_ENFORCE_ORDINARY=1` for **strict** mode, which stops at the
first ordinary-sharing loss and saves a minimized replay. The
[`source documentation`](algebra_sharing/src/main.rs) explains its model,
parameters, and replay commands.
