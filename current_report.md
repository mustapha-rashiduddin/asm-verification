# linear_search Islaris proof - whole-function composition closed

## Status

- `linear_search_loop` (loop body, address `0x4`): **Qed** (genuine `Time Qed`,
  zero residual and shelved goals, `coqchk` 0,
  `Print Assumptions linear_search_loop` → **Closed under the global context**,
  no `Admitted`/`admit`/`Axiom`/`Abort`, no assembly or generated-trace
  changes, no termination claim).
- `linear_search` (whole function under `c_call`, address `0x0`): **Qed**
  (genuine `Time Qed`, zero residual and shelved goals, `coqchk` 0,
  `Print Assumptions linear_search` → **Closed under the global context**).
- `linear_search_composed` (assembly-closed theorem, composing the loop body
  with the wrapper via the normal Islaris/Iris recursion): **Qed** (genuine
  `Qed`, `coqchk` 0, `Print Assumptions linear_search_composed` → **Closed
  under the global context**).

## Design: one loop spec for the body, the wrapper, and the recursion

The earlier blocker was that the loop body and the top-level wrapper required
different loop specs (`linear_search_loop_spec_sep` with `∗`-conjoined exits
vs. `linear_search_loop_spec` with additive `∧` exits); the bridge
`linear_search_loop_spec_sep_to_and` was proved but never used to close a
composition, so the loop proof and the wrapper proof were not tied together.

The closing design (validated empirically first in `scratch/sep_hyp.v`, then
moved into `linear_search_proof.v`):

- **No-exit loop invariant** `linear_search_loop_spec` at `0x4`: registers,
  complete-array ownership, and the pure facts (`i ≤ len`, `len = length data`,
  `base mod 8 = 0`, address range, no-earlier-match prefix). No exit
  obligations inside the invariant, so the top level can furnish it trivially.
- **Named exit contracts** lifted out of the invariant:
  `linear_search_nf_spec` (not-found state at `0x20`; `i' = len` and the full
  no-earlier-match prefix) and `linear_search_f_spec` (found state at `0x28`;
  `i' < len`, matching element, full prefix). Each is stated once as an
  `instr_pre` and given to *both* lemmas as a hypothesis, so the SAME spec and
  the SAME exit contracts run through the body, the wrapper, and the
  composition.

Consequences:

- The loop body `linear_search_loop` proves
  `instr_body 0x10300004 linear_search_loop_spec` from the code words `0x4..0x1c`,
  the two exit `instr_pre`s, and `□ instr_pre 0x4 linear_search_loop_spec`
  (its recursion token).
- The wrapper `linear_search` proves
  `instr_body 0x10300000 (linear_search_spec stack_size)` from the code words
  `0x0..0x2c`, the same two exit `instr_pre`s, and the *same*
  `□ instr_pre 0x4 linear_search_loop_spec` recursion token.
- `linear_search_composed` closes the knot in the standard Islaris/Iris
  recursion pattern (as in `examples/example.v`, `test_state_adequate'`,
  lines 192-220): it `iLöb`s over
  `□ instr_body 0x4 linear_search_loop_spec`, discharges the recursion token
  through `instr_pre_to_body` (with `iModIntro`), and feeds the result back to
  `linear_search`. The theorem's only hypotheses are the 13 code words
  (`instr` is persistent) and the two exit contracts.
  `instr_pre` itself is affine (not persistent; confirmed:
  `Persistent (instr_pre a P)` has no type-class instance), so the exits are
  given once under a `□` in `linear_search_composed` and re-supplied both
  inside the recursion and for the final application of `linear_search`.
  No linear resource is duplicated: `instr` and `□ instr_pre` are duplicable,
  and no assembly code or generated trace was changed.

## Loop theorem (intact from the prior milestone)

- The real AArch64 compare/branch semantics establish both the taken
  `i ≥ len` and non-taken `i < len` cases (`overflow_to_le`, `carry_to_le`,
  `no_carry_to_lt`).
- The actual `ldr x4, [x0, x3, lsl #3]` is justified as an in-bounds read from
  the owned array (strict bound + length, alignment, and address-range
  invariants).
- The no-earlier-match prefix is preserved across the increment (second bullet;
  requires the new helper `bv_sub_extract_neq_zero` to turn the
  WP's subtraction-is-nonzero fact at the found exit into
  `bv_unsigned vmem ≠ bv_unsigned tgt`).
- The not-found exit carries `i' = len`, length agreement, the complete
  no-earlier-match prefix, and unchanged complete-array ownership.
- The found exit carries `i' < len`, the matching element, the no-earlier-match
  prefix, and unchanged complete-array ownership.

## Preserved invariant

`linear_search_loop_spec` still contains all required properties:

- `bv_unsigned i <= bv_unsigned len`
- `bv_unsigned len = length data`
- `bv_unsigned base mod 8 = 0`
- `bv_unsigned base + bv_unsigned len * 8 < 2^52`
- every element before `i` differs from `tgt`
- ownership of the complete original array

The exit facts (not-found: `i' = len` + full prefix; found: matching element +
full prefix) live in `linear_search_nf_spec`/`linear_search_f_spec` and are
unchanged from the prior milestone, only re-packaged as standalone contracts.

## Clean Verification

Working directory:

`/home/ubuntu/asm-verification/armored/linear_search`

Exact clean compile command:

```bash
rm -f '.mod8addr_lemmas.aux' 'mod8addr_lemmas.glob' 'mod8addr_lemmas.vo' 'mod8addr_lemmas.vok' 'mod8addr_lemmas.vos' '.linear_search_proof.aux' 'linear_search_proof.glob' 'linear_search_proof.vo' 'linear_search_proof.vok' 'linear_search_proof.vos' && eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqc mod8addr_lemmas.v && coqc -R /home/ubuntu/asm-verification/armored/linear_search/traces isla.instructions.linear_search linear_search_proof.v
```

Result: exit status 0. (Equivalently `coqc -Q . "" -R traces
isla.instructions.linear_search linear_search_proof.v` after `mod8addr_lemmas.v`
is compiled.)

```text
Tactic call liARun ran for 5.5-6 secs (success)   (loop lemma)
Tactic call liARun ran for 8.5-9 secs (success)   (loop lemma, second liARun)
Finished transaction in 6.3 secs (successful)     (loop lemma Qed)
Tactic call liARun ran for 2.3-2.4 secs (success) (top-level)
Finished transaction in 2.3 secs (successful)     (top-level Qed)
Finished transaction in 2.3 secs (successful)     (composed Qed)
```

Exact kernel check command:

```bash
eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqchk -silent -Q . "" -R traces isla.instructions.linear_search linear_search_proof
```

Result: exit status 0 (only a loadpath-remap warning). `Print Assumptions
linear_search_loop`, `Print Assumptions linear_search`, and `Print Assumptions
linear_search_composed` all report **Closed under the global context**.

## Next Scope

The partial-correctness composition is closed. The only remaining major work is
termination (a well-founded argument that the loop index strictly increases
toward `len`), which is still out of scope for this partial-correctness result.