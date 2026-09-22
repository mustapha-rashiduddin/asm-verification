# linear_search Islaris proof - both theorems complete

## Status

- `linear_search_loop`: **Qed** (genuine `Time Qed`, zero residual and shelved
  goals, `coqchk` 0, `Print Assumptions linear_search_loop` →
  **Closed under the global context**, no `Admitted`/`admit`/`Axiom`/`Abort`,
  no assembly or generated-trace changes, no termination claim).
- Top-level `linear_search` (c_call wrapper): **Qed** (genuine `Time Qed`,
  zero residual and shelved goals, `coqchk` 0,
  `Print Assumptions linear_search` → **Closed under the global context**).

## How the two-`ret` c wrapper was made sound

### Root cause of the earlier top-level blocker

`c_call` grants a single linear resource
`instr_pre (bv_unsigned ret) (c_call_ret ...)` for the caller continuation, and
`0x10300000` returns through **two** `ret` instructions (`0x24` on the
not-found path, `0x2c` on the found path). When the loop invariant recorded its
two exit continuations with `∗`, the found path consumed the shared
caller-return continuation additively-inconclusively (Islaris's
`find_in_context (FindInstrKind (bv_unsigned ret) true)` instantiates the
continuation once and the other exit then finds nothing).

### Fix 1: additive (`∧`) exit continuations at the top level

The loop invariant `linear_search_loop_spec` now records the two exit
obligations with the additive conjunction `∧`:

- `instr_pre 0x10300020 (not-found ...)` (with `i' = len`, `len = length data`,
  no-earlier-match prefix, full-array ownership)
- `instr_pre 0x10300028 (found ...)` (with `i' < len`,
  `data !! Z.to_nat (bv_unsigned i') = Some tgt`, no-earlier-match prefix,
  full-array ownership)

Because both exit shapes are additively available after the loop, the top-level
`liARun` now runs both epilogues with the single `c_call_ret` continuation and
reduces to the two return-post pure disjuncts, each of which is proved directly
(`bv_solve`, `Z.to_nat`/length arithmetic via `to_nat_of_nat_id`,
`lookup_ge_None_2`, and the exit prefix facts). No `Subsume` instance or
framework change was needed.

### Fix 2: `∗` exits inside the loop body

The loop body is its own `instr_body` proof; the `∧` exits are reachable from
the `∗`-conjoined resources at `0x20`/`0x28` *at different addresses*, and the
`FindInstrKind` finder only descends SEP-conjuncts. The body therefore runs
against a twin definition `linear_search_loop_spec_sep` whose exits are
`∗`-conjoined (this is exactly the provably-closed shape from the loop-theorem
milestone). The bridge lemma

`linear_search_loop_spec_sep_to_and : linear_search_loop_spec_sep -∗ linear_search_loop_spec`

shows the `∗` version is at least as strong as the `∧` version (it never
duplicates a linear resource; it only forgets which exit consumes what). It is
proved with `star_and : P ∗ Q -∗ P ∧ Q`. `linear_search` takes the `∧`-version
directly; everything is internally consistent and every lemma is a closed `Qed`.

## Loop theorem (intact)

- The real AArch64 compare/branch semantics establish both the taken
  `i ≥ len` and non-taken `i < len` cases (`overflow_to_le`, `carry_to_le`,
  `no_carry_to_lt`).
- The actual `ldr x4, [x0, x3, lsl #3]` is justified as an in-bounds read from
  the owned array (strict bound + length, alignment, and address-range
  invariants).
- The no-earlier-match prefix is preserved across the increment.
- The not-found exit carries `i' = len`, length agreement, the complete
  no-earlier-match prefix, and unchanged complete-array ownership.
- The found exit carries `i' < len`, the matching element, the no-earlier-match
  prefix, and unchanged complete-array ownership.

## Preserved Invariant

`linear_search_loop_spec` (and `linear_search_loop_spec_sep`) still contains all
required properties:

- `bv_unsigned i <= bv_unsigned len`
- `bv_unsigned len = length data`
- `bv_unsigned base mod 8 = 0`
- `bv_unsigned base + bv_unsigned len * 8 < 2^52`
- every element before `i` differs from `tgt`
- ownership of the complete original array

## Clean Verification

Working directory:

`/home/ubuntu/asm-verification/armored/linear_search`

Exact clean compile command:

```bash
rm -f '.mod8addr_lemmas.aux' 'mod8addr_lemmas.glob' 'mod8addr_lemmas.vo' 'mod8addr_lemmas.vok' 'mod8addr_lemmas.vos' '.linear_search_proof.aux' 'linear_search_proof.glob' 'linear_search_proof.vo' 'linear_search_proof.vok' 'linear_search_proof.vos' && eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqc mod8addr_lemmas.v && coqc -R /home/ubuntu/asm-verification/armored/linear_search/traces isla.instructions.linear_search linear_search_proof.v
```

Result: exit status 0. (Equivalently `coqc -Q . "" -R traces isla.instructions.linear_search linear_search_proof.v`
after `mod8addr_lemmas.v` is compiled.)

```text
Tactic call liARun ran for 5.1-5.4 secs (success)    (loop lemma)
Tactic call liARun ran for 9.7-10.1 secs (success)   (loop lemma)
Tactic call liARun ran for 5.9-6.1 secs  (success)   (top-level)
Finished transaction in 5.6 secs (successful)        (top-level Qed)
```

Exact kernel check command:

```bash
eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqchk -silent -Q . "" -R traces isla.instructions.linear_search linear_search_proof
```

Result: exit status 0 (only a loadpath-remap warning). `Print Assumptions
linear_search_loop`, `Print Assumptions linear_search`, and `Print Assumptions
linear_search_loop_spec_sep_to_and` all report **Closed under the global
context**.

## Next Scope

One proof-engineering point remains before termination work.

`linear_search_loop` now proves
`instr_body 0x10300004 linear_search_loop_spec_sep`, while the top-level
`linear_search` theorem assumes
`□ instr_pre 0x10300004 linear_search_loop_spec`.

Those are different loop specs. The proved bridge

`linear_search_loop_spec_sep_to_and :
  linear_search_loop_spec_sep -∗ linear_search_loop_spec`

only goes from the SEP-exit version to the additive-exit version, and it is not
currently used to close the recursive/top-level composition. Therefore the
current `Qed`s establish the loop theorem and the outer wrapper theorem
separately, but we should not yet claim that the recursive loop proof and the
top-level wrapper have been tied together into one closed whole-function proof
under the normal Islaris recursion/adequacy pattern.

Next task: prove or exhibit the exact composition step, without weakening either
spec, adding assumptions, changing machine code, or duplicating linear
resources. Only after that is closed should termination be tackled.

Termination itself remains unproved and out of scope for the current partial-
correctness result.