# linear_search Islaris proof - loop theorem complete

## Status

`armored/linear_search/linear_search_proof.v` now proves
`linear_search_loop` with a genuine `Qed`.

- zero residual goals
- zero shelved goals
- no `Admitted`, `admit`, `Axiom`, or `Abort`
- no assembly or generated-trace changes
- no termination claim
- no top-level `linear_search` theorem yet

## Architectural Fix

The load failure was not caused by `instr_pre` discarding the loop invariant.
The pure invariant facts survive the `b.cs` branch, but the original proof
stopped at the semantic-memory subgoal before converting the non-taken branch's
raw carry equality into the strict bound needed by the array-read automation.

The proof now:

1. proves `no_carry_to_lt`, which converts the real AArch64 comparison result on
   the non-taken branch into
   `bv_unsigned i < bv_unsigned len`;
2. records that strict bound in the Coq context and resumes `liARun`;
3. lets Islaris's normal `MKArray`/`FindMemMapsTo` rule combine the strict bound
   with the existing length, alignment, and address-range invariants to justify
   the actual `ldr x4, [x0, x3, lsl #3]` as an in-bounds read; and
4. extends the no-earlier-match prefix after a non-matching load before invoking
   the recursive loop precondition.

The failed manual `find_in_context_mem_mapsto_semantic` detour and its debugging
sentinels were removed.

The exit continuations were also corrected to follow the upstream style: each
continuation now existentially quantifies its eventual index `i'` instead of
capturing the current loop iteration's `i`. This allows the continuations to be
framed across the increment and preserves the functional facts needed at exit.

The not-found continuation carries:

- `bv_unsigned i' = bv_unsigned len`
- `bv_unsigned len = length data`
- every element before `i'` differs from `tgt`
- ownership of the unchanged complete array

The found continuation carries:

- `bv_unsigned i' < bv_unsigned len`
- `bv_unsigned len = length data`
- `data !! Z.to_nat (bv_unsigned i') = Some tgt`
- every element before `i'` differs from `tgt`
- ownership of the unchanged complete array

Thus these continuations support the required first-match and no-match results
without weakening the loop invariant.

## Preserved Invariant

`linear_search_loop_spec` still contains all required properties:

- `bv_unsigned i <= bv_unsigned len`
- `bv_unsigned len = length data`
- `bv_unsigned base mod 8 = 0`
- `bv_unsigned base + bv_unsigned len * 8 < 2^52`
- every element before `i` differs from `tgt`
- ownership of the complete original array

The existing taken-carry proof and its helper lemmas were preserved. The address
helper module is now imported cleanly, and its proofs were made compatible with
the pinned Coq/stdpp environment so it also compiles from source.

## Clean Verification

Working directory:

`/home/ubuntu/asm-verification/armored/linear_search`

Exact clean compile command:

```bash
rm -f '.mod8addr_lemmas.aux' 'mod8addr_lemmas.glob' 'mod8addr_lemmas.vo' 'mod8addr_lemmas.vok' 'mod8addr_lemmas.vos' '.linear_search_proof.aux' 'linear_search_proof.glob' 'linear_search_proof.vo' 'linear_search_proof.vok' 'linear_search_proof.vos' && eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqc mod8addr_lemmas.v && coqc -R /home/ubuntu/asm-verification/armored/linear_search/traces isla.instructions.linear_search linear_search_proof.v
```

Result: exit status 0.

```text
Tactic call liARun ran for 6.055 secs (6.029u,0.024s) (success)
Tactic call liARun ran for 9.899 secs (9.831u,0.066s) (success)
```

Exact kernel check command:

```bash
eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqchk -silent -R /home/ubuntu/asm-verification/armored/linear_search/traces isla.instructions.linear_search mod8addr_lemmas linear_search_proof
```

Result: exit status 0 with no output. `Print Assumptions linear_search_loop`
reported `Closed under the global context`.

## Next Scope

Stop here. Termination and the outer `linear_search` theorem remain future work.
