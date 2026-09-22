# linear_search Islaris proof - loop theorem complete, top-level theorem blocked

## Status

- `linear_search_loop`: **Qed** (genuine `Time Qed`, zero residual and shelved
  goals, `coqchk` 0, `Print Assumptions linear_search_loop` →
  **Closed under the global context**, no `Admitted`/`admit`/`Axiom`/`Abort`,
  no assembly or generated-trace changes, no termination claim).
- Top-level `linear_search` (c_call wrapper): **blocked** on two residual
  goals that Islaris's automation cannot discharge for a two-`ret` c wrapper
  (see below). The lemma statement is kept in the file with a documented
  `Abort.` (development state; the file compiles).

## Loop theorem (previous step, intact)

See the `Architectural Fix` and `Preserved Invariant` sections below; nothing
changed in this step except the reported top-level blocker.

## Top-level theorem: what works

- The loop handover at `0x4` is the only real step; the `~2.3s` top-level
  `liARun` runs `a0` (`mov x3, xzr`) and hands control to the loop spec.
- The loop spec carries **two** exit continuations (not-found at `0x20`,
  found at `0x28`); consequently the handover leaves a `subsume` goal:

  ```
  subsume (instr 0x10300020 (Some a20))
          (λ _, instr_pre 0x10300020 (not-found wp))
          (λ _, instr_pre 0x10300028 (found wp))
  ```

  No `Subsume` instance matches `instr -> instr_pre` (`subsume =
  P1 -∗ ∃ x, P2 x ∗ T x`); `liARun` therefore cannot consume it. Every Islaris
  example (binary_search, memcpy, uart, rbit, ...) is a single-exit function,
  so this case is never exercised upstream.

- Manual unfolding works: `iIntros "_"; iExists tt; iSplitL; liARun` executes
  both epilogues (naive `mvn x0,xzr; ret` at `0x20`/`0x24`, found
  `mov x0,x3; ret` at `0x28`/`0x2c`) and closes the found path.

## Top-level theorem: exact residual goals (blocker)

After that manual split and `liARun` rounds, exactly two focused goals remain,
both on the **not-found** path:

1. `find_in_context (FindInstrKind (bv_unsigned ret) true) …`
   (the `ret` at `0x24` looking up the caller continuation). `c_call` grants a
   single `instr_pre (bv_unsigned ret) (c_call_ret …)` hypothesis
   (`calling_convention.v:116`); the function has **two** `ret` instructions
   (`0x24` and `0x2c`), so a double consumption is required and the second
   lookup finds nothing.

2. The not-found `c_call_ret` pure obligation:

   ```
   (bv_unsigned (rets !!! 0%nat) = bv_modulus 64 - 1 ∧ ∀ j, data !! j ≠ Some tgt)
   ∨ (bv_unsigned (rets !!! 0%nat) < length data ∧ …)
   ```

   The left disjunct needs the full not-found fact `∀ j, data !! j ≠ Some tgt`,
   which the `0x20` exit continuation guarantees only as pure conjuncts
   (`i' = len`, `len = length data`, `∀ j < i', data !! j ≠ tgt`); those are
   re-proved as side-conditions and consumed during the epilogue run and are no
   longer in context when the obligation is generated, so it cannot be proven.

Current evidence suggests the shipped `c_call` / `find_in_context` / `subsume`
automation does not directly handle this two-exit / two-`ret` proof shape.
That is the working hypothesis for the next attempt; it is not yet established
whether the right fix is a proof restructuring, a small helper/instance, or a
framework extension. The specification itself has not been shown wrong.

## Fragment retained in the file (for the next attempt)

```coq
  Unshelve.
  all: try (iIntros "_"; iExists tt).
  all: try (iSplitL; liARun).
  all: try liARun.
  Unshelve.
  all: try liARun.
  Time Abort.
```

Suggested next direction: first try a proof restructuring that shares the
caller-return continuation across both epilogues while preserving each exit's
functional facts. Only if that fails should we consider adding a small
`Subsume`/continuation helper or changing Islaris infrastructure.

## Architectural Fix (loop theorem, intact)

The load failure was not caused by `instr_pre` discarding the loop invariant.
The pure invariant facts survive the `b.cs` branch, but the original proof
stopped at the semantic-memory subgoal before converting the non-taken branch's
raw carry equality into the strict bound needed by the array-read automation.

The proof now:

1. proves `no_carry_to_lt`, which converts the real AArch64 comparison result on
   the non-taken branch into `bv_unsigned i < bv_unsigned len`;
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

## Preserved Invariant

`linear_search_loop_spec` still contains all required properties:

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

Result: exit status 0.

```text
Tactic call liARun ran for 5.9-6.0 secs (success)   (loop lemma)
Tactic call liARun ran for 9.5-9.9 secs (success)   (loop lemma)
Tactic call liARun ran for 2.3 secs        (success)   (top-level handover)
```

Exact kernel check command:

```bash
eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqchk -silent -R /home/ubuntu/asm-verification/armored/linear_search/traces isla.instructions.linear_search mod8addr_lemmas linear_search_proof
```

Result: exit status 0 with no output. `Print Assumptions linear_search_loop`
reported **Closed under the global context**.

## Next Scope

Top-level `linear_search` Qed remains blocked (see the residual-goals section).
Termination remains out of scope.