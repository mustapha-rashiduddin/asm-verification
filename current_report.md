# linear_search Islaris proof — current status

## Goal
Finish `armored/linear_search/linear_search_proof.v`:
`Qed` `linear_search_loop` (no leftover/shelved goals), write the `linear_search`
main theorem, no `Admitted`, `Print Assumptions linear_search` closed, append
`worklog.md` §13, commit/push `master`.

## Layout
- 0x0 `mov x3,xzr`; 0x4 `cmp x3,x1`; 0x8 `b.cs 0x20` (i>=len, not-found);
  0xc `ldr x4,[x0,x3,lsl#3]`; 0x10 `cmp x4,x2`; 0x14 `b.eq 0x28` (found);
  0x18 `add x3,x3,#1`; 0x1c `b 0x4`; 0x20 `mvn x0,xzr`; 0x24 `ret`;
  0x28 `mov x0,x3`; 0x2c `ret`.
- Contract: R0 array base (8-aligned, `base + len*8 < 2^52`), R1 len, R2 tgt;
  returns first index or UINT64_MAX; memory preserved.

## Current spec shape (after reshaping)
Loop-spec base (unchanged, not weakened):
`i <= len`, `len = length data`, `base mod 8 = 0`,
`base + len*8 < 2^52`, `forall j < i, data !! j <> Some tgt`.

Exit bodies (now minimal, flag/computation-derivable claims only):
- `instr_pre 0x20` (not-found): `regs * array * ⌜i = len⌝`
  -- `len = length data` removed from this body.
- `instr_pre 0x28` (found): `regs * array * ⌜i < len⌝ * ⌜data !! i = Some tgt⌝`
  -- `len = length data` removed from this body.

## Exact remaining residuals after `all: first [...]` (res30)
Both pure/load goals with no free pure facts in context.

1. `⌜bv_unsigned i = bv_unsigned len⌝` (0x20-exit intro claim; res30:45)
   - Context: 7 `instr` hyps + spatial `instr_pre 0x4` formula + persistent
     `instr_pre 0x28`. No PSTATE flags, no regs, no array, no pure hyps.
   - Needs the b.cs-taken carry-out fact; the flag/overflow hypothesis is not
     in this goal's context (it was present in earlier runs and was closed by
     the `overflow_to_le` bullet).

2. `find_in_context (FindMemMapsTo (bv_unsigned LET13))` (0xc `ldr`; res30:107)
   - Context has `R0↦base`, `R1↦len`, `R3↦i`, `base ↦ₘ* data`, flags, but none
     of `base mod 8 = 0`, `len = length data`, `i <= len`.
   - Array split via `MKArray` needs `(LET13 - base) mod 8 = 0`,
     `i0 = (LET13 - base) div 8`, `i0 < length data`;
     `i0 < length data` needs `i <= len ∧ len = length data`.

## Root cause (Iris/Lithium invariant-design)
The loop-invariant pure facts live only inside the `instr_pre 0x4` formula.
Lithium treats that formula as "checked on fetch then discarded", NOT as
usable pure hypotheses in the loop body. The two residuals are thus two faces
of the same fact: the pure facts (`len = length data`, `base mod 8 = 0`,
array bound, `i <= len`) never surface at the point of use (0xc load and the
exit intros). The C-flag record is consumed by the branch; the constant block
never escapes the locked formula.

## What has been tried
- `iDestruct select (instr_pre _ _)` -- selects the hyp but
  `iExistDestruct: cannot destruct` (∃ sits behind `▷?is_later` in
  `instr_pre'_def`, lifting.v:123).
- `iApply (find_in_context_mem_mapsto_semantic _)` -- cannot unify the λ/`match`
  continuation.
- `liARun`, `bv_solve`, `iFrame`, `all: try liARun` on the residuals -- no-ops
  (facts unreachable as hyps).
- Removed the `forall j` claims and then `len = length data` from both exit
  bodies; the residual set rebalances but a pure claim (or the load find)
  always survives.

## Suggested next moves (not yet executed)
1. Add a persistent `□ ⌜...⌝` copy of the constant invariant block
   (len = length data, base mod-8, array bound) as a conjunct of the loop-spec
   base, so the facts enter the persistent pure context when the spec is
   introed and are available at the 0xc find and exit intros. Risk: on first
   entry that copy must itself be checkable.
2. Reverse-engineer how `wp_next_instr_pre`/lithium treats spec-intro pure
   claims -- whether intro'ed pure claims can be retained as usable hyps.
3. Restructure like binary_search (larger change; exits handled in main
   theorem).

## Files
- proof: armored/linear_search/linear_search_proof.v (tail: debug RESID print + 'Show Proof.' before Qed)
- references: ~/rems/islaris/theories/automation.v, lifting.v, ghost_state.v;
  ~/rems/islaris/examples/binary_search.v (works; exit-claims subset of
  invariant pattern).