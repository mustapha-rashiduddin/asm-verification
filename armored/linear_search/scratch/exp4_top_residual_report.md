# exp4 top-level residual report — monolithic liARun loses exit identity witnesses

Date: 2026-09-24 · Branch of work: `armored/linear_search/scratch/exp4.v` (+ iteration copy `scratch/exp4_iter.v`), top-level `linear_search_from_loop` only. Scratch `.v` files UNTRACKED; only this report is committed, per the exp2/exp3/exp4 convention.

## What this session found

The deferred top-level rebuild (`linear_search_from_loop` in `scratch/exp4.v:432-483`,  target: a genuine `Qed`) was attempted against the approved additive-`∧` loop spec. The loop lemma `linear_search_loop` **Qeds** (`scratch/exp4.v:391`, checked trimmed in `scratch/exp4_assump.v`, `Print Assumptions` closed). The top level does NOT yet Qed.

## The attempt (monolithic `liARun`)

`linear_search_from_loop` (statement at `scratch/exp4.v:434-447`) is entered as `instr_body 0x0 (linear_search_spec stack_size)`. The proof runs the whole region in one push:

- `liARun` (exp4_iter.v:452) then `Unshelve`/`prepare_sidecond`/`bv_solve` barriers, including two `all: try … liARun` drains (exp4_iter.v:462-467, 473-479) that additionally e.g. apply `no_carry_to_lt` on the b.cs/carry side-conditions.
- The final `Unshelve` (exp4_iter.v:481-482) exposes **four** residual goals, intended to be closed loop-lemma-style: project one side of the `∧` exits with `iDestruct select (instr_pre 0x20 _ ∧ instr_pre 0x28 _)`, then `iApply (find_in_context_instr_kind_pre_true <addr> _)`, `iExists true, (linear_search_nf_spec_ep ret)` / `(linear_search_f_spec_ep ret)`, `iFrame`, `liARun`, pure close.
- Those four `iDestruct select (∧)` calls all fail with `No matching clauses for match.` (e.g. `/tmp/opencode/iter10.log` line 512).

## Verified residual shape (bullet 1, the not-found/0x20 path)

`Show` at `scratch/exp4_iter.v:484` (full, readable dump in `/tmp/opencode/iter10.log` lines 422-509):

```
Context (Coq level):
  stack_size, _Hyp_: 0 ≤ stack_size      sp, ret, b0..b18 : bv 64
  data : list (bv 64)
  H2 : bv_unsigned b1 = length data
  H3 : bv_unsigned b0 `mod` 8 = 0
  H4 : bv_unsigned b0 + length data * 8 < 2 ^ 52
  base, len, tgt : bv 64          data0 : list (bv 64)          i', tmp : bv 64
  H5 : bv_unsigned i' = bv_unsigned len
  H6 : bv_unsigned len = length data0
  H7 : ∀ j, (j < Z.to_nat (bv_unsigned i'))%nat → data0 !! j ≠ Some tgt

Goal (envs):
  #Hloop : instr_body 271581188 (loop spec, ∃-cropped: regs + reg_col + mem + pure + the ∧ exits)
  --------------------------------------□
  _ : bv_unsigned base ↦ₘ∗ data0            ← the ONLY spatial hypothesis
  --------------------------------------∗
  bv_unsigned b0 ↦ₘ∗ data ∗
  ⌜(bv_unsigned 18446744073709551615 = bv_modulus 64 - 1 ∧ ∀ j, data !! j ≠ Some b2)
   ∨ bv_unsigned 18446744073709551615 < length data
     ∧ data !! Z.to_nat (bv_unsigned 18446744073709551615) = Some b2
       ∧ ∀ j, (j < Z.to_nat (bv_unsigned 18446744073709551615))%nat → data !! j ≠ Some b2⌝ ∗ True
```

So the four residuals are **not** `find_in_context (FindInstrKind 0x20/0x28)` transfer goals (loop-lemma style). They are the **caller c_call-return contracts**: the returned value is already fixed (`R0 = UINT64_MAX` on the 0x20 path), the exit + epilogue + `ret` have already been executed by the drain scripts, and only the memory-frame + the pure result disjunction remain.

## Root cause: exit-∃ variables never unified, so no identity witnesses survive

Why it is unreachable as standing:

1. The exits were NOT hand-closed identity-preserving (loop-lemma style, `scratch/exp4.v:347-370`: `iFrame "Hnf_"/"Hf_"` **unifies** the `linear_search_…_spec_ep` ∃-binders `base₀/len₀/tgt₀/data₀/i'₀/tmp₀` against the actual register file, so `base₀ := b0`, `tgt₀ := b2`, `ret₀ := real R30`, etc.). Instead the `all: try … liARun` drains consumed the exit finds, leaving those ∃-binders **free** in scope as `base, len, tgt, data0, i', tmp`.
2. The spatial context therefore still holds the exit's array `bv_unsigned base ↦ₘ∗ data0` with `base ≠ b0` (verified raw: `/tmp/opencode/iter8.log`/`iter9.log` — the `Envs`' `env_spatial` is a single `Esnoc` containing only `mem_mapsto_array base data0`).
3. The goal demands `bv_unsigned b0 ↦ₘ∗ data` and the full-array negation `∀ j, data !! j ≠ Some b2`. There is **no hypothesis `base = b0`, `data0 = data`, or `tgt = b2`**, so `iFrame` cannot close it (confirmed: `iFrame.` makes no progress on the residual). The nf pure facts (H5-H7: `i' = len`, `len = length data0`, `∀ j < i', data0 !! j ≠ tgt`) only derive the goal if those identities are in hand.

## Fix direction (for the next session / CTO review)

Restructure `linear_search_from_loop` so the exits are closed the way the verified loop lemma closes them, i.e.:

1. Do NOT let the `all: try … liARun` scripts (exp4_iter.v:462-467, 473-479) silently swallow the four exit finds.
2. Surface the `find_in_context (FindInstrKind 0x20/0x28 …)` goals at a `Unshelve` and hand-close them with the identity-preserving sequence: `iDestruct select (… ∧ …)` → `iApply (find_in_context_instr_kind_pre_true <addr> _)` → `iExists true, (linear_search_nf_spec_ep ret)` / `(linear_search_f_spec_ep ret)` → `iFrame "Hnf_"/"Hf_"` (this is what unifies `base₀ := b0`, `data₀ := data`, `tgt₀ := b2`, `ret₀ := R30`) → then continue the epilogue + `ret` and close the caller-return goal with `iFrame` + the pure `or` (mirroring production `linear_search`, `linear_search_proof.v:333-348`, which Qeds with only a pure residual).
3. As a consequence the top-level c_call-return goals regain their identity witnesses and become `iFrame`-+pure closable, exactly like the verified loop lemma and the production proof.

Alternative considered but not pursued: proving the identities post-hoc (`base = b0`, …) from the affine register/memory uniqueness inside the residual is not possible — all register resources are already consumed and no equality hypotheses survive, so the residual cannot be repaired in place.

## Independent, trivial issue noted

The final `linear_search` (`scratch/exp4.v:493-528`) currently fails at its closing `iModIntro` with `iStartProof: not a BI assertion: (0 ≤ stack_size)` — the `0 ≤ stack_size` subgoal from `iApply (linear_search_from_loop stack_size)` is not discharged by `all: try iAssumption`; needs a `lia`/`exact` for that subgoal. Not part of the loop/top-level wall.

## Evidence logs

- `/tmp/opencode/exp4_now.log` — baseline exp4.v compile (fails at `linear_search`, the `0 ≤ stack_size` hiccup).
- `/tmp/opencode/iter10.log` — readable `Show` of the bullet-1 residual (lines 422-509) + `No matching clauses` at the `iDestruct select (∧)` (line 512).
- `/tmp/opencode/iter8.log`, `/tmp/opencode/iter9.log` — raw `Envs` dumps proving `env_spatial` contains only the array `mem_mapsto base data0` and no regs/`∧` exit hypotheses.
- `/tmp/opencode/exp4_clean.log`, `/tmp/opencode/exp4_assump.log`, `/tmp/opencode/exp4_coqchk.log` — loop-lemma Qed / trimmed-module / coqchk evidence from the exp4 round (still green).

## Notes / rules in force

- `linear_search_spec`, `linear_search_loop_spec`, the nf/f ep specs, and the loop lemma are unchanged; the loop lemma is a genuine `Qed`.
- No `Admitted`/`admit`/`Axiom`; no assembly/trace changes; production `../linear_search_proof.v` untouched.
- Scratch `.v` files untracked; only this report is committed.
- The top-level rebuild was deferred pending CTO review in the exp4 report; this report is the review artifact for that deferral.