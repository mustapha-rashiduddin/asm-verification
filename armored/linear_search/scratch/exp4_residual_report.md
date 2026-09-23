# exp4 residual report — additive `∧` exits, loop lemma Qed

Date: 2026-09-23 · Branch of work: `scratch/exp4.v` only (scratch `.v` files
UNTRACKED; only this report is committed, per the exp2/exp3 convention).

## What was approved and tried

Additive-exit variant of the hypothesis-free refactor: a single
`linear_search_loop_spec` whose two trailing exits are
`instr_pre` targets CONJOINED with `∧` (not `∗`-separated), each pinned to the
loop invariant's own `"R30"` binder `ret`:

```
instr_pre 0x0000000010300020 (linear_search_nf_spec_ep ret) ∧
instr_pre 0x0000000010300028 (linear_search_f_spec_ep ret)
```

(`scratch/exp4.v:149-150`). Goal: re-prove `linear_search_loop` directly against
this one spec, then rebuild the hypothesis-free top-level `linear_search`.
Per CTO direction the top-level rebuild is deferred; this report covers the
Qed'd loop lemma and its verification.

## What works (this session)

- `linear_search_loop` **Qeds** against the additive spec (`Time Qed.` at
  `scratch/exp4.v:391`) — genuine Qed, zero residual/shelved goals when checked
  in the trimmed module `scratch/exp4_assump.v` (exp4.v lines 1-391 + `End proof.`).

- Proof shape: direct WP reasoning (`liARun` + documented `Unshelve`/
  `prepare_sidecond` barriers). Because `lithium/FindInstrKind` does not descend
  through `∧`, the four `find_in_context (FindInstrKind 0x20/0x28 true)`
  residuals (b.cs-taken, b.eq-taken; plain-wp and li_instr_pre continuations)
  are resolved by hand:
  - project one side of the `∧` with a pure `iDestruct select (… ∧ …)`
    (`"[Hnf_ _]"` / `"[_ Hf_]"`),
  - `iApply (find_in_context_instr_kind_pre_true <addr> _)`,
  - `iExists true, (linear_search_nf_spec_ep ret)` / `(linear_search_f_spec_ep ret)`,
  - `iFrame`, `liARun`, then a trivial `iPureIntro` close.
  The fifth bullet is the pure `data !! j ≠ Some tgt` (S(i+1) mismatch),
  kept from the baseline.
- Ending reuses the exp3 closing sequence: `prepare_sidecond` materializes the
  pure sideconds into clean/matchable Coq hypotheses (the `SHELVED_SIDECOND`
  residuals otherwise carry evar-typed hypotheses that `match goal` cannot
  bind), then the exp3 `Hlookup`-match (`replace want with idx by bv_solve;
  replace htgt with value by bv_solve; exact Hlookup`) closes the exit's
  `data !! Z.to_nat (bv_unsigned i) = Some tgt`; the `i = len` exit closes via
  the `carry_to_le`/`bv_simplify_arith`/`lia` block.

- Both exits use the REAL machine R30: `linear_search_loop_spec` pins
  `"R30" ↦ᵣ RVal_Bits ret` (line 142) and both trailing exits are parameterized
  by that same `ret`; each ep spec (`linear_search_nf_spec_ep` /
  `linear_search_f_spec_ep`, lines 86-121) contains the register resource
  `"R30" ↦ᵣ RVal_Bits ret0` — the `ret`s at a24/a2c jump to the genuine
  caller-return address, so `liARun` on the exits lands in the c_call-return
  obligation.

## Spec contents (all still present, unchanged)

`linear_search_loop_spec` (exp4.v:133-153):

- `bv_unsigned i ≤ bv_unsigned len`
- `bv_unsigned len = length data`
- `bv_unsigned base `mod` 8 = 0`
- `bv_unsigned base + bv_unsigned len * 8 < 2 ^ 52`
- `∀ j, (j < Z.to_nat (bv_unsigned i))%nat → data !! j ≠ Some tgt`
- ownership of the complete array `bv_unsigned base ↦ₘ∗ data`
- regs `sys_regs`, `CNVZ_regs`, `R0`=`base`, `R1`=`len`, `R2`=`tgt`,
  `R3`=`i`, `R4`=`tmp`, `R30`=`ret`
- the additive `∧` exits above.

`linear_search_nf_spec_ep ret0` (not-found): memory ownership,
`bv_unsigned i' = bv_unsigned len`, `len = length data`,
`∀ j < i', data !! j ≠ Some tgt`.

`linear_search_f_spec_ep ret0` (found): memory ownership,
`bv_unsigned i' < bv_unsigned len`, `len = length data`,
`data !! Z.to_nat (bv_unsigned i') = Some tgt`,
`∀ j < i', data !! j ≠ Some tgt`.

(Alignment and address-range live in the loop invariant; the exits carry the
regs incl. R30, memory, length, and the result facts the epilogue needs.)

## Clean verification

Working directory:

`/home/ubuntu/asm-verification/armored/linear_search`

Exact commands:

```bash
eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)"
export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib
# (a) full scratch file (fresh .vo): loop lemma Qeds, then the still-deferred
#     top-level stops at its in-progress iIntros (2 goals) — expected.
coqc -Q scratch/scratch "" -R traces isla.instructions.linear_search scratch/exp4.v
# (b) trimmed module through the loop lemma only — exit 0.
coqc -Q scratch/scratch "" -R traces isla.instructions.linear_search scratch/exp4_assump.v
# (c) kernel check — "Modules were successfully checked".
coqchk -Q scratch "" -R traces isla.instructions.linear_search exp4_assump
```

Results:

```text
Tactic call liARun ran for ~6.1 / ~11.5 / ~0.4 / ~0.5 / ~0.6 / ~0.7 secs  (6 liARuns, all success)
Finished transaction in 9.3 secs (successful)      (linear_search_loop Qed)
```

`Print Assumptions linear_search_loop.` → **Closed under the global context**
(no axioms). `grep -n "Admitted\|admit\|Axiom\|Abort"` over exp4.v → no
`Admitted`/`admit`/`Axiom`; only two `Abort.` in the deferred top-level
(`linear_search`, line 478) and the legacy `linear_search_debug` probe
(line 534) — neither in the loop lemma. No assembly or generated-trace changes;
no termination claim.

## Helper lemmas

None added. The nine lemmas the loop proof uses (`overflow_to_le`,
`bv_wrap_64_neg_one`, `bv_modulus_64_eq`, `bv_modulus_128_eq`, `carry_wrap_le`,
`carry_to_le`, `bv_sub_extract_neq_zero`,
`bv_wrap_neq_zero_to_unsigned_neq`, `no_carry_to_lt`) are the identical set as
the exp3 baseline. Library lemmas used: `find_in_context_instr_kind_pre_true`,
`instr_pre`, `liARun`, `prepare_sidecond`.

## Next Scope

Rebuild the hypothesis-free top-level `linear_search` (exp4.v:417-478,
currently `Abort`) against the additive loop spec: after the loop wp resolves,
the two exit-branch goals are the a20 (nf, returns UINT64_MAX) and a28 (f,
returns the index) wp obligations; each must intro its `instr_pre` exit, run the
exit instructions, and close the c_call-return contract via the caller
continuation `instr_pre (bv_unsigned ret) (c_call_ret …)` (the exp3-reported
WALL-1/WALL-2 rigidity concerns apply). Deferred pending CTO review.

## Notes / rules in force

- `linear_search_spec` (public contract) and all functional facts unchanged.
- No `Admitted`/`admit`/`Axiom`; no assembly/trace changes; production
  `../linear_search_proof.v` untouched.
- Scratch `.v` files untracked (per convention); only this report is committed.
- Evidence logs: `/tmp/opencode/exp4_clean.log` (full-file clean compile, loop
  lemma Qed at line 8), `/tmp/opencode/exp4_assump.log` (trimmed module, exit 0,
  Print Assumptions "Closed under the global context"), `/tmp/opencode/exp4_coqchk.log`
  (coqchk, "Modules were successfully checked").