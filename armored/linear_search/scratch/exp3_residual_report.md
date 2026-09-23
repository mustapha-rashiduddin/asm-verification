# exp3 residual report — hypothesis-free exit composition

Date: 2026-09-23 · Branch of work: `scratch/exp3.v` only (UNTRACKED, nothing committed).

## What was approved and tried
User-approved option 1: pin each `linear_search_loop_spec` exit's `ret` to the loop
invariant's own `"R30"` binder (`linear_search_nf_spec_ep ret` /
`linear_search_f_spec_ep ret`, `scratch/exp3.v:86-121`), re-prove
`linear_search_loop`, retry the hypothesis-free top-level `linear_search`.

## What works (this session)
- Pinning change in place: the loop spec's trailing exits are
  `instr_pre 0x...0020 (linear_search_nf_spec_ep ret) ∗
   instr_pre 0x...0028 (linear_search_f_spec_ep ret)` (`exp3.v:146-147`),
  where `ret` is the loop invariant's own `"R30" ↦ᵣ RVal_Bits ret` binder.
- `linear_search_loop` RE-PROVES (`Time Qed.` at `exp3.v:334`) with the pinned exits.
- Pinning is semantically correct: the return address the exit machinery looks up
  is now the genuine machine R30. Pre-pin the jump target was the existential
  `ret0` (rigid-unification blocker `unify ret0 ret`); post-pin `liARun` runs
  `mvn; ret` and reaches `find_in_context (FindInstrKind (bv_unsigned ret) true)`
  — the target is `bv_unsigned ret`, the CALLER's actual return address, and the
  single affine continuation `instr_pre (bv_unsigned ret) (c_call_ret ...)` is
  found and consumed (`liARun` then lands in the c_call-return obligation).
- The hypothesis-free top-level `linear_search` (`exp3.v:360`, `Abort` at :420)
  FAILS at two independent structural walls. The file otherwise compiles clean
  (`coqc ... scratch/exp3.v`, exit 0).

## Wall 1 — exit premise memory cannot be re-pinned (frame-memory pin)
After producing `instr_pre 271581216 (nf_ep ret)` via `instr_pre_intro_Some`,
the premise must be intro'd. Its `∃` witnesses can only be `iDestruct`'d as
rigid Coq binders; they cannot be unified against the wp frame.  Running the
exit (mvn→R0=UINT64_MAX, a24 ret→R30=ret) consumes the caller continuation and
stops at the c_call-return obligation:

```
base, len, tgt : bv 64            data0 : list (bv 64)
i', tmp : bv 64
Heq_i  : bv_unsigned i' = bv_unsigned len
Hlen_eq: bv_unsigned len = length data0
Hnmis  : ∀ j, (j < Z.to_nat (bv_unsigned i'))%nat → data0 !! j ≠ Some tgt
------------------------------------------------□
"Hmem" : bv_unsigned base ↦ₘ∗ data0
------------------------------------------------∗
bv_unsigned b0  ↦ₘ∗ data ∗
⌜bv_unsigned 18446744073709551615 = bv_modulus 64 - 1
 ∧ (∀ j : nat, data !! j ≠ Some b2)
 ∨ …⌝ ∗ True
```
`iFrame`/`iFrame "Hmem"` cannot close `bv_unsigned b0 ↦ₘ∗ data`: `base`/`data0`
are rigid and nothing in scope relates them to `b0`/`data`.  When the SAME exit
spec is intro'd by the WP as a continuation (the flat-hypothesis baseline in
`../linear_search_proof.v:327-349`, or `exp3.v:431` `linear_search_debug`),
the witnesses arrive as EVARS and unify with the frame — which is exactly why
the hypothesis-based proof closes. In the hypothesis-free version the exits
are not WP continuations, so no evar-pinning happens.

## Wall 2 — one affine continuation, two exits
The residual after `liARun` on the top-level subsumption demands BOTH exits:

```
instr_pre 271581216 (linear_search_nf_spec_ep ret) ∗
instr_pre 271581224 (linear_search_f_spec_ep ret)
```
`iSplitR "Ha20"` (or `iSplitL "Ha20"`) gives the single affine caller
continuation to ONE branch; the other branch has no continuation for its
`ret`.  With `iSplitL "Ha20"` the smallest exact residual is:

```
"Ha20" : instr 271581216 (Some a20)
"Hcnv" : reg_col CNVZ_regs
"HR1" : "R1" ↦ᵣ RVal_Bits len
"HR2" : "R2" ↦ᵣ RVal_Bits tgt
"HR3" : "R3" ↦ᵣ RVal_Bits i'
"HR4" : "R4" ↦ᵣ RVal_Bits tmp
"Hmem" : bv_unsigned base ↦ₘ∗ data0
_ : "R0" ↦ᵣ RVal_Bits 18446744073709551615%bv
_ : reg_col sys_regs
_ : "R30" ↦ᵣ RVal_Bits ret
------------------------------------------------∗
find_in_context (FindInstrKind (bv_unsigned ret) true) …
```
No `instr_pre (bv_unsigned ret) (c_call_ret …)` candidate exists in scope.
`instr_pre` is **not** persistent (probes: `probe_pers.v`, `t_persist.v` fail),
so the one continuation cannot be duplicated across two exit constructions.

## Smallest exact residual
The a20-side c_call-return obligation of Wall 1 (with the pinned `ret` reached,
memory rebind `base↦data0 → b0↦data` open), and the Wall-2
`find_in_context (FindInstrKind (bv_unsigned ret) true)` goal that appears on
whichever branch lacks the single affine continuation.

## Pending design options (both still scratch-only)
1. `scratch/exp2_residual_report.md`: restructure `linear_search_loop` to run
   the exits inside the loop lemma and conclude
   `instr_body 0x4 loop_spec ∗ instr_pre 0x20 (nf_ep ret) ∗ instr_pre 0x28 (f_ep ret)`
   so the top-level residual closes by `iFrame` — needs resolving how the
   exit premises get evar-pinned inside the loop lemma (same Wall-1 mechanism).
2. Keep the pinned exits and move only the CONTINUATION-rich work into the loop
   lemma (e.g., deliver the exits with the caller continuation already applied).

## Notes / rules in force
- `linear_search_spec`, all facts (first-match, nowhere-found, unchanged-array
  ownership, bounds, alignment, range, length) unchanged.
- No `Admitted`/`admit`/`Axiom`; no assembly/trace changes; production files
  untouched (`../linear_search_proof.v` baseline is untouched and green).
- Nothing committed or pushed; `scratch/exp3.v` and this report are untracked.
- Evidence logs: `/tmp/opencode/exp3_green.log` (Wall 1, lines 82-91),
  `/tmp/opencode/exp3_wall2.log` (Wall 2, lines 82-93), plus earlier
  `/tmp/opencode/exp3_iSplitR.log`, `exp3_presplit.log`, `exp3_a20show.log`.