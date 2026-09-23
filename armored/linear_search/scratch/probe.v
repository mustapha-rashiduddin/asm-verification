Require Import isla.aarch64.aarch64.
From isla.instructions.linear_search Require Import instrs.

Section probe.
Context `{!islaG Σ} `{!threadG}.

(* Can an instr_pre for the not-found epilogue be derived from the code plus a
   caller continuation?  Probe the goal shape. *)
Lemma probe_nf_epilogue :
  instr 0x0000000010300020 (Some a20) -∗
  instr 0x0000000010300024 (Some a24) -∗
  (∀ (ret : bv 64), instr_pre (bv_unsigned ret) (
     ∃ (r0 r1 r2 r3 r4 : bv 64),
       "R0" ↦ᵣ RVal_Bits r0 ∗ "R1" ↦ᵣ RVal_Bits r1 ∗ "R2" ↦ᵣ RVal_Bits r2 ∗
       "R3" ↦ᵣ RVal_Bits r3 ∗ "R4" ↦ᵣ RVal_Bits r4 ∗ True
  )) -∗
  instr_pre 0x0000000010300020 (
     ∃ (base len tgt ret : bv 64) (data : list (bv 64)) (i' tmp : bv 64),
     reg_col sys_regs ∗
     reg_col CNVZ_regs ∗
     "R0" ↦ᵣ RVal_Bits base ∗
     "R1" ↦ᵣ RVal_Bits len ∗
     "R2" ↦ᵣ RVal_Bits tgt ∗
     "R3" ↦ᵣ RVal_Bits i' ∗
     "R4" ↦ᵣ RVal_Bits tmp ∗
     "R30" ↦ᵣ RVal_Bits ret ∗
     bv_unsigned base ↦ₘ∗ data ∗
     ⌜bv_unsigned i' = bv_unsigned len⌝ ∗
     ⌜bv_unsigned len = length data⌝ ∗
     ⌜∀ j, (j < Z.to_nat (bv_unsigned i'))%nat → data !! j ≠ Some tgt⌝
  ).
Proof.
  iStartProof.
  iIntros "Ha20 Ha24 Hcont".
  iApply (instr_pre_intro_Some true _ a20).
  iIntros "Hpre HPC".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  (* continue *)
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  (* continue *) 
Abort.

End probe.
