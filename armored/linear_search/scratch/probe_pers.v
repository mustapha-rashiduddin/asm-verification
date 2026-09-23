Require Import isla.aarch64.aarch64.
From isla.instructions.linear_search Require Import instrs.

Section t.
Context `{!islaG Σ} `{!threadG}.

Lemma wand_pers (P Q : iProp Σ) : Persistent (P -∗ Q).
Proof. apply _. Qed.

Lemma instr_pers a ins : Persistent (instr a ins).
Proof. apply _. Qed.

Lemma arch_pc_wand_pers (a : Z) (t : isla_trace) :
  Persistent (arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 a) -∗ WPasm t).
Proof. apply _. Qed.

End t.