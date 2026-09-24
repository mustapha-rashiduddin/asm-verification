(****************************************************************************)
(*                                                                          *)
(*  exp5_term.v: machine-level termination building block for linear_search *)
(*                                                                          *)
(*  Proves, at the level of the ACTUAL Islaris operational semantics        *)
(*  (seq_step / nsteps over the generated traces a4 .. a1c), that the       *)
(*  back-edge                                                               *)
(*                                                                          *)
(*      PC = 0x10300004  ->(a4 cmp; a8 b.cs fall; ac ldr; a10 cmp;          *)
(*                          a14 b.eq fall; a18 add; a1c b 0x04)->           *)
(*      PC = 0x10300004                                                     *)
(*                                                                          *)
(*  is executable in a finite number of real seq_step steps, finishes at    *)
(*  the instruction boundary PC = 0x10300004 with R3 = i + 1, R0=base,      *)
(*  R1=len, R2=tgt, and memory unchanged, and hence the natural-number      *)
(*  variant (len - i) strictly decreases.                                   *)
(*                                                                          *)
(****************************************************************************)

From Coq.ssr Require Import ssreflect.
From stdpp Require Import prelude gmap.
From stdpp.bitvector Require Import definitions.
From iris.program_logic Require Export language.
Require Import isla.opsem.
Require Import isla.aarch64.aarch64.
From isla.instructions.linear_search Require Import instrs.

Open Scope Z_scope.

(* ------------------------------------------------------------------------ *)
(* Addresses of the linear_search code words (base 0x10300000).             *)
(* ------------------------------------------------------------------------ *)

Definition ADDR0  : bv 64 := BV 64 0x10300000.
Definition ADDR4  : bv 64 := BV 64 0x10300004.
Definition ADDR8  : bv 64 := BV 64 0x10300008.
Definition ADDrc  : bv 64 := BV 64 0x1030000c.
Definition ADDR10 : bv 64 := BV 64 0x10300010.
Definition ADDR14 : bv 64 := BV 64 0x10300014.
Definition ADDR18 : bv 64 := BV 64 0x10300018.
Definition ADDR1c : bv 64 := BV 64 0x1030001c.

(* The authoritative instruction table for the loop body.  During one back
   edge the machine visits exactly the 7 code words 0x04 .. 0x1c; the
   instruction fetch ([LDone]) looks the successor up in this map. *)
Definition ls_instrs : gmap (bv 64) isla_trace :=
  <[ ADDR4  := a4  ]> $
  <[ ADDR8  := a8  ]> $
  <[ ADDrc  := ac  ]> $
  <[ ADDR10 := a10 ]> $
  <[ ADDR14 := a14 ]> $
  <[ ADDR18 := a18 ]> $
  <[ ADDR1c := a1c ]> $ ∅.

(* ------------------------------------------------------------------------ *)
(* The register file.                                                       *)
(*                                                                          *)
(* A transparent copy of the standard AArch64 initial system-register state  *)
(* (the values match exactly the AssumeReg events of the generated traces), *)
(* layered with the caller frame: R0 = base, R1 = len, R2 = tgt, R3 = i,    *)
(* R4 = (don't care), _PC = pc.                                             *)
(* ------------------------------------------------------------------------ *)

Definition ls_sys_regs : reg_map :=
  <[ "PSTATE" := RegVal_Struct
    [("N", RVal_Bits (BV 1 0)); ("Z", RVal_Bits (BV 1 0));
     ("C", RVal_Bits (BV 1 0)); ("V", RVal_Bits (BV 1 0));
     ("D", RVal_Bits (BV 1 0)); ("SP", RVal_Bits (BV 1 1));
     ("EL", RVal_Bits (BV 2 2)); ("nRW", RVal_Bits (BV 1 0))] ]> $
  <[ "SCTLR_EL2" := RVal_Bits (BV 64 0x0000000004000002) ]> $
  <[ "SCR_EL3" := RVal_Bits (BV 32 0x00000501) ]> $
  <[ "TCR_EL2" := RVal_Bits (BV 64 0) ]> $
  <[ "HCR_EL2" := RVal_Bits (BV 64 0x0000000080000000) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL0" := RVal_Bits (BV 4 1) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL1" := RVal_Bits (BV 4 1) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL2" := RVal_Bits (BV 4 1) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL3" := RVal_Bits (BV 4 1) ]> $
  <[ "OSLSR_EL1" := RVal_Bits (BV 32 0) ]> $
  <[ "OSDLR_EL1" := RVal_Bits (BV 32 0) ]> $
  <[ "EDSCR" := RVal_Bits (BV 32 0) ]> $
  <[ "MPIDR_EL1" := RVal_Bits (BV 64 0) ]> $
  <[ "MDSCR_EL1" := RVal_Bits (BV 32 0) ]> $
  <[ "MDCR_EL2" := RVal_Bits (BV 32 0) ]> $
  <[ "MDCR_EL3" := RVal_Bits (BV 32 0) ]> $
  <[ "__isla_monomorphize_writes" := RVal_Bool false ]> $
  <[ "__isla_monomorphize_reads" := RVal_Bool false ]> $
  <[ "__highest_el_aarch32" := RVal_Bool false ]> $
  <[ "__CNTControlBase" := RVal_Bits (BV 52 0) ]> $
  <[ "__v85_implemented" := RVal_Bool false ]> $
  <[ "__v84_implemented" := RVal_Bool false ]> $
  <[ "__v83_implemented" := RVal_Bool false ]> $
  <[ "__v82_implemented" := RVal_Bool false ]> $
  <[ "__v81_implemented" := RVal_Bool true ]> $
  <[ "__trickbox_enabled" := RVal_Bool false ]> $ ∅.

Definition ls_regs (base len tgt i : bv 64) (r4 : bv 64) (pc : bv 64) : reg_map :=
  <[ "_PC" := RVal_Bits pc ]> $
  <[ "R4" := RVal_Bits r4 ]> $
  <[ "R3" := RVal_Bits i ]> $
  <[ "R2" := RVal_Bits tgt ]> $
  <[ "R1" := RVal_Bits len ]> $
  <[ "R0" := RVal_Bits base ]> $
  ls_sys_regs.

(* A machine state sitting at an instruction boundary with a given trace. *)
Definition ls_θ (t : isla_trace) (regs : reg_map) : seq_local_state :=
  {| seq_trace := t; seq_regs := regs; seq_pc_reg := "_PC"; seq_nb_state := false; |}.

Definition ls_σ (mem : mem_map) : seq_global_state :=
  {| seq_instrs := ls_instrs; seq_mem := mem; |}.

(* ------------------------------------------------------------------------ *)
(* Small infrastructure over Iris's nsteps.                                 *)
(* ------------------------------------------------------------------------ *)

Lemma step_single' (κ : list seq_label) (e1 : seq_local_state) (σ1 : seq_global_state)
      (e2 : seq_local_state) (σ2 : seq_global_state) :
  seq_step e1 σ1 κ e2 σ2 [] ->
  step ([e1], σ1) κ ([e2], σ2).
Proof.
  move => Hs.
  eapply (step_atomic e1 σ1 e2 σ2 [] [] []).
  - reflexivity.
  - reflexivity.
  - exact Hs.
Qed.

Lemma nsteps_step n ρ1 ρ2 ρ3 (κs : list (observation isla_lang)) :
  step ρ1 [] ρ2 ->
  nsteps n ρ2 κs ρ3 ->
  nsteps (S n) ρ1 κs ρ3.
Proof.
  move => H1 H2. eapply (nsteps_l _ ρ1 ρ2 ρ3 [] κs); [exact H1 | exact H2].
Qed.

(* ------------------------------------------------------------------------ *)
(* Semantics of the compare: NZCV flag generation in 128-bit arithmetic as   *)
(* computed by the traces a4 / a10.                                         *)
(*                                                                           *)
(* N and V are never read by the downstream branch instructions, so they     *)
(* serve only as structural placeholders inside the flag register.          *)
(* ------------------------------------------------------------------------ *)

Definition cmp_sum128 (a b : bv 64) : bv 128 :=
  bv_add (bv_add (bv_zero_extend 128 a) (bv_zero_extend 128 (bv_not b))) (BV 128 1).

Definition cmp_res64 (a b : bv 64) : bv 64 :=
  bv_extract 0 64 (cmp_sum128 a b).

Definition cmp_flag_n (a b : bv 64) : bv 1 :=
  bv_or (bv_and (BV 1 0) (bv_not (BV 1 1)))
        (bv_extract 0 1 (bv_shiftr (cmp_res64 a b) (BV 64 0x3f))).

Lemma bv_wf_bool_decide_10 (P : Prop) {d : Decision P} :
  BvWf 1 (if bool_decide P then 1 else 0).
Proof. destruct (bool_decide P); vm_compute; done. Qed.

Lemma bv_wf_bool_decide_01 (P : Prop) {d : Decision P} :
  BvWf 1 (if bool_decide P then 0 else 1).
Proof. destruct (bool_decide P); vm_compute; done. Qed.

Definition cmp_flag_z (a b : bv 64) : bv 1 :=
  @BV 1 (if bool_decide (cmp_res64 a b = BV 64 0) then 1 else 0) (bv_wf_bool_decide_10 _).
Definition cmp_flag_c (a b : bv 64) : bv 1 :=
  @BV 1 (if bool_decide
    (bv_unsigned (bv_zero_extend 128 (bv_extract 0 64 (cmp_sum128 a b))) =
     bv_unsigned (cmp_sum128 a b))
    then 0 else 1) (bv_wf_bool_decide_01 _).
Definition cmp_flag_v (a b : bv 64) : bv 1 :=
  @BV 1 (if bool_decide
    (bv_unsigned (bv_sign_extend 128 (cmp_res64 a b)) =
     bv_unsigned (bv_add (bv_add (bv_sign_extend 128 a) (bv_sign_extend 128 (bv_not b))) (BV 128 1)))
    then 0 else 1) (bv_wf_bool_decide_01 _).

(* The four PSTATE flags as written by a cmp trace, as one 4-bit value. *)
Definition cmp_flags (a b : bv 64) : bv 4 :=
  bv_concat 4 (bv_concat 3 (bv_concat 2 (cmp_flag_n a b) (cmp_flag_z a b)) (cmp_flag_c a b)) (cmp_flag_v a b).

Definition pstate_c (a b : bv 64) : bv 1 := bv_extract 1 1 (cmp_flags a b).
Definition pstate_z (a b : bv 64) : bv 1 := bv_extract 2 1 (cmp_flags a b).

Lemma cmp_res64_zero_iff (a b : bv 64) :
  cmp_res64 a b = BV 64 0 ↔ bv_unsigned a = bv_unsigned b.
Proof.
  unfold cmp_res64, cmp_sum128.
  split; intro H.
  - apply bv_eq in H. bv_simplify_arith H. bv_solve.
  - bv_simplify_arith H. bv_solve.
Qed.

Lemma cmp_sum128_zero_ext_iff (a b : bv 64) :
  bv_unsigned (bv_zero_extend 128 (bv_extract 0 64 (cmp_sum128 a b))) = bv_unsigned (cmp_sum128 a b)
  ↔ (bv_unsigned a < bv_unsigned b)%Z.
Proof.
  unfold cmp_sum128.
  split; intro Hlt.
  - bv_simplify_arith Hlt. bv_solve.
  - bv_simplify_arith Hlt. bv_solve.
Qed.

Lemma cmp_flag_z_ne (a b : bv 64) : a ≠ b → cmp_flag_z a b = BV 1 0.
Proof.
  intros Hne.
  apply (proj2 (bv_eq 1 (cmp_flag_z a b) (BV 1 0))).
  cbn [cmp_flag_z bv_unsigned].
  destruct (bool_decide (cmp_res64 a b = BV 64 0)) eqn:Hzeq.
  + exfalso. apply Hne. apply (proj2 (bv_eq 64 a b)).
    apply (proj1 (cmp_res64_zero_iff a b)).
    apply bool_decide_eq_true_1 in Hzeq. exact Hzeq.
  + reflexivity.
Qed.

Lemma cmp_flag_c_lt (a b : bv 64) : (bv_unsigned a < bv_unsigned b)%Z → cmp_flag_c a b = BV 1 0.
Proof.
  intros Hlt.
  apply (proj2 (bv_eq 1 (cmp_flag_c a b) (BV 1 0))).
  simpl.
  destruct (bool_decide (bv_unsigned (bv_zero_extend 128 (bv_extract 0 64 (cmp_sum128 a b))) = bv_unsigned (cmp_sum128 a b))) eqn:Hceq.
  + reflexivity.
  + exfalso. apply bool_decide_eq_false_1 in Hceq.
    apply Hceq.
    apply (proj1 (cmp_sum128_zero_ext_iff a b)).
    exact Hlt.
Qed.

Lemma cmp_flag_z_ne_ct (a b : bv 64) : (bv_unsigned a < bv_unsigned b)%Z → cmp_flag_z a b = BV 1 0.
Proof.
  intros Hlt.
  apply cmp_flag_z_ne.
  intro Hab. apply bv_eq in Hab. revert Hab. lia.
Qed.

Lemma pstate_c_eq_cmp_flag (a b : bv 64) : pstate_c a b = cmp_flag_c a b.
Proof.
  unfold pstate_c, cmp_flags. bv_solve.
Qed.

Lemma pstate_z_eq_cmp_flag (a b : bv 64) : pstate_z a b = cmp_flag_z a b.
Proof.
  unfold pstate_z, cmp_flags. bv_solve.
Qed.

Lemma pstate_c_zero_lt (a b : bv 64) : (bv_unsigned a < bv_unsigned b)%Z → pstate_c a b = BV 1 0.
Proof. intro Hlt. rewrite pstate_c_eq_cmp_flag. by apply cmp_flag_c_lt. Qed.

Lemma pstate_z_zero_ne (a b : bv 64) : a ≠ b → pstate_z a b = BV 1 0.
Proof. intro Hne. rewrite pstate_z_eq_cmp_flag. by apply cmp_flag_z_ne. Qed.

Lemma pstate_z_zero_lt (a b : bv 64) : (bv_unsigned a < bv_unsigned b)%Z → pstate_z a b = BV 1 0.
Proof. intro Hlt. rewrite pstate_z_eq_cmp_flag. by apply cmp_flag_z_ne_ct. Qed.

(* ------------------------------------------------------------------------ *)
(* Step automation: a full Iris thread step from the actual seq_step         *)
(* operational semantics.                                                   *)
(* ------------------------------------------------------------------------ *)

Ltac ls_eval :=
  match goal with
  | |- eval_exp _ = Some _ => by vm_compute
  | |- eval_a_exp _ _ = Some _ => by vm_compute
  end.

Ltac ls_match :=
  lazymatch goal with
  | |- _ ∧ _ => split; ls_match
  | |- ∃ _, _ => eexists; ls_match
  | |- _ ∨ _ => first [left; ls_match | right; ls_match]
  | |- _ => first [reflexivity | by vm_compute | done]
  end.

Ltac ls_trace_step :=
  match goal with
  | |- trace_step (Smt (DeclareConst _ (Ty_BitVec _)) _ :t: _) _ _ _ =>
      apply (DeclareConstBitVecS' _)
  | |- trace_step (Smt (DeclareConst _ Ty_Bool) _ :t: _) _ _ _ =>
      apply DeclareConstBoolS
  | |- trace_step (Smt (DefineConst _ _) _ :t: _) _ _ _ =>
      eapply DefineConstS; ls_eval
  | |- trace_step (Smt (Assert _) _ :t: _) _ _ _ =>
      eapply AssertS; ls_eval
  | |- trace_step (Assume _ _ :t: _) _ _ _ =>
      eapply AssumeS; ls_eval
  | |- trace_step (ReadReg _ _ _ _ :t: _) _ _ _ =>
      apply ReadRegS
  | |- trace_step (WriteReg _ _ _ _ :t: _) _ _ _ =>
      apply WriteRegS
  | |- trace_step (AssumeReg _ _ _ _ :t: _) _ _ _ =>
      apply AssumeRegS
  | |- trace_step (ReadMem _ _ _ _ _ _ :t: _) _ _ _ => apply ReadMemS
  | |- trace_step (tnil) _ _ _ => apply DoneES
  end.

Ltac ls_step :=
  eapply nsteps_step;
  [ eapply step_single';
    eapply (SeqStep _ _ _ _ None _ _);
    [ reflexivity | ls_trace_step | ls_match ]
  | ].

(* ------------------------------------------------------------------------ *)
(* a18: add x3, x3, #1 followed by the fallthrough fetch of a1c.            *)
(*                                                                           *)
(* 9 steps: DeclareConst 28, ReadReg R3, DefineConst 50 (R3 + 1),           *)
(*          WriteReg R3, DeclareConst 51, ReadReg _PC, DefineConst 52 (pc +  *)
(*          4), WriteReg _PC, DoneES.                                       *)
(* ------------------------------------------------------------------------ *)

Lemma exec_a18 (base len tgt i r4 : bv 64) (mem : mem_map) :
  nsteps 9
    ([ls_θ a18 (ls_regs base len tgt i r4 (BV 64 0x10300018))], ls_σ mem)
    []
    ([ls_θ a1c (ls_regs base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) r4
        (BV 64 0x1030001c))], ls_σ mem).
Proof.
  ls_step.  (* DeclareConst 28 *)
  ls_step.  (* ReadReg R3 *)
  ls_step.  (* DefineConst 50 *)
  ls_step.  (* WriteReg R3 *)
  ls_step.  (* DeclareConst 51 *)
  ls_step.  (* ReadReg _PC *)
  ls_step.  (* DefineConst 52 *)
  ls_step.  (* WriteReg _PC *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split; [reflexivity |].
      eexists. split.
      + by vm_compute.
      + by vm_compute.
  }
  reflexivity.
Qed.