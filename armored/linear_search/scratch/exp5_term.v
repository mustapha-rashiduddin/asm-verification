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

(* The register file immediately after a cmp instruction has executed: the   *)
(* four PSTATE flags N, Z, C, V are left as the given bitvectors (with the   *)
(* remaining sys-register fields D, SP, EL, nRW unchanged).                 *)
Definition ls_regs_nzcv (base len tgt i : bv 64) (r4 : bv 64) (pc : bv 64)
      (N Z C V : bv 1) : reg_map :=
  <[ "PSTATE" := RegVal_Struct
     [("N", RVal_Bits N); ("Z", RVal_Bits Z); ("C", RVal_Bits C); ("V", RVal_Bits V);
      ("D", RVal_Bits (BV 1 0)); ("SP", RVal_Bits (BV 1 1));
      ("EL", RVal_Bits (BV 2 2)); ("nRW", RVal_Bits (BV 1 0))] ]>
  (ls_regs base len tgt i r4 pc).

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
  unfold cmp_flag_z.
  rewrite !bv_unsigned_BV.
  match goal with |- context [bool_decide ?P] => destruct (bool_decide P) eqn:Hzeq end.
  + exfalso. apply Hne. apply (proj2 (bv_eq 64 a b)).
    apply (proj1 (cmp_res64_zero_iff a b)).
    apply bool_decide_eq_true_1 in Hzeq. exact Hzeq.
  + reflexivity.
Qed.

Lemma cmp_flag_c_lt (a b : bv 64) : (bv_unsigned a < bv_unsigned b)%Z → cmp_flag_c a b = BV 1 0.
Proof.
  intros Hlt.
  apply (proj2 (bv_eq 1 (cmp_flag_c a b) (BV 1 0))).
  unfold cmp_flag_c.
  rewrite !bv_unsigned_BV.
  match goal with |- context [bool_decide ?P] => destruct (bool_decide P) eqn:Hceq end.
  + reflexivity.
  + exfalso.
    apply bool_decide_eq_false_1 in Hceq.
    apply Hceq.
    apply (proj2 (cmp_sum128_zero_ext_iff a b)).
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
(* Resolving the symbolic flag conditions of the trace a4 / a10.             *)
(*                                                                           *)
(* DefineConst 57 evaluates an expression whose behaviour depends on three   *)
(* [bool_decide] propositions over (opaque) bitvector equalities.  The       *)
(* propositions cannot be decided by computation, but they are implied by    *)
(* the loop hypotheses i < len (and len < 2^62 for the overflow flag V and   *)
(* the sign flag N).  We prove the exact propositions the lazy-reduced       *)
(* evaluation is stuck on, spelled out in the same form the substitution     *)
(* produces (raw [bv_add] / [bv_extract] / [bv_not] trees of the symbols     *)
(* 39 and 44), so that [rewrite] applies them directly after [ls_lazy].      *)
(*                                                                           *)
(* Under i <len < 2^62 the produced NZCV word is N=1, Z=C=V=0.               *)
(* ------------------------------------------------------------------------ *)

Lemma bv_extract_3f :
  bv_extract 0 64 (BV 128 0x3f) = BV 64 0x3f.
Proof. bv_solve. Qed.

Lemma booldec_Z_false (i len : bv 64) (Hlt : (bv_unsigned i < bv_unsigned len)%Z) :
  bool_decide
    (bv_extract 0 64
       (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1)) =
     BV 64 0) = false.
Proof.
  apply bool_decide_eq_false_2. intro Hze.
  apply (proj1 (cmp_res64_zero_iff i len)) in Hze.
  exfalso. lia.
Qed.

Lemma booldec_C_true (i len : bv 64) (Hlt : (bv_unsigned i < bv_unsigned len)%Z) :
  bool_decide
    (bv_zero_extend 128
       (bv_extract 0 64
          (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1))) =
     bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1)) = true.
Proof.
  apply bool_decide_eq_true_2.
  apply bv_eq.
  change (bv_unsigned (bv_zero_extend 128 (bv_extract 0 64 (cmp_sum128 i len))) =
          bv_unsigned (cmp_sum128 i len)).
  apply (proj2 (cmp_sum128_zero_ext_iff i len)).
  exact Hlt.
Qed.

Lemma booldec_V_true (i len : bv 64) (Hb : (bv_unsigned i < bv_unsigned len < 2^62)%Z) :
  bool_decide
    (bv_sign_extend 128
       (bv_extract 0 64
          (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1))) =
     bv_add (bv_add (bv_sign_extend 128 i) (bv_sign_extend 128 (bv_not len))) (BV 128 1)) = true.
Proof.
  apply bool_decide_eq_true_2.
  bv_simplify_arith Hb.
  bv_solve.
Qed.

(* The exact NZCV word that DefineConst 57 evaluates to once the three flag  *)
(* conditions are resolved (bits Z=C=V=0 for i < len; bit N = sign of the    *)
(* 64-bit result of i - len).                                                *)
Definition e57_nzcv (i len : bv 64) : bv 4 :=
  bv_concat 4
    (bv_concat 3
       (bv_concat 2
          (bv_or (bv_and (BV 1 0) (bv_not (BV 1 1)))
                 (bv_extract 0 1 (bv_shiftr
                     (bv_extract 0 64
                        (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len)))
                                (BV 128 1)))
                     (BV 64 0x3f))))
          (BV 1 0))
       (BV 1 0))
    (BV 1 0).

Lemma e57_nzcv_n_one (i len : bv 64) :
  (bv_unsigned i < bv_unsigned len < 2^62)%Z →
  bv_extract 3 1 (e57_nzcv i len) = BV 1 1.
Proof.
  unfold e57_nzcv. intros Hb.
  bv_simplify_arith Hb. bv_solve.
Qed.

Lemma e57_nzcv_z_zero (i len : bv 64) : bv_extract 2 1 (e57_nzcv i len) = BV 1 0.
Proof. unfold e57_nzcv. bv_solve. Qed.

Lemma e57_nzcv_c_zero (i len : bv 64) : bv_extract 1 1 (e57_nzcv i len) = BV 1 0.
Proof. unfold e57_nzcv. bv_solve. Qed.

Lemma e57_nzcv_v_zero (i len : bv 64) : bv_extract 0 1 (e57_nzcv i len) = BV 1 0.
Proof. unfold e57_nzcv. bv_solve. Qed.

(* The trace writes the PSTATE bits as plain extracts of the DefineConst-57  *)
(* value (a raw concat, not the folded e57_nzcv); bridge via convertibility. *)
Lemma n_pack (i len : bv 64) :
  bv_extract 3 1 (bv_concat 4 (bv_concat 3 (bv_concat 2 (cmp_flag_n i len) (BV 1 0)) (BV 1 0)) (BV 1 0)) =
  bv_extract 3 1 (e57_nzcv i len).
Proof. reflexivity. Qed.

Lemma z_pack (i len : bv 64) :
  bv_extract 2 1 (bv_concat 4 (bv_concat 3 (bv_concat 2 (cmp_flag_n i len) (BV 1 0)) (BV 1 0)) (BV 1 0)) =
  bv_extract 2 1 (e57_nzcv i len).
Proof. reflexivity. Qed.

Lemma c_pack (i len : bv 64) :
  bv_extract 1 1 (bv_concat 4 (bv_concat 3 (bv_concat 2 (cmp_flag_n i len) (BV 1 0)) (BV 1 0)) (BV 1 0)) =
  bv_extract 1 1 (e57_nzcv i len).
Proof. reflexivity. Qed.

Lemma v_pack (i len : bv 64) :
  bv_extract 0 1 (bv_concat 4 (bv_concat 3 (bv_concat 2 (cmp_flag_n i len) (BV 1 0)) (BV 1 0)) (BV 1 0)) =
  bv_extract 0 1 (e57_nzcv i len).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* Step automation: a full Iris thread step from the actual seq_step         *)
(* operational semantics.                                                   *)
(* ------------------------------------------------------------------------ *)

Ltac ls_lazy :=
  lazy [eval_exp eval_a_exp eval_assume_val mapM map_imap mbind option_bind eval_unop eval_manyop eval_binop subst_val_exp subst_val_base_val eq_var_name Z.eqb Zeq_bool map option_fmap option_map fmap mret option_ret guard_or mthrow option_mfail foldl bvn_to_bv bvn_n bvn_val decide decide_rel BinNat.N.eq_dec N.eq_dec N_rec N_rect N.add N.sub Pos.add Pos.succ Pos.pred Pos.sub_mask Pos.double_mask Pos.succ_double_mask Pos.pred_double Pos.double_pred_mask sumbool_rec sumbool_rect BinPos.Pos.eq_dec Pos.eq_dec positive_rect positive_rec eq_rect eq_ind eq_ind_r eq_rect_r eq_rec eq_rec_r eq_sym].

Ltac ls_eval :=
  match goal with
  | |- eval_exp _ = Some _ => ls_lazy; reflexivity
  | |- eval_a_exp _ _ = Some _ => ls_lazy; reflexivity
  end.

Ltac ls_match :=
  lazymatch goal with
  | |- _ ∧ _ => split; ls_match
  | |- ∃ _, _ => eexists; ls_match
  | |- _ ∨ _ => first [left; ls_match | right; ls_match]
  | |- _ => first [reflexivity | by vm_compute | done]
  end.

Ltac ls_trace_step :=
  lazymatch goal with
  | |- trace_step ?l ?regs ?κ ?st =>
      let t := eval cbv [seq_trace ls_θ subst_trace a4 a8 ac a10 a14 a18 a1c] in l in
      let t := eval simpl in t in
      change_no_check (trace_step t regs κ st)
  end;
  lazymatch goal with
  | |- trace_step (Smt (DeclareConst _ (Ty_BitVec _)) _ :t: _) _ _ _ =>
      eapply (DeclareConstBitVecS' _)
  | |- trace_step (Smt (DeclareConst _ Ty_Bool) _ :t: _) _ _ _ =>
      apply DeclareConstBoolS
  | |- trace_step (Smt (DefineConst _ _) _ :t: _) _ _ _ =>
      eapply DefineConstS;
      ls_eval
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
  | |- trace_step (ReadMem _ _ _ _ _ _ _ :t: _) _ _ _ => apply ReadMemS
  | |- trace_step (BranchAddress _ _ :t: _) _ _ _ => apply BranchAddressS
  | |- trace_step (tnil) _ _ _ => apply DoneES
  end.

Ltac ls_consequences :=
  repeat (eexists || split || first [left | right]);
  try reflexivity.

(* Normalise the current trace head (substitutions, definitions, let,       *)
(* match) exactly as ls_trace_step does, without committing to an event.     *)
Ltac ls_change_trace :=
  lazymatch goal with
  | |- trace_step ?l ?regs ?κ ?st =>
      let t := eval cbv [seq_trace ls_θ subst_trace a4 a8 ac a10 a14 a18 a1c] in l in
      let t := eval simpl in t in
      change_no_check (trace_step t regs κ st)
  end.

Ltac ls_step :=
  eapply nsteps_step;
  [ eapply step_single';
    eapply (SeqStep _ _ _ _ None _ _);
    [ reflexivity | ls_trace_step | ls_consequences ]
  | ].

(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* a18: add x3, x3, #1 followed by the fallthrough fetch of a1c.            *)
(*                                                                           *)
(* 9 steps: DeclareConst 28, ReadReg R3, DefineConst 50 (R3 + 1),           *)
(*          WriteReg R3, DeclareConst 51, ReadReg _PC, DefineConst 52 (pc +  *)
(*          4), WriteReg _PC, DoneES.                                       *)
(* ------------------------------------------------------------------------ *)

Lemma bv_add_pc :
  bv_add (BV 64 0x10300018) (BV 64 4) = BV 64 0x1030001c.
Proof.
  apply bv_eq.
  rewrite bv_add_unsigned. rewrite bv_unsigned_BV. rewrite bv_unsigned_BV.
  rewrite (bv_wrap_small 64 (271581208 + 4)); [ reflexivity | unfold bv_modulus; lia ].
Qed.

Lemma ls_instrs_a1c : ls_instrs !! (BV 64 0x1030001c) = Some a1c.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)

Lemma exec_a18 (base len tgt i r4 : bv 64) (mem : mem_map) :
  nsteps 9
    ([ls_θ a18 (ls_regs base len tgt i r4 (BV 64 0x10300018))], ls_σ mem)
    []
    ([ls_θ a1c (ls_regs base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) r4
        (BV 64 0x1030001c))], ls_σ mem).
Proof.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split; [ reflexivity | ].
      eexists (BV 64 0x1030001c).
      split.
      + change (Some (RVal_Bits (bv_add (BV 64 0x10300018) (BV 64 4)))
                 = Some (RVal_Bits (BV 64 0x1030001c))).
        do 4 f_equal.
        exact bv_add_pc.
      + rewrite ls_instrs_a1c.
        split; [ reflexivity | ].
        split; [ reflexivity | reflexivity ].
  }
  rewrite bv_add_pc.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* a1c: b #0x10300004 (the loop back-edge) preceded by the sys-reg           *)
(* assumptions, starting at pc 0x1030001c with R3 already updated to i + 1.  *)
(*                                                                           *)
(* 17 steps: 9 AssumeReg, DeclareConst 26, ReadReg _PC, DefineConst 27       *)
(*           (pc - 24), DefineConst 28 (alias 27), BranchAddress,            *)
(*           DefineConst 29 (alias 27), WriteReg _PC, DoneES.                *)
(* ------------------------------------------------------------------------ *)

Lemma bv_add_pc_a1c :
  bv_add (BV 64 0x1030001c) (BV 64 0xffffffffffffffe8) = BV 64 0x10300004.
Proof.
  apply bv_eq.
  rewrite bv_add_unsigned. rewrite bv_unsigned_BV. rewrite bv_unsigned_BV.
  rewrite bv_unsigned_BV.
  unfold bv_wrap, bv_modulus.
  reflexivity.
Qed.

Lemma ls_instrs_a4 : ls_instrs !! (BV 64 0x10300004) = Some a4.
Proof. reflexivity. Qed.

Lemma exec_a1c (base len tgt i r4 : bv 64) (mem : mem_map) :
  nsteps 17
    ([ls_θ a1c (ls_regs base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) r4
        (BV 64 0x1030001c))], ls_σ mem)
    []
    ([ls_θ a4 (ls_regs base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) r4
        (BV 64 0x10300004))], ls_σ mem).
Proof.
ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split; [ reflexivity | ].
      eexists (BV 64 0x10300004).
      split.
      + change (Some (RVal_Bits (bv_add (BV 64 0x1030001c) (BV 64 0xffffffffffffffe8)))
                 = Some (RVal_Bits (BV 64 0x10300004))).
        do 4 f_equal.
        exact bv_add_pc_a1c.
      + rewrite ls_instrs_a4.
        split; [ reflexivity | ].
        split; [ reflexivity | reflexivity ].
  }
  rewrite bv_add_pc_a1c.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* a4: cmp x3, x1 (i vs len) at pc 0x10300004, computing NZCV into PSTATE   *)
(* and falling through to a8 at 0x10300008.                                 *)
(*                                                                           *)
(* 22 steps: DeclareConst 27, ReadReg R3, DefineConst 28, DeclareConst 29,   *)
(*           ReadReg R1, DefineConst 35 (~R1), DefineConst 39 (i - len in    *)
(*           128-bit), DefineConst 44 (res64), DefineConst 57 (NZCV),        *)
(*           DefineConst 58/59/60/61 (extracts), WriteReg PSTATE N/Z/C/V,    *)
(*           DeclareConst 62, ReadReg _PC, DefineConst 63 (pc + 4),          *)
(*           WriteReg _PC, DoneES.                                           *)
(* ------------------------------------------------------------------------ *)

Lemma bv_add_pc_8 :
  bv_add (BV 64 0x10300004) (BV 64 4) = BV 64 0x10300008.
Proof. apply bv_eq. rewrite bv_add_unsigned. rewrite bv_unsigned_BV. rewrite bv_unsigned_BV. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma ls_instrs_a8 : ls_instrs !! (BV 64 0x10300008) = Some a8.
Proof. reflexivity. Qed.

(* The DefineConst-57 expression, with the trace symbols 28/35/39/44 already  *)
(* replaced by their values (28 -> i, 35 -> bv_not len, 39 -> cmp_sum128,     *)
(* 44 -> cmp_res64).  This is the exact expression the DefineConstS goal of   *)
(* step 9 evaluates after its internal substitution.                          *)
Definition e57_def (i len : bv 64) : exp :=
  Manyop Concat
    [ Manyop Concat
        [ Manyop Concat
            [ Manyop (Bvmanyarith Bvor)
                [ Manyop (Bvmanyarith Bvand)
                    [ Val (Val_Bits (BV 1 0)) Mk_annot;
                      Unop Bvnot (Val (Val_Bits (BV 1 1)) Mk_annot) Mk_annot ] Mk_annot;
                  Unop (Extract 0 0)
                    (Binop (Bvarith Bvlshr)
                       (Val (Val_Bits (cmp_res64 i len)) Mk_annot)
                       (Unop (Extract 63 0) (Val (Val_Bits (BV 128 0x3f)) Mk_annot) Mk_annot)
                       Mk_annot) Mk_annot ] Mk_annot;
              Ite (Binop Eq (Val (Val_Bits (cmp_res64 i len)) Mk_annot)
                     (Val (Val_Bits (BV 64 0)) Mk_annot) Mk_annot)
                (Val (Val_Bits (BV 1 0x1)) Mk_annot)
                (Val (Val_Bits (BV 1 0x0)) Mk_annot) Mk_annot ] Mk_annot;
          Ite (Binop Eq (Unop (ZeroExtend 64) (Val (Val_Bits (cmp_res64 i len)) Mk_annot) Mk_annot)
                  (Val (Val_Bits (cmp_sum128 i len)) Mk_annot) Mk_annot)
            (Val (Val_Bits (BV 1 0x0)) Mk_annot)
            (Val (Val_Bits (BV 1 0x1)) Mk_annot) Mk_annot ] Mk_annot;
      Ite (Binop Eq (Unop (SignExtend 64) (Val (Val_Bits (cmp_res64 i len)) Mk_annot) Mk_annot)
              (Manyop (Bvmanyarith Bvadd)
                 [ Manyop (Bvmanyarith Bvadd)
                     [ Unop (SignExtend 64) (Val (Val_Bits i) Mk_annot) Mk_annot;
                       Unop (SignExtend 64) (Val (Val_Bits (bv_not len)) Mk_annot) Mk_annot ] Mk_annot;
                   Val (Val_Bits (BV 128 1)) Mk_annot ] Mk_annot) Mk_annot)
        (Val (Val_Bits (BV 1 0x0)) Mk_annot)
        (Val (Val_Bits (BV 1 0x1)) Mk_annot) Mk_annot ] Mk_annot.

Lemma eval_e57_def (i len : bv 64)
      (H : (bv_unsigned i < bv_unsigned len < 2^62)%Z) :
  eval_exp (e57_def i len) =
  Some (Val_Bits
          (bv_concat 4 (bv_concat 3 (bv_concat 2 (cmp_flag_n i len) (BV 1 0)) (BV 1 0)) (BV 1 0))).
Proof.
  unfold e57_def.
  lazy [eval_exp eval_a_exp eval_assume_val mapM map_imap mbind option_bind eval_unop eval_manyop eval_binop option_fmap option_map fmap mret option_ret guard_or mthrow option_mfail foldl bvn_to_bv bvn_n bvn_val decide decide_rel BinNat.N.eq_dec N.eq_dec N_rec N_rect N.add N.sub Pos.add Pos.succ Pos.pred Pos.sub_mask Pos.double_mask Pos.succ_double_mask Pos.pred_double Pos.double_pred_mask sumbool_rec sumbool_rect BinPos.Pos.eq_dec Pos.eq_dec positive_rect positive_rec eq_rect eq_ind eq_sym].
  rewrite (booldec_Z_false i len (proj1 H)).
  rewrite (booldec_C_true i len (proj1 H)).
  rewrite (booldec_V_true i len H).
  rewrite bv_extract_3f.
  unfold cmp_flag_n.
  reflexivity.
Qed.

Lemma exec_a4 (base len tgt i r4 : bv 64) (mem : mem_map) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  nsteps 22
    ([ls_θ a4 (ls_regs base len tgt i r4 (BV 64 0x10300004))], ls_σ mem)
    []
    ([ls_θ a8 (ls_regs_nzcv base len tgt i r4 (BV 64 0x10300008)
              (BV 1 1) (BV 1 0) (BV 1 0) (BV 1 0))], ls_σ mem).
Proof.
  intros Hlt Hb.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* step 9: DefineConst 57 (the NZCV word).  Its evaluation is stuck on the  *)
  (* three symbolic [bool_decide] flag conditions; resolve them proposition- *)
  (* ally using the loop hypotheses.                                          *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - eapply DefineConstS.
      rewrite (eval_e57_def i len (conj Hlt Hb)).
      reflexivity.
    - ls_consequences.
  }
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split;
      [ reflexivity
| eexists (BV 64 0x10300008);
        split;
        [ change (Some (RVal_Bits (bv_add (BV 64 0x10300004) (BV 64 4)))
                  = Some (RVal_Bits (BV 64 0x10300008)));
          do 4 f_equal;
          exact bv_add_pc_8
        | rewrite ls_instrs_a8;
          split;
          [ (try (rewrite (n_pack i len); rewrite (e57_nzcv_n_one i len (conj Hlt Hb));
                  rewrite (z_pack i len); rewrite (e57_nzcv_z_zero i len);
                  rewrite (c_pack i len); rewrite (e57_nzcv_c_zero i len);
                  rewrite (v_pack i len); rewrite (e57_nzcv_v_zero i len); cbn; reflexivity);
             try (change (Some (RVal_Bits (bv_add (BV 64 0x10300004) (BV 64 4)))
                          = Some (RVal_Bits (BV 64 0x10300008)));
                  do 4 f_equal; exact bv_add_pc_8);
             try reflexivity)
          | try (split; [ reflexivity | reflexivity ]); try reflexivity ] ] ].
  }
  rewrite bv_add_pc_8.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* a8: b.hs 0x10300020 (branch if higher-or-same, i.e. PSTATE.C = 1).        *)
(*                                                                           *)
(* In the continue case C = 0, so the branch falls through.  The trace is    *)
(*                                                                           *)
(*   9 AssumeRegs, DeclareConst 2, ReadReg PSTATE.C, DefineConst 27          *)
(*     (= C == 1), tcases [ branch taken; branch fall ],                     *)
(*   fall branch: Assert (Not 27), DeclareConst 49, ReadReg _PC,             *)
(*     DefineConst 50 (= pc + 4), WriteReg _PC, tnil.                        *)
(*                                                                           *)
(* 19 events: 9 plus DeclareConst / ReadReg / DefineConst (C, 27), the       *)
(* tcases choice, the 5 events of the fall branch, and DoneES.               *)
(* ------------------------------------------------------------------------ *)

Lemma bv_add_pc_ac :
  bv_add (BV 64 0x10300008) (BV 64 4) = BV 64 0x1030000c.
Proof. apply bv_eq. rewrite bv_add_unsigned. rewrite bv_unsigned_BV. rewrite bv_unsigned_BV. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma ls_instrs_ac : ls_instrs !! (BV 64 0x1030000c) = Some ac.
Proof. reflexivity. Qed.

Lemma exec_a8 (base len tgt i r4 : bv 64) (mem : mem_map) :
  nsteps 19
    ([ls_θ a8 (ls_regs_nzcv base len tgt i r4 (BV 64 0x10300008)
              (BV 1 1) (BV 1 0) (BV 1 0) (BV 1 0))], ls_σ mem)
    []
    ([ls_θ ac (ls_regs_nzcv base len tgt i r4 (bv_add (BV 64 0x10300008) (BV 64 4))
              (BV 1 1) (BV 1 0) (BV 1 0) (BV 1 0))], ls_σ mem).
Proof.
  (* events 1..6: the six system-register AssumeRegs. *)
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* event 7: DeclareConst 2 (the fresh 1-bit symbol for PSTATE.C). *)
  ls_step.
  (* events 8..10: AssumeReg PSTATE.EL, PSTATE.nRW, SCR_EL3. *)
  ls_step.
  ls_step.
  ls_step.
  (* event 11: ReadReg PSTATE.C; the reflexive read pins the fresh symbol    *)
  (* to the concrete C = 0 carried in from exec_a4.                          *)
  ls_step.
  (* event 12: DefineConst 27 = (C == 1) - now evaluates to false. *)
  ls_step.
  (* event 13: tcases; choose the fall-through branch (its assertion claims  *)
  (* ~27, which the concrete C = 0 makes true).                              *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply CasesES.
      right; left; reflexivity.
    - ls_consequences.
  }
  (* fall branch: Assert (Not 27), DeclareConst 49, ReadReg _PC,             *)
  (* DefineConst 50 (pc + 4), WriteReg _PC.                                  *)
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* event 19: tnil -> LDone, fetching the successor ac at pc + 4. *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split;
      [ reflexivity
      | eexists (BV 64 0x1030000c);
        split;
        [ change (Some (RVal_Bits (bv_add (BV 64 0x10300008) (BV 64 4)))
                  = Some (RVal_Bits (BV 64 0x1030000c)));
          rewrite bv_add_pc_ac;
          reflexivity
        | rewrite ls_instrs_ac;
          split;
          [ reflexivity
          | try (split; [ reflexivity | reflexivity ]); try reflexivity ] ] ].
  }
  rewrite bv_add_pc_ac.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* ac: ldr x4, [x0, x3, lsl #3].                                            *)
(*                                                                           *)
(* The real generated trace computes the 64-bit effective address           *)
(*                                                                           *)
(*     E = R0 + (R3 << 3)  =  base + i * 8                                  *)
(*                                                                           *)
(* (symbol 70), asserts the generated alignment constraint (symbol 74:      *)
(* E is 8-aligned), and finally reads 8 bytes from the address              *)
(*                                                                           *)
(*     <E[51:0]> << 4        (zero-extended to 64 bits)                     *)
(*                                                                           *)
(* (the isla "cache line" reshaping of the address, symbols 1397/1398).      *)
(* The loaded 64-bit value is written to R4 and the PC advances by 4 to     *)
(* 0x10300010 (the next instruction word, a10).                              *)
(*                                                                           *)
(* Honest ReadMem premises:                                                  *)
(*   * the generated alignment/constraint is valid,                          *)
(*   * read_mem mem <effective-address> 8 = Some <loaded 64-bit value>.      *)
(* We do NOT link these to a list/array abstraction yet.                     *)
(* ------------------------------------------------------------------------ *)

Definition ac_addr (base i : bv 64) : bv 64 :=
  bv_add base (bv_concat 64 (bv_extract 0 61 i) (BV 3 0)).

Definition ac_rdbase (base i : bv 64) : bv 64 :=
  bv_zero_extend 64 (bv_concat 56 (BV 4 0) (bv_extract 0 52 (ac_addr base i))).

Lemma bv_add_pc_ac10 :
  bv_add (BV 64 0x1030000c) (BV 64 4) = BV 64 0x10300010.
Proof. apply bv_eq. rewrite bv_add_unsigned. rewrite bv_unsigned_BV. rewrite bv_unsigned_BV. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma ls_instrs_a10 : ls_instrs !! (BV 64 0x10300010) = Some a10.
Proof. reflexivity. Qed.

(* The a_exp of the generated alignment constraint (event 17). *)
Definition ac_assume_exp : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [ AExp_Manyop (Bvmanyarith Bvadd)
          [ AExp_Val (AVal_Var "R0" []) Mk_annot
          ; AExp_Manyop (Bvmanyarith Bvmul)
              [ AExp_Val (AVal_Var "R3" []) Mk_annot
              ; AExp_Val (AVal_Bits (BV 64 0x8)) Mk_annot ] Mk_annot ] Mk_annot
      ; AExp_Val (AVal_Bits (BV 64 0xfff0000000000007)) Mk_annot ] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0x0)) Mk_annot) Mk_annot.

Lemma ac_booldec_assume (base i : bv 64)
      (H : bv_and (bv_add base (bv_mul i (BV 64 8))) (BV 64 0xfff0000000000007) = BV 64 0) :
  bool_decide (bv_and (bv_add base (bv_mul i (BV 64 8))) (BV 64 0xfff0000000000007) = BV 64 0) = true.
Proof. apply bool_decide_eq_true_2. exact H. Qed.

Lemma ac_eval_assume (regs : reg_map) (base i : bv 64)
      (HR0 : regs !! "R0" = Some (RVal_Bits base))
      (HR3 : regs !! "R3" = Some (RVal_Bits i))
      (H : bv_and (bv_add base (bv_mul i (BV 64 8))) (BV 64 0xfff0000000000007) = BV 64 0) :
  eval_a_exp regs ac_assume_exp = Some (Val_Bool true).
Proof.
  unfold ac_assume_exp.
  lazy [eval_a_exp eval_assume_val mapM map_imap mbind option_bind read_accessor eq_var_name].
  rewrite HR0.
  rewrite HR3.
  ls_lazy.
  rewrite (ac_booldec_assume base i H).
  reflexivity.
Qed.

Lemma ac_booldec_align (base i : bv 64)
      (H : ac_addr base i = bv_and (ac_addr base i) (BV 64 0xfffffffffffffff8)) :
  bool_decide (ac_addr base i = bv_and (ac_addr base i) (BV 64 0xfffffffffffffff8)) = true.
Proof. apply bool_decide_eq_true_2. exact H. Qed.

Lemma exec_ac (base len tgt i v : bv 64) (r4 : bv 64) (mem : mem_map) :
  bv_and (bv_add base (bv_mul i (BV 64 8))) (BV 64 0xfff0000000000007) = BV 64 0 ->
  ac_addr base i = bv_and (ac_addr base i) (BV 64 0xfffffffffffffff8) ->
  read_mem mem (bv_unsigned (ac_rdbase base i)) 8 = Some (bv_to_bvn v) ->
  nsteps 34
    ([ls_θ ac (ls_regs_nzcv base len tgt i r4 (BV 64 0x1030000c)
              (BV 1 1) (BV 1 0) (BV 1 0) (BV 1 0))], ls_σ mem)
    []
    ([ls_θ a10 (ls_regs_nzcv base len tgt i v (BV 64 0x10300010)
              (BV 1 1) (BV 1 0) (BV 1 0) (BV 1 0))], ls_σ mem).
Proof.
  intros H_assume H_align H_mem.
  (* events 1..14: the AssumeRegs (6 system regs, EDSCR/OSDLR/OSLSR, then    *)
  (* DeclareConst 3, PSTATE.EL, PSTATE.nRW, SCR_EL3, SCTLR_EL2).             *)
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* events 15..16: DeclareConst 26 (fresh R0), DeclareConst 27 (fresh R3).  *)
  ls_step.
  ls_step.
  (* event 17: the generated alignment Assume; its evaluation is stuck on    *)
  (* the symbolic bool_decide (R0 + R3*8) & 0xfff0000000000007 = 0, on top of *)
  (* the two AVal_Var register reads (resolved by reflexivity against the    *)
  (* concrete register map). Resolve the bool_decide propositionally via     *)
  (* H_assume.                                                               *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - eapply AssumeS;
      eapply ac_eval_assume;
      [ reflexivity | reflexivity | exact H_assume ].
    - ls_consequences.
  }
  (* events 18..19: ReadReg R3 (pins symbol 27 to i), ReadReg R0 (pins        *)
  (* symbol 26 to base).                                                     *)
  ls_step.
  ls_step.
  (* event 20: DefineConst 70 (the effective address). *)
  ls_step.
  (* event 21: DefineConst 74 - the 8-alignment check (E = E & ~0x7); its    *)
  (* evaluation is stuck on the symbolic bool_decide, resolved via H_align.  *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - ls_change_trace.
      eapply DefineConstS.
      ls_lazy.
      rewrite (ac_booldec_align base i H_align).
      reflexivity.
    - ls_consequences.
  }
  (* event 22: ReadReg PSTATE.D. *)
  ls_step.
  (* events 23..26: DefineConst 1249 (copy), DefineConst 1397 (56-bit        *)
  (* address reshape), DefineConst 1398 (zero-extend), DeclareConst 1399     *)
  (* (fresh loaded-value).                                                   *)
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* event 27: ReadMem at the reshaped address, len 8.  Manual step: the     *)
  (* premise read_mem mem .. 8 = Some .. decides which side of the isla      *)
  (* memory case we are in.                                                  *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - ls_change_trace.
      apply ReadMemS.
    - eexists (ac_rdbase base i).
      eexists v. eexists v.
      split; [ reflexivity |
      split; [ reflexivity |
      split; [ vm_compute; reflexivity |
        rewrite H_mem;
        split; [ reflexivity |
        split; [ reflexivity |
        split; [ reflexivity |
                 left; split; [ reflexivity | reflexivity ] ]]]]]].
  }
  (* event 28: DefineConst 1403 (copy of the loaded value). *)
  ls_step.
  (* event 29: WriteReg R4. *)
  ls_step.
  (* events 30..33: DeclareConst 1404, ReadReg _PC, DefineConst 1405 (pc+4), *)
  (* WriteReg _PC.                                                           *)
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* event 34: tnil -> LDone, fetching the successor a10 at pc + 4. *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - ls_change_trace.
      apply DoneES.
    - split;
      [ reflexivity
      | eexists (BV 64 0x10300010);
        split;
        [ change (Some (RVal_Bits (bv_add (BV 64 0x1030000c) (BV 64 4)))
                  = Some (RVal_Bits (BV 64 0x10300010)));
          rewrite bv_add_pc_ac10;
          reflexivity
        | rewrite ls_instrs_a10;
          split;
          [ reflexivity
          | try (split; [ reflexivity | reflexivity ]); try reflexivity ] ] ].
  }
  rewrite bv_add_pc_ac10.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* a10: cmp x4, x2 (v vs tgt) at pc 0x10300010, computing NZCV into PSTATE, *)
(* falling through to a14 at 0x10300014.                                    *)
(*                                                                           *)
(* The continuer (loop) case has v != tgt (not yet found), so Z = 0 and the  *)
(* following b.eq at a14 falls through.  N, C, V are not decidable from      *)
(* v != tgt alone, so they are left as the actual computed flag values.      *)
(* The register R4 (= the loaded value v) is preserved by the compare.       *)
(*                                                                           *)
(* The four raw flag conditions inside DefineConst 57 are                     *)
(*   Z : bv_extract/res64 = 0          (decides to false given v != tgt)      *)
(*   C : bv_zero_extend 128 (res64) = cmp_sum128                              *)
(*   V : bv_sign_extend 128 (res64)  = bv_add (sign-extended a) + 1           *)
(* The C/V guards stay symbolic, so the lazy reduction of the trace's         *)
(* DefineConst 57 is blocked by [match (if bool_decide ...)]; we rewrite      *)
(* those guarded option-terms to [Some (Val_Bits (cmp_flag_c10/v10 ...))]     *)
(* so the evaluator's reduction proceeds to a plain concatenation.            *)
(* ------------------------------------------------------------------------ *)

(* C/V flag values with the trace's raw equality conditions (the same form   *)
(* the lazy-reduced evaluation is blocked on), as plain guarded bvs so that   *)
(* the evaluator's if-then-else is definitionally the stored flag value.      *)
Definition cmp_flag_c10 (v tgt : bv 64) : bv 1 :=
  if bool_decide
    (bv_zero_extend 128 (bv_extract 0 64 (cmp_sum128 v tgt)) = cmp_sum128 v tgt)
    then BV 1 0 else BV 1 1.

Definition cmp_flag_v10 (v tgt : bv 64) : bv 1 :=
  if bool_decide
    (bv_sign_extend 128 (bv_extract 0 64 (cmp_sum128 v tgt)) =
     bv_add (bv_add (bv_sign_extend 128 v) (bv_sign_extend 128 (bv_not tgt))) (BV 128 1))
    then BV 1 0 else BV 1 1.

Definition cmp_flags10 (v tgt : bv 64) : bv 4 :=
  bv_concat 4
    (bv_concat 3
       (bv_concat 2 (cmp_flag_n v tgt) (BV 1 0))
       (cmp_flag_c10 v tgt))
    (cmp_flag_v10 v tgt).

Lemma bv_add_pc_14 :
  bv_add (BV 64 0x10300010) (BV 64 4) = BV 64 0x10300014.
Proof. apply bv_eq. rewrite bv_add_unsigned. rewrite bv_unsigned_BV. rewrite bv_unsigned_BV. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma ls_instrs_a14 : ls_instrs !! (BV 64 0x10300014) = Some a14.
Proof. reflexivity. Qed.

Lemma booldec_Z_false_ne (v tgt : bv 64) (Hne : v ≠ tgt) :
  bool_decide
    (bv_extract 0 64
       (bv_add (bv_add (bv_zero_extend 128 v) (bv_zero_extend 128 (bv_not tgt))) (BV 128 1)) =
     BV 64 0) = false.
Proof.
  apply bool_decide_eq_false_2. intro Hze.
  apply (proj1 (cmp_res64_zero_iff v tgt)) in Hze.
  exfalso. apply Hne. apply (proj2 (bv_eq 64 v tgt)). exact Hze.
Qed.

Lemma cmp_c_guard (v tgt : bv 64) :
  (if bool_decide (bv_zero_extend 128 (cmp_res64 v tgt) = cmp_sum128 v tgt)
   then Some (Val_Bits (BV 1 0)) else Some (Val_Bits (BV 1 1)))
  = Some (Val_Bits (cmp_flag_c10 v tgt)).
Proof.
  unfold cmp_flag_c10.
  change (bool_decide (bv_zero_extend 128 (cmp_res64 v tgt) = cmp_sum128 v tgt))
    with (bool_decide (bv_zero_extend 128 (bv_extract 0 64 (cmp_sum128 v tgt)) = cmp_sum128 v tgt)).
  destruct (bool_decide _); reflexivity.
Qed.

Lemma cmp_v_guard (v tgt : bv 64) :
  (if bool_decide (bv_sign_extend 128 (cmp_res64 v tgt) =
                   bv_add (bv_add (bv_sign_extend 128 v) (bv_sign_extend 128 (bv_not tgt))) (BV 128 1))
   then Some (Val_Bits (BV 1 0)) else Some (Val_Bits (BV 1 1)))
  = Some (Val_Bits (cmp_flag_v10 v tgt)).
Proof.
  unfold cmp_flag_v10.
  change (bool_decide (bv_sign_extend 128 (cmp_res64 v tgt) =
                       bv_add (bv_add (bv_sign_extend 128 v) (bv_sign_extend 128 (bv_not tgt))) (BV 128 1)))
    with (bool_decide (bv_sign_extend 128 (bv_extract 0 64 (cmp_sum128 v tgt)) =
                       bv_add (bv_add (bv_sign_extend 128 v) (bv_sign_extend 128 (bv_not tgt))) (BV 128 1))).
  destruct (bool_decide _); reflexivity.
Qed.

(* The full NZCV value produced by DefineConst 57 under v != tgt: N is the    *)
(* concrete (symbolic) sign bit of v - tgt, Z = 0, C/V carry the raw-guard    *)
(* formulas.                                                                  *)
Lemma eval_e57_ne (v tgt : bv 64) (Hne : v ≠ tgt) :
  eval_exp (e57_def v tgt) = Some (Val_Bits (cmp_flags10 v tgt)).
Proof.
  unfold e57_def, cmp_flags10.
  lazy [eval_exp eval_a_exp eval_assume_val mapM map_imap mbind option_bind eval_unop eval_manyop eval_binop subst_val_exp subst_val_base_val eq_var_name Z.eqb Zeq_bool map option_fmap option_map fmap mret option_ret guard_or mthrow option_mfail foldl bvn_to_bv bvn_n bvn_val decide decide_rel BinNat.N.eq_dec N.eq_dec N_rec N_rect N.add N.sub Pos.add Pos.succ Pos.pred Pos.sub_mask Pos.double_mask Pos.succ_double_mask Pos.pred_double Pos.double_pred_mask sumbool_rec sumbool_rect BinPos.Pos.eq_dec Pos.eq_dec positive_rect positive_rec eq_rect eq_ind eq_ind_r eq_rec eq_rec_r eq_rect_r eq_sym].
  rewrite (booldec_Z_false_ne v tgt Hne).
  rewrite (cmp_c_guard v tgt).
  rewrite (cmp_v_guard v tgt).
  rewrite bv_extract_3f.
  unfold cmp_flag_n.
  reflexivity.
Qed.

(* The WriteReg/extract chain leaves the four PSTATE fields as extracts of    *)
(* the DefineConst-57 word; relate them to the stored flag values.            *)
Lemma flags10_n (v tgt : bv 64) :
  bv_extract 3 1 (cmp_flags10 v tgt) = cmp_flag_n v tgt.
Proof. unfold cmp_flags10. bv_solve. Qed.

Lemma flags10_z (v tgt : bv 64) :
  bv_extract 2 1 (cmp_flags10 v tgt) = BV 1 0.
Proof. unfold cmp_flags10. bv_solve. Qed.

Lemma flags10_c (v tgt : bv 64) :
  bv_extract 1 1 (cmp_flags10 v tgt) = cmp_flag_c10 v tgt.
Proof. unfold cmp_flags10. bv_solve. Qed.

Lemma flags10_v (v tgt : bv 64) :
  bv_extract 0 1 (cmp_flags10 v tgt) = cmp_flag_v10 v tgt.
Proof. unfold cmp_flags10. bv_solve. Qed.

Lemma exec_a10 (base len tgt i v : bv 64) (mem : mem_map) :
  v ≠ tgt ->
  nsteps 22
    ([ls_θ a10 (ls_regs_nzcv base len tgt i v (BV 64 0x10300010)
              (BV 1 1) (BV 1 0) (BV 1 0) (BV 1 0))], ls_σ mem)
    []
    ([ls_θ a14 (ls_regs_nzcv base len tgt i v (BV 64 0x10300014)
              (cmp_flag_n v tgt) (BV 1 0) (cmp_flag_c10 v tgt) (cmp_flag_v10 v tgt))], ls_σ mem).
Proof.
  intro Hne.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* step 9: DefineConst 57 (the NZCV word).  Its evaluation is blocked on    *)
  (* the symbolic [bool_decide] flag conditions; resolve Z (via v != tgt) and  *)
  (* fold the C/V guards into their guarded flag values.                      *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - eapply DefineConstS.
      rewrite (eval_e57_ne v tgt Hne).
      reflexivity.
    - ls_consequences.
  }
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - ls_change_trace.
      apply DoneES.
    - split;
      [ reflexivity
      | eexists (BV 64 0x10300014);
        split;
        [ change (Some (RVal_Bits (bv_add (BV 64 0x10300010) (BV 64 4)))
                  = Some (RVal_Bits (BV 64 0x10300014)));
          rewrite bv_add_pc_14;
          reflexivity
        | rewrite ls_instrs_a14;
          split;
          [ (try (rewrite (flags10_n v tgt); rewrite (flags10_z v tgt);
                  rewrite (flags10_c v tgt); rewrite (flags10_v v tgt); cbn; reflexivity);
             try (change (Some (RVal_Bits (bv_add (BV 64 0x10300010) (BV 64 4)))
                       = Some (RVal_Bits (BV 64 0x10300014)));
                  rewrite bv_add_pc_14; reflexivity);
             try reflexivity)
          | try (split; [ reflexivity | reflexivity ]); try reflexivity ] ] ].
  }
  rewrite bv_add_pc_14.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* a14: b.eq 0x10300028 at pc 0x10300014.                                    *)
(*                                                                           *)
(* In the continue case exec_a10 has already fixed PSTATE.Z = 0, so the      *)
(* branch is not taken and the trace falls through to a18 at 0x10300018.     *)
(*                                                                           *)
(* 19 steps: 6 AssumeRegs, DeclareConst 24, AssumeReg PSTATE.EL/nRW/SCR_EL3, *)
(*           ReadReg PSTATE.Z (pins symbol 24 to 0), DefineConst 27 (Z == 1  *)
(*           = false), tcases [ fall ], Assert (Not 27), DeclareConst 49,     *)
(*           ReadReg _PC, DefineConst 50 (pc + 4), WriteReg _PC, DoneES.     *)
(*                                                                           *)
(* No new semantic hypothesis: the concrete Z = 0 carried in from exec_a10   *)
(* is enough.  N/C/V are preserved exactly as received.                      *)
(* ------------------------------------------------------------------------ *)

Lemma bv_add_pc_18 :
  bv_add (BV 64 0x10300014) (BV 64 4) = BV 64 0x10300018.
Proof. apply bv_eq. rewrite bv_add_unsigned. rewrite bv_unsigned_BV. rewrite bv_unsigned_BV. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma ls_instrs_a18 : ls_instrs !! (BV 64 0x10300018) = Some a18.
Proof. reflexivity. Qed.

Lemma exec_a14 (base len tgt i v : bv 64) (mem : mem_map) :
  nsteps 19
    ([ls_θ a14 (ls_regs_nzcv base len tgt i v (BV 64 0x10300014)
              (cmp_flag_n v tgt) (BV 1 0) (cmp_flag_c10 v tgt) (cmp_flag_v10 v tgt))], ls_σ mem)
    []
    ([ls_θ a18 (ls_regs_nzcv base len tgt i v (bv_add (BV 64 0x10300014) (BV 64 4))
              (cmp_flag_n v tgt) (BV 1 0) (cmp_flag_c10 v tgt) (cmp_flag_v10 v tgt))], ls_σ mem).
Proof.
  (* events 1..6: the six system-register AssumeRegs. *)
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* event 7: DeclareConst 24 (the fresh 1-bit symbol for PSTATE.Z). *)
  ls_step.
  (* events 8..10: AssumeReg PSTATE.EL, PSTATE.nRW, SCR_EL3. *)
  ls_step.
  ls_step.
  ls_step.
  (* event 11: ReadReg PSTATE.Z; the reflexive read pins the fresh symbol    *)
  (* to the concrete Z = 0 carried in from exec_a10.                          *)
  ls_step.
  (* event 12: DefineConst 27 = (Z == 1) - now evaluates to false. *)
  ls_step.
  (* event 13: tcases; choose the fall-through branch (its assertion claims  *)
  (* ~27, which the concrete Z = 0 makes true).                              *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply CasesES.
      right; left; reflexivity.
    - ls_consequences.
  }
  (* fall branch: Assert (Not 27), DeclareConst 49, ReadReg _PC,             *)
  (* DefineConst 50 (pc + 4), WriteReg _PC.                                  *)
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* event 19: tnil -> LDone, fetching the successor a18 at pc + 4. *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split;
      [ reflexivity
      | eexists (BV 64 0x10300018);
        split;
        [ change (Some (RVal_Bits (bv_add (BV 64 0x10300014) (BV 64 4)))
                  = Some (RVal_Bits (BV 64 0x10300018)));
          rewrite bv_add_pc_18;
          reflexivity
        | rewrite ls_instrs_a18;
          split;
          [ reflexivity
          | try (split; [ reflexivity | reflexivity ]); try reflexivity ] ] ].
  }
  rewrite bv_add_pc_18.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* NZCV-preserving variants.                                                 *)
(*                                                                           *)
(* In the continue path the loop arrives at a18/a1c carrying the NZCV word   *)
(* produced by exec_a10 (N = cmp_flag_n v tgt, Z = 0, C = cmp_flag_c10,      *)
(* V = cmp_flag_v10).  Neither a18 (add x3, x3, #1) nor a1c (b #0x10300004)  *)
(* touches the PSTATE flags, so the theorems below preserve an ARBITRARY     *)
(* N/Z/C/V (any bv 1) across the executions, matching the real architectural *)
(* state without resetting the flags.                                        *)
(*                                                                           *)
(* The step bodies are exactly those of the concrete-flag exec_a18 /         *)
(* exec_a1c: a18 is 8 ls_steps + DoneES, a1c is 16 ls_steps + DoneES.        *)
(* ------------------------------------------------------------------------ *)

Lemma exec_a18_nzcv (base len tgt i r4 : bv 64) (N Z C V : bv 1) (mem : mem_map) :
  nsteps 9
    ([ls_θ a18 (ls_regs_nzcv base len tgt i r4 (BV 64 0x10300018) N Z C V)], ls_σ mem)
    []
    ([ls_θ a1c (ls_regs_nzcv base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) r4
        (BV 64 0x1030001c) N Z C V)], ls_σ mem).
Proof.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split; [ reflexivity | ].
      eexists (BV 64 0x1030001c).
      split.
      + change (Some (RVal_Bits (bv_add (BV 64 0x10300018) (BV 64 4)))
                 = Some (RVal_Bits (BV 64 0x1030001c))).
        do 4 f_equal.
        exact bv_add_pc.
      + rewrite ls_instrs_a1c.
        split; [ reflexivity | ].
        split; [ reflexivity | reflexivity ].
  }
  rewrite bv_add_pc.
  apply nsteps_refl.
Qed.

Lemma exec_a1c_nzcv (base len tgt i r4 : bv 64) (N Z C V : bv 1) (mem : mem_map) :
  nsteps 17
    ([ls_θ a1c (ls_regs_nzcv base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) r4
        (BV 64 0x1030001c) N Z C V)], ls_σ mem)
    []
    ([ls_θ a4 (ls_regs_nzcv base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) r4
        (BV 64 0x10300004) N Z C V)], ls_σ mem).
Proof.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split; [ reflexivity | ].
      eexists (BV 64 0x10300004).
      split.
      + change (Some (RVal_Bits (bv_add (BV 64 0x1030001c) (BV 64 0xffffffffffffffe8)))
                 = Some (RVal_Bits (BV 64 0x10300004))).
        do 4 f_equal.
        exact bv_add_pc_a1c.
      + rewrite ls_instrs_a4.
        split; [ reflexivity | ].
        split; [ reflexivity | reflexivity ].
  }
  rewrite bv_add_pc_a1c.
  apply nsteps_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* a4_nzcv: NZCV-parameterized variant of exec_a4.                           *)
(*                                                                           *)
(* The comparison at 0x10300004 reads only R3 and R1 and unconditionally      *)
(* overwrites PSTATE.N/Z/C/V via the four WriteReg events.  The incoming     *)
(* flags N0/Z0/C0/V0 are therefore never read: the same execution reaches a8 *)
(* with N = 1, Z = 0, C = 0, V = 0 for arbitrary incoming flags.  This       *)
(* mirrors exec_a4 step-for-step, reuses its symbolic CMP evaluation          *)
(* (eval_e57_def) and its pack lemmas, and takes no assumption on the         *)
(* incoming flags.                                                            *)
(* ------------------------------------------------------------------------ *)

Lemma exec_a4_nzcv (base len tgt i r4 : bv 64) (N0 Z0 C0 V0 : bv 1) (mem : mem_map) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  nsteps 22
    ([ls_θ a4 (ls_regs_nzcv base len tgt i r4 (BV 64 0x10300004) N0 Z0 C0 V0)], ls_σ mem)
    []
    ([ls_θ a8 (ls_regs_nzcv base len tgt i r4 (BV 64 0x10300008)
              (BV 1 1) (BV 1 0) (BV 1 0) (BV 1 0))], ls_σ mem).
Proof.
  intros Hlt Hb.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  (* step 9: DefineConst 57 (the NZCV word).  Its evaluation is stuck on the  *)
  (* three symbolic [bool_decide] flag conditions; resolve them proposition- *)
  (* ally using the loop hypotheses.                                          *)
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - eapply DefineConstS.
      rewrite (eval_e57_def i len (conj Hlt Hb)).
      reflexivity.
    - ls_consequences.
  }
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split;
      [ reflexivity
      | eexists (BV 64 0x10300008);
        split;
        [ change (Some (RVal_Bits (bv_add (BV 64 0x10300004) (BV 64 4)))
                  = Some (RVal_Bits (BV 64 0x10300008)));
          do 4 f_equal;
          exact bv_add_pc_8
        | rewrite ls_instrs_a8;
          split;
          [ (try (rewrite (n_pack i len); rewrite (e57_nzcv_n_one i len (conj Hlt Hb));
                  rewrite (z_pack i len); rewrite (e57_nzcv_z_zero i len);
                  rewrite (c_pack i len); rewrite (e57_nzcv_c_zero i len);
                  rewrite (v_pack i len); rewrite (e57_nzcv_v_zero i len); cbn; reflexivity);
             try (change (Some (RVal_Bits (bv_add (BV 64 0x10300004) (BV 64 4)))
                           = Some (RVal_Bits (BV 64 0x10300008)));
                  do 4 f_equal; exact bv_add_pc_8);
             try reflexivity)
          | try (split; [ reflexivity | reflexivity ]); try reflexivity ] ] ].
  }
  rewrite bv_add_pc_8.
  apply nsteps_refl.
Qed.