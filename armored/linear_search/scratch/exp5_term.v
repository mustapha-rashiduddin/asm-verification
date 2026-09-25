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
  match goal with |- ?G => idtac "T-HEAD:"; idtac G end;
  lazymatch goal with
  | |- trace_step (Smt (DeclareConst _ (Ty_BitVec _)) _ :t: _) _ _ _ =>
      eapply (DeclareConstBitVecS' _)
  | |- trace_step (Smt (DeclareConst _ Ty_Bool) _ :t: _) _ _ _ =>
      apply DeclareConstBoolS
  | |- trace_step (Smt (DefineConst _ _) _ :t: _) _ _ _ =>
      eapply DefineConstS;
      match goal with |- ?G => idtac "EVAL:"; idtac G end;
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
  ls_step.
  eapply nsteps_step.
  { eapply step_single'.
    eapply (SeqStep _ _ _ _ None _ _).
    - reflexivity.
    - apply DoneES.
    - split.
      + rewrite (e57_nzcv_n_one i len (conj Hlt Hb)).
        rewrite (e57_nzcv_z_zero i len).
        rewrite (e57_nzcv_c_zero i len).
        rewrite (e57_nzcv_v_zero i len).
        reflexivity.
      + eexists (BV 64 0x10300008).
        split.
        * change (Some (RVal_Bits (bv_add (BV 64 0x10300004) (BV 64 4)))
                   = Some (RVal_Bits (BV 64 0x10300008))).
          do 4 f_equal.
          exact bv_add_pc_8.
        * rewrite ls_instrs_a8.
          split; [ reflexivity | ].
          split; [ reflexivity | reflexivity ].
  }
  rewrite bv_add_pc_8.
  apply nsteps_refl.
Qed.