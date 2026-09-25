From Coq.ssr Require Import ssreflect.
From stdpp Require Import prelude gmap.
From stdpp.bitvector Require Import definitions.
Require Import isla.opsem.

Open Scope N_scope.
Open Scope Z_scope.

Ltac ls_lazy :=
  lazy [eval_exp mapM mbind option_bind eval_unop eval_manyop eval_binop option_fmap option_map fmap mret option_ret guard_or mthrow option_mfail foldl bvn_to_bv bvn_n bvn_val bv_unsigned decide decide_rel BinNat.N.eq_dec N.eq_dec N_rec N_rect N.add N.mul N.sub Pos.add Pos.mul Pos.succ Pos.pred Pos.sub_mask Pos.double_mask Pos.succ_double_mask Pos.pred_double Pos.double_pred_mask].

Lemma probe_lazy_evar :
  forall (i : bv 64),
  eval_exp (Manyop (Bvmanyarith Bvadd)
      [Unop (Extract 63 0) (Unop (ZeroExtend 64) (Val (Val_Bits (bv_to_bvn i)) Mk_annot) Mk_annot) Mk_annot;
       Val (Val_Bits (bv_to_bvn (BV 64 1))) Mk_annot] Mk_annot)
  = Some (Val_Bits (bv_to_bvn (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)))).
Proof.
  move => i.
  ls_lazy.
  reflexivity.
Qed.

Lemma probe_lazy_goal_evar (i : bv 64) :
  let e := bv_to_bvn i in
  eval_exp (Manyop (Bvmanyarith Bvadd)
      [Unop (Extract 63 0) (Unop (ZeroExtend 64) (Val (Val_Bits e)) Mk_annot) Mk_annot;
       Val (Val_Bits (bv_to_bvn (BV 64 1))) Mk_annot] Mk_annot)
  = Some (Val_Bits (bv_to_bvn (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)))).
Proof.
  move => e.
  ls_lazy.
  reflexivity.
Qed.