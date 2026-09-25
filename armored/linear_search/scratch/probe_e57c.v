From isla Require Import opsem.
From stdpp.bitvector Require Import definitions.
From stdpp.bitvector Require Import tactics.
Import ListNotations.

Open Scope bv_scope. Open Scope Z_scope.

Definition cmp_sum128 (a b : bv 64) : bv 128 :=
  bv_add (bv_add (bv_zero_extend 128 a) (bv_zero_extend 128 (bv_not b))) (BV 128 1).
Definition cmp_res64 (a b : bv 64) : bv 64 :=
  bv_extract 0 64 (cmp_sum128 a b).

Definition cmp_flag_n (a b : bv 64) : bv 1 :=
  bv_or (bv_and (BV 1 0) (bv_not (BV 1 1)))
        (bv_extract 0 1 (bv_shiftr (cmp_res64 a b) (BV 64 0x3f))).

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

(* the 0x3f shift amount: Extract 63 0 of (BV 128 0x3f) = BV 64 0x3f *)
Lemma bv_extract_3f :
  bv_extract 0 64 (BV 128 0x3f) = BV 64 0x3f.
Proof. bv_solve. Qed.

(* ------------ the three stuck bool_decide propositions ------------ *)

Lemma booldec_Z_false (i len : bv 64) (H : (bv_unsigned i < bv_unsigned len)%Z) :
  bool_decide (cmp_res64 i len = BV 64 0) = false.
Proof.
  apply bool_decide_eq_false_2. intro Hze.
  apply (proj1 (cmp_res64_zero_iff i len)) in Hze. lia.
Qed.

Lemma booldec_C_true (i len : bv 64) (H : (bv_unsigned i < bv_unsigned len)%Z) :
  bool_decide (bv_zero_extend 128 (bv_extract 0 64 (cmp_sum128 i len)) = cmp_sum128 i len) = true.
Proof.
  apply bool_decide_eq_true_2. apply bv_eq.
  apply (proj2 (cmp_sum128_zero_ext_iff i len)). exact H.
Qed.

Lemma booldec_V_true (i len : bv 64)
      (H : (bv_unsigned i < bv_unsigned len < 2^62)%Z) :
  bool_decide (bv_sign_extend 128 (cmp_res64 i len) =
               bv_add (bv_add (bv_sign_extend 128 i) (bv_sign_extend 128 (bv_not len))) (BV 128 1)) = true.
Proof.
  apply bool_decide_eq_true_2. unfold cmp_res64, cmp_sum128.
  bv_solve.
Qed.

(* -------------- the DefineConst 57 expression (post-subst) ------------ *)

Definition e57_def (i len : bv 64) : exp :=
  Manyop Concat
    [ Manyop Concat
        [ Manyop Concat
            [ Manyop (Bvmanyarith Bvor)
                [ Manyop (Bvmanyarith Bvand)
                    [Val (Val_Bits (BV 1 0)) Mk_annot;
                     Unop Bvnot (Val (Val_Bits (BV 1 1)) Mk_annot) Mk_annot] Mk_annot;
                  Unop (Extract 0 0)
                    (Binop (Bvarith Bvlshr)
                       (Val (Val_Bits (cmp_res64 i len)) Mk_annot)
                       (Unop (Extract 63 0) (Val (Val_Bits (BV 128 0x3f)) Mk_annot) Mk_annot)
                       Mk_annot) Mk_annot] Mk_annot;
              Ite (Binop Eq (Val (Val_Bits (cmp_res64 i len)) Mk_annot)
                     (Val (Val_Bits (BV 64 0)) Mk_annot) Mk_annot)
                (Val (Val_Bits (BV 1 0x1)) Mk_annot)
                (Val (Val_Bits (BV 1 0x0)) Mk_annot) Mk_annot] Mk_annot;
          Ite (Binop Eq (Unop (ZeroExtend 64) (Val (Val_Bits (cmp_res64 i len)) Mk_annot) Mk_annot)
                  (Val (Val_Bits (cmp_sum128 i len)) Mk_annot) Mk_annot)
            (Val (Val_Bits (BV 1 0x0)) Mk_annot)
            (Val (Val_Bits (BV 1 0x1)) Mk_annot) Mk_annot] Mk_annot;
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
  Some (Val_Bits (bv_concat 4 (bv_concat 3 (bv_concat 2 (cmp_flag_n i len) (BV 1 0)) (BV 1 0)) (BV 1 0))).
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