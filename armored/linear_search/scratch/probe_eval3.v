From isla Require Import opsem.
From stdpp.bitvector Require Import definitions.

Open Scope bv_scope. Open Scope Z_scope.

Check eval_exp.

Example t2b (i : bv 64) :
  eval_exp (Ite
      (Binop Eq
        (Val (Val_Bits (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not (BV 64 16)))) (BV 128 1)))) Mk_annot)
        (Val (Val_Bits (BV 64 0)) Mk_annot) Mk_annot)
      (Val (Val_Bits (BV 1 1)) Mk_annot)
      (Val (Val_Bits (BV 1 0)) Mk_annot) Mk_annot) = None.
Proof.
  lazy [eval_exp eval_binop bvn_to_bv]. reflexivity.
Qed.