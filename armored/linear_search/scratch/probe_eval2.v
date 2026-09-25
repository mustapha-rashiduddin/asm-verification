From isla Require Import opsem.
From stdpp.bitvector Require Import definitions.

Open Scope bv_scope. Open Scope Z_scope.

Check bv_to_bvn.

Example t2 (i : bv 64) :
  eval_exp (Ite
      (Binop Eq
        (Val (Val_Bits (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not (BV 64 16)))) (BV 128 1)))))
        (Val (Val_Bits (BV 64 0))))
      (Val (Val_Bits (BV 1 1)))
      (Val (Val_Bits (BV 1 0)))) = Some (Val_Bits (BV 1 1)).
Proof.
  lazy [eval_exp eval_binop bvn_to_bv bool_decide Decidable.decide decide]. 
  reflexivity.
Fail Qed.
Abort.

Example t2b (i : bv 64) :
  eval_exp (Ite
      (Binop Eq
        (Val (Val_Bits (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not (BV 64 16)))) (BV 128 1)))))
        (Val (Val_Bits (BV 64 0))))
      (Val (Val_Bits (BV 1 1)))
      (Val (Val_Bits (BV 1 0)))) = None.
Proof.
  lazy [eval_exp eval_binop bvn_to_bv]. reflexivity.
Qed.