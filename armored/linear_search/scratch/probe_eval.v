From isla Require Import opsem.
From stdpp.bitvector Require Import definitions.

Open Scope bv_scope. Open Scope Z_scope.

Check eval_binop.
Check eval_manyop.

Example t1 (i : bv 64) :
  eval_binop Eq
    (bvn_of (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not (BV 64 16)))) (BV 128 1))))
    (bvn_of (BV 64 0)) = Some (Val_Bool true).
Proof. lazy [eval_binop bvn_to_bv]. vm_compute. Admitted.

Example t2 (i : bv 64) :
  eval_binop Eq
    (bvn_of (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not (BV 64 16)))) (BV 128 1))))
    (bvn_of (BV 64 0)) = Some (Val_Bool (bool_decide (bv_unsigned (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not (BV 64 16)))) (BV 128 1))) = bv_unsigned (BV 64 0)))).
Proof. lazy [eval_binop bvn_to_bv]. reflexivity. Qed.