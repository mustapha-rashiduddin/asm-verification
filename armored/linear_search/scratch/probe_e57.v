From isla Require Import opsem.
From stdpp.bitvector Require Import definitions.

Open Scope bv_scope. Open Scope Z_scope.

Definition e57_probe (i len : bv 64) : exp :=
  Manyop Concat
    [Manyop Concat
       [Manyop Concat
          [Manyop (Bvmanyarith Bvor)
             [Manyop (Bvmanyarith Bvand)
                [Val (Val_Bits (BV 1 0x0)) Mk_annot;
                 Unop Bvnot (Val (Val_Bits (BV 1 0x1)) Mk_annot) Mk_annot] Mk_annot;
              Unop (Extract 0 0)
                (Binop (Bvarith Bvlshr)
                   (Val (Val_Bits (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1))))) Mk_annot)
                   (Unop (Extract 63 0) (Val (Val_Bits (BV 128 0x3f))) Mk_annot) Mk_annot) Mk_annot] Mk_annot;
           Ite (Binop Eq (Val (Val_Bits (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1))))) (Val (Val_Bits (BV 64 0))) Mk_annot)
             (Val (Val_Bits (BV 1 0x1)) Mk_annot) (Val (Val_Bits (BV 1 0x0)) Mk_annot) Mk_annot] Mk_annot;
       Ite (Binop Eq (Unop (ZeroExtend 64) (Val (Val_Bits (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1))))) Mk_annot)
                      (Val (Val_Bits (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1)))) Mk_annot)
         (Val (Val_Bits (BV 1 0x0)) Mk_annot) (Val (Val_Bits (BV 1 0x1)) Mk_annot) Mk_annot] Mk_annot;
    Ite (Binop Eq (Unop (SignExtend 64) (Val (Val_Bits (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (bv_not len))) (BV 128 1))))) Mk_annot)
                  (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (SignExtend 64) (Val (Val_Bits i)) Mk_annot; Unop (SignExtend 64) (Val (Val_Bits (bv_not len))) Mk_annot] Mk_annot; Val (Val_Bits (BV 128 1)) Mk_annot] Mk_annot) Mk_annot)
       (Val (Val_Bits (BV 1 0x0)) Mk_annot) (Val (Val_Bits (BV 1 0x1)) Mk_annot) Mk_annot] Mk_annot.

Eval lazy [eval_exp eval_unop eval_manyop eval_binop bvn_to_bv bv_to_bvn] in (eval_exp (e57_probe i len)).