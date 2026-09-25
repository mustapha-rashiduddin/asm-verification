From Coq.ssr Require Import ssreflect.
From stdpp Require Import prelude gmap.
From stdpp.bitvector Require Import definitions.
Require Import isla.opsem.

Open Scope N_scope.
Open Scope Z_scope.

Lemma probe_concrete :
  eval_exp (Manyop (Bvmanyarith Bvadd)
      [Unop (Extract 63 0) (Unop (ZeroExtend 64) (Val (Val_Bits (BV 64 42)) Mk_annot) Mk_annot) Mk_annot;
       Val (Val_Bits (BV 64 1)) Mk_annot] Mk_annot)
  = Some (Val_Bits (bv_add (bv_extract 0 64 (bv_zero_extend 64 (BV 64 42))) (BV 64 1))).
Proof.
  time "cbn" cbn.
  reflexivity.
Qed.

Lemma probe_variable (i : bv 64) :
  eval_exp (Manyop (Bvmanyarith Bvadd)
      [Unop (Extract 63 0) (Unop (ZeroExtend 64) (Val (Val_Bits i) Mk_annot) Mk_annot) Mk_annot;
       Val (Val_Bits (BV 64 1)) Mk_annot] Mk_annot)
  = Some (Val_Bits (bv_add (bv_extract 0 64 (bv_zero_extend 64 i)) (BV 64 1))).
Proof.
  time "refl" reflexivity.
Qed.

Lemma probe_variable_vm (i : bv 64) :
  eval_exp (Manyop (Bvmanyarith Bvadd)
      [Unop (Extract 63 0) (Unop (ZeroExtend 64) (Val (Val_Bits i) Mk_annot) Mk_annot) Mk_annot;
       Val (Val_Bits (BV 64 1)) Mk_annot] Mk_annot)
  = Some (Val_Bits (bv_add (bv_extract 0 64 (bv_zero_extend 64 i)) (BV 64 1))).
Proof.
  time "vm" vm_compute.
  reflexivity.
Qed.

Lemma probe_evar :
  eval_exp (Manyop (Bvmanyarith Bvadd)
      [Unop (Extract 63 0) (Unop (ZeroExtend 64) (Val (Val_Bits ?e) Mk_annot) Mk_annot) Mk_annot;
       Val (Val_Bits (BV 64 1)) Mk_annot] Mk_annot)
  = Some (Val_Bits (bv_add (bv_extract 0 64 (bv_zero_extend 64 ?e)) (BV 64 1))).
Proof.
  time "vm-evar" vm_compute.
  reflexivity.
Qed.