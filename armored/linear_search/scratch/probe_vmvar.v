From Coq.ssr Require Import ssreflect.
From stdpp Require Import prelude gmap.
From stdpp.bitvector Require Import definitions.
Require Import isla.opsem.

Open Scope N_scope.
Open Scope Z_scope.

Lemma probe_variable_vm (i : bv 64) :
  eval_exp (Manyop (Bvmanyarith Bvadd)
      [Unop (Extract 63 0) (Unop (ZeroExtend 64) (Val (Val_Bits (bv_to_bvn i)) Mk_annot) Mk_annot) Mk_annot;
       Val (Val_Bits (bv_to_bvn (BV 64 1))) Mk_annot] Mk_annot)
  = Some (Val_Bits (bv_to_bvn (bv_add (bv_extract 0 64 (bv_zero_extend (64 + 64) i)) (BV 64 1)))).
Proof.
  vm_compute.
  reflexivity.
Qed.