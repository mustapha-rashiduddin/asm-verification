Require Import Coq.ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
From stdpp.bitvector Require Import tactics.
From isla.instructions.linear_search Require Import instrs.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma t6 : ls_instrs !! (BV 64 0x1030001c) = Some (a1c).
Proof. reflexivity. Qed.

Lemma bv_add_solve : bv_add (BV 64 0x10300018) (BV 64 4) = BV 64 0x1030001c.
Proof.
  apply bv_eq. simpl. lia.
Qed.