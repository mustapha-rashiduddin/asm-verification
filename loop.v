Require Import ZArith.
From stdpp Require Import bitvector.definitions base.
Require Import SailStdpp.Values.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.MachineWord.
Require Import SailStdpp.TypeCasts.
Require Import SailArm.armv9.
Local Open Scope Z_scope.

(* =====================================================================
   The model's SUB-immediate semantics, exactly as generated from
   v8_base.sail: a subtract runs the ALU with
     operand2 := not_vec(imm), carry_in := 1,
     (result, nzcv) := AddWithCarry x y carry_in.
   We work on 64-bit registers and fix imm = 1, i.e. the instruction
       SUBS X0, X0, #1
   ===================================================================== *)

Definition sub_imm1 (x : mword 64) : mword 64 :=
  fst (AddWithCarry x (not_vec (zero_extend ('b"000000000001" : mword 12) 64)) ('b"1")).

(* uint of a word is its unsigned bit-vector value *)
Lemma uint_to_bv : forall (x : mword 64), uint x = bv_unsigned (get_word x).
Proof.
  intros x.
  unfold uint, MachineWord.word_to_N; simpl.
  apply Z2N.id.
  exact (proj1 (bv_unsigned_in_range 64 (get_word x))).
Qed.

(* register values stay inside 0 .. 2^64 - 1 *)
Lemma bv_modulus64 : bv_modulus 64 = 2^64.
Proof. vm_compute; reflexivity. Qed.

Lemma uint_range : forall (x : mword 64), (0 <= uint x /\ uint x < 2^64)%Z.
Proof.
  intros x.
  rewrite uint_to_bv.
  assert (Hb : (0 <= bv_unsigned (get_word x) < bv_modulus 64)%Z)
    by exact (bv_unsigned_in_range 64 (get_word x)).
  destruct Hb as [Hlb Hub].
  split.
  - exact Hlb.
  - rewrite bv_modulus64 in Hub.
    exact Hub.
Qed.

(* closure-heavy arithmetic facts, checked by computation *)
Lemma uint_carry : uint (MachineWord.N_to_word 1 (1 + 0) : mword 1) = 1.
Proof. vm_compute; reflexivity. Qed.

Lemma uint_not_imm1 :
  uint (not_vec (zero_extend (MachineWord.N_to_word 12 (1 + 0) : mword 12) 64)) = 18446744073709551614.
Proof. vm_compute; reflexivity. Qed.

(* full-width slice keeps the value *)
Lemma slice_cancel_full : forall (v : mword 64),
  bv_unsigned (bv_extract (MachineWord.Z_idx 0) 64 (get_word v)) = bv_unsigned (get_word v).
Proof.
  intros v. simpl.
  rewrite bv_extract_0_unsigned.
  apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

Lemma subrange_dec_full_uint : forall (v : mword 64), uint (subrange_vec_dec v 63 0) = uint v.
Proof.
  intros v; unfold subrange_vec_dec, uint; simpl.
  f_equal.
  unfold MachineWord.word_to_N. f_equal.
  apply slice_cancel_full.
Qed.

(* the canonical integer-to-word embedding keeps i mod bv_modulus 64 *)
Lemma uint_mword_of_int_mod : forall (i : Z), uint (mword_of_int (len := 64) i) = (i mod bv_modulus 64)%Z.
Proof.
  intros i.
  rewrite (uint_to_bv (mword_of_int (len := 64) i)).
  unfold mword_of_int, MachineWord.Z_to_word, MachineWord.Z_idx; cbv [get_word]; simpl.
  rewrite Z_to_bv_unsigned.
  unfold bv_wrap.
  reflexivity.
Qed.

Lemma autocast_mword_refl : forall (v : mword 64), autocast (T := mword) v = v.
Proof.
  intros v. apply autocast_refl.
Qed.

(* integer_subrange i 63 0 keeps the low 64 bits of i :  i mod bv_modulus 64 *)
Lemma integer_subrange_low64 : forall (i : Z), (0 <= i)%Z ->
  uint (integer_subrange i 63 0) = (i mod bv_modulus 64)%Z.
Proof.
  intros i Hi.
  unfold integer_subrange.
  rewrite get_slice_int_eta.
  unfold get_slice_int'.
  destruct (sumbool_of_bool (64 >=? 0)%Z) as [Hlen | Hlen].
  - simpl.
    change (0 + 64 - 1)%Z with 63.
    rewrite autocast_mword_refl.
    rewrite subrange_dec_full_uint.
    apply uint_mword_of_int_mod.
  - vm_compute in Hlen; discriminate.
Qed.

(* (a + (m - 1)) mod m = (a - 1) mod m *)
Lemma sum_mod : forall (a : Z), (a + (bv_modulus 64 - 1)) mod bv_modulus 64 = (a - 1) mod bv_modulus 64.
Proof.
  intros a.
  replace (a + (bv_modulus 64 - 1)) with (a - 1 + bv_modulus 64) by lia.
  replace (a - 1 + bv_modulus 64) with (a - 1 + 1 * bv_modulus 64) by lia.
  apply (Z.mod_add (a - 1) 1 (bv_modulus 64)).
  vm_compute; discriminate.
Qed.

(* The main arithmetic law:  SUBS X0, X0, #1  computes X0 - 1 (no wrap while >0). *)
Lemma uint_sub_imm1 : forall x : mword 64,
  (1 <= uint x)%Z -> uint (sub_imm1 x) = (uint x - 1)%Z.
Proof.
  intros x Hx.
  unfold sub_imm1, AddWithCarry; simpl.
  rewrite uint_carry.
  rewrite uint_not_imm1.
  change (64 - 1)%Z with 63.
  rewrite autocast_mword_refl.
  setoid_rewrite (integer_subrange_low64
            (uint x + 18446744073709551614 + 1)); [ | lia ].
  assert (H64 : 18446744073709551614 + 1 = bv_modulus 64 - 1) by (vm_compute; reflexivity).
  setoid_rewrite <- (Z.add_assoc (uint x) 18446744073709551614 1).
  setoid_rewrite H64.
  setoid_rewrite (sum_mod (uint x)).
  apply (Z.mod_small (uint x - 1) (bv_modulus 64)).
  rewrite bv_modulus64.
  destruct (uint_range x) as [_ Hup].
  lia.
Qed.

(* =====================================================================
   The loop 'loop: SUBS X0, X0, #1 ; B.GT loop' descends every iteration
   ===================================================================== *)
Theorem loop_always_descends : forall (x : mword 64), (0 < uint x)%Z ->
  (uint (sub_imm1 x) < uint x)%Z.
Proof.
  intros x Hx.
  rewrite uint_sub_imm1 by nia.
  nia.
Qed.

Theorem loop_no_underflow : forall (x : mword 64), (0 < uint x)%Z ->
  (0 <= uint (sub_imm1 x))%Z.
Proof.
  intros x Hx.
  rewrite uint_sub_imm1 by nia.
  nia.
Qed.

(* The driver loop: run SUBS X0, X0, #1 while X0 > 0, at most k times. *)
Fixpoint descend (k : nat) (x : mword 64) : mword 64 :=
  match k with
  | O        => x
  | S k'     => if (uint x <=? 0)%Z then x else descend k' (sub_imm1 x)
  end.

(* Termination: from any initial X0 value it reaches 0 in at most uint x0 steps. *)
Theorem loop_terminates' : forall (v : nat) (x0 : mword 64),
  uint x0 = Z.of_nat v -> uint (descend v x0) = 0.
Proof.
  induction v as [| v IH]; intros x0 Hx.
  - simpl. simpl in Hx. lia.
  - simpl.
    destruct (uint x0 <=? 0)%Z eqn:E.
    + apply Z.leb_le in E.
      rewrite Hx in E.
      rewrite Hx.
      rewrite Nat2Z.inj_succ in E.
      rewrite Nat2Z.inj_succ.
      lia.
    + apply Z.leb_gt in E.
      apply IH.
      rewrite uint_sub_imm1; [ | lia ].
      rewrite Hx.
      rewrite Nat2Z.inj_succ.
      lia.
Qed.

Theorem loop_terminates : forall (x0 : mword 64), (0 <= uint x0)%Z ->
  uint (descend (Z.to_nat (uint x0)) x0) = 0.
Proof.
  intros x0 Hx0.
  apply loop_terminates'.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.