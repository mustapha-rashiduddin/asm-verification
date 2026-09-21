From Coq.ssr Require Import ssreflect.
From stdpp Require Import prelude.
From stdpp.bitvector Require Import definitions.

Lemma bv_wrap_le_len (i len : bv 64) :
  (bv_unsigned i ≤ bv_unsigned len)%Z ->
  (bv_unsigned len * 8 < 2 ^ 52)%Z ->
  (0 ≤ bv_unsigned i < bv_modulus (61%N))%Z.
Proof.
  intros Hile Hlim.
  split.
  - apply (bv_unsigned_in_range (64%N) i).
  - have Hm : (bv_modulus (61%N) = 2 ^ 61)%Z by compute; lia.
    have Hpow : (2 ^ 52 = 8 * 2 ^ 49)%Z by compute; lia.
    have Hlt : (bv_unsigned i < 2 ^ 49)%Z.
    { apply (Zmult_lt_reg_r (bv_unsigned i) (2 ^ 49) 8); [lia|].
      rewrite (Z.mul_comm (2 ^ 49) 8).
      rewrite -Hpow.
      lia. }
    have Hpow2 : (2 ^ 49 < 2 ^ 61)%Z by apply Z.pow_lt_mono_r; lia.
    rewrite Hm. lia.
Qed.

Lemma bv_wrap_61_eq_len (i len : bv 64) :
  (bv_unsigned i ≤ bv_unsigned len)%Z ->
  (bv_unsigned len * 8 < 2 ^ 52)%Z ->
  (bv_wrap (61%N) (bv_unsigned i) = bv_unsigned i)%Z.
Proof.
  intros Hile Hlim.
  apply bv_wrap_small.
  apply bv_wrap_le_len; auto.
Qed.

Lemma bv_wrap_52_eq_base (base i len : bv 64) :
  (bv_unsigned base `mod` 8 = 0)%Z ->
  (bv_unsigned i ≤ bv_unsigned len)%Z ->
  (bv_unsigned base + bv_unsigned len * 8 < 2 ^ 52)%Z ->
  (bv_wrap (52%N) (bv_unsigned base + (bv_wrap (61%N) (bv_unsigned i)) * 8) =
   bv_unsigned base + (bv_wrap (61%N) (bv_unsigned i)) * 8)%Z.
Proof.
  intros Hm Hile Hlim.
  apply bv_wrap_small.
  split.
  - have Hwge0 := bv_unsigned_nonneg base. have Hwge1 := bv_wrap_le_len i len Hile Hlim.
    lia.
  - have Hw61 : (bv_wrap (61%N) (bv_unsigned i) = bv_unsigned i)%Z by apply bv_wrap_61_eq_len; auto.
    have Hl : (bv_unsigned base + bv_unsigned i * 8 < 2 ^ 52)%Z by lia.
    lia.
Qed.

Lemma mod8_addr (base i len : bv 64) :
  (bv_unsigned base `mod` 8 = 0)%Z ->
  (bv_unsigned i ≤ bv_unsigned len)%Z ->
  (bv_unsigned base + bv_unsigned len * 8 < 2 ^ 52)%Z ->
  ((bv_wrap (52%N) (bv_unsigned base + (bv_wrap (61%N) (bv_unsigned i)) * 8) -
    bv_unsigned base) `mod` 8 = 0)%Z.
Proof.
  intros Hm Hile Hlim.
  rewrite (bv_wrap_52_eq_base base i len Hm Hile Hlim).
  have Hw : (bv_wrap (61%N) (bv_unsigned i) = bv_unsigned i)%Z by apply bv_wrap_61_eq_len; auto.
  rewrite Hw.
  have -> : (bv_unsigned base + bv_unsigned i * 8 - bv_unsigned base = bv_unsigned i * 8)%Z by lia.
  rewrite Z.mul_comm.
  apply Z.mod_mul.
  compute. discriminate.
Qed.
