Require Import isla.aarch64.aarch64.
From isla.instructions.linear_search Require Import instrs.
Require Import mod8addr_lemmas.

Section proof.
Context `{!islaG Σ} `{!threadG}.

Lemma star_and (P Q : iProp Σ) : P ∗ Q -∗ P ∧ Q.
Proof. iIntros "[HP HQ]". iSplit; iAssumption. Qed.

Lemma to_nat_of_nat_id (n : nat) : Z.to_nat (Z.of_nat n) = n.
Proof. zify; lia. Qed.

Lemma bv_unsigned_or_zero (x : bv 64) :
  bv_unsigned (bv_or (BV 64 0) x) = bv_unsigned x.
Proof. bv_simplify_arith. bv_solve. Qed.

(* The exit continuations, as standalone contracts. *)
Definition linear_search_nf_spec : iProp Σ :=
  ∃ (base len tgt ret : bv 64) (data : list (bv 64)) (i' tmp : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits base ∗
  "R1" ↦ᵣ RVal_Bits len ∗
  "R2" ↦ᵣ RVal_Bits tgt ∗
  "R3" ↦ᵣ RVal_Bits i' ∗
  "R4" ↦ᵣ RVal_Bits tmp ∗
  "R30" ↦ᵣ RVal_Bits ret ∗
  bv_unsigned base ↦ₘ∗ data ∗
  ⌜bv_unsigned i' = bv_unsigned len⌝ ∗
  ⌜bv_unsigned len = length data⌝ ∗
  ⌜∀ j, (j < Z.to_nat (bv_unsigned i'))%nat → data !! j ≠ Some tgt⌝
.

Definition linear_search_f_spec : iProp Σ :=
  ∃ (base len tgt ret : bv 64) (data : list (bv 64)) (i' tmp : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits base ∗
  "R1" ↦ᵣ RVal_Bits len ∗
  "R2" ↦ᵣ RVal_Bits tgt ∗
  "R3" ↦ᵣ RVal_Bits i' ∗
  "R4" ↦ᵣ RVal_Bits tmp ∗
  "R30" ↦ᵣ RVal_Bits ret ∗
  bv_unsigned base ↦ₘ∗ data ∗
  ⌜bv_unsigned i' < bv_unsigned len⌝ ∗
  ⌜bv_unsigned len = length data⌝ ∗
  ⌜data !! Z.to_nat (bv_unsigned i') = Some tgt⌝ ∗
  ⌜∀ j, (j < Z.to_nat (bv_unsigned i'))%nat → data !! j ≠ Some tgt⌝
.

(* The loop invariant WITHOUT the exit contracts: the top can furnish it
   trivially (pure facts + frameable regs/mem), and the exits are provided
   as separate hypotheses by whoever runs the whole function.  The same
   spec is used by the loop-body lemma and the top-level lemma. *)
Definition linear_search_loop_spec_ne : iProp Σ :=
  ∃ (base len tgt i tmp ret : bv 64) (data : list (bv 64)),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits base ∗
  "R1" ↦ᵣ RVal_Bits len ∗
  "R2" ↦ᵣ RVal_Bits tgt ∗
  "R3" ↦ᵣ RVal_Bits i ∗
  "R4" ↦ᵣ RVal_Bits tmp ∗
  "R30" ↦ᵣ RVal_Bits ret ∗
  bv_unsigned base ↦ₘ∗ data ∗
  ⌜bv_unsigned i ≤ bv_unsigned len⌝ ∗
  ⌜bv_unsigned len = length data⌝ ∗
  ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
  ⌜bv_unsigned base + bv_unsigned len * 8 < 2 ^ 52⌝ ∗
  ⌜∀ j, (j < Z.to_nat (bv_unsigned i))%nat → data !! j ≠ Some tgt⌝
.
Arguments linear_search_loop_spec_ne /.
Global Instance : LithiumUnfold (linear_search_loop_spec_ne) := I.
Arguments linear_search_nf_spec /.
Global Instance : LithiumUnfold (linear_search_nf_spec) := I.
Arguments linear_search_f_spec /.
Global Instance : LithiumUnfold (linear_search_f_spec) := I.

Lemma overflow_to_le (a b : bv 64) :
  bv_zero_extend 128 (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 a) (bv_zero_extend 128 (bv_not b))) (BV 128 1)))
  ≠ bv_add (bv_add (bv_zero_extend 128 a) (bv_zero_extend 128 (bv_not b))) (BV 128 1)
  → (bv_unsigned b ≤ bv_unsigned a)%Z.
Proof.
  intros Hovf.
  bv_simplify_arith Hovf.
  bv_solve.
Qed.

Lemma bv_wrap_64_neg_one (b : Z) :
  (0 ≤ b)%Z →
  (b < bv_modulus (64:N))%Z →
  (bv_wrap (64%N) (- b - 1) = bv_modulus (64:N) - 1 - b)%Z.
Proof.
  intros Hb0 Hb1.
  unfold bv_wrap.
  symmetry. apply (Zmod_unique (- b - 1) (bv_modulus (64:N)) (-1%Z) (bv_modulus (64:N) - 1 - b)).
  { split; lia. }
  lia.
Qed.

Lemma bv_modulus_64_eq : bv_modulus (64:N) = (2 ^ 64)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma bv_modulus_128_eq : bv_modulus (128:N) = (2 ^ 128)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma carry_wrap_le (a b : Z) :
  (0 ≤ a < bv_modulus (64:N))%Z →
  (0 ≤ b < bv_modulus (64:N))%Z →
  (bv_wrap (64%N) (a + bv_wrap (64%N) (- b - 1) + 1) ≠
   bv_wrap (128%N) (a + bv_wrap (64%N) (- b - 1) + 1))%Z →
  (b ≤ a)%Z.
Proof.
  intros Ha Hb Hneq.
  destruct Ha as [Ha0 Ha1]. destruct Hb as [Hb0 Hb1].
  assert (Himm := bv_wrap_64_neg_one b Hb0 Hb1).
  rewrite Himm in Hneq.
  assert (Hstep : (a + (bv_modulus (64:N) - 1 - b) + 1 = a - b + bv_modulus (64:N))%Z).
  { lia. }
  rewrite Hstep in Hneq.
  assert (Hm64 := bv_modulus_64_eq).
  assert (Hm128 := bv_modulus_128_eq).
  assert (Hsmall128 : (0 ≤ a - b + bv_modulus (64:N) < bv_modulus (128:N))%Z).
  { subst. lia. }
  rewrite (bv_wrap_small (128%N) (a - b + bv_modulus (64:N)) Hsmall128) in Hneq.
  assert (Hne : (bv_wrap (64%N) (a - b + bv_modulus (64:N)) ≠ a - b + bv_modulus (64:N))%Z) by done.
  destruct (Z_lt_ge_dec a b) as [Hab|Hba].
  - exfalso. apply Hne.
    apply bv_wrap_small.
    split.
    + lia.
    + lia.
  - by lia.
Qed.

Lemma carry_to_le (a b : bv 64) :
  (bv_wrap (64%N) (bv_unsigned a + bv_wrap (64%N) (- bv_unsigned b - 1) + 1) ≠
   bv_wrap (128%N) (bv_unsigned a + bv_wrap (64%N) (- bv_unsigned b - 1) + 1))%Z →
  (bv_unsigned b ≤ bv_unsigned a)%Z.
Proof.
  intros Hneq.
  apply carry_wrap_le; done || exact (bv_unsigned_in_range (64%N) a) || exact (bv_unsigned_in_range (64%N) b).
Qed.


Lemma bv_sub_extract_neq_zero (a b : bv 64) :
  bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 a) (bv_zero_extend 128 (bv_not b))) (BV 128 1)) ≠ BV 64 0 →
  bv_unsigned a ≠ bv_unsigned b.
Proof.
  intros Hne Habs.
  apply Hne.
  bv_simplify_arith.
  bv_solve.
Qed.

Lemma no_carry_to_lt (a b : bv 64) :
  bv_zero_extend 128
    (bv_extract 0 64
      (bv_add
        (bv_add (bv_zero_extend 128 a)
                (bv_zero_extend 128 (bv_not b)))
        (BV 128 1))) =
  bv_add
    (bv_add (bv_zero_extend 128 a)
            (bv_zero_extend 128 (bv_not b)))
    (BV 128 1) →
  (bv_unsigned a < bv_unsigned b)%Z.
Proof.
  intros Hnc.
  bv_simplify_arith Hnc.
  bv_solve.
Qed.

Lemma linear_search_loop_ne :
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c) -∗
  instr_pre 0x0000000010300020 linear_search_nf_spec -∗
  instr_pre 0x0000000010300028 linear_search_f_spec -∗
  □ instr_pre 0x0000000010300004 linear_search_loop_spec_ne -∗
  instr_body 0x0000000010300004 linear_search_loop_spec_ne.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  Unshelve.
  all: try match goal with
  | H : bv_zero_extend 128 _ = _ |- _ =>
      have Hilt : (bv_unsigned i < bv_unsigned len)%Z :=
        no_carry_to_lt i len H;
      liARun
  end.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  all: try (iPureIntro; assumption).
  Unshelve.
  all: try match goal with
  | Hov : bv_zero_extend 128 _ ≠ _ |- bv_unsigned _ = bv_unsigned _ =>
      bv_simplify_arith Hov;
      move: Hov => /carry_to_le Hge;
      lia
  end.
  all: try (iPureIntro; assumption).
  - match goal with
    | Hlookup : data !! ?idx = Some ?value |- data !! ?want = Some tgt =>
        replace want with idx by bv_solve;
        replace tgt with value by bv_solve;
        exact Hlookup
    end.
  - iPureIntro.
    intros j Htoo.
    have Hnext :
      Z.to_nat
        (bv_unsigned (bv_extract 0 64 (bv_zero_extend 128 i) + 1)) =
      S (Z.to_nat (bv_unsigned i)) by bv_solve.
    rewrite Hnext in Htoo.
    have Hpos :
      (j < Z.to_nat (bv_unsigned i))%nat \/
      j = Z.to_nat (bv_unsigned i) by lia.
    destruct Hpos as [Hbefore | Heqj].
    { match goal with
      | Hpre : ∀ j', (j' < Z.to_nat (bv_unsigned i))%nat → data !! j' ≠ Some tgt |- _ =>
          exact (Hpre j Hbefore)
      end. }
    { subst j.
      have Hlookup : data !! Z.to_nat (bv_unsigned i) = Some vmem.
      { match goal with Hmem : data !! ?idx = Some vmem |- _ =>
          replace (Z.to_nat (bv_unsigned i)) with idx by bv_solve;
          exact Hmem
        end. }
      Show.
      have Hne0 : bv_unsigned vmem ≠ bv_unsigned tgt := bv_sub_extract_neq_zero vmem tgt H8.
      have Hne : vmem ≠ tgt by (intros Hv; apply Hne0; f_equal; exact Hv).
      intros Heq.
      rewrite Hlookup in Heq.
      injection Heq as Heq.
      exact (Hne Heq). }
  Time Qed.
Definition linear_search_spec (stack_size : Z) : iProp Σ :=
  (c_call stack_size (λ args sp RET,
    ∃ (data : list (bv 64)),
    bv_unsigned (args !!! 0%nat) ↦ₘ∗ data ∗
    ⌜bv_unsigned (args !!! 1%nat) = length data⌝ ∗
    ⌜bv_unsigned (args !!! 0%nat) `mod` 8 = 0⌝ ∗
    ⌜bv_unsigned (args !!! 0%nat) + length data * 8 < 2 ^ 52⌝ ∗
    RET (λ rets,
      bv_unsigned (args !!! 0%nat) ↦ₘ∗ data ∗
      ⌜(bv_unsigned (rets !!! 0%nat) = bv_modulus 64 - 1 ∧
        ∀ j, data !! j ≠ Some (args !!! 2%nat)) ∨
       (bv_unsigned (rets !!! 0%nat) < length data ∧
        data !! Z.to_nat (bv_unsigned (rets !!! 0%nat)) = Some (args !!! 2%nat) ∧
        ∀ j, (j < Z.to_nat (bv_unsigned (rets !!! 0%nat)))%nat →
             data !! j ≠ Some (args !!! 2%nat))⌝ ∗
      True))
  )%I.
Global Instance : LithiumUnfold (linear_search_spec) := I.

Lemma linear_search_ne stack_size :
  0 ≤ stack_size →
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c) -∗
  instr 0x0000000010300020 (Some a20) -∗
  instr 0x0000000010300024 (Some a24) -∗
  instr 0x0000000010300028 (Some a28) -∗
  instr 0x000000001030002c (Some a2c) -∗
  instr_pre 0x0000000010300020 linear_search_nf_spec -∗
  instr_pre 0x0000000010300028 linear_search_f_spec -∗
  □ instr_pre 0x0000000010300004 linear_search_loop_spec_ne -∗
  instr_body 0x0000000010300000 (linear_search_spec stack_size).
Proof.
  move => ?. iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  all: try (iPureIntro; assumption).
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  Unshelve.
  all: try (iPureIntro;
            intros j Htoo;
            have H0n : bv_unsigned (0 : bv 64) = 0 by bv_solve).
  Unshelve. all: try (rewrite H0n in Htoo).
  Unshelve. all: try (simpl in Htoo; lia).
  Time Qed.
End proof.
