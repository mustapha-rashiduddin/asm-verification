(****************************************************************************)
(*                                                                          *)
(*  Formal sequential memory-safety and functional-correctness proof of     *)
(*  Armored Corp's `linear_search` AArch64 routine, proved against the      *)
(*  Islaris traces generated from the annotated disassembly.                *)
(*                                                                          *)
(*  Code layout (base address 0x10300000, see linear_search.dump):          *)
(*                                                                          *)
(*    0x0000000010300000   mov x3, xzr                (index = 0)           *)
(*    0x0000000010300004   cmp x3, x1                 (i <? len)            *)
(*    0x0000000010300008   b.cs 0x20                  (if i >= len: not_found)*)
(*    0x000000001030000c   ldr x4, [x0, x3, lsl #3]   (tmp = arr[i])        *)
(*    0x0000000010300010   cmp x4, x2                 (tmp <? tgt)          *)
(*    0x0000000010300014   b.eq 0x28                  (if tmp = tgt: found) *)
(*    0x0000000010300018   add x3, x3, #0x1           (index += 1)          *)
(*    0x000000001030001c   b 0x4                      (loop)                *)
(*    0x0000000010300020   mvn x0, xzr                (return UINT64_MAX)   *)
(*    0x0000000010300024   ret                                              *)
(*    0x0000000010300028   mov x0, x3                 (return index)        *)
(*    0x000000001030002c   ret                                              *)
(*                                                                          *)
(*  Contract: on entry R0 = p (uint64 array, 8-aligned, fits below 2^52),   *)
(*  R1 = n (length), R2 = tgt; on return R0 = i if arr[i] = tgt and no      *)
(*  earlier element equals tgt, else R0 = UINT64_MAX (no element equals     *)
(*  tgt).  The array memory is left untouched.  No termination is claimed.  *)
(****************************************************************************)

Require Import isla.aarch64.aarch64.
From isla.instructions.linear_search Require Import instrs.
Require Import mod8addr_lemmas.

(*PROOF_START*)

(* [linear_search_loop_spec] is the loop invariant at address 0x4.  It
   additionally records the two exit obligations: [instr_pre] at 0x20 (the
   not-found epilogue) and [instr_pre] at 0x28 (the found epilogue). *)
Section proof.
Context `{!islaG Σ} `{!threadG}.

Definition linear_search_loop_spec : iProp Σ :=
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
  ⌜∀ j, (j < Z.to_nat (bv_unsigned i))%nat → data !! j ≠ Some tgt⌝ ∗
  (instr_pre 0x0000000010300020 (
    ∃ (i' tmp : bv 64),
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
  ) ∧
  instr_pre 0x0000000010300028 (
    ∃ (i' tmp : bv 64),
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
  ))
.
Arguments linear_search_loop_spec /.
Global Instance : LithiumUnfold (linear_search_loop_spec) := I.

(* Inside the loop body the two exit [instr_pre]s are reached as SEPARATE
   linear resources at two different addresses, so the body proof runs them
   as a conjunction under [∗].  The top-level caller instead receives them as
   the additive [∧] (both continuation shapes are simultaneously available for
   whichever exit actually runs).  [linear_search_loop_spec_sep] is the
   SEP-version used by the body; [linear_search_loop_spec_sep_to_and] shows it
   is at least as strong as the additive version (no linear resources are
   duplicated). *)
Definition linear_search_loop_spec_sep : iProp Σ :=
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
  ⌜∀ j, (j < Z.to_nat (bv_unsigned i))%nat → data !! j ≠ Some tgt⌝ ∗
  (instr_pre 0x0000000010300020 (
    ∃ (i' tmp : bv 64),
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
  ) ∗
  instr_pre 0x0000000010300028 (
    ∃ (i' tmp : bv 64),
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
  ))
.
Arguments linear_search_loop_spec_sep /.
Global Instance : LithiumUnfold (linear_search_loop_spec_sep) := I.

Lemma star_and (P Q : iProp Σ) : P ∗ Q -∗ P ∧ Q.
Proof. iIntros "[HP HQ]". iSplit; iAssumption. Qed.

Lemma to_nat_of_nat_id (n : nat) : Z.to_nat (Z.of_nat n) = n.
Proof. zify; lia. Qed.

Lemma bv_unsigned_or_zero (x : bv 64) :
  bv_unsigned (bv_or (BV 64 0) x) = bv_unsigned x.
Proof. bv_simplify_arith. bv_solve. Qed.

Lemma linear_search_loop_spec_sep_to_and :
  linear_search_loop_spec_sep -∗ linear_search_loop_spec.
Proof.
  iIntros "H".
  iDestruct "H" as (base len tgt i tmp ret data) "H".
  iDestruct "H" as "[Hsys Hrest]".
  iDestruct "Hrest" as "[Hcnvz Hrest]".
  iDestruct "Hrest" as "[H0 Hrest]".
  iDestruct "Hrest" as "[H1 Hrest]".
  iDestruct "Hrest" as "[H2 Hrest]".
  iDestruct "Hrest" as "[H3 Hrest]".
  iDestruct "Hrest" as "[H4 Hrest]".
  iDestruct "Hrest" as "[H30 Hrest]".
  iDestruct "Hrest" as "[Hmem Hrest]".
  iDestruct "Hrest" as "[%Hile Hrest]".
  iDestruct "Hrest" as "[%Hlen Hrest]".
  iDestruct "Hrest" as "[%Hmod Hrest]".
  iDestruct "Hrest" as "[%Hsz Hrest]".
  iDestruct "Hrest" as "[%Hpre Hexit]".
  iDestruct "Hexit" as "[Hnaive Hfound]".
  iExists base, len, tgt, i, tmp, ret, data.
  iSplitL "Hsys"; first done.
  iSplitL "Hcnvz"; first done.
  iSplitL "H0"; first done.
  iSplitL "H1"; first done.
  iSplitL "H2"; first done.
  iSplitL "H3"; first done.
  iSplitL "H4"; first done.
  iSplitL "H30"; first done.
  iSplitL "Hmem"; first done.
  iFrame.
  repeat (iSplit; first by (iPureIntro; assumption)).
  iPureIntro; assumption.
Qed.

(* The b.cs branch at 0x8 is taken iff the C flag is set.  The WP tracks the
   C flag as the carry-out of the comparison i + (not len) + 1 in 128 bits;
   the following lemma turns that "overflow happened" fact into a Z-level
   bound on bv_unsigned len. *)
Lemma overflow_to_le (a b : bv 64) :
  bv_zero_extend 128 (bv_extract 0 64 (bv_add (bv_add (bv_zero_extend 128 a) (bv_zero_extend 128 (bv_not b))) (BV 128 1)))
  ≠ bv_add (bv_add (bv_zero_extend 128 a) (bv_zero_extend 128 (bv_not b))) (BV 128 1)
  → (bv_unsigned b ≤ bv_unsigned a)%Z.
Proof.
  intros Hovf.
  bv_simplify_arith Hovf.
  bv_solve.
Qed.

(* The WP normalizes the C flag to the wrap-form inequality in (1); Lemma 3
   (carry_to_le) turns that into [bv_unsigned len ≤ bv_unsigned i], which is
   the Z-level reading of "the b.cs at 0x8 was taken". *)
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

Lemma linear_search_loop :
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
instr 0x000000001030001c (Some a1c) -∗
  □ instr_pre 0x0000000010300004 linear_search_loop_spec_sep -∗
  instr_body 0x0000000010300004 linear_search_loop_spec_sep.
(*PROOF_END*)
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
  - match goal with
    | Hlookup : data !! ?idx = Some ?value |- data !! ?want = Some tgt =>
        replace want with idx by bv_solve;
        replace tgt with value by bv_solve;
        exact Hlookup
    end.
  - have Hnext :
      Z.to_nat
        (bv_unsigned (bv_extract 0 64 (bv_zero_extend 128 i) + 1)) =
      S (Z.to_nat (bv_unsigned i)) by bv_solve.
    match goal with
    | Hj : (j < Z.to_nat (bv_unsigned (bv_extract 0 64 (bv_zero_extend 128 i) + 1)))%nat |- _ =>
        rewrite Hnext in Hj
    end.
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
      have Hne : vmem ≠ tgt by bv_solve.
      intros Heq.
      rewrite Hlookup in Heq.
      injection Heq as Heq.
      exact (Hne Heq). }
  Unshelve.
  all: try match goal with
  | Hov : bv_zero_extend 128 _ ≠ _ |- bv_unsigned _ = bv_unsigned _ =>
      bv_simplify_arith Hov;
      move: Hov => /carry_to_le Hge;
      lia
  end.
  all: try (iPureIntro; assumption).
  Time Qed.


(* The top-level contract, in the upstream `c_call` style of
   binary_search/rbit.  On entry R0 = p (uint64 array), R1 = n (length),
   R2 = tgt.  On return R0 is either UINT64_MAX (target absent everywhere)
   or the first index whose element equals tgt.  The array is untouched. *)
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

Lemma linear_search_sep_top stack_size :
  0 ≤ stack_size →
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300020 (Some a20) -∗
  instr 0x0000000010300024 (Some a24) -∗
  instr 0x0000000010300028 (Some a28) -∗
  instr 0x000000001030002c (Some a2c) -∗
  □ instr_pre 0x0000000010300004 linear_search_loop_spec_sep -∗
  instr_body 0x0000000010300000 (linear_search_spec stack_size).
Proof.
  move => ?. iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  Unshelve. Show 1.
  Admitted.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  all: try (iPureIntro; assumption).
  Unshelve.
  Show 1.  Show 2.  Show 3.  Show 4.  Show 5.  Show 6.  Show 7.  Show 8.
  Admitted.
  - (* not-found export: R0 = UINT64_MAX and tgt occurs nowhere in data *)
    left.
    split.
    { bv_solve. }
    { intros j.
      destruct (Nat.ltb_spec j (Z.to_nat (bv_unsigned i'))) as [Hlt | Hge].
      { match goal with
        | Hpre : ∀ j', (j' < Z.to_nat (bv_unsigned i'))%nat →
                    data !! j' ≠ Some b2 |- _ => exact (Hpre j Hlt)
        end. }
{ have Hzu : Z.to_nat (bv_unsigned i') = length data.
        { match goal with
          | Hiz : bv_unsigned ?a = bv_unsigned ?b |- _ =>
              rewrite (f_equal Z.to_nat Hiz)
          end.
          match goal with
          | Hlen : bv_unsigned ?c = _ |- _ =>
              rewrite Hlen
          end.
          exact (to_nat_of_nat_id (length data)). }
        rewrite Hzu in Hge.
        have Hnone : data !! j = None := lookup_ge_None_2 data j Hge.
        intros Heq. by rewrite Hnone in Heq. }
    }
  - (* found export: first occurrence *)
    right.
    split.
    { bv_solve. }
    split.
    { rewrite (bv_unsigned_or_zero i').
      match goal with
      | Hfact : data !! Z.to_nat (bv_unsigned i') = Some b2 |- _ =>
          exact Hfact
      end. }
    { intros j Hj.
      match goal with
      | Hpre : ∀ j', (j' < Z.to_nat (bv_unsigned i'))%nat →
                  data !! j' ≠ Some b2 |- _ =>
          rewrite (bv_unsigned_or_zero i') in Hj;
          exact (Hpre j Hj)
      end. }
  Time Qed.
End proof.
