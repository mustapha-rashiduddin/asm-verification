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

(* [linear_search_nf_spec] and [linear_search_f_spec] are the two exit
   contracts reached on the not-found branch (0x20) and on the found branch
   (0x28).  They are stated as separate [instr_pre] hypotheses, not bundled
   into the loop invariant, so that the SAME [instr_pre] resources can be
   used both when proving the loop body and when proving the whole function.
   Because every [instr_pre] is persistent, no linear resource is duplicated
   across the two exits. *)
Section proof.
Context `{!islaG Σ} `{!threadG}.

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
Arguments linear_search_nf_spec /.
Global Instance : LithiumUnfold (linear_search_nf_spec) := I.

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
Arguments linear_search_f_spec /.
Global Instance : LithiumUnfold (linear_search_f_spec) := I.

(* [linear_search_loop_spec] is the loop invariant at address 0x4 WITHOUT
   the exit obligations: it only records the register/pure facts that hold
   at every back-edge, so the top level can furnish it trivially.  The
   exits are supplied as separate hypotheses (see above).  The loop-body
   lemma [linear_search_loop], the whole-function lemma [linear_search]
   and the composition [linear_search_composed] all use this SAME spec. *)
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
  instr_pre 0x0000000010300020 linear_search_nf_spec ∗
  instr_pre 0x0000000010300028 linear_search_f_spec
.
Arguments linear_search_loop_spec /.
Global Instance : LithiumUnfold (linear_search_loop_spec) := I.

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

(* At the found exit (0x14 b.eq 0x28) the WP concludes that the loaded value
   is different from the target; the extracted subtraction-is-nonzero fact
   below is turned into Z-inequality of the two unsigned values. *)
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

Lemma linear_search_loop :
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c) -∗
  □ instr_pre 0x0000000010300004 linear_search_loop_spec -∗
  instr_body 0x0000000010300004 linear_search_loop_spec.
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
  all: try (iPureIntro; assumption).
  Unshelve.
  all: try match goal with
  | Hov : bv_zero_extend 128 _ ≠ _ |- bv_unsigned _ = bv_unsigned _ =>
      bv_simplify_arith Hov;
      move: Hov => /carry_to_le Hge;
      lia
  end.
  all: try (iPureIntro; assumption).
  Set Ltac Debug.
  Unshelve.
  - match goal with
    | Hlookup : ?data' !! ?idx = Some ?value |- ?data' !! ?want = Some ?htgt =>
        replace want with idx;
        [ replace htgt with value; [ exact Hlookup | bv_solve ] | bv_solve ]
    end.
  - match goal with
    | Hlt : (?j < Z.to_nat (bv_unsigned (bv_extract 0 64 (bv_zero_extend 128 ?I) + 1)))%nat
          |- ?data !! ?j ≠ Some ?htgt =>
        have Hnext :
          Z.to_nat (bv_unsigned (bv_extract 0 64 (bv_zero_extend 128 I) + 1)) =
          S (Z.to_nat (bv_unsigned I)) by bv_solve;
        rewrite Hnext in Hlt;
        have Hpos :
          (j < Z.to_nat (bv_unsigned I))%nat \/
          j = Z.to_nat (bv_unsigned I) by lia;
        destruct Hpos as [Hbefore | Heqj];
        [ match goal with
          | Hpre : ∀ j', (j' < Z.to_nat (bv_unsigned I))%nat → ?data' !! j' ≠ Some ?htgt' |- _ =>
              exact (Hpre j Hbefore)
          end
        | subst j;
          match goal with
          | Hmem : ?data'' !! ?w = Some ?value |- _ =>
              assert (Hlookup : data'' !! Z.to_nat (bv_unsigned I) = Some value) by
                (replace (Z.to_nat (bv_unsigned I)) with w by bv_solve; exact Hmem);
              have Hne0 : bv_unsigned value ≠ bv_unsigned htgt := bv_sub_extract_neq_zero value htgt H8;
              have Hne : value ≠ htgt by (intros Hv; apply Hne0; f_equal; exact Hv);
              intros Heq;
              rewrite Hlookup in Heq;
              injection Heq as Heq;
              exact (Hne Heq)
          end ]
    end.
  Unset Ltac Debug.
  all: match goal with |- ?P => idtac "LO242:" P end.
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

Lemma linear_search stack_size :
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
  □ instr_pre 0x0000000010300004 linear_search_loop_spec -∗
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

(* [linear_search_composed] closes the recursion: the [□ instr_pre 0x4
   linear_search_loop_spec] contract that [linear_search_loop] and
   [linear_search] request is produced from the CODE itself by a Löb-style
   induction hypothesis ([iLöb]) over [□ instr_body 0x4
   linear_search_loop_spec], discharged through [instr_pre_to_body] exactly
   as in `examples/example.v` (`test_state_adequate'`, lines 192-220).  The
   only remaining hypotheses are the code words ([instr] is persistent) and
   the two exit contracts; [instr_pre] itself is affine (not persistent), so
   the exits are given once, persistently, under a [□] and may be re-supplied
   both inside the recursion and for the final application of
   [linear_search]. *)
Lemma linear_search_composed stack_size :
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
  instr_body 0x0000000010300000 (linear_search_spec stack_size).
Proof.
  move => ?. iStartProof.
  iIntros "#Ha0 #Ha4 #Ha8 #Hac #Ha10 #Ha14 #Ha18 #Ha1c #Ha20 #Ha24 #Ha28 #Ha2c".
  iAssert (□ instr_body 0x0000000010300004 linear_search_loop_spec)%I as "Hloop".
  {
    iLöb as "IH". iModIntro.
    iApply linear_search_loop.
    all: try iAssumption.
    iModIntro.
    iApply instr_pre_to_body. by iModIntro.
  }
  iApply (linear_search stack_size).
  all: try iAssumption.
  all: try (lia || iAssumption).
  iModIntro.
  iApply instr_pre_to_body. by iModIntro.
  Unshelve. all: done.
Qed.

End proof.