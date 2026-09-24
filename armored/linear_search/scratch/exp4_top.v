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

(* The epilogue pins the state's R30 to the caller's return address [ret0] so
   that the `ret` instructions (a24/a2c) really jump back into the caller's
   c_call-ret continuation.  [linear_search_nf_spec_ep base len tgt data ret0]
   is like [linear_search_nf_spec] but with R30 := ret0 (not-found); likewise
   the found variant.

   The not-found/found identity that must survive the loop -- the array base
   [base], its length [len], the searched-for target [tgt], the array contents
   [data] and the return address [ret0] -- is passed EXPLICITLY, and only the
   genuinely branch-local values ([i'], [tmp]) are existential.  The loop
   invariant therefore reaches its exits with the SAME `base`, `data`, etc. as
   the outer loop-token witnesses: no fresh, unrelated exit witnesses are
   introduced at the epilogues. *)
Definition linear_search_nf_spec_ep
  (base len tgt : bv 64) (data : list (bv 64)) (ret0 : bv 64) : iProp Σ :=
  ∃ (i' tmp : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits base ∗
  "R1" ↦ᵣ RVal_Bits len ∗
  "R2" ↦ᵣ RVal_Bits tgt ∗
  "R3" ↦ᵣ RVal_Bits i' ∗
  "R4" ↦ᵣ RVal_Bits tmp ∗
  "R30" ↦ᵣ RVal_Bits ret0 ∗
  bv_unsigned base ↦ₘ∗ data ∗
  ⌜bv_unsigned i' = bv_unsigned len⌝ ∗
  ⌜bv_unsigned len = length data⌝ ∗
  ⌜∀ j, (j < Z.to_nat (bv_unsigned i'))%nat → data !! j ≠ Some tgt⌝
.
Arguments linear_search_nf_spec_ep /.
Global Instance : LithiumUnfold (linear_search_nf_spec_ep) := I.

Definition linear_search_f_spec_ep
  (base len tgt : bv 64) (data : list (bv 64)) (ret0 : bv 64) : iProp Σ :=
  ∃ (i' tmp : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits base ∗
  "R1" ↦ᵣ RVal_Bits len ∗
  "R2" ↦ᵣ RVal_Bits tgt ∗
  "R3" ↦ᵣ RVal_Bits i' ∗
  "R4" ↦ᵣ RVal_Bits tmp ∗
  "R30" ↦ᵣ RVal_Bits ret0 ∗
  bv_unsigned base ↦ₘ∗ data ∗
  ⌜bv_unsigned i' < bv_unsigned len⌝ ∗
  ⌜bv_unsigned len = length data⌝ ∗
  ⌜data !! Z.to_nat (bv_unsigned i') = Some tgt⌝ ∗
  ⌜∀ j, (j < Z.to_nat (bv_unsigned i'))%nat → data !! j ≠ Some tgt⌝
.
Arguments linear_search_f_spec_ep /.
Global Instance : LithiumUnfold (linear_search_f_spec_ep) := I.

(* [linear_search_loop_spec] is the loop invariant at address 0x4.  The
   exits are pinned to the invariant's own R30 value [ret]: at each exit
   the code `ret`s to [ret], so the continuation demanded at 0x20/0x28 is
   exactly the register value the machine state already carries.  The two
   trailing exits are ADDITIVE (conjoined with /\ instead of separated by
   ∗): the loop lemma and the top level each select the particular side
   needed at the b.cs/b.eq branch, using a pure projection, so that ONE
   spec (and one caller continuation) services both mutually-exclusive
   epilogues.  lithium/FindInstrKind does not descend through /\, so the
   branch plumbing is done by hand with find_in_context_instr_kind_pre_true. *)
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
  instr_pre 0x0000000010300020 (linear_search_nf_spec_ep base len tgt data ret) ∧
  instr_pre 0x0000000010300028 (linear_search_f_spec_ep base len tgt data ret)
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

(* In the continue branch of the loop (the 0x14 b.eq 0x28 was NOT taken) the
   WP instead concludes that the wrapped subtraction differs from 0; that is
   the same "load differs from target" fact, in the [bv_wrap] notation. *)
Lemma bv_wrap_neq_zero_to_unsigned_neq (a b : bv 64) :
  bv_wrap 64 (bv_unsigned a + bv_wrap 64 (- bv_unsigned b - 1) + 1) ≠ 0 →
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
  Unshelve.
  (* The additive trailing exits cannot be reached by lithium/FindInstrKind
     (it does not descend through the /\ inside the intro'd loop invariant),
     so liARun stops at FOUR `find_in_context (FindInstrKind 0x20 / 0x28
     true)` residuals -- the b.cs and b.eq taken paths -- plus the pure
     i+1-mismatch obligation.  For each find: project the appropriate side
     of the /\ exits (a pure projection, no Sep separation of the exit
     resources), then resolve the find with the Islaris pre-true instance.
     Residual order observed after the liARun barrage:
       1. pure:  data !! j ≠ Some tgt               (S i+1 mismatch)
       2. find 0x20 (nf exit, plain wp continuation)
       3. find 0x28 (f exit, plain wp continuation)
       4. find 0x20 (nf exit, li_instr_pre continuation)
       5. find 0x28 (f exit, li_instr_pre continuation) *)
  - assert (Hnextb :
        Z.to_nat (bv_unsigned (bv_extract 0 64 (bv_zero_extend 128 i) + 1)) =
        S (Z.to_nat (bv_unsigned i))) by bv_solve.
    rewrite Hnextb in H9.
    assert (Hpos : (j < Z.to_nat (bv_unsigned i))%nat \/ j = Z.to_nat (bv_unsigned i)) by lia.
    destruct Hpos as [Hbefore | Heqj].
    { exact (H4 j Hbefore). }
    { subst j.
      assert (Hlookup : data !! Z.to_nat (bv_unsigned i) = Some vmem) by
        (match goal with
         | Hmem : data !! ?idx = Some vmem |- _ =>
             replace (Z.to_nat (bv_unsigned i)) with idx by bv_solve; exact Hmem
         end).
      have Hne0 : bv_unsigned vmem ≠ bv_unsigned tgt := bv_wrap_neq_zero_to_unsigned_neq vmem tgt H8.
      have Hne : vmem ≠ tgt by (intros Hv; apply Hne0; f_equal; exact Hv).
      intros Heq.
      rewrite Hlookup in Heq.
      injection Heq as Heq.
      exact (Hne Heq). }
  - iDestruct select ((instr_pre 0x0000000010300020 _ ∧ instr_pre 0x0000000010300028 _)%I) as "[Hnf_ _]".
    iApply (find_in_context_instr_kind_pre_true 271581216 _).
    iExists true, (linear_search_nf_spec_ep base len tgt data ret).
    iFrame "Hnf_".
    liARun.
    iPureIntro. done.
  - iDestruct select ((instr_pre 0x0000000010300020 _ ∧ instr_pre 0x0000000010300028 _)%I) as "[_ Hf_]".
    iApply (find_in_context_instr_kind_pre_true 271581224 _).
    iExists true, (linear_search_f_spec_ep base len tgt data ret).
    iFrame "Hf_".
    liARun.
    iPureIntro. done.
  - iDestruct select ((instr_pre 0x0000000010300020 _ ∧ instr_pre 0x0000000010300028 _)%I) as "[Hnf_ _]".
    iApply (find_in_context_instr_kind_pre_true 271581216 _).
    iExists true, (linear_search_nf_spec_ep base len tgt data ret).
    iFrame "Hnf_".
    liARun.
    iPureIntro. done.
  - iDestruct select ((instr_pre 0x0000000010300020 _ ∧ instr_pre 0x0000000010300028 _)%I) as "[_ Hf_]".
    iApply (find_in_context_instr_kind_pre_true 271581224 _).
    iExists true, (linear_search_f_spec_ep base len tgt data ret).
    iFrame "Hf_".
    liARun.
    iPureIntro. done.
  Unshelve.
  all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  all: try (iPureIntro; assumption).
  Unshelve.
  all: try (match goal with
            | Hov : bv_zero_extend 128 _ ≠ _ |- bv_unsigned _ = bv_unsigned _ =>
                bv_simplify_arith Hov;
                move: Hov => /carry_to_le Hge;
                lia
            end).
  all: try (iPureIntro; assumption).
  Unshelve.
  all: match goal with
       | Hlookup : ?data' !! ?idx = Some ?value |- ?data' !! ?want = Some ?htgt =>
           replace want with idx by bv_solve;
           replace htgt with value by bv_solve;
           exact Hlookup
       end.
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

(* ===========================================================================
   Split at 0x4.
   ---------------------------------------------------------------
   [linear_search_from_loop] is the region [0x0 → 0x4 → loop → exits →
   epilogues → caller-return]: it runs the real instruction `a0` (mov x3, xzr),
   arrives at 0x4, takes over the loop from the persistent
   [□ instr_body 0x4 linear_search_loop_spec] fact (manufactured below from the
   code via Löb), and discharges the real `c_call` return continuation still in
   scope.  Nothing here assumes the exits or the loop precondition; the loop
   token is supplied by [linear_search] itself.

   The 0x2x epilogues need a0..a1c (loop body) and a20..a2c (exits).
   =========================================================================== *)

Lemma linear_search_from_loop stack_size :
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
  □ instr_body 0x0000000010300004 linear_search_loop_spec -∗
  instr_body 0x0000000010300000 (linear_search_spec stack_size).
(*PROOF_END*)
Proof.
  move => ?. iStartProof.
  iIntros "#Ha0 #Ha4 #Ha8 #Hac #Ha10 #Ha14 #Ha18 #Ha1c #Ha20 #Ha24 #Ha28 #Ha2c #Hloop".
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
  all: try (match goal with
            | H : bv_zero_extend 128
                    (bv_extract 0 64
                      (bv_add
                        (bv_add (bv_zero_extend 128 ?ai)
                                (bv_zero_extend 128 (bv_not ?aln)))
                        (BV 128 1))) =
                  bv_add
                    (bv_add (bv_zero_extend 128 ?ai)
                            (bv_zero_extend 128 (bv_not ?aln)))
                    (BV 128 1) |- _ =>
                have Hilt : (bv_unsigned ?ai < bv_unsigned ?aln)%Z :=
                  no_carry_to_lt ai aln H;
                liARun
            end).
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  all: try (iPureIntro; assumption).
  Unshelve.
  all: try (match goal with
            | Hov : bv_zero_extend 128 _ ≠ _ |- bv_unsigned _ = bv_unsigned _ =>
                bv_simplify_arith Hov;
                move: Hov => /carry_to_le Hge;
                lia
            end).
  all: try (iPureIntro; assumption).
  Unshelve.
  - left.
    split.
    { bv_solve. }
    { intros j.
      assert (Hiz : bv_unsigned i' = Z.of_nat (length data)) by lia.
      assert (Hlen : Z.to_nat (bv_unsigned i') = length data).
      { rewrite Hiz. exact (Nat2Z.id (length data)). }
      destruct (Nat.lt_ge_cases j (length data)) as [Hltj | Hgej].
      - assert (Hlti : (j < Z.to_nat (bv_unsigned i'))%nat) by lia.
        exact (H6 j Hlti).
      - rewrite (proj2 (lookup_ge_None data j) Hgej).
        discriminate. }
  - right.
    assert (Hiu : bv_unsigned (bv_or 0 i') = bv_unsigned i') by bv_solve.
    replace (bv_unsigned (bv_or 0 i')) with (bv_unsigned i') by exact Hiu.
    split.
    { assert (Hi0 : (0 ≤ bv_unsigned i')%Z) by
        (destruct (bv_unsigned_in_range (64%N) i') as [Hlo _]; exact Hlo).
      assert (Hub : (bv_unsigned i' < Z.of_nat (length data))%Z).
      { rewrite <- (Z2Nat.id (bv_unsigned i') Hi0).
        exact (proj1 (Nat2Z.inj_lt (Z.to_nat (bv_unsigned i')) (length data)) H7). }
      exact Hub. }
    { split.
      { exact H6. }
      { exact H8. } }
Qed.

(* ===========================================================================
   Closed theorem: the code words a0..a2c suffice.  The persistent
   [□ instr_body 0x4 linear_search_loop_spec] token is produced from the code
   itself by a Löb-style induction (as in `linear_search_proof.v`):
   `iLöb` gives the induction hypothesis, [linear_search_loop] discharges it
   against the loop body code, and `instr_pre_to_body` closes the missing ▷.
   =========================================================================== *)

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
  instr_body 0x0000000010300000 (linear_search_spec stack_size).
(*PROOF_END*)
Proof.
  move => ?. iStartProof.
  iIntros "#Ha0 #Ha4 #Ha8 #Hac #Ha10 #Ha14 #Ha18 #Ha1c #Ha20 #Ha24 #Ha28 #Ha2c".
  iAssert (□ instr_body 0x0000000010300004 linear_search_loop_spec)%I as "#Hloop".
  {
    iLöb as "IH". iModIntro.
    iApply linear_search_loop.
    all: try iAssumption.
    iModIntro.
    iApply instr_pre_to_body. by iModIntro.
  }
  iApply (linear_search_from_loop stack_size).
  all: try iAssumption.
  all: try lia.
Qed.

End proof.