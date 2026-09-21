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
  instr_pre 0x0000000010300020 (
    ∃ (tmp : bv 64),
    reg_col sys_regs ∗
    reg_col CNVZ_regs ∗
    "R0" ↦ᵣ RVal_Bits base ∗
    "R1" ↦ᵣ RVal_Bits len ∗
    "R2" ↦ᵣ RVal_Bits tgt ∗
    "R3" ↦ᵣ RVal_Bits i ∗
    "R4" ↦ᵣ RVal_Bits tmp ∗
    "R30" ↦ᵣ RVal_Bits ret ∗
    bv_unsigned base ↦ₘ∗ data ∗
    ⌜bv_unsigned i = bv_unsigned len⌝
  ) ∗
  instr_pre 0x0000000010300028 (
    ∃ (tmp : bv 64),
    reg_col sys_regs ∗
    reg_col CNVZ_regs ∗
    "R0" ↦ᵣ RVal_Bits base ∗
    "R1" ↦ᵣ RVal_Bits len ∗
    "R2" ↦ᵣ RVal_Bits tgt ∗
    "R3" ↦ᵣ RVal_Bits i ∗
    "R4" ↦ᵣ RVal_Bits tmp ∗
    "R30" ↦ᵣ RVal_Bits ret ∗
    bv_unsigned base ↦ₘ∗ data ∗
    ⌜bv_unsigned i < bv_unsigned len⌝ ∗
    ⌜data !! Z.to_nat (bv_unsigned i) = Some tgt⌝
  )
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
  Unshelve.
  all: first [
    match goal with H : bv_zero_extend _ _ ≠ _ |- _ => move: H => /overflow_to_le Hge; lia end |
    liARun |
    iPureIntro; intros j Hj; exfalso |
    iSimpl; iExists (MKArray 64%N (bv_unsigned base) data); iFrame; bv_solve
  ].
all: match goal with |- ?G => idtac "RESID:" G end.
Show Proof.
Time Qed.

End proof.