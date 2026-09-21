Require Import isla.isla_lang.
Require Export isla.instructions.linear_search.a0.
Require Export isla.instructions.linear_search.a4.
Require Export isla.instructions.linear_search.a8.
Require Export isla.instructions.linear_search.ac.
Require Export isla.instructions.linear_search.a10.
Require Export isla.instructions.linear_search.a14.
Require Export isla.instructions.linear_search.a18.
Require Export isla.instructions.linear_search.a1c.
Require Export isla.instructions.linear_search.a20.
Require Export isla.instructions.linear_search.a24.
Require Export isla.instructions.linear_search.a28.
Require Export isla.instructions.linear_search.a2c.

Definition instr_map := [
  (0x0%Z, a0 (* mov x3, xzr *));
  (0x4%Z, a4 (* cmp x3, x1 *));
  (0x8%Z, a8 (* b.cs 20 <not_found> *));
  (0xc%Z, ac (* ldr x4, [x0, x3, lsl #3] *));
  (0x10%Z, a10 (* cmp x4, x2 *));
  (0x14%Z, a14 (* b.eq 28 <found> *));
  (0x18%Z, a18 (* add x3, x3, #0x1 *));
  (0x1c%Z, a1c (* b 4 <loop> *));
  (0x20%Z, a20 (* mvn x0, xzr *));
  (0x24%Z, a24 (* ret *));
  (0x28%Z, a28 (* mov x0, x3 *));
  (0x2c%Z, a2c (* ret *))
].
