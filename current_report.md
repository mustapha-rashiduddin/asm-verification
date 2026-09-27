# linear_search Islaris proof - current status

## Latest milestone (2026-09-26): trace-level CONTINUE back-edge `exec_continue_backedge` is Qed

### Status

- `exec_continue_backedge` (the real CONTINUE back-edge, one full pass of the
  loop body from PC `0x10300004` with `R3 = i` back to PC `0x10300004` with
  `R3 = i + 1`): **Qed** (genuine `Qed`, no residual or shelved goals,
  `coqc` exit 0, `Print Assumptions exec_continue_backedge` → **Closed under
  the global context**). Proof file: `armored/linear_search/scratch/exp5_term.v`.
- The theorem is **pure composition** of seven already-proved component lemmas.
  No instruction trace was re-executed, no existing Qed theorem was changed, and
  Islaris semantics, assembly, and generated traces were not touched.
- Component chain (all `Qed`, all in `armored/linear_search/scratch/exp5_term.v`):

  | lemma            | from | to   | steps | premise-free |
  |------------------|------|------|-------|--------------|
  | `exec_a4_nzcv`   | `a4` | `a8` | 22    | no (2)       |
  | `exec_a8`        | `a8` | `ac` | 19    | yes          |
  | `exec_ac`        | `ac` | `a10`| 34    | no (3)       |
  | `exec_a10`       | `a10`| `a14`| 22    | no (1)       |
  | `exec_a14`       | `a14`| `a18`| 19    | yes          |
  | `exec_a18_nzcv`  | `a18`| `a1c`| 9     | yes          |
  | `exec_a1c_nzcv`  | `a1c`| `a4` | 17    | yes          |

  `exec_a4_nzcv`, `exec_a18_nzcv`, and `exec_a1c_nzcv` are NZCV-parameterized
  (`ls_regs_nzcv`), so no fake NZCV reset is needed anywhere in the chain.

### Exact theorem statement

```coq
Lemma exec_continue_backedge (base len tgt i r4 v : bv 64) (N0 Z0 C0 V0 : bv 1) (mem : mem_map) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  bv_and (bv_add base (bv_mul i (BV 64 8))) (BV 64 0xfff0000000000007) = BV 64 0 ->
  ac_addr base i = bv_and (ac_addr base i) (BV 64 0xfffffffffffffff8) ->
  read_mem mem (bv_unsigned (ac_rdbase base i)) 8 = Some (bv_to_bvn v) ->
  v ≠ tgt ->
  nsteps 142
    ([ls_θ a4 (ls_regs_nzcv base len tgt i r4 (BV 64 0x10300004) N0 Z0 C0 V0)], ls_σ mem)
    []
    ([ls_θ a4 (ls_regs_nzcv base len tgt
        (bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)) v
        (BV 64 0x10300004)
        (cmp_flag_n v tgt) (BV 1 0) (cmp_flag_c10 v tgt) (cmp_flag_v10 v tgt))], ls_σ mem).
```

Start: trace `a4`, PC `0x10300004`, `R0 = base`, `R1 = len`, `R2 = tgt`,
`R3 = i`, `R4 = r4` (old), arbitrary incoming `N0 Z0 C0 V0`, memory `mem`.
End: trace `a4`, PC `0x10300004`, `R0..R2` unchanged,
`R3 = bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)`, `R4 = v`,
memory unchanged, and NZCV exactly the flags that survive from `cmp x4, x2`
through `a14`/`a18`/`a1c`: `N = cmp_flag_n v tgt`, `Z = BV 1 0`,
`C = cmp_flag_c10 v tgt`, `V = cmp_flag_v10 v tgt`.

The incoming flags are irrelevant and this is now *proved*, not assumed: the
first instruction (`DefineConst 57`, the `a4` compare of `x3` against `x1`)
overwrites `PSTATE.N/Z/C/V` with `(1, 0, 0, 0)` before anything reads them.

### Exact total nsteps proved

`142 = 22 + 19 + 34 + 22 + 19 + 9 + 17`
(`a4`, `a8`, `ac`, `a10`, `a14`, `a18`, `a1c`), i.e. the chain
`a4 → a8 → ac → a10 → a14 → a18 → a1c → a4`.

### Composition helper: exactly one new lemma

Iris' `iris/program_logic/language.v` provides only `nsteps_refl` and
`nsteps_l`; it has **no** `nsteps_trans`/`nsteps_plus`, so the glue was
genuinely required. It is local, minimal, and assumption-free
(`armored/linear_search/scratch/exp5_term.v:1474`):

```coq
Lemma nsteps_trans0 n m (ρ1 ρ2 ρ3 : cfg isla_lang) (κ : list (observation isla_lang)) :
  nsteps n ρ1 κ ρ2 ->
  nsteps m ρ2 [] ρ3 ->
  nsteps (n + m) ρ1 κ ρ3.
```

The empty observation list of the second run is not an abstraction of Islaris
semantics: it records that the continuation run is a fault-free execution of a
generated trace. Call sites must pin `(n := …) (m := …)` explicitly, because
`?n + 120` is not invertible by unification.

### No new semantic hypotheses

The six premises are exactly the union of the component premises: two from
`exec_a4_nzcv` (`i < len`, `len < 2^62`), three from `exec_ac` (the generated
LDR alignment/address premise, the `ac_addr` alignment premise, and
`read_mem … = Some (bv_to_bvn v)`), one from `exec_a10` (`v ≠ tgt`).
`exec_a8`, `exec_a14`, `exec_a18_nzcv`, `exec_a1c_nzcv` are premise-free.
Nothing was invented, strengthened, or weakened.

### Interface check (every junction matched exactly)

- `exec_a4_nzcv` exit: PC `0x08`, flags `(1,0,0,0)`, `R4 = r4` = `exec_a8` entry.
- `exec_a8` exit: PC `bv_add (BV 64 0x10300008) (BV 64 4)` = `exec_ac` entry
  PC `0x1030000c` (via `rewrite bv_add_pc_ac`; definitionally the same value).
- `exec_ac` exit: `R4 = v` supplies the `r4` argument of `exec_a10`.
- `exec_a10` exit: flags `(cmp_flag_n v tgt, BV 1 0, cmp_flag_c10 v tgt,
  cmp_flag_v10 v tgt)` = `exec_a14` entry.
- `exec_a14` exit: PC `bv_add (BV 64 0x10300014) (BV 64 4)` =
  `exec_a18_nzcv` entry PC `0x10300018` (via `rewrite bv_add_pc_18`).
- `exec_a18_nzcv` exit: `R3 = i + 1` = `exec_a1c_nzcv` entry.
- `exec_a1c_nzcv` exit: the required end state, with `R4 = v` and memory `mem`.

The two rewrites only normalize the PC form at a junction; the states are
identical, not weakened.

### Clean verification

Exact clean compile command:

```bash
eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqc -q -Q /home/ubuntu/asm-verification/armored/linear_search/scratch "" -R /home/ubuntu/asm-verification/armored/linear_search/traces isla.instructions.linear_search -R /home/ubuntu/rems/islaris/theories isla /home/ubuntu/asm-verification/armored/linear_search/scratch/exp5_term.v
```

Result: exit status 0.

```text
Require Import exp5_term.
Print Assumptions exec_continue_backedge.
```

Result: **Closed under the global context**.

`git diff --stat` for this milestone: `exp5_term.v` purely additive
(`71 insertions(+)`, 0 deletions). No `Admitted`/`admit`/`Axiom`/`Abort`, no
assembly change, no generated-trace change, no `opsem.v` change, no change to
any existing Qed theorem.

### Scope deliberately not started

Exits (not-found at `0x20`, found at `0x28`), first-encounter/uniqueness of the
match, a generic framework, and the full termination induction are all still
open. This milestone is the back-edge only.

---

## Latest milestone (2026-09-26, second step): the machine increment is unsigned +1 and the variant strictly decreases

### Status

- `next_i_unsigned` : **Qed** — the exact machine R3 result of
  `exec_continue_backedge` is ordinary unsigned `i + 1`.
- `next_i_le_len` : **Qed** — the new index is still inside the loop range.
- `continue_variant_decreases` : **Qed** — `V(i) = len - i` strictly decreases.
- `continue_variant_identity` : **Qed** (extra) — `V(next_i i) = V(i) - 1`.
- `continue_variant_decreases_nat` : **Qed** (extra) — the same decrease at
  `Z.to_nat` level, the form a well-founded induction will consume.
- `coqc exp5_term.v` → exit 0; `Print Assumptions` for all five plus
  `exec_continue_backedge` → **Closed under the global context**.
- Pure arithmetic: no operational semantics used or assumed, no existing Qed
  lemma edited, change is purely additive (96 insertions, 0 deletions).

### Exact statements

```coq
Definition next_i (i : bv 64) : bv 64 :=
  bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1).

Lemma next_i_unsigned (i len : bv 64) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  bv_unsigned (next_i i) = bv_unsigned i + 1.

Lemma next_i_le_len (i len : bv 64) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  (bv_unsigned (next_i i) <= bv_unsigned len)%Z.

Lemma continue_variant_decreases (i len : bv 64) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  (bv_unsigned len - bv_unsigned (next_i i)
     < bv_unsigned len - bv_unsigned i)%Z.

Lemma continue_variant_identity (i len : bv 64) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  (bv_unsigned len - bv_unsigned (next_i i)
     = (bv_unsigned len - bv_unsigned i) - 1)%Z.

Lemma continue_variant_decreases_nat (i len : bv 64) :
  (bv_unsigned i < bv_unsigned len)%Z →
  (bv_unsigned len < 2^62)%Z →
  (Z.to_nat (bv_unsigned len - bv_unsigned (next_i i))
   < Z.to_nat (bv_unsigned len - bv_unsigned i))%Z.
```

### The machine expression is the one actually simplified

`next_i` is *by definition* the exact R3 term of `exec_continue_backedge`
(and of `exec_a18_nzcv` / `exec_a1c_nzcv`), not a hand-written mathematical
successor:

```text
bv_add (bv_extract 0 64 (bv_zero_extend 128 i)) (BV 64 1)
```

`next_i_unsigned` starts with `unfold next_i` and rewrites that term with the
real stdpp bitvector lemmas: `bv_add_unsigned`
(`bv_unsigned (x + y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)`),
`bv_extract_0_unsigned`, and `bv_zero_extend_unsigned' 128 i`. The only
context facts used are the two permitted hypotheses plus `bv_unsigned_in_range
64 i`, which is a *theorem* about every 64-bit value, not an assumption.

### Why wraparound is impossible

`bv_add` is `Z_to_bv 64 (Z.add (bv_unsigned x) (bv_unsigned y))`, so

```text
bv_unsigned (next_i i) = bv_wrap 64 (bv_unsigned i + 1)
bv_wrap 64 z = z mod (bv_modulus 64),  bv_modulus 64 = 2^64
```

(`Hmod : bv_modulus 64 = 2 ^ 64` by `reflexivity`). The loop hypotheses give
`bv_unsigned i < bv_unsigned len` and `bv_unsigned len < 2^62`, hence
`bv_unsigned i + 1 <= 2^62 < 2^64`, so `bv_wrap_small 64 (bv_unsigned i + 1)`
applies and the modular addition is the identity. The two inner wraps are
killed with the generic bound `0 <= bv_unsigned i < 2^64` and `2^64 < 2^128`.
The existing hypotheses alone exclude wraparound; none was strengthened.

### Notes for the eventual induction

- `V(i) = bv_unsigned len - bv_unsigned i` is a `Z` quantity; the nat corollary
  `continue_variant_decreases_nat` is what a well-founded induction on `len - i`
  will consume, and `i < len` guarantees it is non-negative.
- The induction itself, the exits (`0x20` not-found, `0x28` found),
  first-encounter/uniqueness, and any public-contract bridging remain
  deliberately not started.

---

## Earlier milestone (2026-09-22, superseded): whole-function composition closed

The sections below record the earlier invariant-based attempt in
`armored/linear_search/linear_search_proof.v` (`linear_search_loop`,
`linear_search`, `linear_search_composed`). It was superseded by the exp2–exp5
trace-level line of work described above; the notes are kept for history.

## Status

- `linear_search_loop` (loop body, address `0x4`): **Qed** (genuine `Time Qed`,
  zero residual and shelved goals, `coqchk` 0,
  `Print Assumptions linear_search_loop` → **Closed under the global context**,
  no `Admitted`/`admit`/`Axiom`/`Abort`, no assembly or generated-trace
  changes, no termination claim).
- `linear_search` (whole function under `c_call`, address `0x0`): **Qed**
  (genuine `Time Qed`, zero residual and shelved goals, `coqchk` 0,
  `Print Assumptions linear_search` → **Closed under the global context**).
- `linear_search_composed` (assembly-closed theorem, composing the loop body
  with the wrapper via the normal Islaris/Iris recursion): **Qed** (genuine
  `Qed`, `coqchk` 0, `Print Assumptions linear_search_composed` → **Closed
  under the global context**).

## Design: one loop spec for the body, the wrapper, and the recursion

The earlier blocker was that the loop body and the top-level wrapper required
different loop specs (`linear_search_loop_spec_sep` with `∗`-conjoined exits
vs. `linear_search_loop_spec` with additive `∧` exits); the bridge
`linear_search_loop_spec_sep_to_and` was proved but never used to close a
composition, so the loop proof and the wrapper proof were not tied together.

The closing design (validated empirically first in `scratch/sep_hyp.v`, then
moved into `linear_search_proof.v`):

- **No-exit loop invariant** `linear_search_loop_spec` at `0x4`: registers,
  complete-array ownership, and the pure facts (`i ≤ len`, `len = length data`,
  `base mod 8 = 0`, address range, no-earlier-match prefix). No exit
  obligations inside the invariant, so the top level can furnish it trivially.
- **Named exit contracts** lifted out of the invariant:
  `linear_search_nf_spec` (not-found state at `0x20`; `i' = len` and the full
  no-earlier-match prefix) and `linear_search_f_spec` (found state at `0x28`;
  `i' < len`, matching element, full prefix). Each is stated once as an
  `instr_pre` and given to *both* lemmas as a hypothesis, so the SAME spec and
  the SAME exit contracts run through the body, the wrapper, and the
  composition.

Consequences:

- The loop body `linear_search_loop` proves
  `instr_body 0x10300004 linear_search_loop_spec` from the code words `0x4..0x1c`,
  the two exit `instr_pre`s, and `□ instr_pre 0x4 linear_search_loop_spec`
  (its recursion token).
- The wrapper `linear_search` proves
  `instr_body 0x10300000 (linear_search_spec stack_size)` from the code words
  `0x0..0x2c`, the same two exit `instr_pre`s, and the *same*
  `□ instr_pre 0x4 linear_search_loop_spec` recursion token.
- `linear_search_composed` closes the knot in the standard Islaris/Iris
  recursion pattern (as in `examples/example.v`, `test_state_adequate'`,
  lines 192-220): it `iLöb`s over
  `□ instr_body 0x4 linear_search_loop_spec`, discharges the recursion token
  through `instr_pre_to_body` (with `iModIntro`), and feeds the result back to
  `linear_search`. The theorem's only hypotheses are the 13 code words
  (`instr` is persistent) and the two exit contracts.
  `instr_pre` itself is affine (not persistent; confirmed:
  `Persistent (instr_pre a P)` has no type-class instance), so the exits are
  given once under a `□` in `linear_search_composed` and re-supplied both
  inside the recursion and for the final application of `linear_search`.
  No linear resource is duplicated: `instr` and `□ instr_pre` are duplicable,
  and no assembly code or generated trace was changed.

## Loop theorem (intact from the prior milestone)

- The real AArch64 compare/branch semantics establish both the taken
  `i ≥ len` and non-taken `i < len` cases (`overflow_to_le`, `carry_to_le`,
  `no_carry_to_lt`).
- The actual `ldr x4, [x0, x3, lsl #3]` is justified as an in-bounds read from
  the owned array (strict bound + length, alignment, and address-range
  invariants).
- The no-earlier-match prefix is preserved across the increment (second bullet;
  requires the new helper `bv_sub_extract_neq_zero` to turn the
  WP's subtraction-is-nonzero fact at the found exit into
  `bv_unsigned vmem ≠ bv_unsigned tgt`).
- The not-found exit carries `i' = len`, length agreement, the complete
  no-earlier-match prefix, and unchanged complete-array ownership.
- The found exit carries `i' < len`, the matching element, the no-earlier-match
  prefix, and unchanged complete-array ownership.

## Preserved invariant

`linear_search_loop_spec` still contains all required properties:

- `bv_unsigned i <= bv_unsigned len`
- `bv_unsigned len = length data`
- `bv_unsigned base mod 8 = 0`
- `bv_unsigned base + bv_unsigned len * 8 < 2^52`
- every element before `i` differs from `tgt`
- ownership of the complete original array

The exit facts (not-found: `i' = len` + full prefix; found: matching element +
full prefix) live in `linear_search_nf_spec`/`linear_search_f_spec` and are
unchanged from the prior milestone, only re-packaged as standalone contracts.

## Clean Verification

Working directory:

`/home/ubuntu/asm-verification/armored/linear_search`

Exact clean compile command:

```bash
rm -f '.mod8addr_lemmas.aux' 'mod8addr_lemmas.glob' 'mod8addr_lemmas.vo' 'mod8addr_lemmas.vok' 'mod8addr_lemmas.vos' '.linear_search_proof.aux' 'linear_search_proof.glob' 'linear_search_proof.vo' 'linear_search_proof.vok' 'linear_search_proof.vos' && eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqc mod8addr_lemmas.v && coqc -R /home/ubuntu/asm-verification/armored/linear_search/traces isla.instructions.linear_search linear_search_proof.v
```

Result: exit status 0. (Equivalently `coqc -Q . "" -R traces
isla.instructions.linear_search linear_search_proof.v` after `mod8addr_lemmas.v`
is compiled.)

```text
Tactic call liARun ran for 5.5-6 secs (success)   (loop lemma)
Tactic call liARun ran for 8.5-9 secs (success)   (loop lemma, second liARun)
Finished transaction in 6.3 secs (successful)     (loop lemma Qed)
Tactic call liARun ran for 2.3-2.4 secs (success) (top-level)
Finished transaction in 2.3 secs (successful)     (top-level Qed)
Finished transaction in 2.3 secs (successful)     (composed Qed)
```

Exact kernel check command:

```bash
eval "$(opam env --set-switch --switch=/home/ubuntu/rems/islaris)" && export COQPATH=/home/ubuntu/rems/islaris/_build/install/default/lib/coq/user-contrib && coqchk -silent -Q . "" -R traces isla.instructions.linear_search linear_search_proof
```

Result: exit status 0 (only a loadpath-remap warning). `Print Assumptions
linear_search_loop`, `Print Assumptions linear_search`, and `Print Assumptions
linear_search_composed` all report **Closed under the global context**.

## Next Scope

The partial-correctness composition is closed. The only remaining major work is
termination (a well-founded argument that the loop index strictly increases
toward `len`), which is still out of scope for this partial-correctness result.