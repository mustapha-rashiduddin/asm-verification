# linear_search Islaris proof — current status

## Current commit
`c8b781c934b5f7217d36c5740eee97d7f549da74` (`alot of effort`)

This report supersedes the older residual-goal report. The proof source made
substantial progress after that report was written.

## Immediate goal
Finish only:

`armored/linear_search/linear_search_proof.v`

Specifically:

- get `linear_search_loop` to a genuine `Qed`
- zero residual goals
- zero shelved goals
- clean compilation from a fresh Coq invocation
- no `Admitted`, `admit`, `Axiom`, or weakened specification

Do **not** write the top-level `linear_search` theorem yet.
Do **not** work on termination yet.

## Routine layout
- 0x0 `mov x3,xzr`
- 0x4 `cmp x3,x1`
- 0x8 `b.cs 0x20` (i >= len, not-found)
- 0xc `ldr x4,[x0,x3,lsl#3]`
- 0x10 `cmp x4,x2`
- 0x14 `b.eq 0x28` (found)
- 0x18 `add x3,x3,#1`
- 0x1c `b 0x4`
- 0x20 `mvn x0,xzr`
- 0x24 `ret`
- 0x28 `mov x0,x3`
- 0x2c `ret`

Contract remains: R0 = array base, R1 = length, R2 = target; return the first
matching index or UINT64_MAX; preserve the original array memory.

## Required loop invariant
The proof must retain at least:

- `i <= len`
- `len = length data`
- `base mod 8 = 0`
- `base + len*8 < 2^52`
- every element before `i` is not `target`
- ownership of the complete original array

No property may be weakened merely to satisfy automation.

## Progress since the previous report

### 1. The not-found branch arithmetic is essentially solved

The previous residual

`bv_unsigned i = bv_unsigned len`

has been reduced properly through the actual AArch64 comparison/carry semantics.

New lemmas in `linear_search_proof.v` include:

- `bv_wrap_64_neg_one`
- `bv_modulus_64_eq`
- `bv_modulus_128_eq`
- `carry_wrap_le`
- `carry_to_le`

The current branch proof extracts the normalized carry inequality from the
machine-code trace, derives:

`bv_unsigned len <= bv_unsigned i`

and combines it with the invariant:

`bv_unsigned i <= bv_unsigned len`

to obtain equality with `lia`.

This is real progress and should be preserved.

### 2. Effective-address arithmetic has been isolated and proved

New helper file:

`armored/linear_search/mod8addr_lemmas.v`

contains proved arithmetic lemmas:

- `bv_wrap_le_len`
- `bv_wrap_61_eq_len`
- `bv_wrap_52_eq_base`
- `mod8_addr`

These establish the relevant facts about:

- the loop index remaining small enough that 61-bit wrapping is identity
- the effective address remaining small enough that 52-bit wrapping is identity
- `base + i*8` retaining 8-byte alignment

These lemmas should be reused rather than reproved.

## Current blocker

The remaining blocker is the 0xc `ldr` ownership proof.

The proof now manually enters:

`find_in_context_mem_mapsto_semantic`

and constructs:

`MKArray 64%N (bv_unsigned base) data`

which is the correct direction.

The problem is that when the generated memory-membership obligation is being
discharged, the proof state still does not expose the loop-invariant pure facts
needed to apply `mod8_addr` and finish the array split:

- `i <= len`
- `len = length data`
- `base mod 8 = 0`
- `base + len*8 < 2^52`

So the central problem is still **Iris/Lithium proof architecture and scoping**,
not missing arithmetic or missing ISA semantics.

Be precise: it has not been established that `instr_pre` semantically
"discards" these facts. What is established is that the current spec shape plus
Lithium automation does not re-expose them at the generated load obligation.

## Current proof source state

`linear_search_proof.v` is intentionally WIP and does not currently close.

The tail contains debugging sentinels such as:

- `Fail idtac "mod8-bounds-need"`
- `Fail idtac "stop"`

and does not reach a completed `Qed`.

Also, the file currently calls `mod8_addr` but does not import
`mod8addr_lemmas.v`, so the final version must make the module organization
clean and self-contained.

## Required next move

Do **not** keep adding speculative local tactics.

Study and follow the working Islaris proof architecture in:

- `examples/binary_search.v`
- `examples/memcpy.v`

In particular, understand how those proofs structure:

- loop invariants
- recursive `instr_pre`
- exit continuations
- pure invariant facts
- memory ownership
- machine-code load obligations
- the division between loop theorem and outer/main theorem

Then restructure this proof so the invariant facts are available exactly where
the 0xc load proof needs them.

Preserve the existing carry lemmas and address-arithmetic lemmas where they are
correct.

If the upstream-style restructure still fails, stop and record the exact
irreducible proof state here instead of brute-forcing tactics.

## Repository hygiene note

The WIP commit accidentally captured Coq build artifacts including examples of:

- `.lia.cache`
- `*.aux`
- `*.glob`
- `*.vo`
- `*.vok`
- `*.vos`

These are not part of the proof design. Clean them and add suitable ignore rules
when convenient, but do not let repository cleanup distract from finishing the
loop theorem.

## Success condition for the next agent

The next checkpoint is reached only when:

1. `linear_search_loop` is `Qed`.
2. There are no residual or shelved goals.
3. It compiles from a clean invocation.
4. No assumptions/specification were weakened.
5. No `Admitted`, `admit`, or `Axiom` was introduced.
6. The assembly and generated instruction traces remain unchanged.
