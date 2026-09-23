# exp2 (hypothesis-free composition) - residual blocker report

## Goal

Validate the exp2-style **hypothesis-free** composition for `linear_search`:
the final `linear_search_composed` should take ONLY `0 ≤ stack_size` + the 13
instruction resources, with no
`□ instr_pre 0x20 linear_search_nf_spec` / `□ instr_pre 0x28 linear_search_f_spec`
hypotheses; the exit `instr_pre`s should be re-derived from the real epilogue
traces via the loop contract ("loop with output"). No weakening of
`linear_search_spec`; no `Admitted`/`Axiom`/`Abort` in the candidate.

## Exact remaining goal (failing `linear_search` in exp2_b2.v, at the 0x8-divergence)

```
--------------------------------------∗
subsume (instr 271581216 (Some a20))
  (λ _ : (), instr_pre 271581216 (∃ -nf-state-))   (* 0x20 not-found *)
  (λ _ : (), instr_pre 271581224 (∃ -f-state-))    (* 0x28 found *)
```

Persistent side has all 13 `instr` words plus one hypothesis

```
_ : instr_pre 271581188
      (∃ base len tgt i tmp ret0 data0,
         ... body ... ∗
         instr_pre 271581216 (∃ -nf-state-) ∗      (* 0x20 not-found *)
         instr_pre 271581224 (∃ -f-state-))        (* 0x28 found *)
```

The two exits exist **only nested inside the loop invariant**.

## New evidence (this session)

- **The flat-exits theory is confirmed correct**: a debug clone
  `linear_search_debug` (same lemma + `instr_pre 271581216 linear_search_nf_spec`
  and `instr_pre 271581224 linear_search_f_spec` as flat premises, exactly like
  the production proof) **Qed's completely** - liARun closes everything, only
  bv/pure sideconditions remain.
- **The exits cannot be extracted from the invariant**:
  `instr_pre' b a P := ▷ P -∗ ∃ ins, instr a ins ∗ ...` is a ***wand***.
  `iDestruct "... as (…) …"` fails with
  `iExistDestruct: cannot destruct (instr_pre 271581188 linear_search_loop_spec)`,
  and a `linear_search_exits` helper reduced the invariant to the
  wand-with-`▷`-antecedent unresolvable. The exits "exist" only inside the
  wand's antecedent; there is no iProp-level way to separate conjuncts out of
  it.
- Helpers based on this (`linear_search_exits`, `linear_search_exit_subsume`)
  were removed as dead ends.

## What this means

The residual is the same fundamental blocker as before: the top-level needs the
two exit `instr_pre`s **flat**, and the only source (the loop invariant)
sequesters them inside an `instr_pre` wand that logic cannot destruct after the
fact. Since `linear_search`'s premises cannot assume the exits (that is the
hypothesis-free requirement), the exits must be *delivered together with the
loop's output* - i.e. the **loop-with-output lemma** must itself emit
`instr_pre 271581216 nf_spec ∗ instr_pre 271581224 f_spec` as its conclusion
alongside `instr_body 0x4`, not keep them buried in its invariant.

## Proposed next step (design change, pending approval)

Restructure `linear_search_loop` to **run the epilogue/write frames itself**
(a20/a24 and a28/a2c) and conclude
`instr_body 0x4 loop_spec ∗ instr_pre 0x20 nf_spec ∗ instr_pre 0x28 f_spec`,
re-deriving the exit contracts from the code + its own destructed loop-state
(the state is available *inside* the loop's run, where the wands are intro'ed -
unlike post-hoc). Then `linear_search` consumes that output and its residual
closes like `linear_search_debug`.

Alternatives remain Options 2/3 (exits back as premises / special-case
`__inputs`), currently de-prioritized by the user.