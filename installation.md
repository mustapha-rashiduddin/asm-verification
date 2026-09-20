# Installation guide: Rocq + Sail ARM model (hand-verified proofs)

Reproduces the environment used for the verification work in `worklog.md`.
Everything was done on Ubuntu Linux, package-manager user install (no root
required), on 2026-09-20.

Working set:

- OCaml 4.14.1 (opam switch `default`), opam root `~/.opam`
- Rocq (Coq renamed) **9.2.0**  (`rocq-core`, `rocq-runtime`, `rocq-stdlib`)
- `rocq-stdpp` **1.13.0** (+ `rocq-stdpp-bitvector`)
- `rocq-sail-stdpp` **0.20.2**
- Sail ARM model (Rocq sources) from `https://github.com/rems-project/sail-arm`
  (commit `1bf2e55`), model `arm-v9.4-a`

---

## 1. Prerequisites

- Linux (this was Ubuntu). A C toolchain and `make` are needed by opam builds.
- Shell needs `ulimit -s unlimited` before any `rocq compile` on this model —
  the model exceeds the default 8 MB stack. (Sail's own `make` target does the
  same.)

## 2. Install opam and create a switch

```bash
# opam (OCaml package manager), debian/ubuntu:
sudo apt-get install opam       # or: curl -fsSL https://opam.ocaml.org/install.sh | sh

# init for the current user (accept defaults):
opam init --disable-sandboxing   # --disable-sandboxing only if init complains
opam switch create default ocaml-base-compiler.4.14.1
eval $(opam env)                 # put opam's bin/opt on PATH (repeat in each shell)
```

## 3. Install the Rocq packages

```bash
opam update
opam install rocq-core rocq-runtime rocq-stdlib rocq-stdpp rocq-sail-stdpp
```

This is what landed on this machine (versions will drift — keep close to these):

| package | version |
|---|---|
| rocq-core   | 9.2.0 |
| rocq-runtime| 9.2.0 |
| rocq-stdlib | 9.2.0 |
| rocq-stdpp  | 1.13.0 |
| rocq-sail-stdpp | 0.20.2 |

Sanity check:

```bash
eval $(opam env)
rocq --version     # "The Rocq Prover, version 9.2"
```

Note on package names: Coq ≥ 9 was renamed "Rocq" and the opam packages use
the `rocq-*` names. `rocq-sail-stdpp` is the Sail support library (the opam
name inside sail-arm's own file is the historically-named `coq-sail-stdpp`).

## 4. Get the Sail ARM model

```bash
cd ~/rems
git clone https://github.com/rems-project/sail-arm.git
cd sail-arm
git checkout 1bf2e55        # the commit used here
```

The generated Rocq sources live at `arm-v9.4-a/coq/` and are *checked into
the repo* (`arm-v9.4-a/snapshots/coq/` holds the snapshot copy). For re-doing
the proofs below, the compiler itself is **not** required — the sources are
already there.

Optional: regenerate the Rocq model from the .sail sources. This needs the
Sail compiler (repo `https://github.com/rems-project/sail`, v0.20.x). The
checked-in `Makefile` at `arm-v9.4-a/Makefile` has already been adjusted at
this commit for the 0.20 CLI (`--rocq`, `--rocq-undef-axioms`,
`--rocq-output-dir`, `--rocq-lib`); running `make coq` regenerates the model.
If you only work with the vendored `.v` files, skip this.

## 5. Patch arm_extras.v (required)

Sail 0.20.2 emits *measure-less* `while`/`whileM`/`untilM` loops (in the float
print helper and the SVL/page-table-walk computations), but
`rocq-sail-stdpp` only provides the measure-carrying monadic variants. The
checked-in `arm_extras.v` therefore needs three axioms. Append to
`arm-v9.4-a/coq/arm_extras.v`:

```coq
(* Sail 0.20.2 emits a plain (non-monadic) `while` for a terminating pure loop
   in the float print helper, but the Rocq support library only provides the
   well-founded monadic variants (whileMT/whileST).  Axiomatise it; it is only
   used when printing real values and is not part of the architectural
   semantics.  This mirrors Sail's own `--rocq-undef-axioms` treatment. *)
Axiom while : forall {T : Type}, T -> (T -> bool) -> (T -> T) -> T.

(* Sail 0.20.2 also emits a measure-less `whileM` for the terminating SVL
   computation loops, while the support library only provides the
   measure-carrying `whileMT`.  Axiomatise it as well. *)
Axiom whileM : forall {E T : Type}, T -> (T -> Defs.monad E bool) -> (T -> Defs.monad E T) -> Defs.monad E T.

(* Same again for the measure-less `untilM` emitted for the terminating page
   table walk loops. *)
Axiom untilM : forall {E T : Type}, T -> (T -> Defs.monad E bool) -> (T -> Defs.monad E T) -> Defs.monad E T.
```

## 6. Build the model (first time, ~1-2 min)

```bash
eval $(opam env)
ulimit -s unlimited
cd ~/rems/sail-arm/arm-v9.4-a/coq

# header so Rocq knows the logical root:
echo "-R . SailArm" > _CoqProject

rocq compile armv9.v          # includes armv9_types.v, arm_extras.v
```

This produces `armv9.vo`, `armv9_types.vo`, `arm_extras.vo`.

## 7. Compile the proofs

Any proof file that `Require Import SailArm.armv9` can now be compiled against
the model:

```bash
eval $(opam env)
ulimit -s unlimited
rocq compile -R ~/rems/sail-arm/arm-v9.4-a/coq SailArm -o loop.vo loop.v
```

`loop.v` (the SUBS-loop descent/no-underflow/termination proofs) compiles in
~2 s. Feel free to drop in your own `.v` files the same way.

## 8. Quick sanity check

```bash
cd ~/rems/sail-arm/arm-v9.4-a/coq && rocq compile -R . SailArm loop.v
```

exit code 0 and a `loop.vo` = environment is correct. (With `_CoqProject`
present, `-R . SailArm` is already known, but passing it explicitly never
hurts.)

---

## Known foot-guns (learned the hard way)

- **`ulimit -s unlimited` is mandatory**; `rocq compile` on `armv9.v` segfaults
  on stack overflow otherwise.
- **`vm_compute` on terms with abstract variables hangs** (the earlier full
  `loop.v` took 8+ minutes at 100% CPU). Only use `vm_compute` on closed,
  concrete terms (numerals).
- **`rewrite` can silently refuse a subterm that is plainly in the goal** on
  this generated code — use `setoid_rewrite` for those lemmas.
- **`reflexivity` is unreliable on symbolic `mod` goals** reached via a prior
  `rewrite`; close with `apply (Z.mod_add …)`/`apply (Z.mod_small …)` instead.
- If a compile *hangs* visibly, `pkill -f "rocq compile"` (and
  `pkill -f rocqworker`). Use `timeout -k 1 N`, not `timeout N` alone — plain
  `timeout` lets `rocq` survive SIGTERM.