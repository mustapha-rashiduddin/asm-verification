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

---

# Installation guide (part 2): Isla symbolic execution engine

Isla is a symbolic-execution engine for Sail IR; the prebuilt model snapshots
live in `isla-snapshots`. We only installed/build/verified **Isla itself** here —
not Islaris/Iris/ArchSem. Everything below was run on Ubuntu 24.04.5 LTS
(**aarch64**) on 2026-09-20, alongside the Rocq/Sail-ARM setup in part 1 (that
setup was not touched). Build result: `cargo build --release` succeeds and the
ARM 9.4 footprint smoke test **passed** (exit 0, symbolic trace).

Exact working set:

| component | version |
|---|---|
| Rust / Cargo | **1.98.1** (stable, rustup) |
| Z3 (shared lib) | **4.8.12-3.1build1** (Ubuntu `libz3-dev`) |
| isla | commit `bf1a42f8a6097089fba4810fccc73dcc640267ab` |
| isla-snapshots | commit `d8b31014643035a3b11071e56ef30001de3f52ab` |

## 1. Prerequisites (Ubuntu)

Rust (no toolchain was present; rustup):

```bash
curl -fsSL https://sh.rustup.rs -o /tmp/rustup-init.sh
sh /tmp/rustup-init.sh --profile default -y --default-toolchain stable
export PATH="$HOME/.cargo/bin:$PATH"     # add to ~/.bashrc
rustc --version   # 1.98.1
cargo --version   # 1.98.1
```

Z3 development library (a bare `z3` binary is *not* enough — Isla links
`libz3.so` through the `z3-sys 0.5.0` crate):

```bash
sudo apt-get install -y libz3-dev   # Z3 4.8.12 on Ubuntu 24.04 (arm64)
ldconfig -p | grep z3               # libz3.so, libz3.so.4 must appear
```

## 2. Get Isla and the model snapshots

```bash
cd ~/rems
git clone https://github.com/rems-project/isla.git
cd isla
git checkout bf1a42f8a6097089fba4810fccc73dcc640267ab

cd ~/rems
git clone https://github.com/rems-project/isla-snapshots.git
cd isla-snapshots
git checkout d8b31014643035a3b11071e56ef30001de3f52ab
```

## 3. Prepare the ARM 9.4 model

The snapshots ship `armv9p4.ir.gz` and Isla's model loader does **not** read
gzip. Decompress:

```bash
cd ~/rems/isla-snapshots
gzip -dk armv9p4.ir.gz     # keep the .gz, produce armv9p4.ir (~155 MB)
```

## 4. Build Isla (release)

```bash
cd ~/rems/isla
cargo build --release
```

Took ~3 m 49 s on the 4-core aarch64 box. Output: `target/release/isla-*`.
Only dead-code warnings; nothing fatal. (`z3-sys` finds the system Z3 via
pkg-config; the `z3` product of the build is a Rust crate that does **not**
need the `z3` binary on `PATH`.)

## 5. ARM 9.4 footprint smoke test

This was the goal test — instruction `add x0, x1, #3` against the ARM 9.4
snapshot:

```bash
cd ~/rems/isla-snapshots
~/rems/isla/target/release/isla-footprint \
  -A armv9p4.ir -C ~/rems/isla/configs/armv9p4.toml -i "add x0, x1, #3" -s
```

Successful result: exit code **0**, deterministic symbolic trace ending in
`(write-reg |R0| nil …)` after bvadding `#x…3` to a `read-reg |R1|`.

Quirks worth knowing:

- A `No primop emulator_read_tag … emulator_write_tag …` message on stderr is
  benign (two primops in the snapshot this Isla commit does not model);
  execution still completes.
- The release profile has `panic = "abort"`, so piping the tool into an
  early-closing pipe (e.g. `… | head`) aborts it with SIGABRT/EPIPE. Redirect to
  a file instead.

Verify your install is reproducible: the same checkout + `cargo build --release`
on another machine gives the same smoke-test result.

---

# Installation guide (part 3): Islaris

Islaris is the machine-code verification layer on top of the Isla footprint
tool. This guide covers *building Islaris itself* only — no example generation,
no proofs, no ArchSem. Done on Ubuntu 24.04.5 LTS (**aarch64**) on 2026-09-20,
alongside the Rocq/Sail-ARM (part 1) and Isla (part 2) setups, **none of which
were modified**. Build result: **passed** (`make` exit 0).

Exact working set:

| component | version / SHA |
|---|---|
| islaris | commit `c978e10f50db5c40f0fdf113f5f76a779782c6f9` |
| isla (Islaris-compatible) | commit `b8e614bda4a20e42c37d8b216853653133d04322` |
| isla-snapshots (compatible) | commit `b58da9170470a422c9396983ac8f87f0a63ba6f8` |
| isla-lang (opam pin) | git `bda86c9f0bd28bbaa2481f50ddc986ede342805a` |
| OCaml (local switch) | 4.14.0 (`ocaml-variants.4.14.0+options` + `ocaml-option-flambda`) |
| Coq | **8.19.0** in the local switch |
| dune | pinned **3.9.1** (git tag) |
| opam | 2.1.5 |

## 1. Prerequisites (Ubuntu)

GMP and the AArch64 binutils (both were already installed on this box):

```bash
sudo apt-get install -y libgmp-dev binutils-aarch64-linux-gnu
```

Also required for the compatible Isla build: `libz3-dev` (see part 2) and a
Rust toolchain.

## 2. Compatible Isla + snapshot checkouts (do NOT touch parts 1/2 dirs)

Islaris expects a working Isla checkout and its snapshots next to it. Keep the
existing `~/rems/isla` / `~/rems/isla-snapshots` as they are and make separate
checkouts at the tested revisions:

```bash
cd ~/rems
git clone https://github.com/rems-project/isla.git isla-islaris
git -C isla-islaris checkout b8e614bda4a20e42c37d8b216853653133d04322
git clone https://github.com/rems-project/isla-snapshots.git isla-snapshots-islaris
git -C isla-snapshots-islaris checkout b58da9170470a422c9396983ac8f87f0a63ba6f8

cd ~/rems/isla-islaris
cargo build --release        # links system libz3.so.4 (Z3 4.8.12); ~5 min on 4×arm64
```

Islaris's `bin/isla-footprint` finds these either via environment variables or
relative paths. Since we did not use the names it defaults to, export:

```bash
export ISLA_REPO="$HOME/rems/isla-islaris"
export ISLA_SNAP_REPO="$HOME/rems/isla-snapshots-islaris"
```

(The snapshot file Islaris actually loads for aarch64 is `aarch64.ir`, which
ships uncompressed in that snapshot checkout.)

## 3. Local opam switch inside the Islaris checkout

Islaris pins Coq 8.19.0 and dev versions of stdpp/iris/lithium, so use a
dedicated switch — never the Rocq 9.2 `default` switch:

```bash
cd ~/rems/islaris           # AFTER git clone + checkout c978e10f…
opam switch create . ocaml-variants.4.14.0+options ocaml-option-flambda --no-install
```

Add the two non-default repositories and scope them to this switch. Important:
the local switch's id is its **full path** — a bare `--switch islaris` does not
select it (it leaks the repos into the default switch instead). Always use
`--switch=/home/ubuntu/rems/islaris`:

```bash
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released --switch=/home/ubuntu/rems/islaris
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git --switch=/home/ubuntu/rems/islaris
opam update
```

If you accidentally widened the default switch's selection, restore it with
`opam repo remove <repo> --switch=default`.

## 4. Install dependencies and build

Readme procedure, with a flag to survive non-interactive shells and a dune pin
(see quirks below):

```bash
cd ~/rems/islaris
eval $(opam env)
opam pin add dune.3.9.1 'git+https://github.com/ocaml/dune.git#3.9.1'
opam install dune -y
make builddep OPAMFLAGS=-y
make
```

What `make builddep` installs (exact versions on this machine, switch
`/home/ubuntu/rems/islaris`):

| package | version |
|---|---|
| coq / coq-core / coq-stdlib / coqide-server | 8.19.0 |
| coq-lithium | dev.2024-09-11.0.7945a29d |
| coq-stdpp, coq-stdpp-bitvector, coq-stdpp-unstable | dev.2024-09-10.3.a1a12e00 |
| coq-iris | dev.2024-09-10.1.6f24ed4b |
| coq-record-update | 0.3.3 |
| isla-lang | dev (git pin `bda86c9f…`) |
| dune | 3.9.1 (pinned, git tag) |
| menhir & friends | 20260209 |
| ott | 0.34 |
| cmdliner | 2.1.1 |
| integers | 0.8.0 |
| pprint | 20230830 |
| zarith | 1.14 |
| ocamlfind | 1.9.8 |
| ocamlgraph | 2.2.0 |
| conf-gmp / conf-pkg-config / conf-linux-libc-dev | 5 / 5 / 0 |

Build result: `make` → `dune build _build/default/islaris.install` → exit 0.
Artifacts: `_build/default/islaris.install`, `_build/default/frontend/main.exe`.
Sanity check (offline, generates nothing):

```bash
eval $(opam env)
dune exec -- islaris --help     # prints the manual, exit 0
```

## 5. Quirks / workarounds

- **dune 3.9.1 was pruned from the current opam-repository** ("dune = 3.9.1 no
  matching version"; available versions skip 3.6.2 → 3.10.0). Pin from the git
  tag, using the version-qualified pin name so opam doesn't keep the newer
  version: `opam pin add dune.3.9.1 'git+https://github.com/ocaml/dune.git#3.9.1'`.
- **`make builddep` prompts** ("create as a NEW package?", pin confirmations)
  and fails silent-prompt in a non-tty — pass `OPAMFLAGS=-y`.
- **Local-switch repo scoping**: `opam repo add … --switch <basename>` silently
  fails to target a local switch. Use the absolute switch path.
- **Check the untouched installs after any opam work**: `opam switch` to
  `default` must list only the Rocq 9.2 packages from part 1 (see worklog §10 for
  the verified list) and `~/rems/{sail-arm,isla,isla-snapshots}` must still be
  at their original commits.

## 6. Next steps (not done here)

`make generate` (needs `PATH=$PWD/bin:$PATH` so the frontend finds
`bin/isla-footprint`, plus `ISLA_REPO`/`ISLA_SNAP_REPO`), and proving the
generated Coq (`make` builds the shipped examples already, but our own traces
are future work). ArchSem was explicitly **not** installed.

## 7. Run + verify the unaligned_accesses example (done, PASSED)

Example: `examples/unaligned_accesses.dump` (machine instruction
`f9000020  str x0, [x1]` with the constraint
`= (bvand R1 0xfff0000000000007) 0x0000000000000001`). This runs the full
Isla → Islaris(Coq trace) → coqc pipeline and re-checks the shipped
`str_unaligned` theorem.

Environment (reuse the isolated setup from §2–§4; extensions to §3):

```sh
cd ~/rems/islaris
eval $(opam env)
export ISLA_REPO="$HOME/rems/isla-islaris"
export ISLA_SNAP_REPO="$HOME/rems/isla-snapshots-islaris"
export PATH="$HOME/.cargo/bin:$PWD/bin:$PATH"   # NB: cargo must be on PATH — the
                                                # frontend's bin/isla-footprint
                                                # shells out to `cargo run`
```

Generate the instruction trace:

```sh
make generate_unaligned_accesses
```

Expect (exit 0):

```
[islaris] examples/unaligned_accesses.dump
(thread 7) [isla-footprint] instructions/instr_str_unaligned.isla   ← Isla processed opcode f9000020
(thread 7) [coq-generation] instructions/instr_str_unaligned.v      ← Islaris generated the Coq trace
```

Artifacts in `~/rems/islaris/instructions/`: `instr_str_unaligned.isla`
(Isla footprint, git-ignored) and `instr_str_unaligned.v` (Coq trace,
byte-identical to the checked-in copy — dune decides rebuilds by content, so a
plain `make` after an identical regeneration is a no-op).

Force a genuine re-check of the proof against the regenerated trace:

```sh
rm -f _build/default/instructions/instr_str_unaligned.{vo,glob} \
      _build/default/examples/unaligned_accesses.{vo,glob}
make
```

Success = these compile with exit 0:

```
coqc instructions/instr_str_unaligned.{glob,vo}
coqc examples/unaligned_accesses.{glob,vo}
```

Checks that were run (all green on 2026-09-20):

- `grep -n Admitted|admit examples/unaligned_accesses.v instructions/instr_str_unaligned.v` → none.
- `Print Assumptions str_unaligned.` → `Closed under the global context` (no axioms).

`Print Assumptions` recipe (one-liner, uses the same Coq 8.19 switch and the
dune install tree):

```sh
eval $(opam env)
echo 'From isla.examples Require Import unaligned_accesses.
Print Assumptions str_unaligned.' > /tmp/pa.v
COQPATH=$PWD/_build/install/default/lib/coq/user-contrib \
  opam exec -- coqc /tmp/pa.v
```

## 8. Running the frontend on YOUR OWN dump (part 3 supplement)

This is the recipe used for `armored/linear_search` in the worklog §12: an
object dump of our own hand-written assembly (rather than a shipped example),
through the same Isla → Islaris → Coq pipeline.

A `.dump` file is just textual objdump output: label lines
(`0000000000000000 <linear_search>:`) and instruction lines
(`   0:\taa1f03e3 \tmov\tx3, xzr`), with optional `//@constraint:` /
`//@spec:` / `//@base_address:` comment annotations attached to the instruction
that follows them. objdump lines of the form `path: file format …` and
`Disassembly of section .text:` must be removed (the parser treats any line
containing a `:` as an instruction line). Do **not** keep stray `//` comment
text on instruction lines in a way that contains `/` literally … the parser
splits instruction text on `/` for its comment field, which objdump's
`// b.hs, b.nlast` style suffixes already use — that is fine, just don't add
more.

Constraints worth knowing:

- The ARM model checks `MemAddr` for every load/store. For a memory
  instruction, add `//@constraint:` asserting the effective address's
  top-byte-ignore bits and `size-1` low alignment bits are zero. Example from
  the register-offset scaled load `ldr x4, [x0, x3, lsl #3]` (address
  `R0 + R3*8`, 8 bytes, alignment mask `0x7`):

  ```
  //@constraint: = (bvand (bvadd R0 (bvmul R3 0x0000000000000008)) 0xfff0000000000007) 0x0000000000000000
  ```

- Register ALU instructions, branches (`b.cs`/`b.hs`, `b.eq`, `b`,
  `cbz`, …) and `ret` need no constraint; Isla footprints them directly
  (`--tree` gives both branch outcomes). `b.hs` assembles to the `b.cs`
  encoding.

Generate traces for your own routine (reuse the §2–§4 environment; run from
`~/rems/islaris`):

```sh
cd ~/rems/islaris
eval $(opam env)
export ISLA_REPO="$HOME/rems/isla-islaris"
export ISLA_SNAP_REPO="$HOME/rems/isla-snapshots-islaris"
export PATH="$HOME/.cargo/bin:$PWD/bin:$PATH"

dune exec -- islaris /path/to/myroutine.dump -j 8 \
  -o instructions/myroutine --coqdir=isla.instructions.myroutine
rm instructions/instrs.v   # the driver list generated at the top level; unused here
```

Compile the generated traces (they live in `instructions/myroutine/` with a
generated `dune` declaring the `isla.instructions.myroutine` theory):

```sh
dune build instructions/myroutine/
```

Independent re-check on the copies kept in a non-dune repo:

```sh
export COQPATH=$PWD/_build/install/default/lib/coq/user-contrib   # from ~/rems/islaris
coqc -R <traces-dir> isla.instructions.myroutine a0.v   # … each trace file, then instrs.v
```

Use `-R` (not `-Q`) for `instrs.v`: it `Require Export`s its sibling trace
modules under the `isla.instructions.myroutine` logical root, and the generated
`dune` maps that same root. Also note that if the current opam switch is not the
islaris one, `eval $(opam env --switch=/home/ubuntu/rems/islaris)` may fail to
put `coqc` on `PATH`; append `--set-switch` (or `export OPAMSWITCH=…`) and call
`coqc` directly rather than through `opam exec`.