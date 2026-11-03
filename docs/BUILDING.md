# Building, checking, and using the formalization

## Reproduce a check

Run the commands from the repository root. Git and the [elan toolchain manager](https://github.com/leanprover/elan) must be installed, with `lake` available on your `PATH`.

```bash
git clone https://github.com/pportilla/le-conjecture-lean.git
cd le-conjecture-lean
lake exe cache get
lake --wfail build
lake env lean -DwarningAsError=true AuditLeConjectureNative.lean
```

`lake exe cache get` retrieves compiled Mathlib dependencies. `lake --wfail build` builds the aggregate `OnLeConjecture` library and fails on warnings. The last command checks the final theorem’s axiom dependencies and rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`.

Alternatively, after obtaining the Mathlib cache, run the [verification script](../scripts/verify.sh):

```bash
bash scripts/verify.sh
```

It writes `environment.log`, `sources.sha256`, `build.log`, and `audit.log` under `.lake/verification`. To select a different output directory, pass it as the first argument, for example `bash scripts/verify.sh verification/local-check`. The build runs with `lake --wfail build`, so any build warning makes verification fail. The standalone theorem audit also treats Lean warnings as errors. The script records source checksums before the build and checks them afterward, so a concurrent change to an existing source file causes failure. It requires Bash and the standard GNU checksum utilities used in the script.

A successful `lake build` and a successful audit are separate checks. An audit run against existing compiled files does not establish that every source file has just been rebuilt. Run the build first when checking a changed checkout.

## Versions and reproducibility

| File | Role |
| --- | --- |
| [`lean-toolchain`](../lean-toolchain) | Selects `leanprover/lean4:v4.33.1` |
| [`lakefile.toml`](../lakefile.toml) | Defines the library, Lean options, and the Mathlib `v4.33.1` requirement |
| [`lake-manifest.json`](../lake-manifest.json) | Pins Mathlib and its transitive Lake dependencies to Git revisions |

The pinned Mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`. Keep the manifest when reproducing a recorded check. Running `lake update` changes dependency resolution and is unnecessary for ordinary verification.

The working directory `.lake` contains downloaded dependencies and generated build artifacts. It is excluded from version control. Keep substantial free disk space for it: the development includes a large source library as well as Mathlib. A clean build can take significantly longer than a build with existing artifacts. Place the checkout outside cloud-synchronized directories to avoid synchronizing generated files.

For a source rebuild of this project while retaining downloaded dependencies, remove only the project’s generated artifacts and then rerun the build and audit:

```bash
rm -rf .lake/build
lake --wfail build
lake env lean -DwarningAsError=true AuditLeConjectureNative.lean
```

The cache command uses upstream compiled dependencies. Rebuilding all dependencies from source is a separate, more expensive operation and is not what that command does.

## Read the audit

The audit file imports the final theorem, displays its statement and type, and calls `Lean.collectAxioms` on the final declaration. The recorded result is:

```text
OnLeConjecture.Analytic.LeConjecture : Prop
def OnLeConjecture.Analytic.LeConjecture : Prop :=
∀ (g : OnLeConjecture.Analytic.PointedMapGerm 2 3), g.HasInjectiveRepresentative → g.differential ≠ 0
OnLeConjecture.Analytic.leConjecture_native : OnLeConjecture.Analytic.LeConjecture
'OnLeConjecture.Analytic.leConjecture_native' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A forbidden axiom makes the command fail. This includes `sorryAx`, used for unproved placeholders. The check follows dependencies of the final theorem. It is more informative for that theorem than a text search, which can match comments or miss indirect dependencies.

Recorded output is available in [`verification/build.log`](../verification/build.log) and [`verification/audit.log`](../verification/audit.log). The verification script requires a warning-free build and an audit using only the permitted axioms. Run it on the commit you intend to use.

## Use the theorem

Within the project, the following example uses only the final theorem’s import:

```lean
import OnLeConjecture.Analytic.LeConjectureNative

open OnLeConjecture.Analytic

example (g : PointedMapGerm 2 3)
    (hg : g.HasInjectiveRepresentative) : g.differential ≠ 0 :=
  leConjecture_native g hg
```

Save it as `Example.lean` in the repository root and check it after building:

```bash
lake env lean Example.lean
```

The broader `import OnLeConjecture` loads the aggregate development. For navigation in an editor, open the repository root with Lean support enabled and use “go to definition” on the declarations listed in the [proof guide](PROOF_GUIDE.md).

## Compile the written notes

The files under [`written-proofs`](written-proofs) are standalone LaTeX documents. A TeX installation with the packages requested in each preamble and `latexmk` is sufficient to attempt their compilation. For example:

```bash
cd docs/written-proofs
latexmk -pdf -interaction=nonstopmode -halt-on-error J03-J04-finite-tensor-iterated-seam.tex
```

Compiling a note does not verify its mathematical assertions. These notes preserve stages of the development, including statements of then-unresolved issues. See the [note-status discussion](PROOF_GUIDE.md#written-notes-and-the-final-source).

## Troubleshooting

| Symptom | Check |
| --- | --- |
| `lake` is not found | Verify the elan installation and its addition to `PATH`, then open a new terminal. |
| Lean reports an incompatible object-file version | Run from the repository root and check `lake env lean --version` against `lean-toolchain`. Restore the pinned files if they were changed. |
| A dependency cannot be fetched | Check network access to the dependency URL recorded in `lake-manifest.json`. |
| A build stops because the disk is full or a process is killed | Check available disk and memory. Include the last build output when reporting the failure. |
| The audit reports a forbidden axiom | Preserve the exact output and commit identifier and report it as a verification failure. |
| A written note references an unfamiliar `J` or `M` identifier | These are development identifiers. Use the [proof guide](PROOF_GUIDE.md) to locate the current declarations. |
