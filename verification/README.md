# Verification record

The publication sources were checked on **2026-11-03** with Lean **4.33.1**
and the dependency revisions in [`lake-manifest.json`](../lake-manifest.json).

| Check | Result |
| --- | --- |
| Full default-target `lake --wfail build` | Passed, 5,966 jobs, zero warnings |
| `lake env lean -DwarningAsError=true AuditLeConjectureNative.lean` | Passed, zero warnings |
| Final theorem's transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Minimal usage example in the build guide | Passed |
| Source checksums before and after verification | Matched |
| Aggregate import coverage | All 1,890 module files included |
| Dependency checkouts | All nine clean and at the pinned revisions |

The [verification script](../scripts/verify.sh) completed a full build of the
project's default target and the final-theorem audit with warnings treated as
failures. The check used the publication checkout, clean dependency checkouts,
and existing compiled caches. The source checksums matched before and after
the run. They identify the checked working-tree contents independently of the
checkout revision recorded in `environment.log`.

## Records

| File | Contents |
| --- | --- |
| [`environment.log`](environment.log) | Check time in UTC, Lean version, and Lake configuration hashes |
| [`build.log`](build.log) | Successful default-target build output with zero warnings |
| [`audit.log`](audit.log) | Formal statement, final theorem type, and axiom list |
| [`readme-example.log`](readme-example.log) | Output from checking the build-guide usage example |
| [`sources.sha256`](sources.sha256) | SHA-256 hashes of all project Lean source files, including the audit |
| [`source-sha256.json`](source-sha256.json) | Extended inventory of 1,926 source, configuration, and provenance files |
| [`dependencies.log`](dependencies.log) | Pinned dependency revisions and clean checkout status |
| [`written-notes.md`](written-notes.md) | Separate PDF compilation record for the written notes |

All nine dependency commits matched the manifest, and their checkouts had no
local changes. The build, theorem audit, and usage example produced no warnings.

From the repository root, check the distributed Lean source against the record:

```bash
sha256sum -c verification/sources.sha256
```

To perform a new build and audit, follow the [build guide](../docs/BUILDING.md).
The recorded axiom check establishes the dependencies of the formal theorem.
Interpreting its definitions as the intended mathematical conjecture remains
a separate part of mathematical review.
