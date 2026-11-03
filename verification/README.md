# Verification record

The publication sources were checked on **2026-11-03** with Lean **4.33.1**
and the dependency revisions in [`lake-manifest.json`](../lake-manifest.json).

| Check | Result |
| --- | --- |
| Full default-target `lake build` | Passed, 5,966 jobs |
| `lake env lean AuditLeConjectureNative.lean` | Passed |
| Final theorem's transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Minimal usage example in the build guide | Passed |
| Source checksums before and after verification | Matched |
| Aggregate import coverage | All 1,890 module files included |

The [verification script](../scripts/verify.sh) exited successfully. The check
used an isolated source copy to avoid concurrent changes from a directory
synchronization service. It used existing dependency and build caches. It was
a full build of the project's default target, not a rebuild of Mathlib from
source.

## Records

| File | Contents |
| --- | --- |
| [`environment.log`](environment.log) | Check time in UTC, Lean version, and Lake configuration hashes |
| [`build.log`](build.log) | Full build output, including remaining linter warnings |
| [`audit.log`](audit.log) | Formal statement, final theorem type, and axiom list |
| [`readme-example.log`](readme-example.log) | Output from checking the README usage example |
| [`sources.sha256`](sources.sha256) | SHA-256 hashes of all project Lean source files, including the audit |
| [`source-sha256.json`](source-sha256.json) | Extended inventory of 1,926 source, configuration, and provenance files |
| [`dependencies.log`](dependencies.log) | Dependency revisions and inspection of local checkout warnings |
| [`written-notes.md`](written-notes.md) | Separate PDF compilation record for the written notes |

Lake reported local changes in the Mathlib and Batteries checkouts. Inspection
found script permission changes and missing documentation or benchmark
symlinks. All nine dependency commits matched the manifest, and there were no
changes to their Lean source or package configuration files. The warnings are
preserved in the logs rather than removed from the recorded output.

From the repository root, check the distributed Lean source against the record:

```bash
sha256sum -c verification/sources.sha256
```

To perform a new build and audit, follow the [build guide](../docs/BUILDING.md).
The recorded axiom check establishes the dependencies of the formal theorem.
Interpreting its definitions as the intended mathematical conjecture remains
a separate part of mathematical review.
