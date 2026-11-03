/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridDomainBasic
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnweightedPaths
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamMatchingWeights

/-!
# The signed domain of a seam correction path and its factor projections

A correction path from `seamState p.1 p.2` to `seamState q.1 q.2` consists of an entry
rectangle, internal rectangles, and an exit rectangle, together with the selected matching
rectangle `seamComplementRectangle` at each visited matching source. Its signed domain is the
sum of the domains of the actual rectangles minus the domains of the matching rectangles.

On the seam grid of size `N = n + m + 1`, the first projection restricts a domain to the cell
columns `0, …, n - 1, N - 1` and the cell rows `0, …, n`. The second projection restricts it
to the cell columns and cell rows `n, …, N - 1`. The cell `(N - 1, n)` is shared by both
projections. This file contains definitions only.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n m : ℕ}

/-- The sum of the domains of the internal rectangles of an internal path. -/
def SeamInternalPath.rectDomain : {k : ℕ} → {x y : SeamMatchingSource n m} →
    SeamInternalPath k x y → GridDomain (n + m + 1)
  | 0, _, _, _ => 0
  | _ + 1, _, _, π => π.2.1.val.domain + SeamInternalPath.rectDomain π.2.2

/-- The sum of the domains of the matching rectangles at all visited matching sources. -/
def SeamInternalPath.matchingDomain : {k : ℕ} → {x y : SeamMatchingSource n m} →
    SeamInternalPath k x y → GridDomain (n + m + 1)
  | 0, x, _, _ => (seamComplementRectangle x.val).domain
  | _ + 1, x, _, π => (seamComplementRectangle x.val).domain + SeamInternalPath.matchingDomain π.2.2

variable {k : ℕ} {p q : SeamRetainedIndex n m}

/-- The sum of the domains of the entry, internal, and exit rectangles of a correction path. -/
def SeamCorrectionPath.positiveDomain (π : SeamCorrectionPath k p q) : GridDomain (n + m + 1) :=
  π.2.2.1.val.domain + π.2.2.2.1.rectDomain + π.2.2.2.2.val.domain

/-- The sum of the matching rectangle domains of a correction path. -/
def SeamCorrectionPath.matchingDomain (π : SeamCorrectionPath k p q) : GridDomain (n + m + 1) :=
  π.2.2.2.1.matchingDomain

/-- The signed domain of a correction path. -/
def SeamCorrectionPath.signedDomain (π : SeamCorrectionPath k p q) : GridDomain (n + m + 1) :=
  π.positiveDomain - π.matchingDomain

/-- The cell column of the seam grid used by the first projection at factor column `i`:
`i` itself for `i < n`, and the last column `N - 1` for `i = n`. -/
def seamFirstColumn (i : Fin (n + 1)) : Fin (n + m + 1) :=
  if h : i.val < n then ⟨i.val, by omega⟩ else Fin.last (n + m)

/-- The first factor projection `D₁(i, j) = D(seamFirstColumn i, j)`. -/
def seamFirstProjection (D : GridDomain (n + m + 1)) : GridDomain (n + 1) :=
  fun i j => D (seamFirstColumn (m := m) i) (seamLeft n m j)

/-- The second factor projection `D₂(i, j) = D(n + i, n + j)`. -/
def seamSecondProjection (D : GridDomain (n + m + 1)) : GridDomain (m + 1) :=
  fun i j => D (seamRight n m i) (seamRight n m j)

/-- The multiplicity `d = D(N - 1, n)` of the cell shared by the two projections. -/
def seamSharedCell (D : GridDomain (n + m + 1)) : ℤ :=
  D (Fin.last (n + m)) (seamLeft n m (Fin.last n))

end OnLeConjecture.KnotFloer.GridFull
