/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullReflectedCycles
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.TorusLink.Basic

/-!
# The reflected consecutive torus grid and its corner cycle

The diagram is the explicit row reflection of TauCeti's shifted-diagonal
grid `torusLink n (n+1)`. Its O markings have row `N-1-c`, and its X
markings have row `N-1-((c+n+2) mod N)`, where `N=2n+3`.
The corner state has row `-c mod N`.

These definitions fix the convention needed for the two proposed torus
representatives. Identifying the diagram with the positive geometric torus
knot `T(n+1,n+2)` remains a separate theorem.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- The size of the consecutive shifted-diagonal grid. -/
abbrev consecutiveTorusGridSize (n : ℕ) := n + 1 + (n + 1 + 1)

/-- The explicit reflected grid used for the positive-torus comparison. -/
def reflectedTorusGrid (n : ℕ) : GridDiagram (consecutiveTorusGridSize n) :=
  reflectedDiagram (GridDiagram.torusLink n (n + 1))

/-- Its corner state, obtained by reflecting the original diagonal state. -/
def reflectedTorusAnchor (n : ℕ) : GridState (consecutiveTorusGridSize n) :=
  reflectedState (GridDiagram.torusLink n (n + 1)).O

@[simp] theorem reflectedTorusGrid_O_apply (n : ℕ)
    (c : Fin (consecutiveTorusGridSize n)) : (reflectedTorusGrid n).O c = c.rev := by
  simp only [reflectedTorusGrid, reflectedDiagram_O, GridDiagram.torusLink_O_apply]

@[simp] theorem reflectedTorusGrid_X_apply (n : ℕ)
    (c : Fin (consecutiveTorusGridSize n)) :
    (reflectedTorusGrid n).X c =
      ((finRotate (consecutiveTorusGridSize n) ^ (n + 2)) c).rev := by
  simp only [reflectedTorusGrid, reflectedDiagram_X, GridDiagram.torusLink_X_apply]

@[simp] theorem reflectedTorusAnchor_apply (n : ℕ)
    (c : Fin (consecutiveTorusGridSize n)) :
    reflectedTorusAnchor n c = finRotate (consecutiveTorusGridSize n) c.rev := by
  simp only [reflectedTorusAnchor, reflectedState_apply, GridDiagram.torusLink_O_apply]

/-- The explicit corner vector is a cycle of the full Laurent differential. -/
theorem laurentDifferential_reflectedTorusAnchor (n : ℕ) (R : Type*)
    [CommSemiring R] [CharP R 2] :
    laurentDifferential (reflectedTorusGrid n) R
      (Finsupp.single (reflectedTorusAnchor n) 1) = 0 := by
  apply laurentDifferential_reflected_cyclic_state
    (GridDiagram.torusLink n (n + 1)) R (k := 0)
  simp only [GridDiagram.torusLink_O_toPerm, pow_zero]

end OnLeConjecture.KnotFloer.GridFull
