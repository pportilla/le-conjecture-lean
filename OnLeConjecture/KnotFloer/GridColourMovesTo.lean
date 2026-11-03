/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridColourMovesStabilization

/-!
# Colour-natural canonical maps along grid moves

This file proves `ColourMovesToStatement` (`GridExteriorColourTransport`): if `G` is related to
`H` by grid moves, then every component colouring `χ'` of `H` comes from a component colouring
`χ` of `G` with the same colour values, exact exactly when `χ'` is exact, and a native canonical
map from `G` to `H` intertwines the colour derivatives of `χ` and `χ'` up to chain homotopy
(`colourMovesToStatement`).

Every elementary grid move gives colour pullbacks (`ColourPullback`, `GridColourMovesBasic`) in
its own direction (`colourPullback_of_isMove`): cyclic permutations and commutations by
`GridColourMovesSymmetry`, stabilizations and destabilizations by `GridColourMovesStabilization`.
Since an elementary move can be reversed, induction over `GridDiagram.MovesTo` gives colour
pullbacks in both directions (`colourPullback_of_movesTo`). The intermediate grids of a sequence
of moves carry no size hypothesis. The composition step uses that grid moves relate a grid of size
at least two only to grids of size at least two (`grid_size_two_le_iff_of_movesTo`).
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

variable {n k : ℕ}

/-- If an elementary grid move relates `A` to `B`, then there is a colour pullback from `A` to
`B`. -/
theorem colourPullback_of_isMove {A B : Σ n, GridDiagram n} (h : GridDiagram.IsMove A B) :
    ColourPullback A.2 B.2 := by
  cases h with
  | cyclicRows h =>
      rcases h with rfl | rfl
      · exact (colourPullback_cyclicRows _).1
      · exact (colourPullback_cyclicRows _).2
  | cyclicColumns h =>
      rcases h with rfl | rfl
      · exact (colourPullback_cyclicColumns _).1
      · exact (colourPullback_cyclicColumns _).2
  | commutation h => exact colourPullback_of_isCommutation h
  | stabilization h => exact (colourPullback_of_isStabilization h).1
  | destabilization h =>
      exact (colourPullback_of_isStabilization
        ((GridDiagram.isDestabilization_iff_isStabilization _ _).mp h)).2

/-- If grid moves relate `G` to `H`, then there are colour pullbacks from `G` to `H` and from `H`
to `G`. -/
theorem colourPullback_of_movesTo {G : GridDiagram n} {H : GridDiagram k}
    (h : GridDiagram.MovesTo G H) : ColourPullback G H ∧ ColourPullback H G :=
  h.induction_on (motive := fun A B => ColourPullback A.2 B.2 ∧ ColourPullback B.2 A.2)
    (fun h => ⟨colourPullback_of_isMove h, colourPullback_of_isMove h.symm⟩)
    (fun A => ⟨.refl A.2, .refl A.2⟩)
    (fun _ ih => ⟨ih.2, ih.1⟩)
    (fun hAB hBC ih ih' =>
      ⟨ih.1.trans ih'.1 (grid_size_two_le_iff_of_movesTo hAB).mp,
        ih'.2.trans ih.2 (grid_size_two_le_iff_of_movesTo hBC).mpr⟩)

/-- **Colour-natural canonical maps along grid moves.** If `G` is related to `H` by grid moves,
then every component colouring of `H` comes from a component colouring of `G` with the same
colours, exact exactly when it is exact, and a colour-natural native canonical map from `G` to
`H`. -/
theorem colourMovesToStatement : ColourMovesToStatement := by
  intro n k G H h χ' hχ'
  exact (colourPullback_of_movesTo h).1.colourCanonicalTransport χ' hχ'

/-- The form of `colourMovesToStatement` with the additional conclusion that the underlying
Laurent map commutes with the full Laurent differentials (`ColourTransportData`). -/
theorem exists_colourTransportData_of_movesTo {G : GridDiagram n} {H : GridDiagram k}
    (h : G.MovesTo H) (χ' : Fin k → ℕ) (hχ' : ComponentColouring H χ') :
    ∃ χ : Fin n → ℕ, ComponentColouring G χ ∧ (ExactColouring G χ ↔ ExactColouring H χ') ∧
      (∀ v, (∃ c, χ c = v) ↔ ∃ c, χ' c = v) ∧ ColourTransportData G χ H χ' :=
  (colourPullback_of_movesTo h).1 χ' hχ'

end OnLeConjecture.KnotFloer.GridFull
