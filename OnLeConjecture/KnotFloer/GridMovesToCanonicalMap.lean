/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationCornerMaps

/-!
# Native maps along sequences of grid moves

Let `G` and `H` be grid diagrams of sizes `n` and `k` with `2 ≤ n` and `2 ≤ k`. If `G` and `H`
are related by `GridDiagram.MovesTo`, then some chain map
`laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2)` preserves both filtrations and
sends `gridCanonicalClass G` to `gridCanonicalClass H` (`exists_movesTo_canonical_map`).

The map is a composite of the maps of `GridStabilizationCornerMaps` along a sequence of
elementary moves. The intermediate grids of such a sequence carry no size hypothesis, so the
proof uses the following exceptional-case lemma. A grid diagram of size one does not exist,
since its unique `O`-marking and `X`-marking would occupy the same square. An elementary
stabilization of a grid of size `n` splits a marking in some column of that grid, so `n` is
positive and hence at least two. Consequently every grid connected by grid moves to a grid of
size at least two has size at least two (`grid_size_two_le_iff_of_movesTo`).

These statements concern native grid complexes over `ZMod 2` and their normalized classes. They
do not identify grid diagrams with geometric links.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n k : ℕ}

/-! ### Sizes along grid moves -/

/-- A grid diagram of positive size has size at least two. -/
theorem grid_size_two_le_of_ne_zero (G : GridDiagram n) (hn : n ≠ 0) : 2 ≤ n :=
  grid_size_two_le_of_column G ⟨0, Nat.pos_of_ne_zero hn⟩

/-- A grid diagram that admits an elementary stabilization has size at least two. -/
theorem grid_size_two_le_of_isStabilization {G : GridDiagram n} {H : GridDiagram (n + 1)}
    (h : GridDiagram.IsStabilization G H) : 2 ≤ n := by
  obtain ⟨s, -⟩ := h.exists_commutationMovesTo
  exact grid_size_two_le_of_column G s

/-- If an elementary grid move relates `A` to `B`, then `A` has size at least two exactly when `B`
has size at least two. -/
theorem grid_size_two_le_iff_of_isMove {A B : Σ n, GridDiagram n}
    (h : GridDiagram.IsMove A B) : 2 ≤ A.1 ↔ 2 ≤ B.1 := by
  cases h with
  | cyclicRows => exact Iff.rfl
  | cyclicColumns => exact Iff.rfl
  | commutation => exact Iff.rfl
  | stabilization h =>
      have := grid_size_two_le_of_isStabilization h
      dsimp only
      constructor <;> intro <;> omega
  | destabilization h =>
      have := grid_size_two_le_of_isStabilization
        ((GridDiagram.isDestabilization_iff_isStabilization _ _).mp h)
      dsimp only
      constructor <;> intro <;> omega

/-- If grid moves relate `G` to `H`, then `G` has size at least two exactly when `H` has size at
least two. -/
theorem grid_size_two_le_iff_of_movesTo {G : GridDiagram n} {H : GridDiagram k}
    (h : GridDiagram.MovesTo G H) : 2 ≤ n ↔ 2 ≤ k :=
  h.induction_on (motive := fun A B => 2 ≤ A.1 ↔ 2 ≤ B.1)
    grid_size_two_le_iff_of_isMove (fun _ => Iff.rfl) (fun _ ih => ih.symm)
    (fun _ _ ih ih' => ih.trans ih')

/-- Every grid connected by grid moves to a grid of size at least two has size at least two. -/
theorem grid_size_two_le_of_movesTo {G : GridDiagram n} {H : GridDiagram k}
    (h : GridDiagram.MovesTo G H) (hn : 2 ≤ n) : 2 ≤ k :=
  (grid_size_two_le_iff_of_movesTo h).mp hn

/-! ### Maps along grid moves -/

/-- If an elementary grid move relates `A` to `B`, then `GridCanonicalTransport A.2 B.2 0` holds. -/
theorem gridCanonicalTransport_of_isMove {A B : Σ n, GridDiagram n}
    (h : GridDiagram.IsMove A B) : GridCanonicalTransport A.2 B.2 0 := by
  cases h with
  | cyclicRows h =>
      rcases h with rfl | rfl
      · exact gridCanonicalTransport_cyclicRows _
      · exact gridCanonicalTransport_cyclicRows_symm _
  | cyclicColumns h =>
      rcases h with rfl | rfl
      · exact gridCanonicalTransport_cyclicColumns _
      · exact gridCanonicalTransport_cyclicColumns_symm _
  | commutation h => exact gridCanonicalTransport_of_isCommutation h
  | stabilization h => exact (gridCanonicalTransport_of_isStabilization h).1
  | destabilization h =>
      exact (gridCanonicalTransport_of_isStabilization
        ((GridDiagram.isDestabilization_iff_isStabilization _ _).mp h)).2

/-- If grid moves relate `G` to `H`, then `GridCanonicalTransport G H 0` and
`GridCanonicalTransport H G 0` hold. -/
theorem gridCanonicalTransport_of_movesTo {G : GridDiagram n} {H : GridDiagram k}
    (h : GridDiagram.MovesTo G H) :
    GridCanonicalTransport G H 0 ∧ GridCanonicalTransport H G 0 :=
  h.induction_on
    (motive := fun A B => GridCanonicalTransport A.2 B.2 0 ∧ GridCanonicalTransport B.2 A.2 0)
    (fun h => ⟨gridCanonicalTransport_of_isMove h, gridCanonicalTransport_of_isMove h.symm⟩)
    (fun A => ⟨.refl A.2, .refl A.2⟩)
    (fun _ ih => ⟨ih.2, ih.1⟩)
    (fun hAB hBC ih ih' =>
      ⟨(ih.1.trans ih'.1 (grid_size_two_le_iff_of_movesTo hAB).mp).of_eq_shift
          (add_zero 0),
        (ih'.2.trans ih.2 (grid_size_two_le_iff_of_movesTo hBC).mpr).of_eq_shift
          (add_zero 0)⟩)

/-- **Native maps along grid moves.** If two grid diagrams of size at least two are related by
grid moves, then some chain map between their native `ZMod 2` complexes has filtration shifts
`(0, 0)` and sends the normalized class of the first grid to the normalized class of the
second. -/
theorem exists_movesTo_canonical_map (G : GridDiagram n) (H : GridDiagram k)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (h : G.MovesTo H) :
    ∃ φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2),
      (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2)) φ 0 0 ∧
      homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk :=
  (gridCanonicalTransport_of_movesTo h).1 hn hk

/-- If two grid diagrams related by grid moves have sizes `n` and `k` with `2 ≤ n`, then
`2 ≤ k`, and some chain map between their native `ZMod 2` complexes has filtration shifts
`(0, 0)` and sends the normalized class of the first grid to the normalized class of the
second. -/
theorem exists_movesTo_canonical_map_of_two_le (G : GridDiagram n) (H : GridDiagram k)
    (hn : 2 ≤ n) (h : G.MovesTo H) :
    ∃ hk : 2 ≤ k, ∃ φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2),
      (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2)) φ 0 0 ∧
      homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk :=
  ⟨grid_size_two_le_of_movesTo h hn,
    exists_movesTo_canonical_map G H hn (grid_size_two_le_of_movesTo h hn) h⟩

end OnLeConjecture.KnotFloer.GridFull
