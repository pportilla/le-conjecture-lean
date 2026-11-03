/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridColourMovesBasic
public import OnLeConjecture.KnotFloer.GridExteriorCommutationColour
public import OnLeConjecture.KnotFloer.GridExteriorSymmetryColour
public import OnLeConjecture.KnotFloer.GridExteriorOTranspose

/-!
# Colour transport along the moves that keep the size

This file gives colour pullbacks (`ColourPullback`, `GridColourMovesBasic`) for the native maps of
the grid moves that do not change the size of a grid diagram, and for the two symmetries used in
the treatment of stabilizations.

The components of a grid are the cycles of `gridComponentPerm`, the permutation sending a column
`c` to the column of the `X` marking in the row of the `O` marking of `c`. Relabelling the rows
does not change it. Relabelling the columns by `κ` conjugates it by `κ`. Transposition sends it
to `G.O * π⁻¹ * G.O⁻¹`, and the half-turn conjugates it by `Fin.revPerm`. In each case the
cycles correspond, which gives a component map (`ComponentMap`).

The following Laurent relabelling equivalences intertwine the derivative maps exactly.

* Cyclic rows: `laurentCyclicRowsEquiv_comp_oDerivative` (`GridExteriorSymmetryColour`).
* Cyclic columns: `laurentCyclicColumnsEquiv_comp_oDerivative` (`GridExteriorSymmetryColour`).
* Transposition: `laurentTransposeEquiv_comp_oDerivative_finset`, from the single-column case
  `laurentTransposeEquiv_comp_oDerivative` (`GridExteriorOTranspose`).
* Half-turn: `laurentHalfTurnEquiv_comp_oDerivative`, proved here from the bijection
  `GridRectangleBetween.halfTurnEquiv` of rectangles, which reverses both coordinates of the
  covered squares.

The pentagon map of a validated column commutation intertwines the derivative maps up to
homotopy by `commutationMap_oDerivative_homotopy` (`GridExteriorCommutationColour`), and a row
commutation is a column commutation conjugated by transposition. The results are collected in
`colourPullback_of_commutationMovesTo`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex Finsupp GridRectangleBetween

variable {n : ℕ}

/-! ### The component permutation under relabellings -/

/-- Relabelling the rows does not change the component permutation. -/
theorem gridComponentPerm_relabelRows (G : GridDiagram n) (ρ : Equiv.Perm (Fin n)) :
    gridComponentPerm (G.relabelRows ρ) = gridComponentPerm G := by
  ext c
  simp [gridComponentPerm, GridState.relabelRows]

/-- Relabelling the columns by `κ` conjugates the component permutation by `κ`. -/
theorem gridComponentPerm_relabelColumns (G : GridDiagram n) (κ : Equiv.Perm (Fin n)) :
    gridComponentPerm (G.relabelColumns κ) = κ * gridComponentPerm G * κ⁻¹ := by
  ext c
  simp [gridComponentPerm, GridState.relabelColumns, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]

/-- Transposition sends the component permutation `π` to `G.O * π⁻¹ * G.O⁻¹`. -/
theorem gridComponentPerm_transpose (G : GridDiagram n) :
    gridComponentPerm G.transpose =
      G.O.toPerm * (gridComponentPerm G)⁻¹ * G.O.toPerm⁻¹ := by
  ext c
  simp [gridComponentPerm, GridState.transpose, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]

/-- The half-turn conjugates the component permutation by the reversal of the columns. -/
theorem gridComponentPerm_rotate (G : GridDiagram n) :
    gridComponentPerm G.rotate = Fin.revPerm * gridComponentPerm G * Fin.revPerm⁻¹ := by
  ext c
  simp [gridComponentPerm, GridDiagram.rotate, GridState.relabelRows, GridState.relabelColumns,
    Equiv.Perm.mul_apply, Equiv.Perm.inv_def]

/-! ### Transposition and half-turn of the derivative maps -/

/-- Transposition intertwines the derivative map of every set of columns, moving the column `h`
to the column `G.O h`. -/
theorem laurentTransposeEquiv_comp_oDerivative_finset (R : Type*) [CommRing R] (G : GridDiagram n)
    (P : Finset (Fin n)) :
    (laurentTransposeEquiv R).toLinearMap ∘ₗ oDerivative R G P =
      oDerivative R G.transpose (P.map G.O.toPerm.toEmbedding) ∘ₗ
        (laurentTransposeEquiv R).toLinearMap := by
  rw [oDerivative_eq_sum, oDerivative_eq_sum, Finset.sum_map]
  simp only [← Module.End.mul_eq_comp, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Module.End.mul_eq_comp, Equiv.toEmbedding_apply]
  exact laurentTransposeEquiv_comp_oDerivative R G h

/-- The half-turn intertwines the single-column derivative maps, moving the column `h` to the
column `h.rev`. -/
theorem laurentHalfTurnEquiv_comp_oDerivative_singleton (R : Type*) [CommRing R]
    (G : GridDiagram n) (h : Fin n) :
    (laurentHalfTurnEquiv R).toLinearMap ∘ₗ oDerivative R G {h} =
      oDerivative R G.rotate {h.rev} ∘ₗ (laurentHalfTurnEquiv R).toLinearMap := by
  apply gridLinearMap_ext
  intro x y
  obtain ⟨z, rfl⟩ : ∃ z : GridState n, z.halfTurn = y := ⟨y.halfTurn, by simp⟩
  change laurentHalfTurnEquiv R (oDerivative R G {h} (single x 1)) z.halfTurn =
    oDerivative R G.rotate {h.rev} (laurentHalfTurnEquiv R (single x 1)) z.halfTurn
  rw [laurentHalfTurnEquiv_apply, GridState.halfTurn_halfTurn, laurentHalfTurnEquiv_single,
    oDerivative_singleton_single_apply, oDerivative_singleton_single_apply]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_equiv (halfTurnEquiv x z) (fun r => ?_) (fun r _ => ?_)
  · simp only [mem_emptyRectangles, isEmpty_halfTurnEquiv]
  · rw [card_OColumns_halfTurn]
    simp only [mem_coveredSquares_halfTurnEquiv, GridDiagram.rotate_O, GridState.rotate_apply,
      Fin.rev_rev]

/-- The half-turn intertwines the derivative map of every set of columns, moving the column `h`
to the column `h.rev`. -/
theorem laurentHalfTurnEquiv_comp_oDerivative (R : Type*) [CommRing R] (G : GridDiagram n)
    (P : Finset (Fin n)) :
    (laurentHalfTurnEquiv R).toLinearMap ∘ₗ oDerivative R G P =
      oDerivative R G.rotate (P.map Fin.revPerm.toEmbedding) ∘ₗ
        (laurentHalfTurnEquiv R).toLinearMap := by
  rw [oDerivative_eq_sum, oDerivative_eq_sum, Finset.sum_map]
  simp only [← Module.End.mul_eq_comp, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Module.End.mul_eq_comp, Equiv.toEmbedding_apply, Fin.revPerm_apply]
  exact laurentHalfTurnEquiv_comp_oDerivative_singleton R G h

/-! ### Colour pullbacks for the symmetries -/

/-- The cyclic row isomorphism and its inverse give colour pullbacks in both directions. -/
theorem colourPullback_cyclicRows (G : GridDiagram n) :
    ColourPullback G (G.relabelRows (finRotate n)) ∧
      ColourPullback (G.relabelRows (finRotate n)) G := by
  refine colourPullback_of_iso (laurentMaslovCyclicRowsIso G (ZMod 2))
    (laurentCyclicRowsEquiv (ZMod 2)) (Equiv.refl (Fin n))
    (laurentMaslovChainEquiv_cyclicRows G (ZMod 2))
    (laurentDifferential_relabelRows_finRotate G (ZMod 2))
    (laurentMaslovCyclicRows_preserves G (ZMod 2))
    (laurentMaslovCyclicRows_inv_preserves G (ZMod 2)) (fun P => ?_)
    (ComponentMap.of_conj (Equiv.refl (Fin n)) ?_)
  · have hP : P.map (Equiv.refl (Fin n)).toEmbedding = P := by
      ext x
      simp
    rw [hP]
    exact laurentCyclicRowsEquiv_comp_oDerivative (ZMod 2) G P
  · rw [gridComponentPerm_relabelRows]
    ext c
    rfl

/-- The cyclic column isomorphism and its inverse give colour pullbacks in both directions. -/
theorem colourPullback_cyclicColumns (G : GridDiagram n) :
    ColourPullback G (G.relabelColumns (finRotate n)) ∧
      ColourPullback (G.relabelColumns (finRotate n)) G :=
  colourPullback_of_iso (laurentMaslovCyclicColumnsIso G (ZMod 2))
    (laurentCyclicColumnsEquiv (ZMod 2)) (finRotate n)
    (laurentMaslovChainEquiv_cyclicColumns G (ZMod 2))
    (laurentDifferential_relabelColumns_finRotate G (ZMod 2))
    (laurentMaslovCyclicColumns_preserves G (ZMod 2))
    (laurentMaslovCyclicColumns_inv_preserves G (ZMod 2))
    (laurentCyclicColumnsEquiv_comp_oDerivative (ZMod 2) G)
    (ComponentMap.of_conj (finRotate n) (gridComponentPerm_relabelColumns G _))

/-- The transposition isomorphism and its inverse give colour pullbacks in both directions. -/
theorem colourPullback_transpose (G : GridDiagram n) :
    ColourPullback G G.transpose ∧ ColourPullback G.transpose G :=
  colourPullback_of_iso (laurentMaslovTransposeIso G (ZMod 2))
    (laurentTransposeEquiv (ZMod 2)) G.O.toPerm (fun _ _ => rfl)
    (laurentDifferential_transpose G (ZMod 2))
    (laurentMaslovTranspose_preserves G (ZMod 2))
    (laurentMaslovTranspose_inv_preserves G (ZMod 2))
    (laurentTransposeEquiv_comp_oDerivative_finset (ZMod 2) G)
    (ComponentMap.of_conj_inv G.O.toPerm (gridComponentPerm_transpose G))

/-- The half-turn isomorphism and its inverse give colour pullbacks in both directions. -/
theorem colourPullback_halfTurn (G : GridDiagram n) :
    ColourPullback G G.rotate ∧ ColourPullback G.rotate G :=
  colourPullback_of_iso (laurentMaslovHalfTurnIso G (ZMod 2))
    (laurentHalfTurnEquiv (ZMod 2)) Fin.revPerm (fun _ _ => rfl)
    (laurentDifferential_halfTurn G (ZMod 2))
    (laurentMaslovHalfTurn_preserves G (ZMod 2))
    (laurentMaslovHalfTurn_inv_preserves G (ZMod 2))
    (laurentHalfTurnEquiv_comp_oDerivative (ZMod 2) G)
    (ComponentMap.of_conj Fin.revPerm (gridComponentPerm_rotate G))

/-! ### Commutations -/

/-- The pentagon map of a validated column commutation gives colour transport data from `χ` to
`χ` composed with the exchange of the two columns. -/
theorem colourTransportData_columnCommutation (G : GridDiagram n)
    (C : GridDiagram.ColumnCommutationData G) (χ : Fin n → ℕ) :
    ColourTransportData G χ (G.swapColumns C.column (finRotate n C.column))
      (χ ∘ (Equiv.swap C.column (finRotate n C.column)).symm) := by
  intro hn _
  refine ⟨laurentMaslovCommutationHom G (ZMod 2) C, laurentCommutationMap G (ZMod 2) C,
    laurentMaslovChainEquiv_commutation G (ZMod 2) C, ?_,
    Bifiltration.shifts_zero_zero_iff.mpr (laurentMaslovCommutationHom_preserves G (ZMod 2) C),
    gridCanonicalClass_commutation G hn C, fun v => ?_⟩
  · apply LinearMap.ext
    intro z
    exact laurentDifferential_commutationMap G (ZMod 2) C z
  · obtain ⟨L, hL⟩ := commutationMap_oDerivative_homotopy (R := ZMod 2) G C (colourClass χ v)
    refine ⟨L, ?_⟩
    rw [colourClass_comp_symm, laurentModule_sub_eq_add (R := ZMod 2), hL]

/-- An elementary column commutation from `G` to `H` gives a colour pullback from `G` to `H`. -/
theorem colourPullback_of_isColumnCommutation {G H : GridDiagram n}
    (h : GridDiagram.IsColumnCommutation G H) : ColourPullback G H := by
  obtain ⟨C, rfl⟩ := GridDiagram.isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact .of_componentMap
    (ComponentMap.of_conj (Equiv.swap C.column (finRotate n C.column))
      (gridComponentPerm_relabelColumns G _))
    fun χ _ => colourTransportData_columnCommutation G C χ

/-- An elementary row commutation from `G` to `H` gives a colour pullback from `G` to `H`,
through transposition. -/
theorem colourPullback_of_isRowCommutation {G H : GridDiagram n}
    (h : GridDiagram.IsRowCommutation G H) : ColourPullback G H :=
  ((colourPullback_transpose G).1.trans_of_size_eq
    (colourPullback_of_isColumnCommutation
      ((GridDiagram.isColumnCommutation_transpose G H).mpr h))).trans_of_size_eq
    (colourPullback_transpose H).2

/-- An elementary commutation from `G` to `H` gives a colour pullback from `G` to `H`. -/
theorem colourPullback_of_isCommutation {G H : GridDiagram n}
    (h : GridDiagram.IsCommutation G H) : ColourPullback G H :=
  ((GridDiagram.isCommutation_iff G H).mp h).elim colourPullback_of_isRowCommutation
    colourPullback_of_isColumnCommutation

/-- If cyclic permutations and commutations connect `G` to `H`, then there are colour pullbacks
from `G` to `H` and from `H` to `G`. -/
theorem colourPullback_of_commutationMovesTo {G H : GridDiagram n}
    (h : GridDiagram.CommutationMovesTo G H) : ColourPullback G H ∧ ColourPullback H G :=
  h.induction_on (motive := fun G H => ColourPullback G H ∧ ColourPullback H G)
    colourPullback_cyclicRows colourPullback_cyclicColumns
    (fun h => ⟨colourPullback_of_isCommutation h,
      colourPullback_of_isCommutation (GridDiagram.isCommutation_comm.mp h)⟩)
    (fun G => ⟨.refl G, .refl G⟩)
    (fun _ ih => ⟨ih.2, ih.1⟩)
    (fun _ _ ih ih' => ⟨ih.1.trans_of_size_eq ih'.1, ih'.2.trans_of_size_eq ih.2⟩)

end OnLeConjecture.KnotFloer.GridFull
