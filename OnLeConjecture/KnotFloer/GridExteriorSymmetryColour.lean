/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorODerivative
public import OnLeConjecture.KnotFloer.GridExteriorOColour
public import OnLeConjecture.KnotFloer.GridFullCommutationCyclic

/-!
# Colour naturality of the cyclic permutations

Lemma `movesToNativeMap` of the written proof of Statement E (`statement_E_complete_proof.tex`)
asserts that the native maps of ordinary moves intertwine the derivative maps of the O markings.
For the cyclic permutations of rows and columns the native maps are the Laurent relabelings
`laurentCyclicRowsEquiv` and `laurentCyclicColumnsEquiv`, and the intertwining is exact:

* `laurentCyclicRowsEquiv_comp_oDerivative`: `ρ ∘ Φ^G_P = Φ^{G'}_P ∘ ρ` for the cyclic row
  translation `G' = G.relabelRows (finRotate n)`, which keeps every O marking in its column;
* `laurentCyclicColumnsEquiv_comp_oDerivative`: `κ ∘ Φ^G_P = Φ^{G'}_{κ P} ∘ κ` for the cyclic
  column translation `G' = G.relabelColumns (finRotate n)`, which moves the O marking of
  column `h` to column `h + 1`.

Rectangles correspond under the relabelings, with the same O counts and the relabeled covered
squares.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp GridRectangleBetween

variable {n : ℕ} (R : Type*) [CommRing R]

/-- Cyclic row translation intertwines the single-column derivative maps. -/
theorem laurentCyclicRowsEquiv_comp_oDerivative_singleton (G : GridDiagram n) (h : Fin n) :
    (laurentCyclicRowsEquiv R).toLinearMap ∘ₗ oDerivative R G {h} =
      oDerivative R (G.relabelRows (finRotate n)) {h} ∘ₗ
        (laurentCyclicRowsEquiv R).toLinearMap := by
  apply gridLinearMap_ext
  intro x y
  obtain ⟨z, rfl⟩ : ∃ z : GridState n, z.relabelRows (finRotate n) = y :=
    ⟨y.relabelRows (finRotate n).symm, by simp⟩
  change laurentCyclicRowsEquiv R (oDerivative R G {h} (single x 1)) (z.relabelRows _) =
    oDerivative R (G.relabelRows (finRotate n)) {h} (laurentCyclicRowsEquiv R (single x 1))
      (z.relabelRows _)
  rw [laurentCyclicRowsEquiv_apply, GridState.relabelRows_relabelRows, Equiv.self_trans_symm,
    GridState.relabelRows_refl, laurentCyclicRowsEquiv, GridChain.relabelRowsEquiv_single,
    oDerivative_singleton_single_apply, oDerivative_singleton_single_apply]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_equiv (relabelRowsEquiv (finRotate n) x z) (fun r => ?_) (fun r _ => ?_)
  · simp only [mem_emptyRectangles, isEmpty_relabelRowsEquiv_finRotate]
  · rw [G.OColumns_relabelRows_finRotate]
    simp only [mem_coveredSquares_relabelRowsEquiv_finRotate, GridDiagram.relabelRows_O_apply,
      Equiv.symm_apply_apply]

/-- Cyclic column translation intertwines the single-column derivative maps, moving the
column of the O marking. -/
theorem laurentCyclicColumnsEquiv_comp_oDerivative_singleton (G : GridDiagram n) (h : Fin n) :
    (laurentCyclicColumnsEquiv R).toLinearMap ∘ₗ oDerivative R G {h} =
      oDerivative R (G.relabelColumns (finRotate n)) {finRotate n h} ∘ₗ
        (laurentCyclicColumnsEquiv R).toLinearMap := by
  apply gridLinearMap_ext
  intro x y
  obtain ⟨z, rfl⟩ : ∃ z : GridState n, z.relabelColumns (finRotate n) = y :=
    ⟨y.relabelColumns (finRotate n).symm, by simp⟩
  change laurentCyclicColumnsEquiv R (oDerivative R G {h} (single x 1)) (z.relabelColumns _) =
    oDerivative R (G.relabelColumns (finRotate n)) {finRotate n h}
      (laurentCyclicColumnsEquiv R (single x 1)) (z.relabelColumns _)
  rw [laurentCyclicColumnsEquiv_apply, GridState.relabelColumns_relabelColumns,
    Equiv.self_trans_symm, GridState.relabelColumns_refl, laurentCyclicColumnsEquiv,
    GridChain.relabelColumnsEquiv_single, oDerivative_singleton_single_apply,
    oDerivative_singleton_single_apply]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_equiv (relabelColumnsEquiv (finRotate n) x z) (fun r => ?_) (fun r _ => ?_)
  · simp only [mem_emptyRectangles, isEmpty_relabelColumnsEquiv_finRotate]
  · rw [G.OColumns_relabelColumns_finRotate, Finset.card_map]
    simp only [mem_coveredSquares_relabelColumnsEquiv_finRotate,
      GridDiagram.relabelColumns_O_apply, Equiv.symm_apply_apply]

/-- Cyclic row translation intertwines the derivative map of every set of columns. -/
theorem laurentCyclicRowsEquiv_comp_oDerivative (G : GridDiagram n) (P : Finset (Fin n)) :
    (laurentCyclicRowsEquiv R).toLinearMap ∘ₗ oDerivative R G P =
      oDerivative R (G.relabelRows (finRotate n)) P ∘ₗ
        (laurentCyclicRowsEquiv R).toLinearMap := by
  rw [oDerivative_eq_sum, oDerivative_eq_sum]
  simp only [← Module.End.mul_eq_comp, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Module.End.mul_eq_comp]
  exact laurentCyclicRowsEquiv_comp_oDerivative_singleton R G h

/-- Cyclic column translation intertwines the derivative map of every set of columns, with the
translated set of columns. -/
theorem laurentCyclicColumnsEquiv_comp_oDerivative (G : GridDiagram n) (P : Finset (Fin n)) :
    (laurentCyclicColumnsEquiv R).toLinearMap ∘ₗ oDerivative R G P =
      oDerivative R (G.relabelColumns (finRotate n)) (P.map (finRotate n).toEmbedding) ∘ₗ
        (laurentCyclicColumnsEquiv R).toLinearMap := by
  rw [oDerivative_eq_sum, oDerivative_eq_sum, Finset.sum_map]
  simp only [← Module.End.mul_eq_comp, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Module.End.mul_eq_comp, Equiv.toEmbedding_apply]
  exact laurentCyclicColumnsEquiv_comp_oDerivative_singleton R G h

end OnLeConjecture.KnotFloer.GridFull
