/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorODerivative
public import OnLeConjecture.KnotFloer.GridCanonicalSymmetry

/-!
# Transposition of the derivative maps

The scissor construction of the written proof of Statement E (`statement_E_complete_proof.tex`,
Section 9) uses O switches of adjacent rows. Transposing the grid turns rows into columns, so the
row calculus follows from the column calculus once transposition is compatible with the derivative
maps. The O marking of column `h` of `G` lies in column `G.O h` of the transposed grid, and
(`laurentTransposeEquiv_comp_oDerivative`)

  `T ∘ Φ^G_h = Φ^{Gᵀ}_{G.O h} ∘ T`,

where `T` is the Laurent-linear relabeling of states by diagonal reflection.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp GridRectangleBetween

variable {n : ℕ} (R : Type*) [CommRing R]

/-- The O marking of column `G.O h` of the transposed grid lies in row `h`. -/
theorem transpose_O_apply_O (G : GridDiagram n) (h : Fin n) : G.transpose.O (G.O h) = h := by
  have hmem : (G.O h, h) ∈ G.transpose.OSet := by
    rw [GridDiagram.transpose_OSet, Finset.mem_image]
    exact ⟨(h, G.O h), (GridDiagram.mem_OSet G _).mpr rfl, rfl⟩
  exact (GridDiagram.mem_OSet _ _).mp hmem

theorem laurentTransposeEquiv_single (x : GridState n) :
    laurentTransposeEquiv R (single x 1) = (single x.transpose 1 : LaurentChain R n) := by
  ext y : 1
  rw [laurentTransposeEquiv_apply, Finsupp.single_apply, Finsupp.single_apply]
  congr 1
  exact propext ⟨fun hx => by rw [hx, GridState.transpose_transpose],
    fun hx => by rw [← hx, GridState.transpose_transpose]⟩

/-- Transposition intertwines the single-column derivative maps. -/
theorem laurentTransposeEquiv_comp_oDerivative (G : GridDiagram n) (h : Fin n) :
    (laurentTransposeEquiv R).toLinearMap ∘ₗ oDerivative R G {h} =
      oDerivative R G.transpose {G.O h} ∘ₗ (laurentTransposeEquiv R).toLinearMap := by
  apply gridLinearMap_ext
  intro x y
  obtain ⟨z, rfl⟩ : ∃ z : GridState n, z.transpose = y := ⟨y.transpose, by simp⟩
  change laurentTransposeEquiv R (oDerivative R G {h} (single x 1)) z.transpose =
    oDerivative R G.transpose {G.O h} (laurentTransposeEquiv R (single x 1)) z.transpose
  rw [laurentTransposeEquiv_apply, GridState.transpose_transpose, laurentTransposeEquiv_single,
    oDerivative_singleton_single_apply, oDerivative_singleton_single_apply,
    transpose_O_apply_O]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_equiv (transposeEquiv x z) (fun r => ?_) (fun r _ => ?_)
  · simp only [mem_emptyRectangles, transposeEquiv_apply, isEmpty_transpose]
  · rw [transposeEquiv_apply, transpose_toGridRectangle,
      GridRectangle.coveredSquares_transpose, card_OColumns_transpose]
    have hiff : (G.O h, h) ∈ r.toGridRectangle.coveredSquares.image Prod.swap ↔
        (h, G.O h) ∈ r.toGridRectangle.coveredSquares := by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨p, hp, hpe⟩
        have : p = (h, G.O h) := by
          rw [← Prod.swap_swap p, hpe]
          rfl
        exact this ▸ hp
      · intro hp
        exact ⟨_, hp, rfl⟩
    simp only [hiff]

end OnLeConjecture.KnotFloer.GridFull
