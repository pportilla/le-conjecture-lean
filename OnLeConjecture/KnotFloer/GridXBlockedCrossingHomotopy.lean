/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentXBlocking
public import OnLeConjecture.KnotFloer.GridVariableHomotopy

/-!
# Crossing one X square while keeping other X squares blocked

The square derivative counts rectangles crossing a specified X and avoiding a chosen
set of X markings. It commutes with both differentials, before and after that specified
X is blocked. The formula supplies the comparison map for a partially blocked stabilization.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- The derivative at an X marking while all selected X squares retain weight zero. -/
noncomputable def xBlockedCrossingHomotopy (S : Finset (Fin n)) (b : Fin n) :
    Module.End (LaurentPolynomial R) (LaurentChain R n) :=
  squareDerivative (xBlockedSquareWeight G R S) b (G.X b)

/-- The derivative counts precisely the empty rectangles crossing this X and avoiding the others. -/
theorem xBlockedCrossingHomotopy_apply_apply (S : Finset (Fin n)) (b : Fin n)
    (c : LaurentChain R n) (y : GridState n) :
    xBlockedCrossingHomotopy G R S b c y = c.sum fun x p => p *
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter (fun r =>
        (b, G.X b) ∈ r.toGridRectangle.coveredSquares ∧
        ¬∃ a ∈ S, (a, G.X a) ∈ r.toGridRectangle.coveredSquares),
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  simp only [xBlockedCrossingHomotopy, squareDerivative,
    polynomialCoefficientOperator_apply_apply,
    coeff_one_squareWeightedCoefficient_deformAtSquare, squareWeight_xBlockedSquareWeight,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hp : (b, G.X b) ∈ r.toGridRectangle.coveredSquares <;>
    by_cases hS : ∃ a ∈ S, (a, G.X a) ∈ r.toGridRectangle.coveredSquares <;>
    simp only [hp, hS, not_true_eq_false, not_false_eq_true, and_self, and_false,
      ite_true, ite_false, false_and]

/-- The derivative is exactly the part removed by blocking the additional X. -/
theorem xBlockedDifferential_insert_add_crossing (S : Finset (Fin n)) (b : Fin n) :
    laurentXBlockedDifferential G R (insert b S) + xBlockedCrossingHomotopy G R S b =
      laurentXBlockedDifferential G R S := by
  classical
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  simp only [LinearMap.add_apply, Finsupp.add_apply,
    laurentXBlockedDifferential_apply_apply, xBlockedCrossingHomotopy_apply_apply,
    Finsupp.sum, ← Finset.sum_add_distrib, ← mul_add,
    Finset.mem_insert, exists_eq_or_imp, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hp : (b, G.X b) ∈ r.toGridRectangle.coveredSquares <;>
    by_cases hS : ∃ a ∈ S, (a, G.X a) ∈ r.toGridRectangle.coveredSquares <;>
    simp only [hp, hS, not_true_eq_false, not_false_eq_true, and_self, and_false,
      ite_true, ite_false, zero_add, add_zero, false_and, or_true, or_false]

variable [CharP R 2]

/-- Row and column annuli cancel for an X derivative with any other X squares blocked. -/
theorem xBlockedCrossingHomotopy_chain (S : Finset (Fin n)) (b : Fin n) :
    laurentXBlockedDifferential G R S ∘ₗ xBlockedCrossingHomotopy G R S b +
      xBlockedCrossingHomotopy G R S b ∘ₗ laurentXBlockedDifferential G R S = 0 := by
  rw [xBlockedCrossingHomotopy, laurentXBlockedDifferential, squareDerivative_homotopy,
    xBlockedSquareWeight_column, xBlockedSquareWeight_row]
  simp only [Equiv.symm_apply_apply, CharTwo.add_self_eq_zero, zero_smul]

/-- The same crossing map is a chain map after the selected X has also been blocked. -/
theorem xBlockedCrossingHomotopy_insert_chain (S : Finset (Fin n)) (b : Fin n) :
    laurentXBlockedDifferential G R (insert b S) ∘ₗ xBlockedCrossingHomotopy G R S b +
      xBlockedCrossingHomotopy G R S b ∘ₗ
        laurentXBlockedDifferential G R (insert b S) = 0 := by
  have h := xBlockedCrossingHomotopy_chain G R S b
  rw [← xBlockedDifferential_insert_add_crossing G R S b,
    LinearMap.add_comp, LinearMap.comp_add] at h
  have heq :
      (laurentXBlockedDifferential G R (insert b S) ∘ₗ xBlockedCrossingHomotopy G R S b +
        xBlockedCrossingHomotopy G R S b ∘ₗ xBlockedCrossingHomotopy G R S b) +
      (xBlockedCrossingHomotopy G R S b ∘ₗ laurentXBlockedDifferential G R (insert b S) +
        xBlockedCrossingHomotopy G R S b ∘ₗ xBlockedCrossingHomotopy G R S b) =
      laurentXBlockedDifferential G R (insert b S) ∘ₗ xBlockedCrossingHomotopy G R S b +
        xBlockedCrossingHomotopy G R S b ∘ₗ laurentXBlockedDifferential G R (insert b S) := by
    have htwice : xBlockedCrossingHomotopy G R S b ∘ₗ xBlockedCrossingHomotopy G R S b +
        xBlockedCrossingHomotopy G R S b ∘ₗ xBlockedCrossingHomotopy G R S b = 0 := by
      apply LinearMap.ext
      intro c
      apply Finsupp.ext
      intro y
      exact CharTwo.add_self_eq_zero _
    rw [add_add_add_comm, htwice, add_zero]
  exact heq.symm.trans h


omit [CharP R 2] in
/-- Every surviving coefficient comes from an empty rectangle crossing the specified X. -/
theorem xBlockedCrossingHomotopy_support (S : Finset (Fin n)) (b : Fin n)
    (c : LaurentChain R n) {y : GridState n} {k : ℤ}
    (hk : k ∈ (xBlockedCrossingHomotopy G R S b c y).coeff.support) :
    ∃ x, ∃ j ∈ (c x).coeff.support, ∃ r : GridRectangleBetween x y,
      r.IsEmpty ∧ (b, G.X b) ∈ r.toGridRectangle.coveredSquares ∧
      (¬∃ a ∈ S, (a, G.X a) ∈ r.toGridRectangle.coveredSquares) ∧
      k = j + ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [xBlockedCrossingHomotopy_apply_apply, Finsupp.sum, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  rw [AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨r, hr, hd⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hd)
  obtain ⟨hre, hp, hS⟩ := Finset.mem_filter.mp hr
  change d ∈ (single ((G.OColumns r.toGridRectangle).card : ℤ) (1 : R)).support at hd
  have hd' := Finset.mem_singleton.mp (support_single_subset hd)
  exact ⟨x, j, hj, r, (GridRectangleBetween.mem_emptyRectangles r).mp hre, hp, hS,
    congrArg (fun d => j + d) hd'⟩

omit [CharP R 2] in
/-- The partially blocked X-crossing operator has Laurent Maslov degree minus one. -/
theorem xBlockedCrossingHomotopy_mem_maslovPiece (S : Finset (Fin n)) (b : Fin n)
    {m : ℤ} {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    xBlockedCrossingHomotopy G R S b c ∈ laurentMaslovPiece G R (m - 1) := by
  intro y k hk
  obtain ⟨x, j, hj, r, hre, _, _, rfl⟩ := xBlockedCrossingHomotopy_support G R S b c hk
  rw [laurentMaslovDegree_add_card_OColumns G r hre]
  exact congrArg (fun m : ℤ => m - 1) (hc x j hj)

omit [CharP R 2] in
/-- Crossing the specified X lowers Alexander by at least one, regardless of other X blocks. -/
theorem xBlockedCrossingHomotopy_mem_bifiltrationLevel (S : Finset (Fin n)) (b : Fin n)
    {u v : ℝ} {c : LaurentChain R n} (hc : c ∈ laurentBifiltrationLevel G R u v) :
    xBlockedCrossingHomotopy G R S b c ∈ laurentBifiltrationLevel G R u (v - 1) := by
  intro y k hk
  obtain ⟨x, j, hj, r, _, hrX, _, rfl⟩ := xBlockedCrossingHomotopy_support G R S b c hk
  have hb := hc x j hj
  constructor
  · exact (laurentRectangle_coordinates_le G r j).1.trans hb.1
  · have h := G.alexander_sub_alexander_eq_card_sub_card r
    rw [← G.card_OColumns r.toGridRectangle] at h
    have hreal : (G.alexander x : ℝ) - (G.alexander y : ℝ) =
        ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) -
          (G.OColumns r.toGridRectangle).card := by exact_mod_cast h
    have hx : (1 : ℝ) ≤ ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) :=
      by exact_mod_cast one_le_card_X_of_mem G b r hrX
    push_cast
    linarith [hb.2]

end OnLeConjecture.KnotFloer.GridFull
