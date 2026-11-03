/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableFilteredHomotopy
public import OnLeConjecture.KnotFloer.GridSingleSquareDeformation
public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov
public import OnLeConjecture.KnotFloer.GridFullLaurentBifiltration

/-!
# Strict Alexander decrease of the Laurent X-square derivative

The single-square derivative at an X marking counts the empty rectangles containing that
marking, with all O variables collapsed to the Laurent variable. It lowers Maslov degree
by one, preserves the first filtration bound, and lowers the second bound by at least one.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The full Laurent rectangle derivative at the indicated X marking. -/
noncomputable def laurentXMarkingHomotopy (a : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  singleSquareOperator G R a (G.X a) 1

open Classical in
/-- Its matrix entries are the O-weighted sums of all empty rectangles through that X marking. -/
theorem laurentXMarkingHomotopy_apply_apply (a : Fin n) (c : LaurentChain R n)
    (y : GridState n) :
    laurentXMarkingHomotopy G R a c y = c.sum fun x p => p *
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => (a, G.X a) ∈ r.toGridRectangle.coveredSquares),
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  simp only [laurentXMarkingHomotopy, singleSquareOperator,
    polynomialCoefficientOperator_apply_apply,
    coeff_one_squareWeightedCoefficient_singleSquareDeformation]

/-- A surviving coefficient is contributed by a genuine X-crossing empty rectangle. -/
theorem exists_rectangle_of_mem_support_laurentXMarkingHomotopy
    (a : Fin n) (c : LaurentChain R n) {y : GridState n} {k : ℤ}
    (hk : k ∈ (laurentXMarkingHomotopy G R a c y).coeff.support) :
    ∃ x : GridState n, ∃ j ∈ (c x).coeff.support, ∃ r : GridRectangleBetween x y,
      r.IsEmpty ∧ (a, G.X a) ∈ r.toGridRectangle.coveredSquares ∧
        k = j + ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [laurentXMarkingHomotopy_apply_apply, Finsupp.sum, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  rw [AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨r, hr, hd⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hd)
  obtain ⟨hre, hrX⟩ := Finset.mem_filter.mp hr
  change d ∈ (Finsupp.single ((G.OColumns r.toGridRectangle).card : ℤ) (1 : R)).support at hd
  have hd' := Finset.mem_singleton.mp (Finsupp.support_single_subset hd)
  exact ⟨x, j, hj, r, (GridRectangleBetween.mem_emptyRectangles r).mp hre, hrX,
    congrArg (fun d => j + d) hd'⟩

/-- The Laurent X-square derivative has Maslov degree minus one. -/
theorem laurentXMarkingHomotopy_mem_maslovPiece (a : Fin n)
    {m : ℤ} {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    laurentXMarkingHomotopy G R a c ∈ laurentMaslovPiece G R (m - 1) := by
  intro y k hk
  obtain ⟨x, j, hj, r, hre, _, rfl⟩ :=
    exists_rectangle_of_mem_support_laurentXMarkingHomotopy G R a c hk
  rw [laurentMaslovDegree_add_card_OColumns G r hre]
  exact congrArg (fun m : ℤ => m - 1) (hc x j hj)

/-- The X-square derivative preserves the first Laurent bound and lowers the second by one. -/
theorem laurentXMarkingHomotopy_mem_bifiltrationLevel (S : Type*) [CommRing S]
    (a : Fin n) {u v : ℝ} {c : LaurentChain S n}
    (hc : c ∈ laurentBifiltrationLevel G S u v) :
    laurentXMarkingHomotopy G S a c ∈ laurentBifiltrationLevel G S u (v - 1) := by
  intro y k hk
  obtain ⟨x, j, hj, r, _, hrX, rfl⟩ :=
    exists_rectangle_of_mem_support_laurentXMarkingHomotopy G S a c hk
  have hb := hc x j hj
  constructor
  · exact (laurentRectangle_coordinates_le G r j).1.trans hb.1
  · have h := G.alexander_sub_alexander_eq_card_sub_card r
    rw [← G.card_OColumns r.toGridRectangle] at h
    have hreal : (G.alexander x : ℝ) - (G.alexander y : ℝ) =
        ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) -
          (G.OColumns r.toGridRectangle).card := by exact_mod_cast h
    have hx : (1 : ℝ) ≤ ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) :=
      by exact_mod_cast one_le_card_X_of_mem G a r hrX
    push_cast
    linarith [hb.2]

/-- After the O-variable collapse, the X-square derivative commutes with the differential. -/
theorem laurentDifferential_xMarkingHomotopy [CharP R 2] (a : Fin n) :
    laurentDifferential G R ∘ₗ laurentXMarkingHomotopy G R a +
      laurentXMarkingHomotopy G R a ∘ₗ laurentDifferential G R = 0 :=
  singleSquareOperator_one_chain G a (G.X a)

end OnLeConjecture.KnotFloer.GridFull
