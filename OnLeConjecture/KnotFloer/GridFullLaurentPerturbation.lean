/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov
public import OnLeConjecture.KnotFloer.GridFullLaurentBifiltration
public import OnLeConjecture.External.TauCeti.Algebra.Homology.Contraction.Perturbation

/-!
# Local nilpotence from the full Laurent grid grading and filtration

A Laurent-linear endomorphism preserving Maslov degree and decreasing
the Alexander coordinate by at least one is locally nilpotent. Indeed,
its nonzero matrix entries strictly lower the finite state weight
`A(x) - M_O(x)/2`. The checked general nilpotence theorem for a finite
basis then applies, despite the unbounded Laurent exponents.

Consequently a filtered homotopy of degree one followed by a
filtration-decreasing perturbation of degree minus one satisfies the
invertibility hypothesis of the basic perturbation lemma.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- A state with Laurent exponent zero has exactly its stated coordinate bounds. -/
theorem single_one_mem_laurentBifiltrationLevel (x : GridState n) :
    (Finsupp.single x (1 : LaurentPolynomial R) : LaurentChain R n) ∈
      laurentBifiltrationLevel G R 0 (G.alexander x : ℝ) := by
  classical
  intro y k hk
  by_cases hy : y = x
  · subst y
    rw [Finsupp.single_eq_same] at hk
    change k ∈ (Finsupp.single 0 (1 : R)).support at hk
    have hk0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    subst k
    simp
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

/-- Degree preservation turns strict Alexander decrease into finite-state weight decrease. -/
theorem stateWeight_lt_of_mem_support_laurent_lowering
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece G R m)
    (hfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b →
        f c ∈ laurentBifiltrationLevel G R a (b - 1))
    (x y : GridState n) (hy : y ∈ (f (Finsupp.single x 1)).support) :
    (G.alexander y : ℝ) - (G.maslovOℤ y : ℝ) / 2 <
      (G.alexander x : ℝ) - (G.maslovOℤ x : ℝ) / 2 := by
  have hyne := Finsupp.mem_support_iff.mp hy
  have hcne : (f (Finsupp.single x 1) y).coeff ≠ 0 := by
    intro h
    apply hyne
    apply AddMonoidAlgebra.coeff_injective
    simpa only [AddMonoidAlgebra.coeff_zero] using h
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hcne
  have hxdegree : (Finsupp.single x (1 : LaurentPolynomial R) : LaurentChain R n) ∈
      laurentMaslovPiece G R (G.maslovOℤ x) := by
    simpa only [laurentMonomialGenerator, LaurentPolynomial.T_zero,
      laurentMaslovDegree, mul_zero, sub_zero] using
      laurentMonomialGenerator_mem_laurentMaslovPiece G R 0 x
  have hm := (hdegree _ _ hxdegree) y k hk
  have hj := (hfiltration _ _ _ (single_one_mem_laurentBifiltrationLevel G R x)) y k hk
  simp only [laurentMaslovDegree] at hm
  have hmreal : (G.maslovOℤ y : ℝ) - 2 * (k : ℝ) = (G.maslovOℤ x : ℝ) := by
    exact_mod_cast hm
  linarith [hj.2]

/-- Strict Alexander decrease and degree zero imply local nilpotence on the full Laurent module. -/
theorem exists_pow_apply_eq_zero_of_laurent_lowering
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece G R m)
    (hfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b →
        f c ∈ laurentBifiltrationLevel G R a (b - 1))
    (c : LaurentChain R n) : ∃ k : ℕ, (f ^ k) c = 0 := by
  let w : GridState n → ℝ := fun x => (G.alexander x : ℝ) - (G.maslovOℤ x : ℝ) / 2
  have hw : WellFounded (InvImage (· < ·) w) := Finite.wellFounded_of_trans_of_irrefl _
  exact Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt f w hw
    (stateWeight_lt_of_mem_support_laurent_lowering G R f hdegree hfiltration) c

/-- A degree-zero filtration-decreasing perturbation has an invertible geometric-series operator. -/
theorem isUnit_one_add_of_laurent_lowering
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece G R m)
    (hfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b →
        f c ∈ laurentBifiltrationLevel G R a (b - 1)) : IsUnit (1 + f) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero f
    (exists_pow_apply_eq_zero_of_laurent_lowering G R f hdegree hfiltration)

/-- Filtered homotopies and degree-minus-one perturbations satisfy the HPL unit hypothesis. -/
theorem isUnit_one_add_laurent_perturbation_comp_homotopy
    (δ h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hδdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      δ c ∈ laurentMaslovPiece G R (m - 1))
    (hhdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece G R (m + 1))
    (hδfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b →
        δ c ∈ laurentBifiltrationLevel G R a (b - 1))
    (hhfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b → h c ∈ laurentBifiltrationLevel G R a b) :
    IsUnit (1 + δ * h) := by
  apply isUnit_one_add_of_laurent_lowering G R
  · intro m c hc
    simpa only [Module.End.mul_apply, add_sub_cancel_right] using
      hδdegree (m + 1) (h c) (hhdegree m c hc)
  · intro a b c hc
    exact hδfiltration a b (h c) (hhfiltration a b c hc)

/-- Strict decrease of the first coordinate also lowers a finite state weight. -/
theorem negativeMaslov_lt_of_mem_support_laurent_lowering
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece G R m)
    (hfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b →
        f c ∈ laurentBifiltrationLevel G R (a - 1) b)
    (x y : GridState n) (hy : y ∈ (f (Finsupp.single x 1)).support) :
    -(G.maslovOℤ y : ℝ) / 2 < -(G.maslovOℤ x : ℝ) / 2 := by
  have hyne := Finsupp.mem_support_iff.mp hy
  have hcne : (f (Finsupp.single x 1) y).coeff ≠ 0 := by
    intro h
    apply hyne
    apply AddMonoidAlgebra.coeff_injective
    simpa only [AddMonoidAlgebra.coeff_zero] using h
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hcne
  have hxdegree : (Finsupp.single x (1 : LaurentPolynomial R) : LaurentChain R n) ∈
      laurentMaslovPiece G R (G.maslovOℤ x) := by
    simpa only [laurentMonomialGenerator, LaurentPolynomial.T_zero,
      laurentMaslovDegree, mul_zero, sub_zero] using
      laurentMonomialGenerator_mem_laurentMaslovPiece G R 0 x
  have hm := (hdegree _ _ hxdegree) y k hk
  have hi := (hfiltration _ _ _ (single_one_mem_laurentBifiltrationLevel G R x)) y k hk
  simp only [laurentMaslovDegree] at hm
  have hmreal : (G.maslovOℤ y : ℝ) - 2 * (k : ℝ) = (G.maslovOℤ x : ℝ) := by
    exact_mod_cast hm
  linarith [hi.1]

/-- Degree-zero operators strictly lowering the first coordinate are locally nilpotent. -/
theorem exists_pow_apply_eq_zero_of_laurent_first_lowering
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece G R m)
    (hfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b →
        f c ∈ laurentBifiltrationLevel G R (a - 1) b)
    (c : LaurentChain R n) : ∃ k : ℕ, (f ^ k) c = 0 := by
  let w : GridState n → ℝ := fun x => -(G.maslovOℤ x : ℝ) / 2
  have hw : WellFounded (InvImage (· < ·) w) := Finite.wellFounded_of_trans_of_irrefl _
  exact Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt f w hw
    (negativeMaslov_lt_of_mem_support_laurent_lowering G R f hdegree hfiltration) c

/-- Positive-U perturbations have the finite inverse required by HPL. -/
theorem isUnit_one_add_of_laurent_first_lowering
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdegree : ∀ (m : ℤ) (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece G R m)
    (hfiltration : ∀ (a b : ℝ) (c : LaurentChain R n),
      c ∈ laurentBifiltrationLevel G R a b →
        f c ∈ laurentBifiltrationLevel G R (a - 1) b) : IsUnit (1 + f) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero f
    (exists_pow_apply_eq_zero_of_laurent_first_lowering G R f hdegree hfiltration)

end OnLeConjecture.KnotFloer.GridFull
