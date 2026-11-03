/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentMapBounds

/-!
# Recovering homogeneous Laurent matrices from U = 1

Every fixed-degree matrix entry has at most one Laurent exponent. Its coefficient is
therefore recovered by evaluation at U = 1. Equality of homogeneous grid maps can be
checked on the finite coefficient matrices after this specialization.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open Finsupp

variable {R : Type*} [CommRing R]

/-- Evaluation of a Laurent polynomial at the unit one. -/
noncomputable def laurentEvalOne : LaurentPolynomial R →+* R :=
  LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ)

/-- A Laurent monomial evaluates to its coefficient at one. -/
theorem laurentEvalOne_single (k : ℤ) (a : R) :
    laurentEvalOne (AddMonoidAlgebra.single k a : LaurentPolynomial R) = a := by
  rw [laurentEvalOne, LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
  simp

/-- Every Laurent power evaluates to one. -/
theorem laurentEvalOne_T (k : ℤ) :
    laurentEvalOne (LaurentPolynomial.T k : LaurentPolynomial R) = 1 :=
  laurentEvalOne_single k 1

/-- At U = 1 the full rectangle coefficient is exactly the number of empty rectangles. -/
theorem laurentEvalOne_coefficient {n : ℕ} (G : TauCeti.GridDiagram n)
    (x y : TauCeti.GridState n) :
    laurentEvalOne (laurentCoefficient G R x y) =
      ((TauCeti.GridRectangleBetween.emptyRectangles x y).card : R) := by
  classical
  rw [laurentCoefficient_eq, map_sum]
  simp only [laurentEvalOne_T, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A Laurent polynomial supported in one Maslov degree is zero if its value at one is zero. -/
theorem eq_zero_of_laurentEvalOne_eq_zero_of_homogeneous (p : LaurentPolynomial R)
    (a b : ℤ) (hp : ∀ k ∈ p.coeff.support, a - 2 * k = b)
    (heval : laurentEvalOne p = 0) : p = 0 := by
  classical
  by_contra hne
  have hcne : p.coeff ≠ 0 := by
    intro h
    apply hne
    exact AddMonoidAlgebra.coeff_injective (by simpa using h)
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hcne
  have hs : p.coeff.support ⊆ {k} := by
    intro j hj
    have h1 := hp j hj
    have h2 := hp k hk
    have heq : j = k := by omega
    exact Finset.mem_singleton.mpr heq
  have heq : p = AddMonoidAlgebra.single k (p.coeff k) := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.support_subset_singleton.mp hs
  rw [heq, laurentEvalOne_single] at heval
  exact Finsupp.mem_support_iff.mp hk heval

/-- Within a fixed homogeneous degree, evaluation at one determines the Laurent polynomial. -/
theorem eq_of_laurentEvalOne_eq_of_homogeneous (p q : LaurentPolynomial R) (a b : ℤ)
    (hp : ∀ k ∈ p.coeff.support, a - 2 * k = b)
    (hq : ∀ k ∈ q.coeff.support, a - 2 * k = b)
    (heval : laurentEvalOne p = laurentEvalOne q) : p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_laurentEvalOne_eq_zero_of_homogeneous (p - q) a b
  · intro k hk
    rw [AddMonoidAlgebra.coeff_sub] at hk
    rcases Finset.mem_union.mp (Finsupp.support_sub hk) with h | h
    · exact hp k h
    · exact hq k h
  · rw [map_sub, heval, sub_self]

/-- Homogeneous Laurent-linear maps are determined by their specialized basis matrices. -/
theorem laurentMap_eq_of_evalOne_matrix_eq {ι κ : Type*}
    (M : ι → ℤ) (N : κ → ℤ) (d : ℤ)
    (f g : (ι →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R] (κ →₀ LaurentPolynomial R))
    (hf : ∀ x y k, k ∈ (f (single x 1) y).coeff.support → N y - 2 * k = M x + d)
    (hg : ∀ x y k, k ∈ (g (single x 1) y).coeff.support → N y - 2 * k = M x + d)
    (heval : ∀ x y, laurentEvalOne (f (single x 1) y) = laurentEvalOne (g (single x 1) y)) :
    f = g := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro y
  exact eq_of_laurentEvalOne_eq_of_homogeneous _ _ (N y) (M x + d)
    (hf x y) (hg x y) (heval x y)

end OnLeConjecture.KnotFloer.GridFull
