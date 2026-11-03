/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

/-!
# The cokernel of the Sylvester map

For a monic polynomial `P` of degree `m` and a polynomial `Q` of degree at
most `n`, the cokernel of the Sylvester map is the quotient by `(P,Q)`.
Monic division bounds the two coefficients in a Bezout expression. This
proves the kernel calculation without an assumed exactness hypothesis.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]
variable {m n : ℕ}

/-- A polynomial of degree less than `m+n` in `(P,Q)` admits a Bezout
expression with the degree bounds used in the Sylvester map. -/
theorem exists_bounded_bezout_of_mem_span_pair
    (P Q H : R[X]) (hP : P.Monic) (hPm : P.natDegree = m)
    (hQn : Q.natDegree ≤ n) (hH : H.degree < (m + n : ℕ))
    (hmem : H ∈ Ideal.span ({P, Q} : Set R[X])) :
    ∃ A B : R[X], A.degree < (n : ℕ) ∧ B.degree < (m : ℕ) ∧
      P * A + Q * B = H := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hmem
  let B' := B %ₘ P
  let A' := A + Q * (B /ₘ P)
  have hB' : B'.degree < (m : ℕ) := by
    simpa only [B', degree_eq_natDegree hP.ne_zero, hPm] using
      degree_modByMonic_lt B hP
  have heq : P * A' + Q * B' = H := by
    calc
      P * A' + Q * B' = A * P + Q * (B %ₘ P + P * (B /ₘ P)) := by
        dsimp [A', B']; ring
      _ = H := by rw [modByMonic_add_div, mul_comm Q B]; exact hAB
  have hQB' : (Q * B').degree < (m + n : ℕ) := by
    by_cases hQzero : Q = 0
    · simp [hQzero]
    have h := (degree_mul_le Q B').trans_lt
      (WithBot.add_lt_add_of_le_of_lt (by simpa using hQzero)
        (degree_le_of_natDegree_le hQn) hB')
    simpa only [← Nat.cast_add, Nat.add_comm n m] using h
  have hPA' : (P * A').degree < (m + n : ℕ) := by
    have hrewrite : P * A' = H - Q * B' := by rw [← heq]; ring
    rw [hrewrite]
    exact (degree_sub_le H (Q * B')).trans_lt (max_lt hH hQB')
  have hA' : A'.degree < (n : ℕ) := by
    by_cases hAzero : A' = 0
    · simp [hAzero]
    rw [hP.degree_mul_comm, hP.degree_mul, degree_eq_natDegree hP.ne_zero,
      degree_eq_natDegree hAzero, hPm] at hPA'
    have hnat : m + A'.natDegree < m + n := by
      simpa only [add_comm A'.natDegree m] using
        (show A'.natDegree + m < m + n by exact_mod_cast hPA')
    rw [degree_eq_natDegree hAzero]
    exact_mod_cast (Nat.lt_of_add_lt_add_left hnat)
  exact ⟨A', B', hA', hB', heq⟩

/-- Reduction modulo the ideal `(P,Q)`, restricted to polynomials of
degree less than `m+n`. -/
@[expose] noncomputable def sylvesterQuotientMap
    (P Q : R[X]) (m n : ℕ) :
    R[X]_(m + n) →ₗ[R] R[X] ⧸ Ideal.span ({P, Q} : Set R[X]) :=
  (Ideal.Quotient.mkₐ R (Ideal.span ({P, Q} : Set R[X]))).toLinearMap.comp
    (degreeLT R (m + n)).subtype

/-- Monic division by `P` proves that the restricted quotient map is
surjective. -/
theorem sylvesterQuotientMap_surjective
    (P Q : R[X]) (hP : P.Monic) (hPm : P.natDegree = m) :
    Function.Surjective (sylvesterQuotientMap P Q m n) := by
  intro x
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hrem : (H %ₘ P).degree < (m + n : ℕ) := by
    have h := degree_modByMonic_lt H hP
    rw [degree_eq_natDegree hP.ne_zero, hPm] at h
    exact h.trans_le (by exact_mod_cast Nat.le_add_right m n)
  refine ⟨⟨H %ₘ P, mem_degreeLT.mpr hrem⟩, ?_⟩
  change Ideal.Quotient.mk _ (H %ₘ P) = Ideal.Quotient.mk _ H
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  apply Ideal.mem_span_pair.mpr
  refine ⟨-(H /ₘ P), 0, ?_⟩
  have h := modByMonic_add_div H P
  linear_combination -h

/-- The kernel of the quotient map is exactly the range of the Sylvester
map. The reverse inclusion uses bounded Bezout coefficients derived by
monic division. -/
theorem ker_sylvesterQuotientMap_eq_range
    (P Q : R[X]) (hP : P.Monic) (hPm : P.natDegree = m)
    (hQn : Q.natDegree ≤ n) :
    LinearMap.ker (sylvesterQuotientMap P Q m n) =
      LinearMap.range (sylvesterMap P Q hPm.le hQn) := by
  ext H
  rw [LinearMap.mem_ker]
  change Ideal.Quotient.mk _ H.val = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hmem
    obtain ⟨A, B, hA, hB, hAB⟩ :=
      exists_bounded_bezout_of_mem_span_pair P Q H.val hP hPm hQn
        (mem_degreeLT.mp H.property) hmem
    refine ⟨(⟨B, mem_degreeLT.mpr hB⟩, ⟨A, mem_degreeLT.mpr hA⟩), ?_⟩
    exact Subtype.ext hAB
  · rintro ⟨⟨B, A⟩, rfl⟩
    apply Ideal.mem_span_pair.mpr
    refine ⟨A.val, B.val, ?_⟩
    change A.val * P + B.val * Q = P * A.val + Q * B.val
    ring

/-- The cokernel of the Sylvester map is naturally linearly equivalent
to the polynomial quotient by `(P,Q)`. The result includes `Q = 0` and
degree-zero bounds. No domain hypothesis is necessary. -/
@[expose] noncomputable def sylvesterCokernelEquiv
    (P Q : R[X]) (hP : P.Monic) (hPm : P.natDegree = m)
    (hQn : Q.natDegree ≤ n) :
    (R[X]_(m + n) ⧸ LinearMap.range (sylvesterMap P Q hPm.le hQn)) ≃ₗ[R]
      R[X] ⧸ Ideal.span ({P, Q} : Set R[X]) :=
  (Submodule.quotEquivOfEq _ _
    (ker_sylvesterQuotientMap_eq_range P Q hP hPm hQn).symm).trans
      ((sylvesterQuotientMap P Q m n).quotKerEquivOfSurjective
        (sylvesterQuotientMap_surjective P Q hP hPm))

/-- The cokernel equivalence sends the class of a bounded polynomial to
the class of the same polynomial in the ideal quotient. -/
@[simp] theorem sylvesterCokernelEquiv_apply_mk
    (P Q : R[X]) (hP : P.Monic) (hPm : P.natDegree = m)
    (hQn : Q.natDegree ≤ n) (H : R[X]_(m + n)) :
    sylvesterCokernelEquiv P Q hP hPm hQn (Submodule.Quotient.mk H) =
      Ideal.Quotient.mk _ H.val := by
  simp only [sylvesterCokernelEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end OnLeConjecture.Polynomial
