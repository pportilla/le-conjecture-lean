/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RationalPreparedWeightedInitialPair

/-!
# Rational-number form of the prepared initial-pair bounds

Dividing the integral degrees by the ramification exponent gives the
rational weights in the manuscript. The corresponding polynomial Omega
differs from its integral version by a nonzero scalar, so its degree and
vanishing are unchanged.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

/-- Dividing both weights by the same scalar divides their weighted
derivative polynomial by that scalar. -/
theorem weightedPairOmega_div_scalar
    (m : ℕ) (L r s : ℂ) (p q : ℂ[X]) :
    weightedPairOmega m (L / s) (r / s) p q =
      C s⁻¹ * weightedPairOmega m L r p q := by
  simp only [weightedPairOmega, div_eq_mul_inv, map_mul]
  ring

end OnLeConjecture.Polynomial

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- The constructed rational initial pair satisfies the manuscript's
bounds with `alpha = r/s`, `ell = L/s`, and the corresponding rationally
scaled complex polynomial Omega. -/
theorem RationalPreparedWeightedPair.rational_dichotomy
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite) (hm : 3 ≤ m) :
    let α : ℚ := (r : ℚ) / s
    let ℓ : ℚ := (data.degree : ℚ) / s
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial
    let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial
    let Ω := OnLeConjecture.Polynomial.weightedPairOmega m
      ((data.degree : ℂ) / s) ((r : ℂ) / s) p q
    let i := PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) u hfinite
    (m : ℚ) * ℓ ≤ (i : ℚ) ∧
      (Ω ≠ 0 → Ω.natDegree ≤ m - 2 ∧
        (t : ℚ) ≤ ℓ + α * ((m : ℚ) - 1 - (Ω.natDegree : ℚ)) ∧
        ℓ = α * (q.natDegree : ℚ) ∧ m + 1 ≤ q.natDegree) ∧
      (Ω = 0 → ℓ = α * (q.natDegree : ℚ) ∧
        (∃ c : ℂ, c ≠ 0 ∧ q ^ m = C c * p ^ q.natDegree) ∧ (m : ℚ) * ℓ < (i : ℚ)) := by
  dsimp only
  let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial
  let q := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial
  let Ω := OnLeConjecture.Polynomial.weightedPairOmega m (data.degree : ℂ) (r : ℂ) p q
  let Ωr := OnLeConjecture.Polynomial.weightedPairOmega m
    ((data.degree : ℂ) / s) ((r : ℂ) / s) p q
  have hsRat : 0 < (s : ℚ) := by exact_mod_cast hs
  have hsComplex : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hscalar : C (s : ℂ)⁻¹ ≠ 0 := C_ne_zero.mpr (inv_ne_zero hsComplex)
  have hscale : Ωr = C (s : ℂ)⁻¹ * Ω :=
    OnLeConjecture.Polynomial.weightedPairOmega_div_scalar m data.degree r s p q
  have hdegree : Ωr.natDegree = Ω.natDegree := by
    rw [hscale, natDegree_C_mul (inv_ne_zero hsComplex)]
  refine ⟨?_, ?_, ?_⟩
  · rw [← mul_div_assoc, div_le_iff₀ hsRat]
    have hbound := data.lower_bound
    have hcast : (m : ℚ) * data.degree ≤ (s : ℚ) * PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P) u hfinite := by
      exact_mod_cast hbound
    simpa only [mul_comm] using hcast
  · intro hnonzero
    have hΩ : Ω ≠ 0 := by
      intro hzero
      apply hnonzero
      change Ωr = 0
      rw [hscale, hzero, mul_zero]
    obtain ⟨hdeg, hbound, hweight, hk⟩ := data.nonzero_omega hΩ
    change Ω.natDegree ≤ m - 2 at hdeg
    change s * t ≤ data.degree + r * (m - 1 - Ω.natDegree) at hbound
    change data.degree = r * q.natDegree at hweight
    refine ⟨?_, ?_, ?_, hk⟩
    · change Ωr.natDegree ≤ m - 2
      rwa [hdegree]
    · change (t : ℚ) ≤ (data.degree : ℚ) / s +
        (r : ℚ) / s * ((m : ℚ) - 1 - (Ωr.natDegree : ℚ))
      rw [hdegree]
      have hcast : (s : ℚ) * t ≤ (data.degree : ℚ) +
          (r : ℚ) * ((m - 1 - Ω.natDegree : ℕ) : ℚ) := by exact_mod_cast hbound
      rw [Nat.cast_sub (by omega : Ω.natDegree ≤ m - 1),
        Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hcast
      have hright : (data.degree : ℚ) / s +
          (r : ℚ) / s * ((m : ℚ) - 1 - (Ω.natDegree : ℚ)) =
          ((data.degree : ℚ) + (r : ℚ) * ((m : ℚ) - 1 - (Ω.natDegree : ℚ))) / s := by ring
      rw [hright, le_div_iff₀ hsRat]
      simpa only [mul_comm] using hcast
    · change (data.degree : ℚ) / s = (r : ℚ) / s * (q.natDegree : ℚ)
      rw [hweight, Nat.cast_mul]
      ring
  · intro hzero
    have hΩ : Ω = 0 := by
      change Ωr = 0 at hzero
      rw [hscale] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hscalar
    obtain ⟨hweight, hidentity, hstrict⟩ := data.zero_omega hΩ
    change data.degree = r * q.natDegree at hweight
    refine ⟨?_, hidentity, ?_⟩
    · change (data.degree : ℚ) / s = (r : ℚ) / s * (q.natDegree : ℚ)
      rw [hweight, Nat.cast_mul]
      ring
    · rw [← mul_div_assoc, div_lt_iff₀ hsRat]
      have hcast : (m : ℚ) * data.degree < (s : ℚ) * PlaneCurve.intersectionMultiplicity
          (U * firstCoordinatePolynomialEvaluation P) u hfinite := by
        exact_mod_cast hstrict
      simpa only [mul_comm] using hcast

end OnLeConjecture.Analytic.Germ
