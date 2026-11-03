/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IntersectionResultant
public import OnLeConjecture.Analytic.PlaneFiniteFiberCriterion
public import OnLeConjecture.Analytic.TwoWeightPairElimination

/-!
# The analytic pair preceding cyclic preparation

The pair `(x² + yᵏ, xᵖ + yᵏ β)` generates the rectangle ideal `(x², yᵏ)`
when `p ≥ 3` and `β(0) ≠ 0`. Its analytic coordinate colength is `2k`.
The coefficient `β` may depend on both source coordinates in these results.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

/-- The first component of the prepared pair. -/
@[expose] noncomputable def cyclicFirst (k : ℕ) : Germ 2 :=
  Germ.coordinate 0 ^ 2 + Germ.coordinate 1 ^ k

/-- The second component of the prepared pair. -/
@[expose] noncomputable def cyclicSecond (k p : ℕ) (β : Germ 2) : Germ 2 :=
  Germ.coordinate 0 ^ p + Germ.coordinate 1 ^ k * β

/-- The prepared pair has exactly the rectangle ideal. Oddness of `p`
and positivity of `k` are not needed for this ideal identity. -/
theorem cyclic_pairIdeal_eq (k p : ℕ) (hp : 3 ≤ p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0) :
    PlaneCurve.pairIdeal (cyclicFirst k) (cyclicSecond k p β) =
      PlaneCurve.pairIdeal (Germ.coordinate 0 ^ 2) (Germ.coordinate 1 ^ k) := by
  let x : Germ 2 := Germ.coordinate 0
  let y : Germ 2 := Germ.coordinate 1
  have hpow : x ^ (p - 2) * x ^ 2 = x ^ p := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hu : IsUnit (β - x ^ (p - 2)) := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    simpa [x, show p - 2 ≠ 0 by omega] using hβ
  let I := PlaneCurve.pairIdeal (cyclicFirst k) (cyclicSecond k p β)
  have hP : cyclicFirst k ∈ I := Ideal.subset_span (by simp)
  have hQ : cyclicSecond k p β ∈ I := Ideal.subset_span (by simp)
  have hprod : (β - x ^ (p - 2)) * y ^ k ∈ I := by
    have h := I.sub_mem hQ (I.mul_mem_left (x ^ (p - 2)) hP)
    convert h using 1
    dsimp [cyclicFirst, cyclicSecond, x, y] at *
    linear_combination hpow
  have hy : y ^ k ∈ I := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu] at hprod
    have h := I.mul_mem_left (↑u⁻¹ : Germ 2) hprod
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using h
  have hx : x ^ 2 ∈ I := by
    convert I.sub_mem hP hy using 1
    dsimp [cyclicFirst, x, y]
    ring
  apply le_antisymm
  · rw [PlaneCurve.pairIdeal, Ideal.span_le]
    intro z hz
    rcases hz with rfl | hz
    · exact Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp))
    · have hz' : z = cyclicSecond k p β := Set.mem_singleton_iff.mp hz
      subst z
      have hx' : x ^ 2 ∈ PlaneCurve.pairIdeal (x ^ 2) (y ^ k) :=
        Ideal.subset_span (by simp)
      have hy' : y ^ k ∈ PlaneCurve.pairIdeal (x ^ 2) (y ^ k) :=
        Ideal.subset_span (by simp)
      change x ^ p + y ^ k * β ∈ PlaneCurve.pairIdeal (x ^ 2) (y ^ k)
      rw [← hpow]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx') (Ideal.mul_mem_right _ _ hy')
  · rw [PlaneCurve.pairIdeal, Ideal.span_le]
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · exact Set.mem_singleton_iff.mp hz ▸ hy

private theorem rectangle_resultant (k : ℕ) :
    (Polynomial.X ^ 2 : Polynomial (Germ 1)).resultant
      (Polynomial.C (Germ.coordinate 0 ^ k)) = Germ.coordinate 0 ^ (2 * k) := by
  rw [PolynomialResultant.resultant_C_eq_pow_of_monic _ _ (Polynomial.monic_X.pow 2)]
  simp [pow_mul, Nat.mul_comm]

private theorem rectangle_first_eval :
    Germ.firstCoordinatePolynomialEvaluation (Polynomial.X ^ 2 : Polynomial (Germ 1)) =
      Germ.coordinate 0 ^ 2 := by
  simp [Germ.firstCoordinatePolynomialEvaluation]

private theorem rectangle_second_eval (k : ℕ) :
    Germ.firstCoordinatePolynomialEvaluation
      (Polynomial.C (Germ.coordinate 0 ^ k)) = Germ.coordinate 1 ^ k := by
  rw [Germ.firstCoordinatePolynomialEvaluation, Polynomial.eval₂_C, map_pow,
    Germ.hyperplaneExtension_coordinate_plane]

/-- The quotient by `(x², yᵏ)` is finite dimensional, including `k = 0`. -/
theorem rectangle_hasFiniteIntersection (k : ℕ) :
    PlaneCurve.HasFiniteIntersection (Germ.coordinate 0 ^ 2) (Germ.coordinate 1 ^ k) := by
  rw [← rectangle_first_eval, ← rectangle_second_eval k]
  apply Germ.hasFiniteIntersection_of_resultant_ne_zero 1 _ _
    (Polynomial.monic_X.pow 2) (by simp)
  · intro j hj
    have hj' : j ≠ 2 := by omega
    simp [Polynomial.coeff_X_pow, hj']
  · rw [rectangle_resultant]
    exact pow_ne_zero _ Germ.coordinate_zero_ne_zero

/-- The rectangle quotient has complex dimension `2k`. -/
theorem rectangle_quotient_finrank (k : ℕ) :
    Module.finrank ℂ (Germ 2 ⧸
      PlaneCurve.pairIdeal (Germ.coordinate 0 ^ 2) (Germ.coordinate 1 ^ k)) = 2 * k := by
  have hfinite : PlaneCurve.HasFiniteIntersection
      (Germ.firstCoordinatePolynomialEvaluation (Polynomial.X ^ 2 : Polynomial (Germ 1)))
      (Germ.firstCoordinatePolynomialEvaluation (Polynomial.C (Germ.coordinate 0 ^ k))) := by
    simpa only [rectangle_first_eval, rectangle_second_eval] using
      rectangle_hasFiniteIntersection k
  have h := Germ.intersectionMultiplicity_eq_resultant_order 1 _ _
    (Polynomial.monic_X.pow 2) (by simp)
    (by intro j hj; simp [Polynomial.coeff_X_pow, show j ≠ 2 by omega]) hfinite
  simp only [rectangle_first_eval, rectangle_second_eval, rectangle_resultant,
    Germ.vanishingOrder_coordinate_pow, ENat.toNat_natCast] at h
  exact h

/-- A pointed map with the prepared components has finite coordinate fibre. -/
theorem cyclic_hasFiniteCoordinateFiber (f : PointedMapGerm 2 2)
    (k p : ℕ) (hp : 3 ≤ p) (β : Germ 2) (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β) : f.HasFiniteCoordinateFiber := by
  unfold PointedMapGerm.HasFiniteCoordinateFiber
  rw [PlaneCurve.coordinateIdeal_eq_pairIdeal, hP, hQ, cyclic_pairIdeal_eq k p hp β hβ]
  exact rectangle_hasFiniteIntersection k

/-- The prepared plane map is finite as an analytic map germ. -/
theorem cyclic_isFiniteAtOrigin (f : PointedMapGerm 2 2)
    (k p : ℕ) (hp : 3 ≤ p) (β : Germ 2) (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β) : f.IsFiniteAtOrigin :=
  PointedMapGerm.finiteFiberCriterionAtOrigin_two 2 f
    (cyclic_hasFiniteCoordinateFiber f k p hp β hβ hP hQ)

/-- The prepared map has coordinate colength `2k`. -/
theorem cyclic_coordinateColength (f : PointedMapGerm 2 2)
    (k p : ℕ) (hp : 3 ≤ p) (β : Germ 2) (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β) (hf : f.IsFiniteAtOrigin) :
    f.coordinateColength hf = 2 * k := by
  change Module.finrank ℂ (Germ 2 ⧸ f.1.coordinateIdeal) = _
  rw [PlaneCurve.coordinateIdeal_eq_pairIdeal, hP, hQ, cyclic_pairIdeal_eq k p hp β hβ]
  exact rectangle_quotient_finrank k

/-- The two polynomial initial forms for source weights `(k,p)`. -/
@[expose] noncomputable def cyclicInitialPair (k p : ℕ) (c : ℂ) :
    Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 ^ p + MvPolynomial.C c * MvPolynomial.X 1 ^ k]

/-- Both displayed initial components have their claimed two weights. -/
theorem cyclicInitialPair_homogeneous (k p : ℕ) (c : ℂ) (i : Fin 2) :
    (cyclicInitialPair k p c i).IsWeightedHomogeneous ![k, p] (![2 * k, p * k] i) := by
  fin_cases i
  · simpa [cyclicInitialPair, nsmul_eq_mul] using
      (MvPolynomial.isWeightedHomogeneous_X ℂ ![k, p] 0).pow 2
  · apply MvPolynomial.IsWeightedHomogeneous.add
    · simpa [cyclicInitialPair, nsmul_eq_mul] using
        (MvPolynomial.isWeightedHomogeneous_X ℂ ![k, p] 0).pow p
    · simpa [cyclicInitialPair, nsmul_eq_mul, mul_comm] using
        ((MvPolynomial.isWeightedHomogeneous_X ℂ ![k, p] 1).pow k).C_mul c

/-- The prepared pair has strict tails above its polynomial initial forms. -/
theorem cyclic_pair_strict_tails (f : PointedMapGerm 2 2)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (β : Germ 2)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β) (i : Fin 2) :
    f.1.component i - Germ.coordinatePolynomialAlgHom 2
        (cyclicInitialPair k p (Germ.valueRingHom 2 β) i) ∈
      Germ.twoWeightOrderIdeal k p (![2 * k, p * k] i + 1) := by
  have hp' : 0 < p := by omega
  fin_cases i
  · simpa [hP, cyclicFirst, cyclicInitialPair] using
      Germ.monomial_mem_twoWeightOrderIdeal_of_threshold k p (2 * k + 1) 0 k hk hp'
        (by nlinarith)
  · have hy : Germ.coordinate (1 : Fin 2) ^ k ∈ Germ.twoWeightOrderIdeal k p (p * k) := by
      simpa using Germ.monomial_mem_twoWeightOrderIdeal_of_threshold
        k p (p * k) 0 k hk hp' (by simp)
    have hβ : β - Germ.constRingHom 2 (Germ.valueRingHom 2 β) ∈
        Germ.twoWeightOrderIdeal k p 1 := by
      rw [Germ.twoWeightOrderIdeal_one_eq_maximalIdeal k p hk hp',
        Germ.mem_maximalIdeal_iff]
      simp
    have h := Germ.twoWeightOrderIdeal_mul_mem k p (p * k) 1 hk hp' hy hβ
    change f.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (cyclicInitialPair k p (Germ.valueRingHom 2 β) 1) ∈
        Germ.twoWeightOrderIdeal k p (p * k + 1)
    simp only [hQ, cyclicSecond, cyclicInitialPair, Matrix.cons_val_one,
      Matrix.cons_val_zero, map_add, map_mul, map_pow,
      Germ.coordinatePolynomialAlgHom_X, Germ.coordinatePolynomialAlgHom_C]
    convert h using 1
    ring

/-- Finite analytic elimination for the prepared pair gives a nonzero
initial remainder outside the algebra of its two polynomial initial forms. -/
theorem cyclic_exists_initial_form_outside_pair_algebra (f : PointedMapGerm 2 2)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β)
    (H : Germ 2) (hH : H ∉ f.ImageRing) :
    ∃ D : ℕ, ∃ Φ : Germ 2, ∃ R : MvPolynomial (Fin 2) ℂ,
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      H - f.pullbackRingHom Φ ∈ Germ.twoWeightOrderIdeal k p D ∧
      H - f.pullbackRingHom Φ - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      R ∉ Set.range (MvPolynomial.aeval (cyclicInitialPair k p (Germ.valueRingHom 2 β)) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) :=
  f.exists_twoWeight_initial_form_outside_pair_algebra
    (cyclic_isFiniteAtOrigin f k p hp β hβ hP hQ) k p hk (by omega)
    ![2 * k, p * k] (cyclicInitialPair k p (Germ.valueRingHom 2 β))
    (cyclicInitialPair_homogeneous k p _) (cyclic_pair_strict_tails f k p hk hp β hP hQ) H hH

end OnLeConjecture.DTwo
