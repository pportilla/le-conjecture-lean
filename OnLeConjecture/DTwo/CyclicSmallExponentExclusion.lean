/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPreparedNoninjectivity
public import OnLeConjecture.DTwo.ResidualSameCoordinateCollision
public import OnLeConjecture.DTwo.CyclicNormalFormExclusion

/-!
# Cyclic preparation for every exponent at least two

The last collision can use equal second coordinates and opposite nonzero
first coordinates. Consequently the exponent need not be even or exceed
two. A nontrivial primitive root is used only in the preceding preparation.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

private theorem residualInitialPair_eq_cyclicAverageInitialPair
    (k j N : ℕ) (c b : ℂ) (hc : c ≠ 0)
    (Ψ : PreparedOddFamily N) (model : Ψ.BivariateModel) (i : Fin 2) :
    residualWeightedInitialPolynomials k (k + j) c (-b / c) Ψ model
      (i.castLE (by omega)) = cyclicAverageInitialPair k j c b i := by
  fin_cases i
  · rfl
  · change MvPolynomial.C (-c) *
        (MvPolynomial.X 0 ^ 2 + MvPolynomial.C (-b / c) * MvPolynomial.X 1 ^ (k + j)) =
      -(MvPolynomial.C c * MvPolynomial.X 0 ^ 2) +
        MvPolynomial.C b * MvPolynomial.X 1 ^ (k + j)
    have hscalar : (MvPolynomial.C (-c) * MvPolynomial.C (-b / c) :
        MvPolynomial (Fin 2) ℂ) = MvPolynomial.C b := by
      rw [← map_mul]
      congr 1
      field_simp
    rw [mul_add, ← mul_assoc, hscalar, map_neg, neg_mul]

theorem cyclic_prepared_not_hasInjectiveRepresentative_of_two_le
    (g : PointedMapGerm 2 3)
    (k p N : ℕ) (hk : 2 ≤ k)
    (hp : 3 ≤ p) (hodd : Odd p) (hN : 3 ≤ N) (hNodd : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 =
      cyclicSecond k p (hyperplaneExtension 1 (cyclicCoefficientGerm β hβ)))
    (htail : g.1.component 2 - coordinate (0 : Fin 2) ^ N ∈
      twoWeightOrderIdeal k p (k * N + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  have hk0 : 0 < k := by omega
  let ζ := residualPrimitiveRoot k
  have hζ := residualPrimitiveRoot_isPrimitiveRoot hk0
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  obtain ⟨j, hj, hchar, b, hb, cD, hcD, P, _hP0, hhom, f, hequiv, hfirst, hthird, hchart⟩ :=
    exists_cyclic_primitive_degree_preparation g hg k p N hk0 hp hodd hNodd
      β hβ hc hP hQ htail ζ hζ hζ1
  obtain ⟨_hminus, s, hs, Ψ, model, hquotient, _hidentity⟩ :=
    exists_cyclic_prepared_model_of_primitive_weighted_chart hk0 hN hNodd hb hc hcD
      hζ hchar P hhom (by
        intro x X hX hpoint
        exact hchart x X hX (by simpa only [neg_div] using hpoint))
  let H := residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 2
  have hH : H.IsWeightedHomogeneous ![k + j, 2] ((k + j) * N) := by
    simpa [H, residualWeightedDegrees, mul_comm] using
      residualWeightedInitialPolynomials_isWeightedHomogeneous k (k + j) (β 0) (-b / β 0) Ψ model 2
  have hquotient' : P - MvPolynomial.C s * H ∈
      Set.range (MvPolynomial.aeval (cyclicAverageInitialPair k j (β 0) b) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
    simpa [H, residualWeightedInitialPolynomials, MvPolynomial.aeval_eq_bind₁,
      residualParameterPolynomialSubstitution, cyclicAverageInitialPair, neg_mul] using hquotient
  obtain ⟨g', hequiv', hg'0, hg'1, hg'2⟩ :=
    f.exists_weighted_third_initial_replacement (k + j) 2 ((k + j) * N)
      (by omega) (by decide) (Nat.mul_pos (by omega) (by omega))
      ![2 * k, 2 * (k + j)] (cyclicAverageInitialPair k j (β 0) b)
      (cyclicAverageInitialPair_homogeneous k j _ _) hfirst P H hhom hH s hs hthird hquotient'
  apply residual_sameCoordinate_orderTails_not_hasInjectiveRepresentative
    g' k (k + j) N hk0 (by omega) hN (β 0) (-b / β 0) hc
    (div_ne_zero (neg_ne_zero.mpr hb) hc) Ψ model _
    ((hequiv.trans hequiv').hasInjectiveRepresentative hg)
  intro i
  fin_cases i
  · change g'.1.component 0 - coordinatePolynomialAlgHom 2
        (residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 0) ∈
      twoWeightOrderIdeal (k + j) 2 (2 * k + 1)
    have hpoly : residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 0 =
        cyclicAverageInitialPair k j (β 0) b 0 := by
      simpa using residualInitialPair_eq_cyclicAverageInitialPair k j N (β 0) b hc Ψ model 0
    rw [hg'0, hpoly]
    simpa using hfirst 0
  · change g'.1.component 1 - coordinatePolynomialAlgHom 2
        (residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 1) ∈
      twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1)
    have hpoly : residualWeightedInitialPolynomials k (k + j) (β 0) (-b / β 0) Ψ model 1 =
        cyclicAverageInitialPair k j (β 0) b 1 := by
      simpa using residualInitialPair_eq_cyclicAverageInitialPair k j N (β 0) b hc Ψ model 1
    rw [hg'1, hpoly]
    simpa using hfirst 1
  · simpa [H, residualWeightedDegrees, mul_comm] using hg'2

/-- The third component may be any analytic multiple of `y^k`. -/
theorem cyclic_oneVariable_coefficient_not_hasInjectiveRepresentative_of_two_le
    (g : PointedMapGerm 2 3)
    (k p : ℕ) (hk : 2 ≤ k) (hp : 3 ≤ p) (hodd : Odd p)
    (β : Germ 1) (hβ : valueRingHom 1 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p (hyperplaneExtension 1 β))
    (h : Germ 2) (hH : g.1.component 2 = coordinate 1 ^ k * h) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  have hk0 : 0 < k := by omega
  have hβext : valueRingHom 2 (hyperplaneExtension 1 β) ≠ 0 := by
    rw [hyperplaneExtension, PointedMapGerm.valueRingHom_pullback]
    exact hβ
  obtain ⟨q₀, g', hequiv, hg'0, hg'1, htail⟩ :=
    exists_cyclic_normalized_odd_preparation g hg k p hk0 hp hodd
      (hyperplaneExtension 1 β) hβext hP hQ h hH
  obtain ⟨B, hB, hBβ⟩ := exists_cyclicCoefficientGerm_representation β
  have hc : B 0 ≠ 0 := by
    have hvalue : valueRingHom 1 (cyclicCoefficientGerm B hB) = B 0 := rfl
    rw [← hvalue, hBβ]
    exact hβ
  have hNodd : Odd (p + 2 * q₀) := hodd.add_even (even_two_mul q₀)
  apply cyclic_prepared_not_hasInjectiveRepresentative_of_two_le g' k p (p + 2 * q₀)
    hk hp hodd (by omega) hNodd B hB hc (hg'0.trans hP) _ htail
      (hequiv.hasInjectiveRepresentative hg)
  rw [hBβ]
  exact hg'1.trans hQ

/-- The two-variable unit coefficient is normalized by an analytic source
equivalence preserving `x²+y^k` and the ideal generated by `y^k`. -/
theorem cyclic_normal_form_not_hasInjectiveRepresentative_of_two_le
    (g : PointedMapGerm 2 3)
    (k p : ℕ) (hk : 2 ≤ k) (hp : 3 ≤ p) (hodd : Odd p)
    (h₂ h₃ : Germ 2) (hunit : valueRingHom 2 h₂ ≠ 0 ∨ valueRingHom 2 h₃ ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p h₂)
    (hZ : g.1.component 2 = coordinate 1 ^ k * h₃) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  obtain ⟨f, h, hequiv, hh, hf0, hf1, hf2⟩ :=
    exists_cyclic_unit_second_coefficient g k p h₂ h₃ hunit hP hQ hZ
  obtain ⟨e, β, hβ, he0, he1, hideal⟩ :=
    CyclicNormalization.exists_normalization_equiv k p hk hp h hh
  let f' := f.comp e.forward
  have hequiv' : f.RightLeftEquivalent f' := by
    refine ⟨e, PointedEquivGerm.identity 3, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  have hf'0 : f'.1.component 0 = cyclicFirst k := by
    rw [PointedMapGerm.component_comp_eq_pullback, hf0]
    exact he0
  have hf'1 : f'.1.component 1 = cyclicSecond k p (hyperplaneExtension 1 β) := by
    rw [PointedMapGerm.component_comp_eq_pullback, hf1]
    exact he1
  have hf2ideal : f.1.component 2 ∈ Ideal.span {coordinate (1 : Fin 2) ^ k} := by
    rw [Ideal.mem_span_singleton, hf2]
    exact dvd_mul_right _ _
  have hf'2ideal : f'.1.component 2 ∈ Ideal.span {coordinate (1 : Fin 2) ^ k} := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← hideal]
    exact Ideal.mem_map_of_mem e.forward.pullbackRingHom hf2ideal
  rw [Ideal.mem_span_singleton] at hf'2ideal
  obtain ⟨h', hh'⟩ := hf'2ideal
  exact cyclic_oneVariable_coefficient_not_hasInjectiveRepresentative_of_two_le f' k p
    hk hp hodd β (hβ ▸ hh) hf'0 hf'1 h' hh'
      ((hequiv.trans hequiv').hasInjectiveRepresentative hg)

end OnLeConjecture.DTwo
