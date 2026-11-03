/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IdealPreservingWeightedElimination
public import OnLeConjecture.Analytic.AnalyticCoordinateEndomorphism
public import OnLeConjecture.DTwo.ExtremeThetaPreparation
public import OnLeConjecture.DTwo.ExtremeResidualFourier
public import OnLeConjecture.Polynomial.CoordinatePowerDivisibility

/-!
# Ideal-preserving preparation of the extreme residual

The first pair is noninjective by an explicit persistent collision.
Consequently an injective triple has its third component outside the pair
image ring. Finite filtered elimination preserves the fourth-power
ramified coordinate ideal and constructs a nonbase initial residual.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def extremeInitialPair (a : ℕ) :
    Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ (2 * a),
    2 * MvPolynomial.X 0 ^ 3 + 3 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a)]

theorem extremeInitialPair_homogeneous (a : ℕ) (i : Fin 2) :
    (extremeInitialPair a i).IsWeightedHomogeneous ![a, 1] (![2 * a, 3 * a] i) := by
  fin_cases i
  · exact extremeMonomial_homogeneous a 1 1 0
  · exact extremeMonomial_homogeneous a 1 1 1

theorem extreme_pair_not_hasInjectiveRepresentative
    (f : PointedMapGerm 2 2) (a : ℕ) (ha : 0 < a)
    (htail : ∀ i, f.1.component i - coordinatePolynomialAlgHom 2 (extremeInitialPair a i) ∈
      weightedOrderIdeal a (![2 * a, 3 * a] i + 1)) :
    ¬ f.HasInjectiveRepresentative := by
  obtain ⟨g, hg⟩ := PointedMapGerm.exists_with_components
    (![f.1.component 0, f.1.component 1, coordinate 1] : Fin 3 → Germ 2) (by
      intro i
      fin_cases i
      · change f.1.component 0 ∈ maximalIdeal 2
        rw [mem_maximalIdeal_iff, MapGerm.valueRingHom_component, f.2]; rfl
      · change f.1.component 1 ∈ maximalIdeal 2
        rw [mem_maximalIdeal_iff, MapGerm.valueRingHom_component, f.2]; rfl
      · exact coordinate_mem_maximalIdeal 1)
  have hpair : g.firstTwo = f := by
    apply PointedMapGerm.ext_components
    intro i
    fin_cases i
    · rw [PointedMapGerm.firstTwo_component]
      exact hg 0
    · rw [PointedMapGerm.firstTwo_component]
      exact hg 1
  have hnon : ¬ g.HasInjectiveRepresentative := by
    apply extremeMonomial_orderTails_not_hasInjectiveRepresentative g a 1 ha one_pos 1 one_ne_zero
    intro i
    fin_cases i
    · change g.1.component 0 - coordinatePolynomialAlgHom 2 (extremeInitialPair a 0) ∈ _
      rw [hg 0]
      exact htail 0
    · change g.1.component 1 - coordinatePolynomialAlgHom 2 (extremeInitialPair a 1) ∈ _
      rw [hg 1]
      exact htail 1
    · change g.1.component 2 - coordinatePolynomialAlgHom 2
        (extremeMonomialPolynomials a 1 1 2) ∈ _
      rw [hg 2]
      simp [extremeMonomialPolynomials]
  intro hf
  apply hnon
  apply PointedMapGerm.hasInjectiveRepresentative_of_comp PointedMapGerm.firstTwoProjection g
  have hproj : PointedMapGerm.firstTwoProjection.comp g = g.firstTwo := by
    apply PointedMapGerm.ext_components
    intro i
    rw [PointedMapGerm.component_comp_eq_pullback, PointedMapGerm.firstTwoProjection_component,
      PointedMapGerm.pullback_coordinate, PointedMapGerm.firstTwo_component]
  rwa [hproj, hpair]

theorem extreme_prepared_pair_tails
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a) (C₂ : Germ 2)
    (hP : g.1.component 0 = cyclicFirst (2 * a))
    (hQ : g.1.component 1 = extremeTheta (2 * a) + coordinate 1 ^ (4 * a) * C₂) :
    (∀ i, g.firstTwo.1.component i - coordinatePolynomialAlgHom 2 (extremeInitialPair a i) ∈
      weightedOrderIdeal a (![2 * a, 3 * a] i + 1)) ∧
    (∀ i, coordinate (1 : Fin 2) ^ (4 * a) ∣
      g.firstTwo.1.component i - coordinatePolynomialAlgHom 2 (extremeInitialPair a i)) := by
  have hp : coordinatePolynomialAlgHom 2 (extremeInitialPair a 0) = cyclicFirst (2 * a) := by
    simp [extremeInitialPair, cyclicFirst]
  have hq : coordinatePolynomialAlgHom 2 (extremeInitialPair a 1) = extremeTheta (2 * a) := by
    simp [extremeInitialPair, extremeTheta_eq, map_ofNat]
  have hcoord0 : g.firstTwo.1.component 0 = g.1.component 0 :=
    PointedMapGerm.firstTwo_component g 0
  have hcoord1 : g.firstTwo.1.component 1 = g.1.component 1 :=
    PointedMapGerm.firstTwo_component g 1
  have hfirst : g.firstTwo.1.component 0 - coordinatePolynomialAlgHom 2
      (extremeInitialPair a 0) = 0 := by rw [hcoord0, hP, hp, sub_self]
  have hsecond : g.firstTwo.1.component 1 - coordinatePolynomialAlgHom 2
      (extremeInitialPair a 1) = coordinate 1 ^ (4 * a) * C₂ := by
    rw [hcoord1, hQ, hq, add_sub_cancel_left]
  constructor
  · intro i
    fin_cases i
    · change g.firstTwo.1.component 0 - coordinatePolynomialAlgHom 2
        (extremeInitialPair a 0) ∈ _
      rw [hfirst]; exact Ideal.zero_mem _
    · change g.firstTwo.1.component 1 - coordinatePolynomialAlgHom 2
        (extremeInitialPair a 1) ∈ _
      rw [hsecond]
      apply Ideal.mul_mem_right
      simpa using monomial_mem_weightedOrderIdeal_of_threshold a (3 * a + 1) 0 (4 * a)
        ha (by omega)
  · intro i
    fin_cases i
    · change coordinate (1 : Fin 2) ^ (4 * a) ∣ g.firstTwo.1.component 0 -
        coordinatePolynomialAlgHom 2 (extremeInitialPair a 0)
      rw [hfirst]; exact dvd_zero _
    · change coordinate (1 : Fin 2) ^ (4 * a) ∣ g.firstTwo.1.component 1 -
        coordinatePolynomialAlgHom 2 (extremeInitialPair a 1)
      rw [hsecond]; exact dvd_mul_right _ _

/-- The original finite prepared pair and injectivity construct all
residual data, including the analytic target change and divisibility. -/
theorem exists_extreme_ideal_preserving_residual
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (hfinite : g.firstTwo.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a) (C₂ C₃ : Germ 2)
    (hP : g.1.component 0 = cyclicFirst (2 * a))
    (hQ : g.1.component 1 = extremeTheta (2 * a) + coordinate 1 ^ (4 * a) * C₂)
    (hZ : g.1.component 2 = coordinate 1 ^ (4 * a) * C₃) :
    ∃ f : PointedMapGerm 2 3, ∃ D : ℕ, ∃ R : MvPolynomial (Fin 2) ℂ, ∃ C : Germ 2,
      g.RightLeftEquivalent f ∧ f.1.component 0 = g.1.component 0 ∧
      f.1.component 1 = g.1.component 1 ∧
      f.1.component 2 = coordinate 1 ^ (4 * a) * C ∧
      4 * a ≤ D ∧ R ≠ 0 ∧ R.IsWeightedHomogeneous ![a, 1] D ∧
      MvPolynomial.X (1 : Fin 2) ^ (4 * a) ∣ R ∧
      R ∉ Set.range (MvPolynomial.aeval (extremeInitialPair a) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
      ∀ i, f.1.component i - coordinatePolynomialAlgHom 2 (extremeResidualPolynomialMap a R i) ∈
        weightedOrderIdeal a (![2 * a, 3 * a, D] i + 1) := by
  obtain ⟨htail, hmod⟩ := extreme_prepared_pair_tails g a ha C₂ hP hQ
  have hpair := extreme_pair_not_hasInjectiveRepresentative g.firstTwo a ha htail
  have hnot := g.third_not_mem_imageRing_firstTwo_of_injective hg hpair
  obtain ⟨D, q, R, hqdiv, hremdiv, hRne, hRhom, _, hRtail, hRdiv, hRbase⟩ :=
    g.firstTwo.exists_ideal_preserving_initial_form_outside_pair_algebra hfinite
      a (4 * a) ha ![2 * a, 3 * a] (extremeInitialPair a) (extremeInitialPair_homogeneous a)
      htail hmod (g.1.component 2) (by rw [hZ]; exact dvd_mul_right _ _) hnot
  have hq : q ∈ maximalIdeal 2 := by
    obtain ⟨C, hC⟩ := hqdiv
    rw [mem_maximalIdeal_iff, ← PointedMapGerm.valueRingHom_pullback g.firstTwo, hC,
      map_mul, map_pow, valueRingHom_coordinate, zero_pow (by omega), zero_mul]
  obtain ⟨f, hgf, hf0, hf1, hf2⟩ := g.exists_target_subtraction q hq
  obtain ⟨C, hC⟩ := hremdiv
  have hD : 4 * a ≤ D := by
    obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.coeff d R ≠ 0 := by
      by_contra! hall
      apply hRne
      ext d
      simpa using hall d
    have hd1 : 4 * a ≤ d 1 := by
      by_contra hh
      exact hd ((OnLeConjecture.Polynomial.variable_pow_dvd_iff_coeff_eq_zero
        1 (4 * a) R).mp hRdiv d (by omega))
    have hweight : a * d 0 + d 1 = D := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hRhom hd
    omega
  refine ⟨f, D, R, C, hgf, hf0, hf1, hf2.trans hC, hD, hRne, hRhom, hRdiv,
    hRbase, ?_⟩
  intro i
  fin_cases i
  · change f.1.component 0 - coordinatePolynomialAlgHom 2 (extremeInitialPair a 0) ∈ _
    rw [hf0]
    have hh := htail 0
    rw [PointedMapGerm.firstTwo_component] at hh
    exact hh
  · change f.1.component 1 - coordinatePolynomialAlgHom 2 (extremeInitialPair a 1) ∈ _
    rw [hf1]
    have hh := htail 1
    rw [PointedMapGerm.firstTwo_component] at hh
    exact hh
  · change f.1.component 2 - coordinatePolynomialAlgHom 2 R ∈ _
    rw [hf2]
    exact hRtail

end OnLeConjecture.DTwo
