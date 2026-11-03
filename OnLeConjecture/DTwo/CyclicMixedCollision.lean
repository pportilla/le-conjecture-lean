/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicCrossingElimination

/-!
# Exclusion of mixed cyclic residuals with positive first exponent

The isolated crossing persists for all strictly higher weighted analytic
terms. The remaining mixed alternative retains a noninvariant monomial
with first exponent zero.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

/-- A mixed residual with positive first exponent forces collisions of
the analytic germ, including all its strictly higher weighted terms. -/
theorem cyclicMixedPositive_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (k p i j d D : ℕ)
    (hk : 0 < k) (hp : Odd p) (hi : 0 < i) (hj : ¬ k ∣ j)
    (hdegree : k * i + p * j = k * d)
    (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 0 ^ i * X 1 ^ j))
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨ζ, Y, hζzero, hζone, hζ, hY, hYzero, hYplane, hplus, hminus⟩ :=
    exists_cyclicMixed_crossing_branches k p i j d hk hp hj hdegree
      c γ hc hγ L hL R hfactor
  have hRzero : eval ![0, 1] R - eval ![0, ζ] R = 0 := by
    rw [hfactor]
    simp [cyclicInvariantLift_eval, hζ, zero_pow hi.ne']
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
      k p hk hp.pos ![2 * k, p * k, D] (cyclicResidualPolynomialMap k p c R)
      (cyclicResidualPolynomialMap_homogeneous k p D c R hR)
      representative hanalytic (fun index ↦ by rw [hcomponents index]; exact htail index)
  simp only [weightedPolynomialMap_cyclicResidualPolynomialMap] at hexpansion
  rw [heq]
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_twoWeightChartZeros
    k p ![2 * k, p * k, D] (cyclicResidualInitialMap k p c R)
    representative remainder 0 0 ζ hk hp.pos hζone (hexpansion (0, 1)) (hexpansion (0, ζ))
  intro U hU
  apply eventually_exists_cyclicCrossingZero_mem_nhds
    (weightedRescaledPerturbation (cyclicResidualInitialMap k p c R) remainder)
    k p hk hp.pos c ζ hc hζzero hζ R ?_ ?_ Y hY hYzero hYplane hRzero hplus hminus U hU
  · apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_cyclicResidualInitialDifference k p c R _
    · exact (hexpansion (0, 1)).remainder_analyticAt
    · exact (hexpansion (0, ζ)).remainder_analyticAt
  · intro q
    exact weightedRescaledPerturbation_zero _ _ q

/-- Invariant degree descent and injectivity force first exponent zero
in the mixed alternative extracted by ideal-preserving elimination. -/
theorem cyclicMixed_first_exponent_eq_zero
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p i j E D : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : k * i + p * j = E)
    (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (R Λinv : MvPolynomial (Fin 2) ℂ)
    (hinv : Λinv ∈ cyclicInvariantAlgebra k)
    (hinvHom : Λinv.IsWeightedHomogeneous ![k, p] E) (hinvZero : Λinv ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (Λinv + C γ * X 0 ^ i * X 1 ^ j))
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) : i = 0 := by
  obtain ⟨d, L, _, hL, hE, hΛinv⟩ :=
    exists_cyclicInvariant_homogeneous_descent k p E hk Λinv hinvZero hinvHom hinv
  by_contra hi
  exact cyclicMixedPositive_not_hasInjectiveRepresentative g k p i j d D hk hp
    (Nat.pos_of_ne_zero hi) hj (hdegree.trans hE) c γ hc hγ L R hL hR
    (by simpa only [hΛinv] using hfactor) htail hg

/-- The mixed alternative with first exponent zero, retaining the full
analytic elimination data and its nonzero invariant polynomial. -/
@[expose] def CyclicMixedZeroResidual (g : PointedMapGerm 2 3) (k p : ℕ) (c : ℂ) : Prop :=
  ∃ g' : PointedMapGerm 2 3, ∃ D : ℕ, ∃ h : Germ 2,
    ∃ R Λ Λinv : MvPolynomial (Fin 2) ℂ, ∃ j : ℕ, ∃ γ : ℂ,
      g.RightLeftEquivalent g' ∧ g'.HasInjectiveRepresentative ∧
      g'.1.component 0 = g.1.component 0 ∧ g'.1.component 1 = g.1.component 1 ∧
      h ∈ Germ.maximalIdeal 2 ∧ h ≠ 0 ∧
      g'.1.component 2 = Germ.coordinate 1 ^ k * h ∧
      p * k < D ∧ R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      Germ.coordinate 1 ^ k * h ∈ Germ.twoWeightOrderIdeal k p D ∧
      Germ.coordinate 1 ^ k * h - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      R ∉ Set.range (aeval (cyclicInitialPair k p c) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
      Λ ≠ 0 ∧ Λ.IsWeightedHomogeneous ![k, p] (D - p * k) ∧ R = X 1 ^ k * Λ ∧
      Λinv ∈ cyclicInvariantAlgebra k ∧ Λinv.IsWeightedHomogeneous ![k, p] (D - p * k) ∧
      γ ≠ 0 ∧ ¬ k ∣ j ∧ p * j = D - p * k ∧
      Λ = Λinv + C γ * X 1 ^ j ∧ Λinv ≠ 0

/-- The prepared analytic pair excludes every positive first exponent
from the mixed residual alternative. -/
theorem cyclic_mixed_residual_has_zero_first_exponent
    (g : PointedMapGerm 2 3) (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p)
    (β : Germ 2) (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (hresidual : CyclicMixedResidual g k p (Germ.valueRingHom 2 β)) :
    CyclicMixedZeroResidual g k p (Germ.valueRingHom 2 β) := by
  obtain ⟨g', D, h, R, Λ, Λinv, i, j, γ, hequiv, hg', hzero, hone,
    hh, hhzero, hthird, hD, hRzero, hR, horder, htail, hbase, hΛzero, hΛ, hfactor,
    hinv, hinvHom, hγ, hj, hdegree, hΛeq, hinvZero⟩ := hresidual
  have hpairtail := cyclic_pair_strict_tails g'.firstTwo k p hk hp β
    (by simpa using hzero.trans hP) (by simpa using hone.trans hQ)
  have htriple : ∀ index, g'.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p (Germ.valueRingHom 2 β) R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1) := by
    intro index
    fin_cases index
    · simpa [cyclicResidualPolynomialMap] using hpairtail 0
    · simpa [cyclicResidualPolynomialMap] using hpairtail 1
    · change g'.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1)
      rw [hthird]
      exact htail
  have hi := cyclicMixed_first_exponent_eq_zero g' hg' k p i j (D - p * k) D
    hk hodd hj hdegree (Germ.valueRingHom 2 β) γ hβ hγ R Λinv hinv hinvHom hinvZero
    hR (hfactor.trans (by rw [hΛeq])) htriple
  subst i
  refine ⟨g', D, h, R, Λ, Λinv, j, γ, hequiv, hg', hzero, hone,
    hh, hhzero, hthird, hD, hRzero, hR, horder, htail, hbase, hΛzero, hΛ, hfactor,
    hinv, hinvHom, hγ, hj, ?_, ?_, hinvZero⟩
  · simpa only [mul_zero, zero_add] using hdegree
  · simpa only [pow_zero, mul_one] using hΛeq

/-- The original prepared germ has pure odd preparation or a mixed
residual whose noninvariant monomial involves only the second variable. -/
theorem cyclic_preparation_pure_odd_or_mixed_zero
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hH : g.1.component 2 = Germ.coordinate 1 ^ k * h) :
    CyclicPureOddPreparation g k p ∨ CyclicMixedZeroResidual g k p (Germ.valueRingHom 2 β) := by
  rcases cyclic_preparation_pure_odd_or_mixed g hg k p hk hp hodd β hβ hP hQ h hh hH with
    hpure | hresidual
  · exact Or.inl hpure
  · exact Or.inr
      (cyclic_mixed_residual_has_zero_first_exponent g k p hk hp hodd β hβ hP hQ hresidual)

end OnLeConjecture.DTwo
