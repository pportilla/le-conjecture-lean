/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicOppositeCollision
public import OnLeConjecture.Analytic.TwoWeightPolynomialComposition
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction

/-!
# Analytic preparation in the invariant cyclic branch

Opposite-sign collisions exclude nonzero roots of the odd coefficient.
The resulting pure odd initial remainder follows from actual injectivity,
not from an assumed root restriction.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

theorem cyclicInvariantLift_homogeneous (k p N : ℕ)
    (F : MvPolynomial (Fin 2) ℂ) (hF : F.IsWeightedHomogeneous ![1, p] N) :
    (cyclicInvariantLift k F).IsWeightedHomogeneous ![k, p] (k * N) := by
  rw [cyclicInvariantLift, aeval_eq_bind₁]
  apply OnLeConjecture.Analytic.MvPolynomial.IsWeightedHomogeneous.bind₁_scaled hF
  intro i
  fin_cases i
  · simpa using isWeightedHomogeneous_X ℂ (![k, p] : Fin 2 → ℕ) 0
  · simpa [nsmul_eq_mul, mul_comm] using
      (isWeightedHomogeneous_X ℂ (![k, p] : Fin 2 → ℕ) 1).pow k

theorem cyclicInvariantLift_base (k p : ℕ) (c : ℂ) (A : MvPolynomial (Fin 2) ℂ) :
    cyclicInvariantLift k (cyclicInvariantBaseHom p c A) =
      aeval (cyclicInitialPair k p c) A := by
  rw [cyclicInvariantLift, cyclicInvariantBaseHom, comp_aeval_apply]
  apply congrArg (fun g : Fin 2 → MvPolynomial (Fin 2) ℂ ↦ aeval g A)
  funext i
  fin_cases i <;> simp [cyclicInitialPair]

/-- Strict two weight tails at a nonzero opposite-sign residual root
prevent local injectivity, including when its second `y` coordinate is zero. -/
theorem cyclicOppositeTails_not_hasInjectiveRepresentative
    (k p D : ℕ) (hk : 0 < k) (hp : Odd p) (c s : ℂ) (hc : c ≠ 0) (hs : s ≠ 0)
    (F A B : MvPolynomial (Fin 2) ℂ)
    (hdecomp : F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B)
    (hR : (cyclicInvariantLift k F).IsWeightedHomogeneous ![k, p] D)
    (hF : cyclicOddRestriction p c B ≠ 0) (hroot : (cyclicOddRestriction p c B).IsRoot s)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0) (hzero : representative 0 = 0)
    (htail : ∀ i, pairRepresentativeComponentGerm representative hanalytic i -
      Germ.coordinatePolynomialAlgHom 2
        (cyclicResidualPolynomialMap k p c (cyclicInvariantLift k F) i) ∈
          Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨Y, hYpow⟩ := IsAlgClosed.exists_pow_nat_eq (1 + 2 * s ^ p / c) hk
  have hY : 2 * s ^ p = c * (Y ^ k - 1) := by
    rw [hYpow]
    field_simp
    ring
  have hYone : Y ≠ 1 := by
    intro h
    have hsp : 2 * s ^ p = 0 := by simpa [h] using hY
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hs) hsp
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
      k p hk hp.pos ![2 * k, p * k, D]
      (cyclicResidualPolynomialMap k p c (cyclicInvariantLift k F))
      (cyclicResidualPolynomialMap_homogeneous k p D c _ hR)
      representative hanalytic htail
  simp only [weightedPolynomialMap_cyclicResidualPolynomialMap] at hexpansion
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_twoWeightChartZeros
    k p ![2 * k, p * k, D] (cyclicResidualInitialMap k p c (cyclicInvariantLift k F))
    representative remainder s (-s) Y hk hp.pos hYone
    (hexpansion (s, 1)) (hexpansion (-s, Y))
  intro U hU
  apply eventually_exists_cyclicOppositeZero_mem_nhds
    (weightedRescaledPerturbation
      (cyclicResidualInitialMap k p c (cyclicInvariantLift k F)) remainder)
    k p hk hp c s Y hc hs hY F A B hdecomp hF hroot ?_ ?_ U hU
  · apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_cyclicResidualInitialDifference k p c _ _
    · exact (hexpansion (s, 1)).remainder_analyticAt
    · exact (hexpansion (-s, Y)).remainder_analyticAt
  · intro q
    exact weightedRescaledPerturbation_zero _ _ q

/-- Injectivity of the actual analytic triple excludes every nonzero root
of the nonzero homogeneous odd coefficient restricted to `(s²,sᵖ+c)`. -/
theorem cyclicInvariant_oddRestriction_no_nonzero_roots_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p D E : ℕ) (hk : 0 < k) (hp : Odd p) (c : ℂ) (hc : c ≠ 0)
    (F A B : MvPolynomial (Fin 2) ℂ)
    (hdecomp : F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B)
    (hR : (cyclicInvariantLift k F).IsWeightedHomogeneous ![k, p] D)
    (hB : B.IsWeightedHomogeneous ![2, p] E) (hBzero : B ≠ 0)
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c (cyclicInvariantLift k F) i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] i + 1)) :
    ∀ s : ℂ, (cyclicOddRestriction p c B).eval s = 0 → s = 0 := by
  intro s hs
  by_contra hsne
  have hrestriction := cyclicOddRestriction_ne_zero p E hp c hc B hB hBzero
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  apply cyclicOppositeTails_not_hasInjectiveRepresentative k p D hk hp c s hc hsne
    F A B hdecomp hR hrestriction hs representative hanalytic hzero
    (fun i ↦ by rw [hcomponents i]; exact htail i)
  rw [← heq]
  exact hg

/-- An invariant initial form outside the pair algebra has a pure odd
remainder after polynomial target subtraction. All root restrictions are
deduced from injectivity and the actual analytic tails. -/
theorem cyclicInvariant_pure_odd_initial_remainder_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p N₀ : ℕ) (hk : 0 < k) (hp : Odd p) (hN₀ : 0 < N₀)
    (c : ℂ) (hc : c ≠ 0) (Λ : MvPolynomial (Fin 2) ℂ)
    (hΛ : Λ.IsWeightedHomogeneous ![1, p] N₀)
    (hbase : cyclicInvariantLift k (X 1 * Λ) ∉ Set.range
      (aeval (cyclicInitialPair k p c) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ))
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c (cyclicInvariantLift k (X 1 * Λ)) i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, k * (N₀ + p)] i + 1)) :
    ∃ A B : MvPolynomial (Fin 2) ℂ, ∃ κ : ℂ, ∃ r q₀ : ℕ,
      A.IsWeightedHomogeneous ![2, p] (N₀ + p) ∧
      B.IsWeightedHomogeneous ![2, p] (N₀ + p - 1) ∧ B ≠ 0 ∧
      κ ≠ 0 ∧ 0 < q₀ ∧ N₀ = 2 * q₀ ∧ 2 * r = N₀ + p - 1 ∧
      B = C κ * X 0 ^ r ∧
      cyclicInvariantLift k (X 1 * Λ) - aeval (cyclicInitialPair k p c) A =
        C κ * X 0 ^ (p + N₀) := by
  have hFbase : X 1 * Λ ∉ Set.range (cyclicInvariantBaseHom p c) := by
    rintro ⟨A, hA⟩
    apply hbase
    refine ⟨A, ?_⟩
    rw [← cyclicInvariantLift_base, hA]
  obtain ⟨A, B, hA, hB, hBzero, hdecomp⟩ :=
    cyclicInvariant_t_mul_nonbase_decomposition p N₀ hp c hc Λ hΛ hFbase
  have hF : (X 1 * Λ).IsWeightedHomogeneous ![1, p] (N₀ + p) := by
    simpa [Nat.add_comm] using (isWeightedHomogeneous_X ℂ ![1, p] 1).mul hΛ
  have hroots := cyclicInvariant_oddRestriction_no_nonzero_roots_of_injective
    g hg k p (k * (N₀ + p)) (N₀ + p - 1) hk hp c hc _ A B hdecomp
    (cyclicInvariantLift_homogeneous k p (N₀ + p) _ hF) hB hBzero htail
  obtain ⟨κ, r, q₀, hκ, hq₀, hN₀eq, hr, hBeq, hrem⟩ :=
    cyclicInvariant_pure_odd_remainder p N₀ hp hN₀ c hc Λ A B hB hdecomp hroots
  refine ⟨A, B, κ, r, q₀, hA, hB, hBzero, hκ, hq₀, hN₀eq, hr, hBeq, ?_⟩
  have hlift := congrArg (cyclicInvariantLift k) hrem
  change aeval _ (X 1 * Λ - cyclicInvariantBaseHom p c A) = _ at hlift
  rw [map_sub] at hlift
  change cyclicInvariantLift k (X 1 * Λ) -
    cyclicInvariantLift k (cyclicInvariantBaseHom p c A) =
      cyclicInvariantLift k (C κ * X 0 ^ (p + N₀)) at hlift
  rw [cyclicInvariantLift_base] at hlift
  have hmonomial : cyclicInvariantLift k (C κ * X 0 ^ (p + N₀)) =
      C κ * X 0 ^ (p + N₀) := by simp [cyclicInvariantLift]
  rw [hmonomial] at hlift
  exact hlift

/-- In the invariant branch, actual pointed analytic target subtraction
produces a pure odd initial third coordinate and preserves injectivity. -/
theorem cyclicInvariant_analytic_pure_odd_preparation
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p N₀ : ℕ) (hk : 0 < k) (hp : Odd p) (hN₀ : 0 < N₀)
    (c : ℂ) (hc : c ≠ 0) (Λ : MvPolynomial (Fin 2) ℂ)
    (hΛ : Λ.IsWeightedHomogeneous ![1, p] N₀)
    (hbase : cyclicInvariantLift k (X 1 * Λ) ∉ Set.range
      (aeval (cyclicInitialPair k p c) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ))
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c (cyclicInvariantLift k (X 1 * Λ)) i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, k * (N₀ + p)] i + 1)) :
    ∃ g' : PointedMapGerm 2 3, ∃ κ : ℂ, ∃ q₀ : ℕ,
      g.RightLeftEquivalent g' ∧ g'.HasInjectiveRepresentative ∧
      g'.1.component 0 = g.1.component 0 ∧ g'.1.component 1 = g.1.component 1 ∧
      κ ≠ 0 ∧ 0 < q₀ ∧ N₀ = 2 * q₀ ∧
      g'.1.component 2 - Germ.coordinatePolynomialAlgHom 2
        (C κ * X 0 ^ (p + 2 * q₀)) ∈
          Germ.twoWeightOrderIdeal k p (k * (p + 2 * q₀) + 1) := by
  obtain ⟨A, B, κ, r, q₀, hA, _, _, hκ, hq₀, hN₀eq, _, _, hrem⟩ :=
    cyclicInvariant_pure_odd_initial_remainder_of_injective
      g hg k p N₀ hk hp hN₀ c hc Λ hΛ hbase htail
  have hAscale : A.IsWeightedHomogeneous ![2 * k, p * k] (k * (N₀ + p)) := by
    intro d hd
    have hweight : 2 * d 0 + p * d 1 = N₀ + p := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hA hd
    have hscaled : (2 * k) * d 0 + (p * k) * d 1 = k * (N₀ + p) := by
      calc
        (2 * k) * d 0 + (p * k) * d 1 = k * (2 * d 0 + p * d 1) := by ring
        _ = _ := by rw [hweight]
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hscaled
  let correction := Germ.coordinatePolynomialAlgHom 2 A
  have hcorrection : correction ∈ Germ.maximalIdeal 2 := by
    rw [← Germ.twoWeightOrderIdeal_one_eq_maximalIdeal 2 p (by omega) hp.pos]
    exact Germ.twoWeightOrderIdeal_antitone 2 p 1 (N₀ + p) (by omega) hp.pos (by omega)
      (Germ.coordinatePolynomial_mem_twoWeightOrderIdeal 2 p (N₀ + p) (by omega) hp.pos hA)
  have hpairtail : ∀ i, g.firstTwo.1.component i - Germ.coordinatePolynomialAlgHom 2
      (cyclicInitialPair k p c i) ∈ Germ.twoWeightOrderIdeal k p (![2 * k, p * k] i + 1) := by
    intro i
    fin_cases i
    · simpa [cyclicResidualPolynomialMap] using htail 0
    · simpa [cyclicResidualPolynomialMap] using htail 1
  have hcomposition := Germ.twoWeight_polynomial_expression_initial_form
    k p hk hp.pos ![2 * k, p * k] (fun i ↦ g.firstTwo.1.component i)
    (cyclicInitialPair k p c) (cyclicInitialPair_homogeneous k p c) hpairtail hAscale
  have hpull : g.firstTwo.pullbackRingHom correction =
      aeval (fun i ↦ g.firstTwo.1.component i) A := by
    rw [Germ.PointedMapGerm.pullback_coordinatePolynomialAlgHom]
    rfl
  rw [← hpull] at hcomposition
  have hthird : g.1.component 2 - g.firstTwo.pullbackRingHom correction -
      Germ.coordinatePolynomialAlgHom 2 (C κ * X 0 ^ (p + N₀)) ∈
        Germ.twoWeightOrderIdeal k p (k * (N₀ + p) + 1) := by
    have h := (Germ.twoWeightOrderIdeal k p (k * (N₀ + p) + 1)).sub_mem
      (htail 2) hcomposition
    change g.1.component 2 - Germ.coordinatePolynomialAlgHom 2
      (cyclicInvariantLift k (X 1 * Λ)) -
        (g.firstTwo.pullbackRingHom correction -
          Germ.coordinatePolynomialAlgHom 2 (aeval (cyclicInitialPair k p c) A)) ∈ _ at h
    have heq := congrArg (Germ.coordinatePolynomialAlgHom 2) hrem
    rw [map_sub] at heq
    rw [← heq]
    convert h using 1
    ring
  obtain ⟨g', hequivalent, hzero, hone, htwo⟩ := g.exists_target_subtraction correction hcorrection
  refine ⟨g', κ, q₀, hequivalent, hequivalent.hasInjectiveRepresentative hg,
    hzero, hone, hκ, hq₀, hN₀eq, ?_⟩
  rw [htwo]
  simpa only [hN₀eq, Nat.add_comm] using hthird

end OnLeConjecture.DTwo
