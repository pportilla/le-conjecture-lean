/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightRotationNoninjectivity
public import OnLeConjecture.Analytic.SimpleZeroPersistence
public import OnLeConjecture.DThree.PairRepresentativeComponents

/-!
# Simple collisions with two positive source weights

The implicit function theorem constructs persistent chart zeros from an
invertible derivative of the initial difference. Strict weighted tails
then give collisions of the actual analytic germ.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DThree

theorem eventually_exists_weighted_simple_collision
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ) (p : Fin 3 → ℂ)
    (hinitial : AnalyticAt ℂ (weightedInitialDifference initialMap) p)
    (hzero : weightedInitialDifference initialMap p = 0)
    (D : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))
    (hD : HasStrictFDerivAt (weightedInitialDifference initialMap) D p)
    (hinvertible : D.IsInvertible)
    (hfirst : AnalyticAt ℂ remainder (0, residueFirstChartPoint p))
    (hsecond : AnalyticAt ℂ remainder (0, residueSecondChartPoint p))
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, p)) :
    ∀ᶠ tau in nhds 0, ∃ q : Fin 3 → ℂ,
      (tau, q) ∈ U ∧ weightedRescaledPerturbation initialMap remainder (tau, q) = 0 := by
  let Phi := weightedRescaledPerturbation initialMap remainder
  have hPhi : AnalyticAt ℂ Phi (0, p) :=
    analyticAt_weightedRescaledPerturbation initialMap remainder p hinitial hfirst hsecond
  have hpoint : (fderiv ℂ Phi (0, p) ∘L
      ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ)).IsInvertible := by
    rw [fderiv_weightedRescaledPerturbation_point initialMap remainder p D hPhi hD]
    exact hinvertible
  obtain ⟨branch, _, hbranch, hzeros⟩ := exists_simpleZeroBranch Phi p
    (fderiv ℂ Phi (0, p)) (by simpa only [Phi, weightedRescaledPerturbation_zero] using hzero)
    hPhi.hasStrictFDerivAt hpoint
  have hmem := (tendsto_id.prodMk_nhds hbranch).eventually hU
  filter_upwards [hmem, hzeros] with tau hm hz
  exact ⟨branch tau, hm, hz⟩

/-- Strict polynomial tails and an invertible initial chart derivative
exclude injectivity. Both radial weights may be arbitrary positive
integers. -/
theorem twoWeight_simple_collision_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (degrees : Fin 3 → ℕ) (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, b] (degrees i))
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2 (P i) ∈
      Germ.twoWeightOrderIdeal a b (degrees i + 1))
    (x X zeta : ℂ) (hseparate : x ≠ X ∨ zeta ≠ 1)
    (hinitial : AnalyticAt ℂ (weightedInitialDifference (weightedPolynomialMap P)) ![x, X, zeta])
    (hzero : weightedInitialDifference (weightedPolynomialMap P) ![x, X, zeta] = 0)
    (D : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))
    (hD : HasStrictFDerivAt (weightedInitialDifference (weightedPolynomialMap P)) D ![x, X, zeta])
    (hinvertible : D.IsInvertible) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hrepzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal a b ha hb degrees P hP
      representative hanalytic (fun i => by rw [hcomponents i]; exact htail i)
  rw [heq]
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_twoWeightSeparatedChartZeros a b degrees
    (weightedPolynomialMap P) representative remainder x X zeta ha hb hseparate
    (hexpansion (x, 1)) (hexpansion (X, zeta))
  apply eventually_exists_weighted_simple_collision _ _ _ hinitial hzero D hD hinvertible
  · simpa [residueFirstChartPoint] using
      (hexpansion (x, 1)).remainder_analyticAt
  · simpa [residueSecondChartPoint] using
      (hexpansion (X, zeta)).remainder_analyticAt

end OnLeConjecture.Analytic
