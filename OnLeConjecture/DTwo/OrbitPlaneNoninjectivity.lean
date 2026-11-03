/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitCollisionPersistence
public import OnLeConjecture.DThree.OrdinaryOrderExpansion
public import OnLeConjecture.DThree.PairRepresentativeComponents
public import OnLeConjecture.DThree.WeightedResidueNoninjectivity

/-!
# Noninjectivity of the analytic quadratic orbit pair

The quadratic and cubic orbit forms have a pair of distinct points in one
fibre. The derivative in the second point is invertible. The implicit
function theorem therefore preserves a collision after analytic terms of
higher ordinary order are added to the two forms.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- The first two analytic coordinates with orbit initial forms cannot be
locally injective. -/
theorem orbitPlane_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 2)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨representative, hanalytic, hzero, hg⟩ :=
    g.exists_ofPairFunction
  let extended : ℂ × ℂ → Fin 3 → ℂ := fun z ↦
    ![representative z 0, representative z 1, 0]
  have hextendedAnalytic : AnalyticAt ℂ extended 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact analyticAt_pi_iff.mp hanalytic 0
    · exact analyticAt_pi_iff.mp hanalytic 1
    · exact analyticAt_const
  have hextendedZero : extended 0 = 0 := by
    funext i
    fin_cases i
    all_goals simp [extended, hzero]
  have hcomponentZero :
      pairRepresentativeComponentGerm extended hextendedAnalytic 0 =
        g.1.component 0 := by
    rw [hg]
    apply Subtype.ext
    simp [pairRepresentativeComponentGerm, extended,
      PointedMapGerm.ofPairFunction, PointedMapGerm.ofFunction]
  have hcomponentOne :
      pairRepresentativeComponentGerm extended hextendedAnalytic 1 =
        g.1.component 1 := by
    rw [hg]
    apply Subtype.ext
    simp [pairRepresentativeComponentGerm, extended,
      PointedMapGerm.ofPairFunction, PointedMapGerm.ofFunction]
  have hcomponentTwo :
      pairRepresentativeComponentGerm extended hextendedAnalytic 2 = 0 := by
    apply Subtype.ext
    change ((fun _ : Source 2 ↦ (0 : ℂ)) : FunctionGerm 2) = 0
    exact Filter.Germ.coe_zero
  have htail : ∀ i,
      pairRepresentativeComponentGerm extended hextendedAnalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (orbitInitialPolynomialMap (0 : OrbitSourceForm) i) ∈
        Germ.weightedOrderIdeal 1 (orbitInitialDegrees 4 i + 1) := by
    intro i
    rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow]
    fin_cases i
    · simpa [orbitInitialPolynomialMap, orbitInitialDegrees,
        hcomponentZero] using hphi
    · simpa [orbitInitialPolynomialMap, orbitInitialDegrees,
        hcomponentOne] using hpsi
    · simp [orbitInitialPolynomialMap, orbitInitialDegrees, hcomponentTwo]
  have hzeroHomogeneous :
      (0 : OrbitSourceForm).IsHomogeneous 4 :=
    MvPolynomial.isHomogeneous_zero (Fin 2) ℂ 4
  obtain ⟨remainder, hexpansion⟩ :=
    exists_orbitWeightedRadialExpansion hzeroHomogeneous extended
      hextendedAnalytic htail
  obtain ⟨delta, hdelta⟩ :=
    IsAlgClosed.exists_pow_nat_eq (3 : ℂ) (by norm_num : 0 < 2)
  let initialMap := weightedPolynomialMap
    (orbitInitialPolynomialMap (0 : OrbitSourceForm))
  let Phi := orbitPairRescaledPerturbation initialMap remainder
  let pair := orbitFiniteChartPair delta 0
  let q := orbitSecondVariableExplicitBranch delta 0 0
  let plane := orbitSecondVariablePlanePart Phi delta 0
  have hreparamBase :
      orbitSecondVariableReparametrization delta 0
          (((0, 0) : ℂ × ℂ), q) =
        (0, pair) := by
    ext
    all_goals simp [orbitSecondVariableReparametrization,
      orbitSecondVariablePair, orbitSecondVariableExplicitBranch,
      orbitPointOfFinTwo, orbitFinTwoOfPoint,
      orbitFiniteChartPair, pair, q]
  have hPhi : AnalyticAt ℂ Phi (0, pair) := by
    apply analyticAt_orbitPairRescaledPerturbation
    · exact analyticAt_orbitInitialPolynomialMap 0 pair.1
    · exact analyticAt_orbitInitialPolynomialMap 0 pair.2
    · exact (hexpansion pair.1).remainder_analyticAt
    · exact (hexpansion pair.2).remainder_analyticAt
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_orbitSecondVariablePlanePart
    rw [hreparamBase]
    exact hPhi
  have hspecialPlane : ∀ lambda v,
      plane ((0, lambda), v) =
        orbitSecondVariablePlaneDifference delta 0 (lambda, v) := by
    intro lambda v
    exact orbitSecondVariablePlanePart_rescaled_zero
      delta 0 0 remainder lambda v
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        orbitNegativePointDerivative pair.2.1 pair.2.2 := by
    have hcomposition := hplane.hasStrictFDerivAt.comp q
      ((hasStrictFDerivAt_const (𝕜 := ℂ) ((0, 0) : ℂ × ℂ) q).prodMk
        (hasStrictFDerivAt_id q))
    have hinr :
        (0 : (Fin 2 → ℂ) →L[ℂ] (ℂ × ℂ)).prod
            (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) := by
      ext v
      all_goals rfl
    rw [hinr] at hcomposition
    have hfixed :
        (fun v ↦ plane (((0, 0) : ℂ × ℂ), v)) =
          fun v ↦ orbitSecondVariablePlaneDifference delta 0 (0, v) := by
      funext v
      exact hspecialPlane 0 v
    rw [hfixed] at hcomposition
    have hstrict :=
      hasStrictFDerivAt_orbitSecondVariablePlaneDifference_point delta 0
    have hpairSecond : orbitFiniteChartSecondPoint delta 0 = pair.2 := by
      rfl
    rw [hpairSecond] at hstrict
    exact hcomposition.hasFDerivAt.unique hstrict.hasFDerivAt
  have hsecondCoordinate : pair.2.2 ≠ 0 := by
    intro hzeroSecond
    have hdeltaZero : delta = 0 := by
      simpa [pair, orbitFiniteChartPair, orbitFiniteChartSecondPoint,
        orbitConicZeta_eval, orbitConicRhoValue_eq,
        orbitConicAlphaValue_eq] using hzeroSecond
    rw [hdeltaZero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hdelta
    norm_num at hdelta
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ)
          (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    simpa [orbitNegativePointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := orbitNegativePointDerivativeEquiv
          pair.2.1 pair.2.2 hsecondCoordinate))
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    rw [hspecialPlane]
    simpa [q] using
      orbitSecondVariablePlaneDifference_explicitBranch_zero
        hdelta (0 : OrbitSourceForm) 0 0
  let branch := analyticImplicitBranch plane
    (((0, 0) : ℂ × ℂ), q) hplane hpoint
  have hparameter : Tendsto (fun tau : ℂ ↦ (tau, 0))
      (nhds 0) (nhds ((0, 0) : ℂ × ℂ)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hbranch : Tendsto (fun tau : ℂ ↦ branch (tau, 0))
      (nhds 0) (nhds q) := by
    have hbranchAt :=
      (analyticAt_analyticImplicitBranch plane
        (((0, 0) : ℂ × ℂ), q) hplane hpoint).continuousAt.tendsto
    have ht := hbranchAt.comp hparameter
    rw [analyticImplicitBranch_apply_base] at ht
    change Tendsto (branch ∘ fun tau : ℂ ↦ (tau, 0))
      (nhds 0) (nhds q)
    exact ht
  have hplaneBranch : ∀ᶠ tau in nhds 0,
      plane ((tau, 0), branch (tau, 0)) = 0 := by
    have hsolve := eventually_analyticImplicitBranch_eq plane
      (((0, 0) : ℂ × ℂ), q) hplane hpoint
    filter_upwards [hparameter.eventually hsolve] with tau htau
    simpa only [hplaneZero] using htau
  let pairBranch : ℂ → (ℂ × ℂ) × (ℂ × ℂ) := fun tau ↦
    orbitSecondVariablePair delta 0 (branch (tau, 0))
  have hpointBranch : Tendsto
      (fun tau ↦ orbitPointOfFinTwo (branch (tau, 0)))
      (nhds 0) (nhds (orbitPointOfFinTwo q)) := by
    have hcontinuous : Continuous orbitPointOfFinTwo := by
      change Continuous (fun q : Fin 2 → ℂ ↦ (q 0, q 1))
      exact (continuous_apply 0).prodMk (continuous_apply 1)
    exact hcontinuous.continuousAt.tendsto.comp hbranch
  have hpairBranch : Tendsto pairBranch (nhds 0) (nhds pair) := by
    have hqpoint : orbitPointOfFinTwo q =
        orbitFiniteChartSecondPoint delta 0 := by
      simp [q, orbitSecondVariableExplicitBranch, orbitPointOfFinTwo,
        orbitFinTwoOfPoint]
    rw [hqpoint] at hpointBranch
    simpa [pairBranch, pair, orbitSecondVariablePair,
      orbitFiniteChartPair] using
        tendsto_const_nhds.prodMk_nhds hpointBranch
  have hpairNe : pair.1 ≠ pair.2 := by
    intro heq
    have hfirst := congrArg (fun p : ℂ × ℂ ↦ p.1) heq
    norm_num [pair, orbitFiniteChartPair, orbitFiniteChartFirstPoint,
      orbitFiniteChartSecondPoint, orbitConicS_eval, orbitConicT_eval,
      orbitConicAlphaValue_eq, orbitConicBetaValue_eq] at hfirst
  have hdifference :=
    eventually_representative_difference_eq_orbitPairRescaledPerturbation
      (orbitInitialDegrees 4) initialMap extended remainder pair pairBranch
      hpairBranch (hexpansion pair.1) (hexpansion pair.2)
  have hequal : ∀ᶠ tau in nhds 0,
      representative
          (weightedRadialSource 1 tau (pairBranch tau).1) =
        representative
          (weightedRadialSource 1 tau (pairBranch tau).2) := by
    filter_upwards [hdifference, hplaneBranch] with tau hdifferenceAt hplaneAt
    funext i
    fin_cases i
    · apply sub_eq_zero.mp
      have hzeroPhi : Phi (tau, pairBranch tau) 0 = 0 := by
        simpa [plane, orbitSecondVariablePlanePart,
          orbitSecondVariableReparametrization, pairBranch] using
            congrFun hplaneAt 0
      simpa [extended, plane, orbitSecondVariablePlanePart,
        orbitSecondVariableReparametrization, pairBranch, Phi,
        initialMap, hzeroPhi] using hdifferenceAt 0
    · apply sub_eq_zero.mp
      have hzeroPhi : Phi (tau, pairBranch tau) 1 = 0 := by
        simpa [plane, orbitSecondVariablePlanePart,
          orbitSecondVariableReparametrization, pairBranch] using
            congrFun hplaneAt 1
      simpa [extended, plane, orbitSecondVariablePlanePart,
        orbitSecondVariableReparametrization, pairBranch, Phi,
        initialMap, hzeroPhi] using hdifferenceAt 1
  have hdistinct := eventually_orbitPairRadialSource_ne
    pair pairBranch hpairNe hpairBranch
  have hfirstSource : Tendsto
      (fun tau ↦ weightedRadialSource 1 tau (pairBranch tau).1)
      (nhds 0) (nhds 0) := by
    exact tendsto_weightedRadialSource_zero 1 (by omega) _ pair.1
      (continuous_fst.tendsto pair |>.comp hpairBranch)
  have hsecondSource : Tendsto
      (fun tau ↦ weightedRadialSource 1 tau (pairBranch tau).2)
      (nhds 0) (nhds 0) := by
    exact tendsto_weightedRadialSource_zero 1 (by omega) _ pair.2
      (continuous_snd.tendsto pair |>.comp hpairBranch)
  rw [hg]
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  intro hinjective
  obtain ⟨s, hs, hsInjective⟩ := hinjective
  have hfirstMem := hfirstSource.eventually hs
  have hsecondMem := hsecondSource.eventually hs
  have hall : ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      weightedRadialSource 1 tau (pairBranch tau).1 ∈ s ∧
      weightedRadialSource 1 tau (pairBranch tau).2 ∈ s ∧
      representative
          (weightedRadialSource 1 tau (pairBranch tau).1) =
        representative
          (weightedRadialSource 1 tau (pairBranch tau).2) ∧
      weightedRadialSource 1 tau (pairBranch tau).1 ≠
        weightedRadialSource 1 tau (pairBranch tau).2 := by
    filter_upwards [hfirstMem.filter_mono nhdsWithin_le_nhds,
      hsecondMem.filter_mono nhdsWithin_le_nhds,
      hequal.filter_mono nhdsWithin_le_nhds, hdistinct] with
      tau hfirstMemAt hsecondMemAt hequalAt hdistinctAt
    exact ⟨hfirstMemAt, hsecondMemAt, hequalAt, hdistinctAt⟩
  obtain ⟨tau, hfirstMemAt, hsecondMemAt, hequalAt, hdistinctAt⟩ :=
    hall.exists
  exact hdistinctAt
    (hsInjective hfirstMemAt hsecondMemAt hequalAt)

end OnLeConjecture.DTwo
