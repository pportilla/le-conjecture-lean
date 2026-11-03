/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddOrdinaryPersistence
public import OnLeConjecture.DThree.HZeroSecondCollisionPersistence

/-!
# Ordinary persistence in the zero second coordinate H chart

The transverse chart for a source point with zero second coordinate also
applies to the ordinary homogeneous H map. The third equation is evaluated
by the full homogeneous form before analytic elimination.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Source branch data for an ordinary H collision whose second point has
zero second coordinate at the base. -/
structure HHardOddZeroSecondSourceBranchData (R : Form ℂ) where
  T : ℂ → ℂ
  point : ℂ → Fin 2 → ℂ
  firstX : ℂ
  secondX : ℂ
  order : ℕ
  unit : ℂ → ℂ
  T_analyticAt : AnalyticAt ℂ T 0
  point_analyticAt : AnalyticAt ℂ point 0
  T_zero : T 0 = 0
  point_zero : point 0 = ![firstX, secondX]
  plane_zero : ∀ᶠ lambda in nhds 0,
    hZeroSecondPlaneDifference 1 T (lambda, point lambda) = 0
  order_pos : 0 < order
  unit_analyticAt : AnalyticAt ℂ unit 0
  unit_zero_ne : unit 0 ≠ 0
  third_factor : ∀ᶠ lambda in nhds 0,
    MvPolynomial.eval ![point lambda 0, 1] R -
        MvPolynomial.eval ![point lambda 1, T lambda] R =
      lambda ^ order * unit lambda

/-- At radial parameter zero, the first two ordinary H differences agree
with the equations in the zero second coordinate chart. -/
theorem hZeroSecondPlanePart_hOrdinaryInitialMap_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (T : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    hZeroSecondPlanePart
        (weightedRescaledPerturbation
          (hOrdinaryInitialMap R) remainder) T ((0, lambda), v) =
      hZeroSecondPlaneDifference 1 T (lambda, v) := by
  funext i
  fin_cases i
  all_goals simp [hZeroSecondPlanePart, hZeroSecondReparametrization,
    hZeroSecondAffinePoint, hZeroSecondPlaneDifference,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    hOrdinaryInitialMap, weightedPolynomialMap, hOrdinaryPolynomialMap,
    cubicForm, quarticForm, formX, formT, hP, hQ]
  all_goals ring

/-- At radial parameter zero, the third ordinary H difference is the
difference of the full homogeneous form at the two chart points. -/
theorem hZeroSecondThirdPart_hOrdinaryInitialMap_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (T : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    hZeroSecondThirdPart
        (weightedRescaledPerturbation
          (hOrdinaryInitialMap R) remainder) T ((0, lambda), v) =
      MvPolynomial.eval ![v 0, 1] R -
        MvPolynomial.eval ![v 1, T lambda] R := by
  simp [hZeroSecondThirdPart, hZeroSecondReparametrization,
    hZeroSecondAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint, hOrdinaryInitialMap,
    weightedPolynomialMap, hOrdinaryPolynomialMap]

/-- The rescaled perturbation has a zero in every neighborhood of an
ordinary zero second coordinate source branch. -/
theorem eventually_exists_hHardOddZeroSecondZero_mem_nhds
    (R : Form ℂ)
    (data : HHardOddZeroSecondSourceBranchData R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (data.firstX, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (data.secondX, 0)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![data.firstX, data.secondX, 0])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (hOrdinaryInitialMap R) remainder (tau, point) = 0 := by
  let Phi := weightedRescaledPerturbation
    (hOrdinaryInitialMap R) remainder
  let q : Fin 2 → ℂ := ![data.firstX, data.secondX]
  let plane := hZeroSecondPlanePart Phi data.T
  let third := hZeroSecondThirdPart Phi data.T
  have hreparamBase : hZeroSecondReparametrization data.T
      (((0, 0) : ℂ × ℂ), q) =
        (0, ![data.firstX, data.secondX, 0]) := by
    ext i
    all_goals simp [hZeroSecondReparametrization,
      hZeroSecondAffinePoint, q, data.T_zero]
  have hPhi : AnalyticAt ℂ Phi
      (0, ![data.firstX, data.secondX, 0]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (hOrdinaryPolynomialMap R) _
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_hZeroSecondPlanePart
    · exact data.T_analyticAt
    · simpa [hreparamBase] using hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_hZeroSecondThirdPart
    · exact data.T_analyticAt
    · simpa [hreparamBase] using hPhi
  have hmodelAt := data.plane_zero.self_of_nhds
  have hPfiber : hP data.firstX 1 = hP data.secondX 0 := by
    have hcomponent := congrFun hmodelAt 0
    have hcomponent' :
        hP data.firstX 1 - hP data.secondX 0 = 0 := by
      simpa [hZeroSecondPlaneDifference, data.point_zero, data.T_zero]
        using hcomponent
    exact sub_eq_zero.mp hcomponent'
  have hQfiber : hQ data.firstX 1 = hQ data.secondX 0 := by
    have hcomponent := congrFun hmodelAt 1
    have hcomponent' :
        hQ data.firstX 1 - hQ data.secondX 0 = 0 := by
      simpa [hZeroSecondPlaneDifference, data.point_zero, data.T_zero]
        using hcomponent
    exact sub_eq_zero.mp hcomponent'
  let pointEquiv := hZeroSecondPointDerivativeEquiv
    data.firstX data.secondX hPfiber hQfiber
  have hmodelDerivative : HasStrictFDerivAt
      (fun point ↦ hZeroSecondPlaneDifference 1 data.T (0, point))
      (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) q := by
    simpa [pointEquiv, q, hZeroSecondPointDerivativeEquiv] using
      hasStrictFDerivAt_hZeroSecondPlaneDifference_point
        1 (by norm_num) data.T data.firstX data.secondX data.T_zero
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) := by
    have hcomposition := hplane.hasStrictFDerivAt.comp q
      ((hasStrictFDerivAt_const (𝕜 := ℂ) ((0, 0) : ℂ × ℂ) q).prodMk
        (hasStrictFDerivAt_id q))
    have hinr :
        (0 : (Fin 2 → ℂ) →L[ℂ] (ℂ × ℂ)).prod
            (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) := by
      ext point
      all_goals rfl
    rw [hinr] at hcomposition
    have hfixed : (fun point ↦ plane (((0, 0) : ℂ × ℂ), point)) =
        fun point ↦ hZeroSecondPlaneDifference 1 data.T (0, point) := by
      funext point
      exact hZeroSecondPlanePart_hOrdinaryInitialMap_zero
        R remainder data.T 0 point
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique hmodelDerivative.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    change hZeroSecondPlanePart Phi data.T ((0, 0), q) = 0
    rw [hZeroSecondPlanePart_hOrdinaryInitialMap_zero]
    simpa [q, data.point_zero] using hmodelAt
  let branch := analyticImplicitBranch
    plane (((0, 0), q)) hplane hpoint
  have hparameter : AnalyticAt ℂ
      (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hlift : Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ), data.point lambda))
      (nhds 0) (nhds (((0, 0) : ℂ × ℂ), q)) := by
    have ht := (hparameter.prod data.point_analyticAt).continuousAt
    change Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ), data.point lambda))
      (nhds 0)
      (nhds (((0, (0 : ℂ)) : ℂ × ℂ), data.point 0)) at ht
    rw [data.point_zero] at ht
    exact ht
  have hlocal := hplane.hasStrictFDerivAt
    |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint
  have hbranchExplicit : ∀ᶠ lambda in nhds 0,
      branch (0, lambda) = data.point lambda := by
    filter_upwards [hlift.eventually hlocal, data.plane_zero]
      with lambda hlocalAt hzeroAt
    apply hlocalAt.mp
    change hZeroSecondPlanePart Phi data.T
      ((0, lambda), data.point lambda) = plane ((0, 0), q)
    rw [hZeroSecondPlanePart_hOrdinaryInitialMap_zero,
      hplaneZero]
    exact hzeroAt
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) =
        lambda ^ data.order * data.unit lambda := by
    filter_upwards [hbranchExplicit, data.third_factor]
      with lambda hbranchAt hfactorAt
    rw [hbranchAt]
    change hZeroSecondThirdPart Phi data.T
      ((0, lambda), data.point lambda) = _
    rw [hZeroSecondThirdPart_hOrdinaryInitialMap_zero]
    exact hfactorAt
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    hZeroSecondReparametrization data.T ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have ht := (analyticAt_hZeroSecondReparametrization data.T
      (((0, 0) : ℂ × ℂ), q) data.T_analyticAt).continuousAt
    have ht' : Tendsto (hZeroSecondReparametrization data.T)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, ![data.firstX, data.secondX, 0])) := by
      change Tendsto (hZeroSecondReparametrization data.T)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (hZeroSecondReparametrization data.T
          (((0, 0), q)))) at ht
      rw [hreparamBase] at ht
      exact ht
    exact ht'.eventually hU
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird data.order data.unit
      data.order_pos data.unit_analyticAt data.unit_zero_ne hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  let point := hZeroSecondAffinePoint data.T lambda (branch (tau, lambda))
  refine ⟨point, hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

/-- An ordinary zero second coordinate collision excludes injectivity on
every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_hHardOddZeroSecondCollision
    (R : Form ℂ) (N : ℕ)
    (data : HHardOddZeroSecondSourceBranchData R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt 1
      (hOrdinaryDegrees N) (hOrdinaryInitialMap R)
        representative remainder (data.firstX, 1))
    (hsecond : HasWeightedRadialExpansionAt 1
      (hOrdinaryDegrees N) (hOrdinaryInitialMap R)
        representative remainder (data.secondX, 0)) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_chart
    1 (hOrdinaryDegrees N) (hOrdinaryInitialMap R)
      representative remainder data.firstX data.secondX 0 (by norm_num)
      (by
        intro h
        have ht := congrArg Prod.snd h
        norm_num at ht)
      hfirst hsecond
  intro U hU
  exact eventually_exists_hHardOddZeroSecondZero_mem_nhds
    R data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- Ordinary maximal ideal tails exclude an injective representative at a
zero second coordinate collision. -/
theorem hHardOddZeroSecondMaximalIdealTails_not_hasInjectiveRepresentative
    (R : Form ℂ) (N : ℕ) (hR : R.IsHomogeneous N)
    (data : HHardOddZeroSecondSourceBranchData R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hOrdinaryPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (hOrdinaryDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasOrdinaryRadialExpansionAt_of_mem_maximalIdeal_pow
      (hOrdinaryDegrees N) (hOrdinaryPolynomialMap R)
      (hOrdinaryPolynomialMap_isWeightedHomogeneous R N hR)
      representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hHardOddZeroSecondCollision
    R N data representative remainder
      (hexpansion (data.firstX, 1)) (hexpansion (data.secondX, 0))

end OnLeConjecture.DThree
