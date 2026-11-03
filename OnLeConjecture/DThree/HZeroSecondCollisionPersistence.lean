/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HZeroSecondCollisionChart

/-!
# Persistence in the zero second coordinate H chart

An explicit analytic branch identifies the implicit branch in the two first
coordinates.  A positive finite order of the third equation then persists
under analytic perturbation.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

@[expose]
noncomputable def hZeroSecondAffinePoint
    (T : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![v 0, v 1, T lambda]

@[expose]
noncomputable def hZeroSecondReparametrization
    (T : ℂ → ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × (Fin 3 → ℂ) :=
  (q.1.1, hZeroSecondAffinePoint T q.1.2 q.2)

@[expose]
noncomputable def hZeroSecondPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (T : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (hZeroSecondReparametrization T q) 0,
    Phi (hZeroSecondReparametrization T q) 1]

@[expose]
noncomputable def hZeroSecondThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (T : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (hZeroSecondReparametrization T q) 2

theorem analyticAt_hZeroSecondReparametrization
    (T : ℂ → ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hT : AnalyticAt ℂ T q.1.2) :
    AnalyticAt ℂ (hZeroSecondReparametrization T) q := by
  have hparameter : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.1.1) q :=
    analyticAt_fst.fun_comp analyticAt_fst
  have hlambda : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.1.2) q :=
    analyticAt_snd.fun_comp analyticAt_fst
  have hTcomp : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ T q.1.2) q :=
    AnalyticAt.fun_comp (x := q) hT hlambda
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.2 i) q := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt q.2).comp
        (analyticAt_snd : AnalyticAt ℂ
          (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.2) q)
  have hpoint : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        hZeroSecondAffinePoint T q.1.2 q.2) q := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact hcoordinate 0
    · exact hcoordinate 1
    · exact hTcomp
  exact hparameter.prod hpoint

theorem analyticAt_hZeroSecondPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (T : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hT : AnalyticAt ℂ T q.1.2)
    (hPhi : AnalyticAt ℂ Phi (hZeroSecondReparametrization T q)) :
    AnalyticAt ℂ (hZeroSecondPlanePart Phi T) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (hZeroSecondReparametrization T u)) q :=
    hPhi.fun_comp (analyticAt_hZeroSecondReparametrization T q hT)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · have hcoordinate : AnalyticAt ℂ
        (fun u ↦ (Phi (hZeroSecondReparametrization T u)) 0) q :=
      AnalyticAt.fun_comp
        (g := fun value : Fin 3 → ℂ ↦ value 0)
        (f := fun u ↦ Phi (hZeroSecondReparametrization T u))
        ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt
          (Phi (hZeroSecondReparametrization T q))) hfull
    simpa [hZeroSecondPlanePart] using hcoordinate
  · have hcoordinate : AnalyticAt ℂ
        (fun u ↦ (Phi (hZeroSecondReparametrization T u)) 1) q :=
      AnalyticAt.fun_comp
        (g := fun value : Fin 3 → ℂ ↦ value 1)
        (f := fun u ↦ Phi (hZeroSecondReparametrization T u))
        ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt
          (Phi (hZeroSecondReparametrization T q))) hfull
    simpa [hZeroSecondPlanePart] using hcoordinate

theorem analyticAt_hZeroSecondThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (T : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hT : AnalyticAt ℂ T q.1.2)
    (hPhi : AnalyticAt ℂ Phi (hZeroSecondReparametrization T q)) :
    AnalyticAt ℂ (hZeroSecondThirdPart Phi T) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (hZeroSecondReparametrization T u)) q :=
    hPhi.fun_comp (analyticAt_hZeroSecondReparametrization T q hT)
  have hcoordinate : AnalyticAt ℂ
      (fun u ↦ (Phi (hZeroSecondReparametrization T u)) 2) q :=
    AnalyticAt.fun_comp
      (g := fun value : Fin 3 → ℂ ↦ value 2)
      (f := fun u ↦ Phi (hZeroSecondReparametrization T u))
      ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt
        (Phi (hZeroSecondReparametrization T q))) hfull
  change AnalyticAt ℂ
    (fun u ↦ Phi (hZeroSecondReparametrization T u) 2) q
  exact hcoordinate

/-- Source branch data for a collision whose second chart point has zero
second coordinate at the base. -/
structure HZeroSecondSourceBranchData
    (a N : ℕ) (R : MvPolynomial (Fin 2) ℂ) where
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
    hZeroSecondPlaneDifference a T (lambda, point lambda) = 0
  order_pos : 0 < order
  unit_analyticAt : AnalyticAt ℂ unit 0
  unit_zero_ne : unit 0 ≠ 0
  third_factor : ∀ᶠ lambda in nhds 0,
    hFormEval (point lambda 0) 1 R -
        hFormEval (point lambda 1) (T lambda ^ (2 * a)) R =
      lambda ^ order * unit lambda

theorem hZeroSecondPlanePart_weightedRescaledPerturbation_zero
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (T : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    hZeroSecondPlanePart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
            remainder) T ((0, lambda), v) =
      hZeroSecondPlaneDifference a T (lambda, v) := by
  funext i
  fin_cases i
  all_goals simp [hZeroSecondPlanePart, hZeroSecondReparametrization,
    hZeroSecondAffinePoint, hZeroSecondPlaneDifference,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    weightedPolynomialMap_hQuadraticWeightedPolynomialMap]

theorem hZeroSecondThirdPart_weightedRescaledPerturbation_zero
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (T : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    hZeroSecondThirdPart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
            remainder) T ((0, lambda), v) =
      hFormEval (v 0) 1 R - hFormEval (v 1) (T lambda ^ (2 * a)) R := by
  simp [hZeroSecondThirdPart, hZeroSecondReparametrization,
    hZeroSecondAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint,
    weightedPolynomialMap_hQuadraticWeightedPolynomialMap]

/-- A zero second coordinate branch persists through analytic perturbations. -/
theorem eventually_exists_hZeroSecondZero_mem_nhds
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (data : HZeroSecondSourceBranchData a N R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (data.firstX, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (data.secondX, 0)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![data.firstX, data.secondX, 0])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
              remainder (tau, point) = 0 := by
  let Phi := weightedRescaledPerturbation
    (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)) remainder
  let q : Fin 2 → ℂ := ![data.firstX, data.secondX]
  let plane := hZeroSecondPlanePart Phi data.T
  let third := hZeroSecondThirdPart Phi data.T
  have hreparamBase : hZeroSecondReparametrization data.T
      (((0, 0) : ℂ × ℂ), q) =
        (0, ![data.firstX, data.secondX, 0]) := by
    ext i <;> simp [hZeroSecondReparametrization,
      hZeroSecondAffinePoint, q, data.T_zero]
  have hPhi : AnalyticAt ℂ Phi
      (0, ![data.firstX, data.secondX, 0]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_hQuadratic a R _
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
      simpa [hZeroSecondPlaneDifference, data.point_zero, data.T_zero,
        zero_pow (by omega : 2 * a ≠ 0)] using hcomponent
    exact sub_eq_zero.mp hcomponent'
  have hQfiber : hQ data.firstX 1 = hQ data.secondX 0 := by
    have hcomponent := congrFun hmodelAt 1
    have hcomponent' :
        hQ data.firstX 1 - hQ data.secondX 0 = 0 := by
      simpa [hZeroSecondPlaneDifference, data.point_zero, data.T_zero,
        zero_pow (by omega : 2 * a ≠ 0)] using hcomponent
    exact sub_eq_zero.mp hcomponent'
  let pointEquiv := hZeroSecondPointDerivativeEquiv
    data.firstX data.secondX hPfiber hQfiber
  have hmodelDerivative : HasStrictFDerivAt
      (fun point ↦ hZeroSecondPlaneDifference a data.T (0, point))
      (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) q := by
    simpa [pointEquiv, q, hZeroSecondPointDerivativeEquiv] using
      hasStrictFDerivAt_hZeroSecondPlaneDifference_point
        a ha data.T data.firstX data.secondX data.T_zero
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
      ext point <;> rfl
    rw [hinr] at hcomposition
    have hfixed : (fun point ↦ plane (((0, 0) : ℂ × ℂ), point)) =
        fun point ↦ hZeroSecondPlaneDifference a data.T (0, point) := by
      funext point
      exact hZeroSecondPlanePart_weightedRescaledPerturbation_zero
        a R remainder data.T 0 point
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique hmodelDerivative.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    change hZeroSecondPlanePart Phi data.T ((0, 0), q) = 0
    rw [hZeroSecondPlanePart_weightedRescaledPerturbation_zero]
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
    rw [hZeroSecondPlanePart_weightedRescaledPerturbation_zero,
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
    rw [hZeroSecondThirdPart_weightedRescaledPerturbation_zero]
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

/-- A zero second coordinate collision excludes an injective representative
on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_hZeroSecondCollision
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (data : HZeroSecondSourceBranchData a N R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.firstX, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.secondX, 0)) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_chart
    a (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
      representative remainder data.firstX data.secondX 0 ha
      (by intro h; have := congrArg Prod.snd h; norm_num at this)
      hfirst hsecond
  intro U hU
  exact eventually_exists_hZeroSecondZero_mem_nhds
    a N ha R data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- Weighted order tails exclude an injective representative at a zero
second coordinate collision. -/
theorem hZeroSecondWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (data : HZeroSecondSourceBranchData a N R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (hQuadraticWeightedDegrees a N)
        (hQuadraticWeightedPolynomialMap a R)
          (hQuadraticWeightedPolynomialMap_isWeightedHomogeneous a N R hR)
            representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hZeroSecondCollision
    a N ha R data representative remainder
      (hexpansion (data.firstX, 1))
      (hexpansion (data.secondX, 0))

end OnLeConjecture.DThree
