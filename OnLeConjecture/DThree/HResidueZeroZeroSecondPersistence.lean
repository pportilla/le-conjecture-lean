/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddZeroSecondPersistence
public import OnLeConjecture.DThree.HResidueZeroOrdinaryBranchPersistence

/-!
# Zero coordinate H collisions after a power substitution

An ordinary source branch whose second coordinate vanishes at the base
lifts through the map `y ↦ y^a` after ramifying its parameter. The lifted
branch supplies the transverse data needed to persist a collision through
strict weighted tails.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- An analytic function which vanishes at the origin acquires an analytic
`a`th root after composition with `z ↦ z^a`. -/
theorem exists_analyticAt_ramified_root
    (a : ℕ) (ha : 0 < a) (T : ℂ → ℂ)
    (hT : AnalyticAt ℂ T 0) (hT0 : T 0 = 0) :
    ∃ S : ℂ → ℂ,
      AnalyticAt ℂ S 0 ∧ S 0 = 0 ∧
        ∀ᶠ z in nhds 0, S z ^ a = T (z ^ a) := by
  have hpower : Tendsto (fun z : ℂ ↦ z ^ a) (nhds 0) (nhds 0) := by
    have hpowerAnalytic : AnalyticAt ℂ (fun z : ℂ ↦ z ^ a) 0 :=
      analyticAt_id.pow a
    have hcontinuous := hpowerAnalytic.continuousAt
    change Tendsto (fun z : ℂ ↦ z ^ a)
      (nhds 0) (nhds (0 ^ a)) at hcontinuous
    simpa [zero_pow ha.ne'] using hcontinuous
  by_cases hlocal : ∀ᶠ z in nhds 0, T z = 0
  · refine ⟨fun _ ↦ 0,
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (0 : ℂ)) 0),
        rfl, ?_⟩
    filter_upwards [hpower.eventually hlocal] with z hz
    simp [hz, zero_pow ha.ne']
  · obtain ⟨n, u, hu, hu0, hfactor⟩ :=
      hT.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hlocal
    have hn : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      have hfactor0 := hfactor.self_of_nhds
      have hfactor0' : T 0 = u 0 := by
        simpa [hnzero] using hfactor0
      rw [hT0] at hfactor0'
      exact hu0 hfactor0'.symm
    let uPower : ℂ → ℂ := fun z ↦ u (z ^ a)
    have huPower : AnalyticAt ℂ uPower 0 := by
      have hpowerAnalytic : AnalyticAt ℂ (fun z : ℂ ↦ z ^ a) 0 :=
        analyticAt_id.pow a
      have huAt : AnalyticAt ℂ u (0 ^ a) := by
        simpa [zero_pow ha.ne'] using hu
      exact AnalyticAt.fun_comp
        (x := (0 : ℂ)) (g := u) (f := fun z : ℂ ↦ z ^ a)
          huAt hpowerAnalytic
    have huPower0 : uPower 0 ≠ 0 := by
      simpa [uPower, zero_pow ha.ne'] using hu0
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (uPower 0) ha
    obtain ⟨v, hv, hv0, hvPower⟩ :=
      exists_analyticAt_root_with_value uPower huPower huPower0
        a ha.ne' c hc
    let S : ℂ → ℂ := fun z ↦ z ^ n * v z
    have hS : AnalyticAt ℂ S 0 := (analyticAt_id.pow n).mul hv
    have hS0 : S 0 = 0 := by
      simp [S, zero_pow hn.ne']
    refine ⟨S, hS, hS0, ?_⟩
    filter_upwards [hpower.eventually hfactor] with z hz
    calc
      S z ^ a = (z ^ n) ^ a * v z ^ a := by
        change (z ^ n * v z) ^ a = _
        rw [mul_pow]
      _ = (z ^ a) ^ n * uPower z := by
        rw [hvPower]
        have hp : (z ^ n) ^ a = (z ^ a) ^ n := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm n a]
        rw [hp]
      _ = T (z ^ a) := by
        rw [hz]
        simp [uPower]

/-- Source branch data for a zero coordinate collision after the power
substitution of an ordinary `H` form. -/
structure HResidueZeroZeroSecondSourceBranchData
    (a : ℕ) (R : Form ℂ) where
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
    MvPolynomial.eval ![point lambda 0, 1] R -
        MvPolynomial.eval ![point lambda 1, T lambda ^ a] R =
      lambda ^ order * unit lambda

/-- An ordinary zero coordinate source branch lifts after a power
substitution and a ramification of its parameter. -/
theorem
    exists_hResidueZeroZeroSecondSourceBranchData_of_ordinarySourceBranch
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (data : HHardOddZeroSecondSourceBranchData R) :
    Nonempty (HResidueZeroZeroSecondSourceBranchData a R) := by
  obtain ⟨T, hTAnalytic, hTZero, hTPower⟩ :=
    exists_analyticAt_ramified_root
      a ha data.T data.T_analyticAt data.T_zero
  let powerParameter : ℂ → ℂ := fun lambda ↦ lambda ^ a
  have hpowerAnalytic : AnalyticAt ℂ powerParameter 0 := by
    exact analyticAt_id.pow a
  have hpower : Tendsto powerParameter (nhds 0) (nhds 0) := by
    have ht := hpowerAnalytic.continuousAt
    change Tendsto powerParameter
      (nhds 0) (nhds (powerParameter 0)) at ht
    simpa [powerParameter, zero_pow ha.ne'] using ht
  let point : ℂ → Fin 2 → ℂ := fun lambda ↦
    data.point (powerParameter lambda)
  let unit : ℂ → ℂ := fun lambda ↦
    data.unit (powerParameter lambda)
  have hpointAnalytic : AnalyticAt ℂ point 0 := by
    have hpointAt : AnalyticAt ℂ data.point (powerParameter 0) := by
      simpa [powerParameter, zero_pow ha.ne'] using data.point_analyticAt
    exact AnalyticAt.fun_comp
      (x := (0 : ℂ)) (g := data.point) (f := powerParameter)
        hpointAt hpowerAnalytic
  have hunitAnalytic : AnalyticAt ℂ unit 0 := by
    have hunitAt : AnalyticAt ℂ data.unit (powerParameter 0) := by
      simpa [powerParameter, zero_pow ha.ne'] using data.unit_analyticAt
    exact AnalyticAt.fun_comp
      (x := (0 : ℂ)) (g := data.unit) (f := powerParameter)
        hunitAt hpowerAnalytic
  have hpointZero : point 0 = ![data.firstX, data.secondX] := by
    simpa [point, powerParameter, zero_pow ha.ne'] using data.point_zero
  have hunitZero : unit 0 ≠ 0 := by
    simpa [unit, powerParameter, zero_pow ha.ne'] using data.unit_zero_ne
  have hplane : ∀ᶠ lambda in nhds 0,
      hZeroSecondPlaneDifference a T (lambda, point lambda) = 0 := by
    filter_upwards [hpower.eventually data.plane_zero, hTPower]
      with lambda hplaneAt hTPowerAt
    have htwo : T lambda ^ (2 * a) =
        data.T (powerParameter lambda) ^ 2 := by
      rw [Nat.mul_comm 2 a, pow_mul, hTPowerAt]
    funext i
    fin_cases i
    · simpa [hZeroSecondPlaneDifference, point, htwo] using
        congrFun hplaneAt 0
    · simpa [hZeroSecondPlaneDifference, point, htwo] using
        congrFun hplaneAt 1
  have hthird : ∀ᶠ lambda in nhds 0,
      MvPolynomial.eval ![point lambda 0, 1] R -
          MvPolynomial.eval ![point lambda 1, T lambda ^ a] R =
        lambda ^ (a * data.order) * unit lambda := by
    filter_upwards [hpower.eventually data.third_factor, hTPower]
      with lambda hfactorAt hTPowerAt
    rw [hTPowerAt]
    simpa [point, unit, powerParameter, pow_mul] using hfactorAt
  exact ⟨
    { T := T
      point := point
      firstX := data.firstX
      secondX := data.secondX
      order := a * data.order
      unit := unit
      T_analyticAt := hTAnalytic
      point_analyticAt := hpointAnalytic
      T_zero := hTZero
      point_zero := hpointZero
      plane_zero := hplane
      order_pos := Nat.mul_pos ha data.order_pos
      unit_analyticAt := hunitAnalytic
      unit_zero_ne := hunitZero
      third_factor := hthird }⟩

/-- At radial parameter zero, the first two differences are the weighted
`H` fibre equations in the zero coordinate chart. -/
theorem hZeroSecondPlanePart_hResidueZeroInitialMap_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (T : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    hZeroSecondPlanePart
        (weightedRescaledPerturbation
          (hResidueZeroInitialMap a R) remainder) T ((0, lambda), v) =
      hZeroSecondPlaneDifference a T (lambda, v) := by
  funext i
  fin_cases i
  · simp [hZeroSecondPlanePart, hZeroSecondReparametrization,
      hZeroSecondAffinePoint, hZeroSecondPlaneDifference,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      hResidueZeroInitialMap, weightedPolynomialMap,
      hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      weightedPowerSubstitutionForm, cubicForm, formX, formT, hP]
    all_goals ring_nf
    all_goals simp
  · simp [hZeroSecondPlanePart, hZeroSecondReparametrization,
      hZeroSecondAffinePoint, hZeroSecondPlaneDifference,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      hResidueZeroInitialMap, weightedPolynomialMap,
      hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      weightedPowerSubstitutionForm, quarticForm, formX, formT, hQ]
    all_goals ring_nf

/-- At radial parameter zero, the third difference evaluates the ordinary
form after the power substitution. -/
theorem hZeroSecondThirdPart_hResidueZeroInitialMap_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (T : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    hZeroSecondThirdPart
        (weightedRescaledPerturbation
          (hResidueZeroInitialMap a R) remainder) T ((0, lambda), v) =
      MvPolynomial.eval ![v 0, 1] R -
        MvPolynomial.eval ![v 1, T lambda ^ a] R := by
  rw [hZeroSecondThirdPart, hZeroSecondReparametrization,
    hZeroSecondAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint, hResidueZeroInitialMap]
  change
    MvPolynomial.eval ![v 0, 1]
          (weightedPowerSubstitutionForm a R) -
        MvPolynomial.eval ![v 1, T lambda]
          (weightedPowerSubstitutionForm a R) =
      MvPolynomial.eval ![v 0, 1] R -
        MvPolynomial.eval ![v 1, T lambda ^ a] R
  have hfirst :
      MvPolynomial.eval ![v 0, 1]
          (weightedPowerSubstitutionForm a R) =
        MvPolynomial.eval ![v 0, 1 ^ a] R := by
    simpa using eval_weightedPowerSubstitutionForm a R (v 0, 1)
  have hsecond :
      MvPolynomial.eval ![v 1, T lambda]
          (weightedPowerSubstitutionForm a R) =
        MvPolynomial.eval ![v 1, T lambda ^ a] R := by
    simpa using
      eval_weightedPowerSubstitutionForm a R (v 1, T lambda)
  rw [hfirst, hsecond]
  simp

/-- A zero coordinate source branch persists through a weighted analytic
perturbation. -/
theorem eventually_exists_hResidueZeroZeroSecondZero_mem_nhds
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (data : HResidueZeroZeroSecondSourceBranchData a R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (data.firstX, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (data.secondX, 0)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![data.firstX, data.secondX, 0])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (hResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  let Phi := weightedRescaledPerturbation
    (hResidueZeroInitialMap a R) remainder
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
        (hResidueZeroPolynomialMap a R) _
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
      ext point
      all_goals rfl
    rw [hinr] at hcomposition
    have hfixed :
        (fun point ↦ plane (((0, 0) : ℂ × ℂ), point)) =
          fun point ↦ hZeroSecondPlaneDifference a data.T (0, point) := by
      funext point
      exact hZeroSecondPlanePart_hResidueZeroInitialMap_zero
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
    rw [hZeroSecondPlanePart_hResidueZeroInitialMap_zero]
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
    rw [hZeroSecondPlanePart_hResidueZeroInitialMap_zero,
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
    rw [hZeroSecondThirdPart_hResidueZeroInitialMap_zero]
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

/-- A lifted zero coordinate branch excludes injectivity on every
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_hResidueZeroZeroSecondSourceBranch
    (a N : ℕ) (ha : 0 < a) (R : Form ℂ)
    (data : HResidueZeroZeroSecondSourceBranchData a R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N) (hResidueZeroInitialMap a R)
        representative remainder (data.firstX, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N) (hResidueZeroInitialMap a R)
        representative remainder (data.secondX, 0)) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_chart
    a (hQuadraticWeightedDegrees a N) (hResidueZeroInitialMap a R)
      representative remainder data.firstX data.secondX 0 ha
      (by
        intro h
        have ht := congrArg Prod.snd h
        norm_num at ht)
      hfirst hsecond
  intro U hU
  exact eventually_exists_hResidueZeroZeroSecondZero_mem_nhds
    a ha R data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- Weighted tails exclude an injective representative when a lifted zero
coordinate source branch is available. -/
theorem
    hResidueZeroZeroSecondWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (R : Form ℂ)
    (hR : R.IsHomogeneous N)
    (data : HResidueZeroZeroSecondSourceBranchData a R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (hQuadraticWeightedDegrees a N)
        (hResidueZeroPolynomialMap a R)
          (hResidueZeroPolynomialMap_isWeightedHomogeneous a N R hR)
            representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hResidueZeroZeroSecondSourceBranch
    a N ha R data representative remainder
      (hexpansion (data.firstX, 1))
      (hexpansion (data.secondX, 0))

/-- An ordinary zero coordinate source branch excludes an injective
representative after every positive power substitution. -/
theorem
    hOrdinaryZeroSecondResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (R : Form ℂ)
    (hR : R.IsHomogeneous N)
    (data : HHardOddZeroSecondSourceBranchData R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨lifted⟩ :=
    exists_hResidueZeroZeroSecondSourceBranchData_of_ordinarySourceBranch
      a ha R data
  exact
    hResidueZeroZeroSecondWeightedOrderTails_not_hasInjectiveRepresentative
      a N ha R hR lifted representative hanalytic hzero htail

end OnLeConjecture.DThree
