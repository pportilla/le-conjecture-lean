/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroInvariantExceptional
public import OnLeConjecture.DThree.ECNineAnalyticPersistence

/-!
# C9 persistence after a power substitution

The ordinary finite C9 section controls the special fibre after a power
substitution. At a nonzero root coordinate, an analytic root chart preserves
the ordinary transverse derivative. At a zero root coordinate, its power is
used as the curve parameter.
-/

public section

noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The ordinary C9 chart point associated with a substituted chart point. -/
@[expose]
def eCNinePowerChart (a : ℕ) (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(q 0) ^ a, q 1, (q 2) ^ a]

theorem analyticAt_eCNinePowerChart
    (a : ℕ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ (eCNinePowerChart a) q := by
  have hcoordinate (i : Fin 3) : AnalyticAt ℂ
      (fun value : Fin 3 → ℂ ↦ value i) q :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt q
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact (hcoordinate 0).pow a
  · exact hcoordinate 1
  · exact (hcoordinate 2).pow a

/-- Evaluation of the substituted initial map is evaluation of the ordinary
initial map at the powered chart point. -/
theorem eCNineXChartInitialDifference_eResidueZeroInitialMap
    (a : ℕ) (R : Form ℂ) (q : Fin 3 → ℂ) :
    eCNineXChartInitialDifference (eResidueZeroInitialMap a R) q =
      eCNineXChartInitialDifference
        (weightedPolynomialMap (eInvariantPolynomialMap R))
          (eCNinePowerChart a q) := by
  funext i
  simp only [eCNineXChartInitialDifference, Pi.sub_apply,
    eResidueZeroInitialMap]
  change
    MvPolynomial.eval ![1, q 0]
          (weightedPowerSubstitutionForm a (eInvariantPolynomialMap R i)) -
        MvPolynomial.eval ![q 1, q 2]
          (weightedPowerSubstitutionForm a (eInvariantPolynomialMap R i)) = _
  have hfirst := eval_weightedPowerSubstitutionForm
    a (eInvariantPolynomialMap R i) (1, q 0)
  have hsecond := eval_weightedPowerSubstitutionForm
    a (eInvariantPolynomialMap R i) (q 1, q 2)
  simpa [weightedPolynomialMap, eCNineXChartFirstPoint,
    eCNineXChartSecondPoint, eCNinePowerChart] using
      congrArg₂ (· - ·) hfirst hsecond

/-- A regular weighted chart obtained by taking analytic roots of the two
ordinary root coordinates. -/
@[expose]
def eCNineRegularRootParametrization
    (z : ℂ) (firstRoot secondRoot : ℂ → ℂ) : ECNineParametrization :=
  fun lambda v ↦ ![firstRoot (v 0), z + lambda, secondRoot (v 1)]

/-- A first root boundary chart with an analytic root in the remaining
nonzero root coordinate. -/
@[expose]
def eCNineFirstRootBoundaryPowerParametrization
    (secondRoot : ℂ → ℂ) : ECNineParametrization :=
  fun lambda v ↦ ![lambda, v 0, secondRoot (v 1)]

/-- The finite ordinary parametrization corresponding to the first root
boundary chart. -/
@[expose]
def eCNineFirstRootBoundaryFiniteParametrization
    (a : ℕ) : ECNineParametrization :=
  fun lambda v ↦ ![lambda ^ a, v 0, v 1]

/-- A second root boundary chart with an analytic root in the remaining
nonzero root coordinate. -/
@[expose]
def eCNineSecondRootBoundaryPowerParametrization
    (firstRoot : ℂ → ℂ) : ECNineParametrization :=
  fun lambda v ↦ ![firstRoot (v 0), v 1, lambda]

/-- The finite ordinary parametrization corresponding to the second root
boundary chart. -/
@[expose]
def eCNineSecondRootBoundaryFiniteParametrization
    (a : ℕ) : ECNineParametrization :=
  fun lambda v ↦ ![v 0, v 1, lambda ^ a]

theorem analyticAt_eCNineRegularRootParametrization
    (z : ℂ) (firstRoot secondRoot : ℂ → ℂ)
    (q : ℂ × (Fin 2 → ℂ))
    (hfirst : AnalyticAt ℂ firstRoot (q.2 0))
    (hsecond : AnalyticAt ℂ secondRoot (q.2 1)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineRegularRootParametrization
        z firstRoot secondRoot s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact AnalyticAt.fun_comp
      (x := q) (g := firstRoot)
        (f := fun s : ℂ × (Fin 2 → ℂ) ↦ s.2 0) hfirst
          ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2
            |>.fun_comp analyticAt_snd)
  · exact analyticAt_const.add analyticAt_fst
  · exact AnalyticAt.fun_comp
      (x := q) (g := secondRoot)
        (f := fun s : ℂ × (Fin 2 → ℂ) ↦ s.2 1) hsecond
          ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2
            |>.fun_comp analyticAt_snd)

theorem analyticAt_eCNineFirstRootBoundaryPowerParametrization
    (secondRoot : ℂ → ℂ) (q : ℂ × (Fin 2 → ℂ))
    (hsecond : AnalyticAt ℂ secondRoot (q.2 1)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineFirstRootBoundaryPowerParametrization
        secondRoot s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact analyticAt_fst
  · simpa [eCNineFirstRootBoundaryPowerParametrization,
      Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2
        |>.fun_comp analyticAt_snd)
  · exact AnalyticAt.fun_comp
      (x := q) (g := secondRoot)
        (f := fun s : ℂ × (Fin 2 → ℂ) ↦ s.2 1) hsecond
          ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2
            |>.fun_comp analyticAt_snd)

theorem analyticAt_eCNineFirstRootBoundaryFiniteParametrization
    (a : ℕ) (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineFirstRootBoundaryFiniteParametrization a s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact analyticAt_fst.pow a
  · simpa [eCNineFirstRootBoundaryFiniteParametrization,
      Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2
        |>.fun_comp analyticAt_snd)
  · simpa [eCNineFirstRootBoundaryFiniteParametrization,
      Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2
        |>.fun_comp analyticAt_snd)

theorem analyticAt_eCNineSecondRootBoundaryPowerParametrization
    (firstRoot : ℂ → ℂ) (q : ℂ × (Fin 2 → ℂ))
    (hfirst : AnalyticAt ℂ firstRoot (q.2 0)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineSecondRootBoundaryPowerParametrization
        firstRoot s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact AnalyticAt.fun_comp
      (x := q) (g := firstRoot)
        (f := fun s : ℂ × (Fin 2 → ℂ) ↦ s.2 0) hfirst
          ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2
            |>.fun_comp analyticAt_snd)
  · simpa [eCNineSecondRootBoundaryPowerParametrization,
      Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2
        |>.fun_comp analyticAt_snd)
  · exact analyticAt_fst

theorem analyticAt_eCNineSecondRootBoundaryFiniteParametrization
    (a : ℕ) (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineSecondRootBoundaryFiniteParametrization a s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · simpa [eCNineSecondRootBoundaryFiniteParametrization,
      Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2
        |>.fun_comp analyticAt_snd)
  · simpa [eCNineSecondRootBoundaryFiniteParametrization,
      Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2
        |>.fun_comp analyticAt_snd)
  · exact analyticAt_fst.pow a

/-- A transverse weighted chart persists when its special zeros map to the
finite ordinary C9 section. -/
theorem eventually_exists_eCNinePowerChartZero_mem_nhds
    (R : Form ℂ)
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (chart finiteParametrize : ECNineParametrization)
    (model : ℂ × (Fin 2 → ℂ) → Fin 2 → ℂ)
    (derivative : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))
    (q : Fin 2 → ℂ)
    (weightedBase ordinaryBase : Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hchart : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ chart s.1 s.2) (0, q))
    (hchartBase : chart 0 q = weightedBase)
    (hfiniteParametrize : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ finiteParametrize s.1 s.2)
        (0, q))
    (hfiniteBase : finiteParametrize 0 q = ordinaryBase)
    (hbaseDirection : ordinaryBase 1 ≠ 1)
    (hPhi : AnalyticAt ℂ Phi (0, weightedBase))
    (hcollision : Phi (0, weightedBase) = 0)
    (hspecialPlane : ∀ lambda v,
      eCNineParametrizedPlanePart Phi chart ((0, lambda), v) =
        model (lambda, v))
    (hspecialFull : ∀ lambda v,
      Phi (0, chart lambda v) =
        eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (finiteParametrize lambda v))
    (hmodelDerivative : HasStrictFDerivAt
      (fun v ↦ model (0, v)) derivative q)
    (hmodelInvertible : derivative.IsInvertible)
    (hparameter : ∀ lambda v,
      finiteParametrize lambda v = ordinaryBase → lambda = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, weightedBase)) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ, (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let plane := eCNineParametrizedPlanePart Phi chart
  let third := eCNineParametrizedThirdPart Phi chart
  have hPhiBase : AnalyticAt ℂ Phi (0, chart 0 q) := by
    simpa [hchartBase] using hPhi
  have hplane : AnalyticAt ℂ plane ((0, 0), q) :=
    analyticAt_eCNineParametrizedPlanePart Phi chart ((0, 0), q)
      hchart hPhiBase
  have hthird : AnalyticAt ℂ third ((0, 0), q) :=
    analyticAt_eCNineParametrizedThirdPart Phi chart ((0, 0), q)
      hchart hPhiBase
  have hpointEq :
      fderiv ℂ plane ((0, 0), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        derivative := by
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
        (fun v ↦ plane ((0, 0), v)) = fun v ↦ model (0, v) := by
      funext v
      exact hspecialPlane 0 v
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique hmodelDerivative.hasFDerivAt
  have hderivative :
      (fderiv ℂ plane ((0, 0), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact hmodelInvertible
  have hplaneZero : plane ((0, 0), q) = 0 := by
    funext i
    fin_cases i
    · change Phi (0, chart 0 q) 0 = 0
      rw [hchartBase]
      exact congrFun hcollision 0
    · change Phi (0, chart 0 q) 1 = 0
      rw [hchartBase]
      exact congrFun hcollision 1
  have hthirdZero : third ((0, 0), q) = 0 := by
    change Phi (0, chart 0 q) 2 = 0
    rw [hchartBase]
    exact congrFun hcollision 2
  have hfiniteTendsto : Tendsto
      (fun s : ℂ × (Fin 2 → ℂ) ↦ finiteParametrize s.1 s.2)
      (nhds (0, q)) (nhds ordinaryBase) := by
    have ht := hfiniteParametrize.continuousAt.tendsto
    rw [hfiniteBase] at ht
    exact ht
  have hdirection : ∀ᶠ s : ℂ × (Fin 2 → ℂ) in nhds (0, q),
      finiteParametrize s.1 s.2 1 ≠ 1 :=
    (tendsto_pi_nhds.mp hfiniteTendsto 1).eventually_ne hbaseDirection
  have hmem : ∀ᶠ s : ℂ × (Fin 2 → ℂ) in nhds (0, q),
      plane ((0, s.1), s.2) = 0 →
      third ((0, s.1), s.2) = 0 →
      finiteParametrize s.1 s.2 ∈ eCNineUnitSectionZeroSet R := by
    filter_upwards [hdirection] with s hsDirection hplaneAt hthirdAt
    apply mem_eCNineUnitSectionZeroSet_of_initialDifference_eq_zero
      R (finiteParametrize s.1 s.2) hsDirection
    rw [← hspecialFull s.1 s.2]
    funext i
    fin_cases i
    · exact congrFun hplaneAt 0
    · exact congrFun hplaneAt 1
    · exact hthirdAt
  let reparametrize : ((ℂ × ℂ) × (Fin 2 → ℂ)) →
      ℂ × (Fin 3 → ℂ) :=
    fun s ↦ (s.1.1, chart s.1.2 s.2)
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) := reparametrize ⁻¹' U
  have hreparametrize : AnalyticAt ℂ reparametrize ((0, 0), q) := by
    have hparameter : AnalyticAt ℂ
        (fun s : ((ℂ × ℂ) × (Fin 2 → ℂ)) ↦ s.1.1) ((0, 0), q) :=
      analyticAt_fst.fun_comp analyticAt_fst
    have hlocal : AnalyticAt ℂ
        (fun s : ((ℂ × ℂ) × (Fin 2 → ℂ)) ↦ (s.1.2, s.2))
          ((0, 0), q) :=
      (analyticAt_snd.fun_comp analyticAt_fst).prod analyticAt_snd
    exact hparameter.prod (hchart.comp_of_eq hlocal rfl)
  have hreparametrizeBase :
      reparametrize ((0, 0), q) = (0, weightedBase) := by
    simp [reparametrize, hchartBase]
  have hV : V ∈ nhds ((0, 0), q) := by
    have ht := hreparametrize.continuousAt.tendsto
    rw [hreparametrizeBase] at ht
    exact ht.eventually hU
  have hzero :=
    eventually_exists_fullZero_mem_nhds_of_finite_specialFiber
      plane third finiteParametrize q ordinaryBase
        (eCNineUnitSectionZeroSet R) hplane hderivative hplaneZero
          hthird hthirdZero hfiniteParametrize hfiniteBase hmem hparameter
            (eCNineUnitSectionZeroSet_finite R hnorm) V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hVAt, hplaneAt, hthirdAt⟩ := htau
  let branch := analyticImplicitBranch
    plane ((0, 0), q) hplane hderivative
  let point := chart lambda (branch (tau, lambda))
  refine ⟨point, hVAt, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

/-- The first two ordinary initial differences in the regular chart. -/
theorem eCNineRegularInitialPlane
    (R : Form ℂ) (z lambda : ℂ) (v : Fin 2 → ℂ) :
    ![eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (eCNineRegularParametrization z lambda v) 0,
      eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (eCNineRegularParametrization z lambda v) 1] =
      eCNineRegularPlaneDifference z (lambda, v) := by
  funext i
  fin_cases i
  · simp [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineRegularParametrization,
      eCNineRegularPlaneDifference, eInvariantPolynomialMap_first]
  · simp [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineRegularParametrization,
      eCNineRegularPlaneDifference, eInvariantPolynomialMap_second]

/-- The first two ordinary initial differences in the first root boundary
chart after powering its parameter. -/
@[expose]
def eCNineFirstRootBoundaryPlaneDifferencePower
    (a : ℕ) (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  eCNineFirstRootBoundaryPlaneDifference (s.1 ^ a, s.2)

theorem eCNineFirstRootBoundaryInitialPlane
    (a : ℕ) (R : Form ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    ![eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (eCNineFirstRootBoundaryFiniteParametrization a lambda v) 0,
      eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (eCNineFirstRootBoundaryFiniteParametrization a lambda v) 1] =
      eCNineFirstRootBoundaryPlaneDifferencePower a (lambda, v) := by
  funext i
  fin_cases i
  · simp [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint,
      eCNineFirstRootBoundaryFiniteParametrization,
      eCNineFirstRootBoundaryPlaneDifferencePower,
      eCNineFirstRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_first]
  · simp [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint,
      eCNineFirstRootBoundaryFiniteParametrization,
      eCNineFirstRootBoundaryPlaneDifferencePower,
      eCNineFirstRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_second]

/-- The first two ordinary initial differences in the second root boundary
chart after powering its parameter. -/
@[expose]
def eCNineSecondRootBoundaryPlaneDifferencePower
    (a : ℕ) (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  eCNineSecondRootBoundaryPlaneDifference (s.1 ^ a, s.2)

theorem eCNineSecondRootBoundaryInitialPlane
    (a : ℕ) (R : Form ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) :
    ![eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (eCNineSecondRootBoundaryFiniteParametrization a lambda v) 0,
      eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (eCNineSecondRootBoundaryFiniteParametrization a lambda v) 1] =
      eCNineSecondRootBoundaryPlaneDifferencePower a (lambda, v) := by
  funext i
  fin_cases i
  · simp [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint,
      eCNineSecondRootBoundaryFiniteParametrization,
      eCNineSecondRootBoundaryPlaneDifferencePower,
      eCNineSecondRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_first]
  · simp [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint,
      eCNineSecondRootBoundaryFiniteParametrization,
      eCNineSecondRootBoundaryPlaneDifferencePower,
      eCNineSecondRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_second]

theorem eCNinePowerChart_regularRootParametrization
    (a : ℕ) (z : ℂ) (firstRoot secondRoot : ℂ → ℂ)
    (hfirst : ∀ w, firstRoot w ^ a = w)
    (hsecond : ∀ w, secondRoot w ^ a = w)
    (lambda : ℂ) (v : Fin 2 → ℂ) :
    eCNinePowerChart a
        (eCNineRegularRootParametrization
          z firstRoot secondRoot lambda v) =
      eCNineRegularParametrization z lambda v := by
  funext i
  fin_cases i
  · change firstRoot (v 0) ^ a = v 0
    exact hfirst (v 0)
  · rfl
  · change secondRoot (v 1) ^ a = v 1
    exact hsecond (v 1)

theorem eCNinePowerChart_firstRootBoundaryPowerParametrization
    (a : ℕ) (secondRoot : ℂ → ℂ)
    (hsecond : ∀ w, secondRoot w ^ a = w)
    (lambda : ℂ) (v : Fin 2 → ℂ) :
    eCNinePowerChart a
        (eCNineFirstRootBoundaryPowerParametrization secondRoot lambda v) =
      eCNineFirstRootBoundaryFiniteParametrization a lambda v := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp [eCNinePowerChart,
      eCNineFirstRootBoundaryPowerParametrization,
      eCNineFirstRootBoundaryFiniteParametrization, hsecond]

theorem eCNinePowerChart_secondRootBoundaryPowerParametrization
    (a : ℕ) (firstRoot : ℂ → ℂ)
    (hfirst : ∀ w, firstRoot w ^ a = w)
    (lambda : ℂ) (v : Fin 2 → ℂ) :
    eCNinePowerChart a
        (eCNineSecondRootBoundaryPowerParametrization firstRoot lambda v) =
      eCNineSecondRootBoundaryFiniteParametrization a lambda v := by
  funext i
  fin_cases i
  · simp [eCNinePowerChart,
      eCNineSecondRootBoundaryPowerParametrization,
      eCNineSecondRootBoundaryFiniteParametrization, hfirst]
  · rfl
  · rfl

theorem eCNineRegularPointDerivative_isInvertible
    (z t T : ℂ) (hz : z ≠ 1) (ht : t ≠ 0) (hT : T ≠ 0) :
    (eCNineRegularPointDerivative z t T).IsInvertible := by
  let pointEquiv :=
    (eCNineRegularPointDerivative z t T)
      |>.toContinuousLinearEquivOfDetNeZero <| by
        rw [det_eCNineRegularPointDerivative]
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))
            (pow_ne_zero 2 hT)) (sub_ne_zero.mpr hz.symm)
  have hcoe :
      (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) =
        eCNineRegularPointDerivative z t T :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  rw [← hcoe]
  exact ContinuousLinearMap.isInvertible_equiv

theorem eCNineFirstRootBoundaryPointDerivative_isInvertible
    (z T : ℂ) (hT : T ≠ 0) :
    (eCNineFirstRootBoundaryPointDerivative z T).IsInvertible := by
  let pointEquiv :=
    (eCNineFirstRootBoundaryPointDerivative z T)
      |>.toContinuousLinearEquivOfDetNeZero <| by
        rw [det_eCNineFirstRootBoundaryPointDerivative]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 5 hT)
  have hcoe :
      (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) =
        eCNineFirstRootBoundaryPointDerivative z T :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  rw [← hcoe]
  exact ContinuousLinearMap.isInvertible_equiv

theorem eCNineSecondRootBoundaryPointDerivative_isInvertible
    (t z : ℂ) (hz : z ≠ 1) (ht : t ≠ 0) (hzZero : z ≠ 0) :
    (eCNineSecondRootBoundaryPointDerivative t z).IsInvertible := by
  let pointEquiv :=
    (eCNineSecondRootBoundaryPointDerivative t z)
      |>.toContinuousLinearEquivOfDetNeZero <| by
        rw [det_eCNineSecondRootBoundaryPointDerivative]
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))
            (pow_ne_zero 2 hzZero)) (sub_ne_zero.mpr hz.symm)
  have hcoe :
      (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) =
        eCNineSecondRootBoundaryPointDerivative t z :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  rw [← hcoe]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Persistence in the powered C9 chart when both ordinary root coordinates
are nonzero. -/
theorem eventually_exists_eResidueZeroCNineRegularZero_mem_nhds
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (t z T eta Theta : ℂ) (heta : eta ^ a = t)
    (hTheta : Theta ^ a = T)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hz : z ≠ 1) (ht : t ≠ 0) (hT : T ≠ 0)
    (hfirst : AnalyticAt ℂ remainder (0, (1, eta)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, Theta)))
    (hcollision : eCNineXChartInitialDifference
      (eResidueZeroInitialMap a R) ![eta, z, Theta] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![eta, z, Theta])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  obtain ⟨firstRoot, hfirstRoot, hfirstRootValue, hfirstRootPower⟩ :=
    exists_analyticAt_root_identity_with_value a ha t eta ht heta
  obtain ⟨secondRoot, hsecondRoot, hsecondRootValue, hsecondRootPower⟩ :=
    exists_analyticAt_root_identity_with_value a ha T Theta hT hTheta
  let Phi := eCNineXChartRescaledPerturbation
    (eResidueZeroInitialMap a R) remainder
  let chart := eCNineRegularRootParametrization z firstRoot secondRoot
  let q : Fin 2 → ℂ := ![t, T]
  let weightedBase : Fin 3 → ℂ := ![eta, z, Theta]
  let ordinaryBase : Fin 3 → ℂ := ![t, z, T]
  have hchartBase : chart 0 q = weightedBase := by
    funext i
    fin_cases i
    · simp [chart, q, weightedBase, eCNineRegularRootParametrization,
        hfirstRootValue]
    · simp [chart, q, weightedBase, eCNineRegularRootParametrization]
    · simp [chart, q, weightedBase, eCNineRegularRootParametrization,
        hsecondRootValue]
  have hfiniteBase : eCNineRegularParametrization z 0 q = ordinaryBase := by
    funext i
    fin_cases i <;>
      simp [q, ordinaryBase, eCNineRegularParametrization]
  have hPhi : AnalyticAt ℂ Phi (0, weightedBase) := by
    apply analyticAt_eCNineXChartRescaledPerturbation
    · exact analyticAt_eCNineXChartInitialDifference_weightedPolynomialMap
        (eResidueZeroPolynomialMap a R) weightedBase
    · simpa [weightedBase, eCNineXChartFirstPoint,
        eResidueZeroInitialMap] using hfirst
    · simpa [weightedBase, eCNineXChartSecondPoint,
        eResidueZeroInitialMap] using hsecond
  have hspecialFull (lambda : ℂ) (v : Fin 2 → ℂ) :
      Phi (0, chart lambda v) =
        eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (eCNineRegularParametrization z lambda v) := by
    dsimp only [Phi, chart]
    rw [eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference_eResidueZeroInitialMap]
    rw [eCNinePowerChart_regularRootParametrization
      a z firstRoot secondRoot hfirstRootPower hsecondRootPower]
  apply eventually_exists_eCNinePowerChartZero_mem_nhds
    R Phi chart (eCNineRegularParametrization z)
      (eCNineRegularPlaneDifference z)
        (eCNineRegularPointDerivative z t T) q weightedBase ordinaryBase hnorm
  · exact analyticAt_eCNineRegularRootParametrization
      z firstRoot secondRoot (0, q)
        (by simpa [q] using hfirstRoot)
        (by simpa [q] using hsecondRoot)
  · exact hchartBase
  · exact analyticAt_eCNineRegularParametrization z (0, q)
  · exact hfiniteBase
  · simpa [ordinaryBase] using hz
  · exact hPhi
  · simpa [Phi, weightedBase] using hcollision
  · intro lambda v
    funext i
    fin_cases i
    · exact congrFun (hspecialFull lambda v) 0 |>.trans
        (congrFun (eCNineRegularInitialPlane R z lambda v) 0)
    · exact congrFun (hspecialFull lambda v) 1 |>.trans
        (congrFun (eCNineRegularInitialPlane R z lambda v) 1)
  · exact hspecialFull
  · simpa [q] using
      hasStrictFDerivAt_eCNineRegularPlaneDifference_point z t T
  · exact eCNineRegularPointDerivative_isInvertible z t T hz ht hT
  · intro lambda v heq
    have hcoordinate : z + lambda = z := by
      simpa [eCNineRegularParametrization, ordinaryBase] using congrFun heq 1
    linear_combination hcoordinate
  · simpa [weightedBase] using hU

/-- Persistence in the powered C9 chart at a zero first root coordinate. -/
theorem eventually_exists_eResidueZeroCNineFirstRootBoundaryZero_mem_nhds
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (z T Theta : ℂ) (hTheta : Theta ^ a = T)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hz : z ≠ 1) (hT : T ≠ 0)
    (hfirst : AnalyticAt ℂ remainder (0, (1, 0)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, Theta)))
    (hcollision : eCNineXChartInitialDifference
      (eResidueZeroInitialMap a R) ![0, z, Theta] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![0, z, Theta])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  obtain ⟨secondRoot, hsecondRoot, hsecondRootValue, hsecondRootPower⟩ :=
    exists_analyticAt_root_identity_with_value a ha T Theta hT hTheta
  let Phi := eCNineXChartRescaledPerturbation
    (eResidueZeroInitialMap a R) remainder
  let chart := eCNineFirstRootBoundaryPowerParametrization secondRoot
  let finiteParametrize := eCNineFirstRootBoundaryFiniteParametrization a
  let q : Fin 2 → ℂ := ![z, T]
  let weightedBase : Fin 3 → ℂ := ![0, z, Theta]
  let ordinaryBase : Fin 3 → ℂ := ![0, z, T]
  have hchartBase : chart 0 q = weightedBase := by
    funext i
    fin_cases i <;>
      simp [chart, q, weightedBase,
        eCNineFirstRootBoundaryPowerParametrization, hsecondRootValue]
  have hfiniteBase : finiteParametrize 0 q = ordinaryBase := by
    funext i
    fin_cases i <;>
      simp [finiteParametrize, q, ordinaryBase,
        eCNineFirstRootBoundaryFiniteParametrization, zero_pow ha.ne']
  have hPhi : AnalyticAt ℂ Phi (0, weightedBase) := by
    apply analyticAt_eCNineXChartRescaledPerturbation
    · exact analyticAt_eCNineXChartInitialDifference_weightedPolynomialMap
        (eResidueZeroPolynomialMap a R) weightedBase
    · simpa [weightedBase, eCNineXChartFirstPoint,
        eResidueZeroInitialMap] using hfirst
    · simpa [weightedBase, eCNineXChartSecondPoint,
        eResidueZeroInitialMap] using hsecond
  have hspecialFull (lambda : ℂ) (v : Fin 2 → ℂ) :
      Phi (0, chart lambda v) =
        eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (finiteParametrize lambda v) := by
    dsimp only [Phi, chart, finiteParametrize]
    rw [eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference_eResidueZeroInitialMap]
    rw [eCNinePowerChart_firstRootBoundaryPowerParametrization
      a secondRoot hsecondRootPower]
  apply eventually_exists_eCNinePowerChartZero_mem_nhds
    R Phi chart finiteParametrize
      (eCNineFirstRootBoundaryPlaneDifferencePower a)
        (eCNineFirstRootBoundaryPointDerivative z T)
          q weightedBase ordinaryBase hnorm
  · exact analyticAt_eCNineFirstRootBoundaryPowerParametrization
      secondRoot (0, q) (by simpa [q] using hsecondRoot)
  · exact hchartBase
  · exact analyticAt_eCNineFirstRootBoundaryFiniteParametrization a (0, q)
  · exact hfiniteBase
  · simpa [ordinaryBase] using hz
  · exact hPhi
  · simpa [Phi, weightedBase] using hcollision
  · intro lambda v
    funext i
    fin_cases i
    · exact congrFun (hspecialFull lambda v) 0 |>.trans
        (congrFun (eCNineFirstRootBoundaryInitialPlane a R lambda v) 0)
    · exact congrFun (hspecialFull lambda v) 1 |>.trans
        (congrFun (eCNineFirstRootBoundaryInitialPlane a R lambda v) 1)
  · exact hspecialFull
  · simpa [eCNineFirstRootBoundaryPlaneDifferencePower,
      zero_pow ha.ne', q] using
      hasStrictFDerivAt_eCNineFirstRootBoundaryPlaneDifference_point z T
  · exact eCNineFirstRootBoundaryPointDerivative_isInvertible z T hT
  · intro lambda v heq
    have hpower : lambda ^ a = 0 := by
      simpa [finiteParametrize, ordinaryBase,
        eCNineFirstRootBoundaryFiniteParametrization] using congrFun heq 0
    exact (pow_eq_zero_iff ha.ne').mp hpower
  · simpa [weightedBase] using hU

/-- Persistence in the powered C9 chart at a zero second root coordinate. -/
theorem eventually_exists_eResidueZeroCNineSecondRootBoundaryZero_mem_nhds
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (t z eta : ℂ) (heta : eta ^ a = t)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hz : z ≠ 1) (ht : t ≠ 0) (hzZero : z ≠ 0)
    (hfirst : AnalyticAt ℂ remainder (0, (1, eta)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, 0)))
    (hcollision : eCNineXChartInitialDifference
      (eResidueZeroInitialMap a R) ![eta, z, 0] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![eta, z, 0])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  obtain ⟨firstRoot, hfirstRoot, hfirstRootValue, hfirstRootPower⟩ :=
    exists_analyticAt_root_identity_with_value a ha t eta ht heta
  let Phi := eCNineXChartRescaledPerturbation
    (eResidueZeroInitialMap a R) remainder
  let chart := eCNineSecondRootBoundaryPowerParametrization firstRoot
  let finiteParametrize := eCNineSecondRootBoundaryFiniteParametrization a
  let q : Fin 2 → ℂ := ![t, z]
  let weightedBase : Fin 3 → ℂ := ![eta, z, 0]
  let ordinaryBase : Fin 3 → ℂ := ![t, z, 0]
  have hchartBase : chart 0 q = weightedBase := by
    funext i
    fin_cases i <;>
      simp [chart, q, weightedBase,
        eCNineSecondRootBoundaryPowerParametrization, hfirstRootValue]
  have hfiniteBase : finiteParametrize 0 q = ordinaryBase := by
    funext i
    fin_cases i <;>
      simp [finiteParametrize, q, ordinaryBase,
        eCNineSecondRootBoundaryFiniteParametrization, zero_pow ha.ne']
  have hPhi : AnalyticAt ℂ Phi (0, weightedBase) := by
    apply analyticAt_eCNineXChartRescaledPerturbation
    · exact analyticAt_eCNineXChartInitialDifference_weightedPolynomialMap
        (eResidueZeroPolynomialMap a R) weightedBase
    · simpa [weightedBase, eCNineXChartFirstPoint,
        eResidueZeroInitialMap] using hfirst
    · simpa [weightedBase, eCNineXChartSecondPoint,
        eResidueZeroInitialMap] using hsecond
  have hspecialFull (lambda : ℂ) (v : Fin 2 → ℂ) :
      Phi (0, chart lambda v) =
        eCNineXChartInitialDifference
          (weightedPolynomialMap (eInvariantPolynomialMap R))
            (finiteParametrize lambda v) := by
    dsimp only [Phi, chart, finiteParametrize]
    rw [eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference_eResidueZeroInitialMap]
    rw [eCNinePowerChart_secondRootBoundaryPowerParametrization
      a firstRoot hfirstRootPower]
  apply eventually_exists_eCNinePowerChartZero_mem_nhds
    R Phi chart finiteParametrize
      (eCNineSecondRootBoundaryPlaneDifferencePower a)
        (eCNineSecondRootBoundaryPointDerivative t z)
          q weightedBase ordinaryBase hnorm
  · exact analyticAt_eCNineSecondRootBoundaryPowerParametrization
      firstRoot (0, q) (by simpa [q] using hfirstRoot)
  · exact hchartBase
  · exact analyticAt_eCNineSecondRootBoundaryFiniteParametrization a (0, q)
  · exact hfiniteBase
  · simpa [ordinaryBase] using hz
  · exact hPhi
  · simpa [Phi, weightedBase] using hcollision
  · intro lambda v
    funext i
    fin_cases i
    · exact congrFun (hspecialFull lambda v) 0 |>.trans
        (congrFun (eCNineSecondRootBoundaryInitialPlane a R lambda v) 0)
    · exact congrFun (hspecialFull lambda v) 1 |>.trans
        (congrFun (eCNineSecondRootBoundaryInitialPlane a R lambda v) 1)
  · exact hspecialFull
  · simpa [eCNineSecondRootBoundaryPlaneDifferencePower,
      zero_pow ha.ne', q] using
      hasStrictFDerivAt_eCNineSecondRootBoundaryPlaneDifference_point t z
  · exact eCNineSecondRootBoundaryPointDerivative_isInvertible
      t z hz ht hzZero
  · intro lambda v heq
    have hpower : lambda ^ a = 0 := by
      simpa [finiteParametrize, ordinaryBase,
        eCNineSecondRootBoundaryFiniteParametrization] using congrFun heq 2
    exact (pow_eq_zero_iff ha.ne').mp hpower
  · simpa [weightedBase] using hU

/-- Every lifted affine C9 collision away from the diagonal lies in one of
the three powered transverse charts. -/
theorem eventually_exists_eResidueZeroCNineZero_mem_nhds
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (t z T eta Theta : ℂ) (heta : eta ^ a = t)
    (hTheta : Theta ^ a = T)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hequations : ECNineEquations 1 t z T)
    (hz : z ≠ 1)
    (hfirst : AnalyticAt ℂ remainder (0, (1, eta)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, Theta)))
    (hcollision : eCNineXChartInitialDifference
      (eResidueZeroInitialMap a R) ![eta, z, Theta] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![eta, z, Theta])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  by_cases ht : t = 0
  · have hetaZero : eta = 0 := by
      apply (pow_eq_zero_iff ha.ne').mp
      rw [heta, ht]
    subst eta
    exact eventually_exists_eResidueZeroCNineFirstRootBoundaryZero_mem_nhds
      a ha R z T Theta hTheta remainder hnorm hz
        (eCNine_second_root_ne_zero_of_first_root_eq_zero
          hequations hz ht) hfirst hsecond hcollision U hU
  · by_cases hT : T = 0
    · have hThetaZero : Theta = 0 := by
        apply (pow_eq_zero_iff ha.ne').mp
        rw [hTheta, hT]
      subst Theta
      exact eventually_exists_eResidueZeroCNineSecondRootBoundaryZero_mem_nhds
        a ha R t z eta heta remainder hnorm hz ht
          (eCNine_direction_ne_zero_of_second_root_eq_zero hequations hT)
            hfirst hsecond hcollision U hU
    · exact eventually_exists_eResidueZeroCNineRegularZero_mem_nhds
        a ha R t z T eta Theta heta hTheta remainder hnorm hz ht hT
          hfirst hsecond hcollision U hU

end OnLeConjecture.DThree
