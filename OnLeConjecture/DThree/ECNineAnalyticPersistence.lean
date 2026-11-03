/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineAffineZeroFiniteness
public import OnLeConjecture.DThree.ResidueRotationNoninjectivity
public import OnLeConjecture.DThree.WeightedOrderExpansion
public import OnLeConjecture.Analytic.OrdinaryWeightedOrder

/-!
# Analytic persistence of C9 collisions

The nonzero determinant norm makes the special fibre zero set finite. The
first two C9 equations are eliminated in three charts. The remaining scalar
equation has positive finite order and therefore persists under analytic
weighted perturbations.
-/

public section

noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A finite special fibre makes the scalar equation obtained after
transverse elimination nonzero. Its zero at the base point therefore has
positive finite order. -/
theorem eventually_exists_fullZero_mem_nhds_of_finite_specialFiber
    (plane : ((ℂ × ℂ) × (Fin 2 → ℂ)) → Fin 2 → ℂ)
    (third : ((ℂ × ℂ) × (Fin 2 → ℂ)) → ℂ)
    (parametrize : ℂ → (Fin 2 → ℂ) → Fin 3 → ℂ)
    (q : Fin 2 → ℂ) (base : Fin 3 → ℂ)
    (specialZeroSet : Set (Fin 3 → ℂ))
    (hplane : AnalyticAt ℂ plane ((0, 0), q))
    (hderivative :
      (fderiv ℂ plane ((0, 0), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible)
    (hplaneZero : plane ((0, 0), q) = 0)
    (hthird : AnalyticAt ℂ third ((0, 0), q))
    (hthirdZero : third ((0, 0), q) = 0)
    (hparametrize : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ parametrize s.1 s.2) (0, q))
    (hparametrizeBase : parametrize 0 q = base)
    (hmem : ∀ᶠ s : ℂ × (Fin 2 → ℂ) in nhds (0, q),
      plane ((0, s.1), s.2) = 0 →
      third ((0, s.1), s.2) = 0 →
      parametrize s.1 s.2 ∈ specialZeroSet)
    (hparameter : ∀ lambda v,
      parametrize lambda v = base → lambda = 0)
    (hfinite : specialZeroSet.Finite)
    (U : Set (((ℂ × ℂ) × (Fin 2 → ℂ))))
    (hU : U ∈ nhds ((0, 0), q)) :
    ∀ᶠ tau in nhds 0,
      ∃ lambda,
        ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hderivative
            (tau, lambda)) ∈ U ∧
        plane ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hderivative
            (tau, lambda)) = 0 ∧
        third ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hderivative
            (tau, lambda)) = 0 := by
  let branch := analyticImplicitBranch
    plane ((0, 0), q) hplane hderivative
  have hbranch : AnalyticAt ℂ branch (0, 0) :=
    analyticAt_analyticImplicitBranch
      plane ((0, 0), q) hplane hderivative
  have hbranchBase : branch (0, 0) = q :=
    analyticImplicitBranch_apply_base
      plane ((0, 0), q) hplane hderivative
  let scalar : ℂ → ℂ := fun lambda ↦
    third ((0, lambda), branch (0, lambda))
  have hembed : AnalyticAt ℂ
      (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hbranchSpecial : AnalyticAt ℂ
      (fun lambda ↦ branch (0, lambda)) 0 :=
    hbranch.fun_comp hembed
  have hlift : AnalyticAt ℂ
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ), branch (0, lambda))) 0 :=
    hembed.prod hbranchSpecial
  have hliftBase :
      (((0, 0) : ℂ × ℂ), branch (0, 0)) = (((0, 0) : ℂ × ℂ), q) := by
    rw [hbranchBase]
  have hscalar : AnalyticAt ℂ scalar 0 := by
    simpa [scalar, Function.comp_def] using
      hthird.comp_of_eq hlift hliftBase
  have hplaneBranch : ∀ᶠ p in nhds (0, 0),
      plane (p, branch p) = 0 := by
    filter_upwards
      [eventually_analyticImplicitBranch_eq
        plane ((0, 0), q) hplane hderivative] with p hp
    simpa [hplaneZero] using hp
  have hplaneSpecial : ∀ᶠ lambda in nhds 0,
      plane ((0, lambda), branch (0, lambda)) = 0 :=
    hembed.continuousAt.tendsto.eventually hplaneBranch
  have hparametrized : AnalyticAt ℂ
      (fun lambda ↦ parametrize lambda (branch (0, lambda))) 0 :=
    hparametrize.comp_of_eq (analyticAt_id.prod hbranchSpecial) (by
      simp [hbranchBase])
  have hparametrizedBase :
      parametrize 0 (branch (0, 0)) = base := by
    rw [hbranchBase, hparametrizeBase]
  have hbaseMem : base ∈ specialZeroSet := by
    rw [← hparametrizeBase]
    exact hmem.self_of_nhds hplaneZero hthirdZero
  have hspecialInput : Tendsto
      (fun lambda ↦ (lambda, branch (0, lambda)))
      (nhds 0) (nhds (0, q)) := by
    have ht := (analyticAt_id.prod hbranchSpecial).continuousAt.tendsto
    simpa [hbranchBase] using ht
  have hmemSpecial : ∀ᶠ lambda in nhds 0,
      plane ((0, lambda), branch (0, lambda)) = 0 →
      third ((0, lambda), branch (0, lambda)) = 0 →
      parametrize lambda (branch (0, lambda)) ∈ specialZeroSet :=
    hspecialInput.eventually hmem
  have hscalarNotZero : ¬∀ᶠ lambda in nhds 0, scalar lambda = 0 := by
    intro hzero
    have hspecialMem : ∀ᶠ lambda in nhds 0,
        parametrize lambda (branch (0, lambda)) ∈ specialZeroSet := by
      filter_upwards [hplaneSpecial, hzero, hmemSpecial] with
        lambda hplaneAt hthirdAt hmemAt
      exact hmemAt hplaneAt hthirdAt
    have htendsto : Tendsto
        (fun lambda ↦ parametrize lambda (branch (0, lambda)))
        (nhds 0) (nhds base) := by
      have ht := hparametrized.continuousAt.tendsto
      rw [hparametrizedBase] at ht
      exact ht
    have htendstoWithin : Tendsto
        (fun lambda ↦ parametrize lambda (branch (0, lambda)))
        (nhds 0) (nhdsWithin base specialZeroSet) := by
      rw [nhdsWithin]
      simpa using htendsto.inf
        (show Tendsto
          (fun lambda ↦ parametrize lambda (branch (0, lambda)))
          (nhds 0) (Filter.principal specialZeroSet) by
            rw [tendsto_principal]
            exact hspecialMem)
    rw [hfinite.isDiscrete.nhdsWithin base hbaseMem] at htendstoWithin
    have hequal : ∀ᶠ lambda in nhds 0,
        parametrize lambda (branch (0, lambda)) = base :=
      Filter.tendsto_pure.mp htendstoWithin
    have hlambdaZero : ∀ᶠ lambda : ℂ in nhds 0, lambda = 0 :=
      hequal.mono fun lambda hEq ↦
        hparameter lambda (branch (0, lambda)) hEq
    have hfalse : ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
        lambda = 0 ∧ lambda ≠ 0 := by
      filter_upwards
        [hlambdaZero.filter_mono nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin] with lambda hEq hmemComplement
      exact ⟨hEq, by simpa using hmemComplement⟩
    obtain ⟨lambda, hlambda, hlambdaNe⟩ := hfalse.exists
    exact hlambdaNe hlambda
  obtain ⟨m, u, hu, hu0, hfactorRaw⟩ :=
    hscalar.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hscalarNotZero
  have hfactor : ∀ᶠ lambda in nhds 0,
      scalar lambda = lambda ^ m * u lambda := by
    simpa [sub_zero, smul_eq_mul] using hfactorRaw
  have hscalarZero : scalar 0 = 0 := by
    simp [scalar, hbranchBase, hthirdZero]
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hmZero
    have hfactorAt := hfactor.self_of_nhds
    rw [hmZero, pow_zero, one_mul, hscalarZero] at hfactorAt
    exact hu0 hfactorAt.symm
  exact eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hderivative hplaneZero hthird m u hm hu hu0
      (by simpa [scalar, branch] using hfactor) U hU

/-- The first source point in the affine chart `x = 1`. -/
@[expose]
def eCNineXChartFirstPoint (q : Fin 3 → ℂ) : ℂ × ℂ :=
  (1, q 0)

/-- The second source point in the affine chart `x = 1`. -/
@[expose]
def eCNineXChartSecondPoint (q : Fin 3 → ℂ) : ℂ × ℂ :=
  (q 1, q 2)

/-- The initial difference in the affine chart `x = 1`. -/
@[expose]
def eCNineXChartInitialDifference
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  initialMap (eCNineXChartFirstPoint q) -
    initialMap (eCNineXChartSecondPoint q)

/-- The difference of the two analytic radial remainders. -/
@[expose]
def eCNineXChartRemainderDifference
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (s : ℂ × (Fin 3 → ℂ)) : Fin 3 → ℂ :=
  remainder (s.1, eCNineXChartFirstPoint s.2) -
    remainder (s.1, eCNineXChartSecondPoint s.2)

/-- The extended divided difference in the chart `x = 1`. -/
@[expose]
def eCNineXChartRescaledPerturbation
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (s : ℂ × (Fin 3 → ℂ)) : Fin 3 → ℂ :=
  eCNineXChartInitialDifference initialMap s.2 +
    s.1 • eCNineXChartRemainderDifference remainder s

@[simp]
theorem eCNineXChartRescaledPerturbation_zero
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (q : Fin 3 → ℂ) :
    eCNineXChartRescaledPerturbation initialMap remainder (0, q) =
      eCNineXChartInitialDifference initialMap q := by
  simp [eCNineXChartRescaledPerturbation]

theorem analyticAt_eCNineXChartFirstPoint (q : Fin 3 → ℂ) :
    AnalyticAt ℂ eCNineXChartFirstPoint q := by
  change AnalyticAt ℂ (fun q : Fin 3 → ℂ ↦ (1, q 0)) q
  exact analyticAt_const.prod
    ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt q)

theorem analyticAt_eCNineXChartSecondPoint (q : Fin 3 → ℂ) :
    AnalyticAt ℂ eCNineXChartSecondPoint q := by
  change AnalyticAt ℂ (fun q : Fin 3 → ℂ ↦ (q 1, q 2)) q
  exact ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt q).prod
    ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt q)

theorem analyticAt_eCNineXChartRescaledPerturbation
    (initialMap : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (p : Fin 3 → ℂ)
    (hinitial : AnalyticAt ℂ (eCNineXChartInitialDifference initialMap) p)
    (hfirst : AnalyticAt ℂ remainder (0, eCNineXChartFirstPoint p))
    (hsecond : AnalyticAt ℂ remainder (0, eCNineXChartSecondPoint p)) :
    AnalyticAt ℂ
      (eCNineXChartRescaledPerturbation initialMap remainder) (0, p) := by
  have hfirstLift : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1, eCNineXChartFirstPoint s.2)) (0, p) :=
    analyticAt_fst.prod
      ((analyticAt_eCNineXChartFirstPoint p).fun_comp analyticAt_snd)
  have hsecondLift : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1, eCNineXChartSecondPoint s.2)) (0, p) :=
    analyticAt_fst.prod
      ((analyticAt_eCNineXChartSecondPoint p).fun_comp analyticAt_snd)
  have hfirstRemainder : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        remainder (s.1, eCNineXChartFirstPoint s.2)) (0, p) :=
    hfirst.comp_of_eq hfirstLift rfl
  have hsecondRemainder : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        remainder (s.1, eCNineXChartSecondPoint s.2)) (0, p) :=
    hsecond.comp_of_eq hsecondLift rfl
  have hremainder : AnalyticAt ℂ
      (eCNineXChartRemainderDifference remainder) (0, p) := by
    change AnalyticAt ℂ
      ((fun s ↦ remainder (s.1, eCNineXChartFirstPoint s.2)) -
        fun s ↦ remainder (s.1, eCNineXChartSecondPoint s.2)) (0, p)
    exact hfirstRemainder.sub hsecondRemainder
  have hinitialLift : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        eCNineXChartInitialDifference initialMap s.2) (0, p) :=
    hinitial.fun_comp analyticAt_snd
  change AnalyticAt ℂ
    ((fun s : ℂ × (Fin 3 → ℂ) ↦
      eCNineXChartInitialDifference initialMap s.2) +
      fun s ↦ s.1 • eCNineXChartRemainderDifference remainder s) (0, p)
  exact hinitialLift.add (analyticAt_fst.smul hremainder)

theorem analyticAt_eCNineXChartInitialDifference_weightedPolynomialMap
    (P : Fin 3 → Form ℂ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (eCNineXChartInitialDifference (weightedPolynomialMap P)) q := by
  change AnalyticAt ℂ
    ((fun q ↦ weightedPolynomialMap P (eCNineXChartFirstPoint q)) -
      fun q ↦ weightedPolynomialMap P (eCNineXChartSecondPoint q)) q
  have hweighted (point : ℂ × ℂ) :
      AnalyticAt ℂ (weightedPolynomialMap P) point := by
    rw [analyticAt_pi_iff]
    intro i
    have hcoordinate (j : Fin 2) : AnalyticAt ℂ
        (fun z : ℂ × ℂ ↦
          (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z j) point := by
      exact (((ContinuousLinearMap.proj (R := ℂ) j).comp
        (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.toContinuousLinearMap)
          |>.analyticAt point)
    change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ MvPolynomial.eval
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) (P i)) point
    simpa [MvPolynomial.aeval_def] using
      AnalyticAt.aeval_mvPolynomial hcoordinate (P i)
  exact
    (hweighted (eCNineXChartFirstPoint q)).fun_comp
      (analyticAt_eCNineXChartFirstPoint q) |>.sub
        ((hweighted (eCNineXChartSecondPoint q)).fun_comp
            (analyticAt_eCNineXChartSecondPoint q))

/-- A zero of all three initial differences away from the diagonal belongs
to the finite affine C9 section zero set. -/
theorem mem_eCNineUnitSectionZeroSet_of_initialDifference_eq_zero
    (R : Form ℂ) (q : Fin 3 → ℂ) (hq : q 1 ≠ 1)
    (hzero : eCNineXChartInitialDifference
      (weightedPolynomialMap (eInvariantPolynomialMap R)) q = 0) :
    q ∈ eCNineUnitSectionZeroSet R := by
  have hfirstValue := congrFun hzero 0
  have hsecondValue := congrFun hzero 1
  have hthirdValue := congrFun hzero 2
  have hP : eP 1 ((q 0) ^ 3) = eP (q 1) ((q 2) ^ 3) := by
    apply sub_eq_zero.mp
    simpa [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eInvariantPolynomialMap_first] using hfirstValue
  have hQ : eQ 1 ((q 0) ^ 3) = eQ (q 1) ((q 2) ^ 3) := by
    apply sub_eq_zero.mp
    simpa [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eInvariantPolynomialMap_second] using hsecondValue
  have hequations : ECNineEquations 1 (q 0) (q 1) (q 2) :=
    (e_fibre_iff_C9 (fun h ↦ hq h.symm)).mp ⟨hP, hQ⟩
  refine ⟨hequations, ?_⟩
  simpa [eCNineXChartInitialDifference, eCNineXChartFirstPoint,
    eCNineXChartSecondPoint, weightedPolynomialMap,
    eInvariantPolynomialMap, eCNineDifferenceValue] using hthirdValue

/-- A three variable point obtained by choosing a curve parameter and two
point variables. -/
abbrev ECNineParametrization := ℂ → (Fin 2 → ℂ) → Fin 3 → ℂ

/-- The first two coordinates of a rescaled difference after a local
parametrization of the C9 curve. -/
@[expose]
def eCNineParametrizedPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (parametrize : ECNineParametrization)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (s.1.1, parametrize s.1.2 s.2) 0,
    Phi (s.1.1, parametrize s.1.2 s.2) 1]

/-- The third coordinate after a local parametrization of the C9 curve. -/
@[expose]
def eCNineParametrizedThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (parametrize : ECNineParametrization)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (s.1.1, parametrize s.1.2 s.2) 2

theorem analyticAt_eCNineParametrizedReparametrization
    (parametrize : ECNineParametrization)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hparametrize : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ parametrize s.1 s.2)
        (q.1.2, q.2)) :
    AnalyticAt ℂ
      (fun s : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        (s.1.1, parametrize s.1.2 s.2)) q := by
  have hparameter : AnalyticAt ℂ
      (fun s : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ s.1.1) q :=
    analyticAt_fst.fun_comp analyticAt_fst
  have hlocal : AnalyticAt ℂ
      (fun s : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ (s.1.2, s.2)) q :=
    (analyticAt_snd.fun_comp analyticAt_fst).prod analyticAt_snd
  exact hparameter.prod (hparametrize.comp_of_eq hlocal rfl)

theorem analyticAt_eCNineParametrizedPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (parametrize : ECNineParametrization)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hparametrize : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ parametrize s.1 s.2)
        (q.1.2, q.2))
    (hPhi : AnalyticAt ℂ Phi (q.1.1, parametrize q.1.2 q.2)) :
    AnalyticAt ℂ (eCNineParametrizedPlanePart Phi parametrize) q := by
  have hfull : AnalyticAt ℂ
      (fun s ↦ Phi (s.1.1, parametrize s.1.2 s.2)) q :=
    hPhi.comp_of_eq
      (analyticAt_eCNineParametrizedReparametrization parametrize q
        hparametrize) rfl
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · simpa [eCNineParametrizedPlanePart, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt
        (Phi (q.1.1, parametrize q.1.2 q.2))).comp_of_eq hfull rfl
  · simpa [eCNineParametrizedPlanePart, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt
        (Phi (q.1.1, parametrize q.1.2 q.2))).comp_of_eq hfull rfl

theorem analyticAt_eCNineParametrizedThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (parametrize : ECNineParametrization)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hparametrize : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ parametrize s.1 s.2)
        (q.1.2, q.2))
    (hPhi : AnalyticAt ℂ Phi (q.1.1, parametrize q.1.2 q.2)) :
    AnalyticAt ℂ (eCNineParametrizedThirdPart Phi parametrize) q := by
  have hfull : AnalyticAt ℂ
      (fun s ↦ Phi (s.1.1, parametrize s.1.2 s.2)) q :=
    hPhi.comp_of_eq
      (analyticAt_eCNineParametrizedReparametrization parametrize q
        hparametrize) rfl
  change AnalyticAt ℂ
    (fun s ↦ Phi (s.1.1, parametrize s.1.2 s.2) 2) q
  simpa [Function.comp_def] using
    ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt
      (Phi (q.1.1, parametrize q.1.2 q.2))).comp_of_eq hfull rfl

/-- The chart used when both cubic root coordinates are nonzero. -/
@[expose]
def eCNineRegularParametrization (z : ℂ) : ECNineParametrization :=
  fun lambda v ↦ ![v 0, z + lambda, v 1]

/-- The chart used at a zero of the first cubic root coordinate. -/
@[expose]
def eCNineFirstRootBoundaryParametrization : ECNineParametrization :=
  fun lambda v ↦ ![lambda, v 0, v 1]

/-- The chart used at a zero of the second cubic root coordinate. -/
@[expose]
def eCNineSecondRootBoundaryParametrization : ECNineParametrization :=
  fun lambda v ↦ ![v 0, v 1, lambda]

theorem analyticAt_eCNineRegularParametrization
    (z : ℂ) (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineRegularParametrization z s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · simpa [eCNineRegularParametrization, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2).fun_comp
        analyticAt_snd
  · exact analyticAt_const.add analyticAt_fst
  · simpa [eCNineRegularParametrization, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2).fun_comp
        analyticAt_snd

theorem analyticAt_eCNineFirstRootBoundaryParametrization
    (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineFirstRootBoundaryParametrization s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact analyticAt_fst
  · simpa [eCNineFirstRootBoundaryParametrization, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2).fun_comp
        analyticAt_snd
  · simpa [eCNineFirstRootBoundaryParametrization, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2).fun_comp
        analyticAt_snd

theorem analyticAt_eCNineSecondRootBoundaryParametrization
    (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ
      (fun s ↦ eCNineSecondRootBoundaryParametrization s.1 s.2) q := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · simpa [eCNineSecondRootBoundaryParametrization, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt q.2).fun_comp
        analyticAt_snd
  · simpa [eCNineSecondRootBoundaryParametrization, Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt q.2).fun_comp
        analyticAt_snd
  · exact analyticAt_fst

/-- The two C9 fibre equations in the chart where both root coordinates
are nonzero. -/
@[expose]
def eCNineRegularPlaneDifference
    (z : ℂ) (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![eP 1 ((s.2 0) ^ 3) - eP (z + s.1) ((s.2 1) ^ 3),
    eQ 1 ((s.2 0) ^ 3) - eQ (z + s.1) ((s.2 1) ^ 3)]

/-- The two C9 fibre equations when the first root coordinate is the curve
parameter. -/
@[expose]
def eCNineFirstRootBoundaryPlaneDifference
    (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![eP 1 (s.1 ^ 3) - eP (s.2 0) ((s.2 1) ^ 3),
    eQ 1 (s.1 ^ 3) - eQ (s.2 0) ((s.2 1) ^ 3)]

/-- The two C9 fibre equations when the second root coordinate is the curve
parameter. -/
@[expose]
def eCNineSecondRootBoundaryPlaneDifference
    (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![eP 1 ((s.2 0) ^ 3) - eP (s.2 1) (s.1 ^ 3),
    eQ 1 ((s.2 0) ^ 3) - eQ (s.2 1) (s.1 ^ 3)]

theorem eCNineRegularPlanePart_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z lambda : ℂ) (v : Fin 2 → ℂ) :
    eCNineParametrizedPlanePart
        (eCNineXChartRescaledPerturbation
          (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
        (eCNineRegularParametrization z) ((0, lambda), v) =
      eCNineRegularPlaneDifference z (lambda, v) := by
  funext i
  fin_cases i
  · simp [eCNineParametrizedPlanePart,
      eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineRegularParametrization,
      eCNineRegularPlaneDifference, eInvariantPolynomialMap_first]
  · simp [eCNineParametrizedPlanePart,
      eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineRegularParametrization,
      eCNineRegularPlaneDifference, eInvariantPolynomialMap_second]

theorem eCNineFirstRootBoundaryPlanePart_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (lambda : ℂ) (v : Fin 2 → ℂ) :
    eCNineParametrizedPlanePart
        (eCNineXChartRescaledPerturbation
          (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
        eCNineFirstRootBoundaryParametrization ((0, lambda), v) =
      eCNineFirstRootBoundaryPlaneDifference (lambda, v) := by
  funext i
  fin_cases i
  · simp [eCNineParametrizedPlanePart,
      eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineFirstRootBoundaryParametrization,
      eCNineFirstRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_first]
  · simp [eCNineParametrizedPlanePart,
      eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineFirstRootBoundaryParametrization,
      eCNineFirstRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_second]

theorem eCNineSecondRootBoundaryPlanePart_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (lambda : ℂ) (v : Fin 2 → ℂ) :
    eCNineParametrizedPlanePart
        (eCNineXChartRescaledPerturbation
          (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
        eCNineSecondRootBoundaryParametrization ((0, lambda), v) =
      eCNineSecondRootBoundaryPlaneDifference (lambda, v) := by
  funext i
  fin_cases i
  · simp [eCNineParametrizedPlanePart,
      eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineSecondRootBoundaryParametrization,
      eCNineSecondRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_first]
  · simp [eCNineParametrizedPlanePart,
      eCNineXChartRescaledPerturbation_zero,
      eCNineXChartInitialDifference, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, eCNineSecondRootBoundaryParametrization,
      eCNineSecondRootBoundaryPlaneDifference,
      eInvariantPolynomialMap_second]

/-- The Jacobian in the two point variables in the regular chart. -/
@[expose]
def eCNineRegularPointJacobian
    (z t T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![9 * t ^ 2, -9 * T ^ 2;
    12 * t ^ 2, -12 * z * T ^ 2]

@[expose]
def eCNineRegularPointDerivative
    (z t T : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (eCNineRegularPointJacobian z t T))
    |>.toContinuousLinearMap

/-- The Jacobian in the point variables at the first root boundary. -/
@[expose]
def eCNineFirstRootBoundaryPointJacobian
    (z T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-3 * z ^ 2, -9 * T ^ 2;
    -(4 * z ^ 3 + 4 * T ^ 3), -12 * z * T ^ 2]

@[expose]
def eCNineFirstRootBoundaryPointDerivative
    (z T : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (eCNineFirstRootBoundaryPointJacobian z T))
    |>.toContinuousLinearMap

/-- The Jacobian in the point variables at the second root boundary. -/
@[expose]
def eCNineSecondRootBoundaryPointJacobian
    (t z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![9 * t ^ 2, -3 * z ^ 2;
    12 * t ^ 2, -4 * z ^ 3]

@[expose]
def eCNineSecondRootBoundaryPointDerivative
    (t z : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (eCNineSecondRootBoundaryPointJacobian t z))
    |>.toContinuousLinearMap

theorem hasStrictFDerivAt_eCNineRegularPlaneDifference_point
    (z t T : ℂ) :
    HasStrictFDerivAt
      (fun v ↦ eCNineRegularPlaneDifference z (0, v))
      (eCNineRegularPointDerivative z t T) ![t, T] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [eCNineRegularPlaneDifference, eP, eQ]
  · convert
      (((hasStrictFDerivAt_const (𝕜 := ℂ)
          (1 - z ^ 3) ![t, T]).add
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![t, T]).pow 3)
          |>.const_mul (3 : ℂ))).sub
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![t, T]).pow 3)
            |>.const_mul (3 : ℂ)))
      using 1
    · funext v
      simp
      ring
    · ext v
      simp [eCNineRegularPointDerivative, eCNineRegularPointJacobian,
        Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
      ring
  · convert
      (((hasStrictFDerivAt_const (𝕜 := ℂ)
          (1 - z ^ 4) ![t, T]).add
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![t, T]).pow 3)
          |>.const_mul (4 : ℂ))).sub
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![t, T]).pow 3)
            |>.const_mul (4 * z)))
      using 1
    · funext v
      simp
      ring
    · ext v
      simp [eCNineRegularPointDerivative, eCNineRegularPointJacobian,
        Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
      ring

theorem hasStrictFDerivAt_eCNineFirstRootBoundaryPlaneDifference_point
    (z T : ℂ) :
    HasStrictFDerivAt
      (fun v ↦ eCNineFirstRootBoundaryPlaneDifference (0, v))
      (eCNineFirstRootBoundaryPointDerivative z T) ![z, T] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [eCNineFirstRootBoundaryPlaneDifference, eP, eQ]
  · convert
      (((hasStrictFDerivAt_const (𝕜 := ℂ) 1 ![z, T]).sub
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![z, T]).pow 3)).sub
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![z, T]).pow 3)
            |>.const_mul (3 : ℂ)))
      using 1
    · funext v
      simp
      ring
    · ext v
      simp [eCNineFirstRootBoundaryPointDerivative,
        eCNineFirstRootBoundaryPointJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring
  · convert
      (((hasStrictFDerivAt_const (𝕜 := ℂ) 1 ![z, T]).sub
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![z, T]).pow 4)).sub
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![z, T]).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![z, T]).pow 3))
            |>.const_mul (4 : ℂ)))
      using 1
    · funext v
      simp
      ring
    · ext v
      simp [eCNineFirstRootBoundaryPointDerivative,
        eCNineFirstRootBoundaryPointJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring

theorem hasStrictFDerivAt_eCNineSecondRootBoundaryPlaneDifference_point
    (t z : ℂ) :
    HasStrictFDerivAt
      (fun v ↦ eCNineSecondRootBoundaryPlaneDifference (0, v))
      (eCNineSecondRootBoundaryPointDerivative t z) ![t, z] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [eCNineSecondRootBoundaryPlaneDifference, eP, eQ]
  · convert
      (((hasStrictFDerivAt_const (𝕜 := ℂ) 1 ![t, z]).add
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![t, z]).pow 3)
          |>.const_mul (3 : ℂ))).sub
          ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![t, z]).pow 3))
      using 1
    · funext v
      simp
    · ext v
      simp [eCNineSecondRootBoundaryPointDerivative,
        eCNineSecondRootBoundaryPointJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring
  · convert
      (((hasStrictFDerivAt_const (𝕜 := ℂ) 1 ![t, z]).add
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![t, z]).pow 3)
          |>.const_mul (4 : ℂ))).sub
          ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![t, z]).pow 4))
      using 1
    · funext v
      simp
    · ext v
      simp [eCNineSecondRootBoundaryPointDerivative,
        eCNineSecondRootBoundaryPointJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring

theorem det_eCNineRegularPointDerivative (z t T : ℂ) :
    (eCNineRegularPointDerivative z t T).det =
      108 * t ^ 2 * T ^ 2 * (1 - z) := by
  simp [eCNineRegularPointDerivative, eCNineRegularPointJacobian,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two]
  ring

theorem det_eCNineFirstRootBoundaryPointDerivative (z T : ℂ) :
    (eCNineFirstRootBoundaryPointDerivative z T).det = -36 * T ^ 5 := by
  simp [eCNineFirstRootBoundaryPointDerivative,
    eCNineFirstRootBoundaryPointJacobian,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two]
  ring

theorem det_eCNineSecondRootBoundaryPointDerivative (t z : ℂ) :
    (eCNineSecondRootBoundaryPointDerivative t z).det =
      36 * t ^ 2 * z ^ 2 * (1 - z) := by
  simp [eCNineSecondRootBoundaryPointDerivative,
    eCNineSecondRootBoundaryPointJacobian,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two]
  ring

/-- A transverse parametrization of a C9 collision persists when the special
fibre section has finite zero set. -/
theorem eventually_exists_eCNineXChartZero_mem_nhds_of_parametrization
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (parametrize : ECNineParametrization)
    (model : ℂ × (Fin 2 → ℂ) → Fin 2 → ℂ)
    (derivative : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))
    (q : Fin 2 → ℂ) (base : Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hparametrize : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ parametrize s.1 s.2) (0, q))
    (hparametrizeBase : parametrize 0 q = base)
    (hbaseDirection : base 1 ≠ 1)
    (hPhi : AnalyticAt ℂ
      (eCNineXChartRescaledPerturbation
        (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
      (0, base))
    (hcollision : eCNineXChartInitialDifference
      (weightedPolynomialMap (eInvariantPolynomialMap R)) base = 0)
    (hspecialPlane : ∀ lambda v,
      eCNineParametrizedPlanePart
          (eCNineXChartRescaledPerturbation
            (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
          parametrize ((0, lambda), v) = model (lambda, v))
    (hmodelDerivative : HasStrictFDerivAt
      (fun v ↦ model (0, v)) derivative q)
    (hmodelInvertible : derivative.IsInvertible)
    (hparameter : ∀ lambda v,
      parametrize lambda v = base → lambda = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, base)) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
              (tau, point) = 0 := by
  let Phi := eCNineXChartRescaledPerturbation
    (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
  let plane := eCNineParametrizedPlanePart Phi parametrize
  let third := eCNineParametrizedThirdPart Phi parametrize
  have hPhiBase : AnalyticAt ℂ Phi (0, parametrize 0 q) := by
    simpa [hparametrizeBase] using hPhi
  have hplane : AnalyticAt ℂ plane ((0, 0), q) := by
    exact analyticAt_eCNineParametrizedPlanePart Phi parametrize
      ((0, 0), q) hparametrize hPhiBase
  have hthird : AnalyticAt ℂ third ((0, 0), q) := by
    exact analyticAt_eCNineParametrizedThirdPart Phi parametrize
      ((0, 0), q) hparametrize hPhiBase
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
      ext v <;> rfl
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
    · change Phi (0, parametrize 0 q) 0 = 0
      rw [hparametrizeBase]
      change eCNineXChartRescaledPerturbation
        (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
          (0, base) 0 = 0
      rw [eCNineXChartRescaledPerturbation_zero]
      simpa using congrFun hcollision 0
    · change Phi (0, parametrize 0 q) 1 = 0
      rw [hparametrizeBase]
      change eCNineXChartRescaledPerturbation
        (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
          (0, base) 1 = 0
      rw [eCNineXChartRescaledPerturbation_zero]
      simpa using congrFun hcollision 1
  have hthirdZero : third ((0, 0), q) = 0 := by
    change Phi (0, parametrize 0 q) 2 = 0
    rw [hparametrizeBase]
    change eCNineXChartRescaledPerturbation
      (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
        (0, base) 2 = 0
    rw [eCNineXChartRescaledPerturbation_zero]
    simpa using congrFun hcollision 2
  have hparametrizeTendsto : Tendsto
      (fun s : ℂ × (Fin 2 → ℂ) ↦ parametrize s.1 s.2)
      (nhds (0, q)) (nhds base) := by
    have ht := hparametrize.continuousAt.tendsto
    rw [hparametrizeBase] at ht
    exact ht
  have hdirection : ∀ᶠ s : ℂ × (Fin 2 → ℂ) in nhds (0, q),
      parametrize s.1 s.2 1 ≠ 1 :=
    (tendsto_pi_nhds.mp hparametrizeTendsto 1).eventually_ne hbaseDirection
  have hmem : ∀ᶠ s : ℂ × (Fin 2 → ℂ) in nhds (0, q),
      plane ((0, s.1), s.2) = 0 →
      third ((0, s.1), s.2) = 0 →
      parametrize s.1 s.2 ∈ eCNineUnitSectionZeroSet R := by
    filter_upwards [hdirection] with s hsDirection hplaneAt hthirdAt
    apply mem_eCNineUnitSectionZeroSet_of_initialDifference_eq_zero
      R (parametrize s.1 s.2) hsDirection
    have hfull : Phi (0, parametrize s.1 s.2) = 0 := by
      funext i
      fin_cases i
      · exact congrFun hplaneAt 0
      · exact congrFun hplaneAt 1
      · exact hthirdAt
    simpa [Phi] using hfull
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    (fun s ↦ (s.1.1, parametrize s.1.2 s.2)) ⁻¹' U
  have hV : V ∈ nhds ((0, 0), q) := by
    have ht :=
      (analyticAt_eCNineParametrizedReparametrization parametrize
        ((0, 0), q) hparametrize).continuousAt.tendsto
    have htBase : Tendsto
        (fun s : ((ℂ × ℂ) × (Fin 2 → ℂ)) ↦
          (s.1.1, parametrize s.1.2 s.2))
        (nhds ((0, 0), q)) (nhds (0, base)) := by
      rw [hparametrizeBase] at ht
      exact ht
    exact htBase.eventually hU
  have hzero :=
    eventually_exists_fullZero_mem_nhds_of_finite_specialFiber
      plane third parametrize q base (eCNineUnitSectionZeroSet R)
        hplane hderivative hplaneZero hthird hthirdZero hparametrize
          hparametrizeBase hmem hparameter
            (eCNineUnitSectionZeroSet_finite R hnorm) V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hVAt, hplaneAt, hthirdAt⟩ := htau
  let branch := analyticImplicitBranch
    plane ((0, 0), q) hplane hderivative
  let point := parametrize lambda (branch (tau, lambda))
  refine ⟨point, hVAt, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

/-- Persistence in the chart where both root coordinates are nonzero. -/
theorem eventually_exists_eCNineRegularZero_mem_nhds
    (R : Form ℂ) (t z T : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hz : z ≠ 1) (ht : t ≠ 0) (hT : T ≠ 0)
    (hfirst : AnalyticAt ℂ remainder (0, (1, t)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, T)))
    (hcollision : eCNineXChartInitialDifference
      (weightedPolynomialMap (eInvariantPolynomialMap R)) ![t, z, T] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![t, z, T])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
              (tau, point) = 0 := by
  let q : Fin 2 → ℂ := ![t, T]
  let base : Fin 3 → ℂ := ![t, z, T]
  have hbase : eCNineRegularParametrization z 0 q = base := by
    funext i
    fin_cases i <;> simp [eCNineRegularParametrization, q, base]
  have hPhi : AnalyticAt ℂ
      (eCNineXChartRescaledPerturbation
        (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
      (0, base) := by
    apply analyticAt_eCNineXChartRescaledPerturbation
    · exact analyticAt_eCNineXChartInitialDifference_weightedPolynomialMap
        (eInvariantPolynomialMap R) base
    · simpa [base, eCNineXChartFirstPoint] using hfirst
    · simpa [base, eCNineXChartSecondPoint] using hsecond
  apply eventually_exists_eCNineXChartZero_mem_nhds_of_parametrization
    R remainder (eCNineRegularParametrization z)
      (eCNineRegularPlaneDifference z)
        (eCNineRegularPointDerivative z t T) q base hnorm
  · exact analyticAt_eCNineRegularParametrization z (0, q)
  · exact hbase
  · simpa [base] using hz
  · exact hPhi
  · simpa [base] using hcollision
  · exact eCNineRegularPlanePart_zero R remainder z
  · simpa [q] using
      hasStrictFDerivAt_eCNineRegularPlaneDifference_point z t T
  · let pointEquiv :=
      (eCNineRegularPointDerivative z t T)
        |>.toContinuousLinearEquivOfDetNeZero <| by
          rw [det_eCNineRegularPointDerivative]
          exact mul_ne_zero
            (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))
              (pow_ne_zero 2 hT)) (sub_ne_zero.mpr hz.symm)
    have hcoe :
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) =
          eCNineRegularPointDerivative z t T := by
      exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    rw [← hcoe]
    exact ContinuousLinearMap.isInvertible_equiv
  · intro lambda v heq
    have hcoordinate : z + lambda = z := by
      simpa [eCNineRegularParametrization, base] using congrFun heq 1
    linear_combination hcoordinate
  · simpa [base] using hU

/-- Persistence at a collision with zero first root coordinate. -/
theorem eventually_exists_eCNineFirstRootBoundaryZero_mem_nhds
    (R : Form ℂ) (z T : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hz : z ≠ 1) (hT : T ≠ 0)
    (hfirst : AnalyticAt ℂ remainder (0, (1, 0)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, T)))
    (hcollision : eCNineXChartInitialDifference
      (weightedPolynomialMap (eInvariantPolynomialMap R)) ![0, z, T] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![0, z, T])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
              (tau, point) = 0 := by
  let q : Fin 2 → ℂ := ![z, T]
  let base : Fin 3 → ℂ := ![0, z, T]
  have hbase : eCNineFirstRootBoundaryParametrization 0 q = base := by
    funext i
    fin_cases i <;>
      simp [eCNineFirstRootBoundaryParametrization, q, base]
  have hPhi : AnalyticAt ℂ
      (eCNineXChartRescaledPerturbation
        (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
      (0, base) := by
    apply analyticAt_eCNineXChartRescaledPerturbation
    · exact analyticAt_eCNineXChartInitialDifference_weightedPolynomialMap
        (eInvariantPolynomialMap R) base
    · simpa [base, eCNineXChartFirstPoint] using hfirst
    · simpa [base, eCNineXChartSecondPoint] using hsecond
  apply eventually_exists_eCNineXChartZero_mem_nhds_of_parametrization
    R remainder eCNineFirstRootBoundaryParametrization
      eCNineFirstRootBoundaryPlaneDifference
        (eCNineFirstRootBoundaryPointDerivative z T) q base hnorm
  · exact analyticAt_eCNineFirstRootBoundaryParametrization (0, q)
  · exact hbase
  · simpa [base] using hz
  · exact hPhi
  · simpa [base] using hcollision
  · exact eCNineFirstRootBoundaryPlanePart_zero R remainder
  · simpa [q] using
      hasStrictFDerivAt_eCNineFirstRootBoundaryPlaneDifference_point z T
  · let pointEquiv :=
      (eCNineFirstRootBoundaryPointDerivative z T)
        |>.toContinuousLinearEquivOfDetNeZero <| by
          rw [det_eCNineFirstRootBoundaryPointDerivative]
          exact mul_ne_zero (by norm_num) (pow_ne_zero 5 hT)
    have hcoe :
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) =
          eCNineFirstRootBoundaryPointDerivative z T := by
      exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    rw [← hcoe]
    exact ContinuousLinearMap.isInvertible_equiv
  · intro lambda v heq
    have hcoordinate := congrFun heq 0
    simpa [eCNineFirstRootBoundaryParametrization, base] using hcoordinate
  · simpa [base] using hU

/-- Persistence at a collision with zero second root coordinate. -/
theorem eventually_exists_eCNineSecondRootBoundaryZero_mem_nhds
    (R : Form ℂ) (t z : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hz : z ≠ 1) (ht : t ≠ 0) (hzZero : z ≠ 0)
    (hfirst : AnalyticAt ℂ remainder (0, (1, t)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, 0)))
    (hcollision : eCNineXChartInitialDifference
      (weightedPolynomialMap (eInvariantPolynomialMap R)) ![t, z, 0] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![t, z, 0])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
              (tau, point) = 0 := by
  let q : Fin 2 → ℂ := ![t, z]
  let base : Fin 3 → ℂ := ![t, z, 0]
  have hbase : eCNineSecondRootBoundaryParametrization 0 q = base := by
    funext i
    fin_cases i <;>
      simp [eCNineSecondRootBoundaryParametrization, q, base]
  have hPhi : AnalyticAt ℂ
      (eCNineXChartRescaledPerturbation
        (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
      (0, base) := by
    apply analyticAt_eCNineXChartRescaledPerturbation
    · exact analyticAt_eCNineXChartInitialDifference_weightedPolynomialMap
        (eInvariantPolynomialMap R) base
    · simpa [base, eCNineXChartFirstPoint] using hfirst
    · simpa [base, eCNineXChartSecondPoint] using hsecond
  apply eventually_exists_eCNineXChartZero_mem_nhds_of_parametrization
    R remainder eCNineSecondRootBoundaryParametrization
      eCNineSecondRootBoundaryPlaneDifference
        (eCNineSecondRootBoundaryPointDerivative t z) q base hnorm
  · exact analyticAt_eCNineSecondRootBoundaryParametrization (0, q)
  · exact hbase
  · simpa [base] using hz
  · exact hPhi
  · simpa [base] using hcollision
  · exact eCNineSecondRootBoundaryPlanePart_zero R remainder
  · simpa [q] using
      hasStrictFDerivAt_eCNineSecondRootBoundaryPlaneDifference_point t z
  · let pointEquiv :=
      (eCNineSecondRootBoundaryPointDerivative t z)
        |>.toContinuousLinearEquivOfDetNeZero <| by
          rw [det_eCNineSecondRootBoundaryPointDerivative]
          exact mul_ne_zero
            (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))
              (pow_ne_zero 2 hzZero)) (sub_ne_zero.mpr hz.symm)
    have hcoe :
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) =
          eCNineSecondRootBoundaryPointDerivative t z := by
      exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    rw [← hcoe]
    exact ContinuousLinearMap.isInvertible_equiv
  · intro lambda v heq
    have hcoordinate := congrFun heq 2
    simpa [eCNineSecondRootBoundaryParametrization, base] using hcoordinate
  · simpa [base] using hU

theorem eCNine_second_root_ne_zero_of_first_root_eq_zero
    {t z T : ℂ} (hequations : ECNineEquations 1 t z T)
    (hz : z ≠ 1) (ht : t = 0) : T ≠ 0 := by
  intro hT
  have hfirst := hequations.1
  have hsecond := hequations.2
  rw [ht, hT] at hfirst hsecond
  have hdirection : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hquadraticFirst : z ^ 2 + 2 * z + 3 = 0 := by
    simp [eCNineFirstValue] at hfirst
    exact hfirst.resolve_left hdirection
  have hquadraticSecond : 3 * z ^ 2 + 2 * z + 1 = 0 := by
    simp [eCNineSecondValue] at hsecond
    exact hsecond.resolve_left hdirection
  have hfalse : (12 : ℂ) = 0 := by
    linear_combination (-3 * z + 4) * hquadraticFirst +
      z * hquadraticSecond
  norm_num at hfalse

theorem eCNine_direction_ne_zero_of_second_root_eq_zero
    {t z T : ℂ} (hequations : ECNineEquations 1 t z T)
    (hT : T = 0) : z ≠ 0 := by
  intro hz
  have hsecond := hequations.2
  rw [hT, hz] at hsecond
  norm_num [eCNineSecondValue] at hsecond

/-- Every affine C9 collision away from the diagonal lies in one of the
three transverse charts. -/
theorem eventually_exists_eCNineZero_mem_nhds
    (R : Form ℂ) (t z T : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hequations : ECNineEquations 1 t z T)
    (hz : z ≠ 1)
    (hfirst : AnalyticAt ℂ remainder (0, (1, t)))
    (hsecond : AnalyticAt ℂ remainder (0, (z, T)))
    (hcollision : eCNineXChartInitialDifference
      (weightedPolynomialMap (eInvariantPolynomialMap R)) ![t, z, T] = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![t, z, T])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          eCNineXChartRescaledPerturbation
            (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder
              (tau, point) = 0 := by
  by_cases ht : t = 0
  · subst t
    exact eventually_exists_eCNineFirstRootBoundaryZero_mem_nhds
      R z T remainder hnorm hz
        (eCNine_second_root_ne_zero_of_first_root_eq_zero
          hequations hz rfl) hfirst hsecond hcollision U hU
  · by_cases hT : T = 0
    · subst T
      exact eventually_exists_eCNineSecondRootBoundaryZero_mem_nhds
        R t z remainder hnorm hz ht
          (eCNine_direction_ne_zero_of_second_root_eq_zero
            hequations rfl) hfirst hsecond hcollision U hU
    · exact eventually_exists_eCNineRegularZero_mem_nhds
        R t z T remainder hnorm hz ht hT hfirst hsecond hcollision U hU

/-- Radial expansions identify the representative difference with the C9
rescaled perturbation. -/
theorem representative_difference_eq_eCNineXChartRescaledPerturbation
    (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (tau : ℂ) (q : Fin 3 → ℂ)
    (hfirst : ∀ i,
      representative
          (weightedRadialSource 1 tau (eCNineXChartFirstPoint q)) i =
        tau ^ degrees i *
          (initialMap (eCNineXChartFirstPoint q) i +
            tau * remainder (tau, eCNineXChartFirstPoint q) i))
    (hsecond : ∀ i,
      representative
          (weightedRadialSource 1 tau (eCNineXChartSecondPoint q)) i =
        tau ^ degrees i *
          (initialMap (eCNineXChartSecondPoint q) i +
            tau * remainder (tau, eCNineXChartSecondPoint q) i)) :
    ∀ i,
      representative
          (weightedRadialSource 1 tau (eCNineXChartFirstPoint q)) i -
        representative
          (weightedRadialSource 1 tau (eCNineXChartSecondPoint q)) i =
      tau ^ degrees i *
        eCNineXChartRescaledPerturbation initialMap remainder (tau, q) i := by
  intro i
  rw [hfirst i, hsecond i]
  simp only [eCNineXChartRescaledPerturbation,
    eCNineXChartInitialDifference, eCNineXChartRemainderDifference,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Persistent C9 zeros based at distinct affine directions contradict
injectivity in every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_eCNineWeightedZeros
    (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (t z T : ℂ) (hz : z ≠ 1)
    (hfirst : HasWeightedRadialExpansionAt 1 degrees initialMap
      representative remainder (1, t))
    (hsecond : HasWeightedRadialExpansionAt 1 degrees initialMap
      representative remainder (z, T))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![t, z, T]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              eCNineXChartRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  intro hinjective
  obtain ⟨sourceSet, hsourceSet, hsourceInjective⟩ := hinjective
  let base : Fin 3 → ℂ := ![t, z, T]
  have hfirstLift : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1, eCNineXChartFirstPoint s.2))
      (nhds (0, base)) (nhds (0, (1, t))) := by
    have hpoint : AnalyticAt ℂ
        (fun s : ℂ × (Fin 3 → ℂ) ↦
          eCNineXChartFirstPoint s.2) (0, base) := by
      exact (analyticAt_eCNineXChartFirstPoint base).comp_of_eq
        (analyticAt_snd : AnalyticAt ℂ
          (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2) (0, base)) rfl
    have ht := (analyticAt_fst.prod hpoint).continuousAt.tendsto
    simpa [base, eCNineXChartFirstPoint] using ht
  have hsecondLift : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1, eCNineXChartSecondPoint s.2))
      (nhds (0, base)) (nhds (0, (z, T))) := by
    have hpoint : AnalyticAt ℂ
        (fun s : ℂ × (Fin 3 → ℂ) ↦
          eCNineXChartSecondPoint s.2) (0, base) := by
      exact (analyticAt_eCNineXChartSecondPoint base).comp_of_eq
        (analyticAt_snd : AnalyticAt ℂ
          (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2) (0, base)) rfl
    have ht := (analyticAt_fst.prod hpoint).continuousAt.tendsto
    simpa [base, eCNineXChartSecondPoint] using ht
  have hfirstExpansion := hfirstLift.eventually hfirst.expansion
  have hsecondExpansion := hsecondLift.eventually hsecond.expansion
  have hcoordinate (i : Fin 3) : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2 i) (0, base) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, base))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
          analyticAt_snd)
  have hfirstSourceAnalytic : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource 1 s.1 (eCNineXChartFirstPoint s.2))
      (0, base) := by
    change AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1 ^ 1 * 1, s.1 * s.2 0)) (0, base)
    exact ((analyticAt_fst.pow 1).mul analyticAt_const).prod
      (analyticAt_fst.mul (hcoordinate 0))
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource 1 s.1 (eCNineXChartSecondPoint s.2))
      (0, base) := by
    change AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1 ^ 1 * s.2 1, s.1 * s.2 2)) (0, base)
    exact ((analyticAt_fst.pow 1).mul (hcoordinate 1)).prod
      (analyticAt_fst.mul (hcoordinate 2))
  have hfirstSource : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource 1 s.1 (eCNineXChartFirstPoint s.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hfirstSourceAnalytic.continuousAt.tendsto
    change Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource 1 s.1 (eCNineXChartFirstPoint s.2))
      (nhds (0, base)) (nhds ((0, 0) : ℂ × ℂ))
    simpa [base, weightedRadialSource, eCNineXChartFirstPoint] using ht
  have hsecondSource : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource 1 s.1 (eCNineXChartSecondPoint s.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hsecondSourceAnalytic.continuousAt.tendsto
    change Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource 1 s.1 (eCNineXChartSecondPoint s.2))
      (nhds (0, base)) (nhds ((0, 0) : ℂ × ℂ))
    simpa [base, weightedRadialSource, eCNineXChartSecondPoint] using ht
  have hdirectionTendsto : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2 1)
      (nhds (0, base)) (nhds z) := by
    have ht := (hcoordinate 1).continuousAt.tendsto
    simpa [base] using ht
  let conditions : ℂ × (Fin 3 → ℂ) → Prop := fun s ↦
      (∀ i,
        representative
            (weightedRadialSource 1 s.1
              (eCNineXChartFirstPoint s.2)) i =
          s.1 ^ degrees i *
            (initialMap (eCNineXChartFirstPoint s.2) i +
              s.1 * remainder (s.1, eCNineXChartFirstPoint s.2) i)) ∧
      (∀ i,
        representative
            (weightedRadialSource 1 s.1
              (eCNineXChartSecondPoint s.2)) i =
          s.1 ^ degrees i *
            (initialMap (eCNineXChartSecondPoint s.2) i +
              s.1 * remainder (s.1, eCNineXChartSecondPoint s.2) i)) ∧
      weightedRadialSource 1 s.1 (eCNineXChartFirstPoint s.2) ∈
        sourceSet ∧
      weightedRadialSource 1 s.1 (eCNineXChartSecondPoint s.2) ∈
        sourceSet ∧
      s.2 1 ≠ 1
  have hconditions : ∀ᶠ s in nhds (0, base), conditions s := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hsourceSet,
      hsecondSource.eventually hsourceSet,
      hdirectionTendsto.eventually_ne hz] with
      s hfirstAt hsecondAt hfirstMem hsecondMem hsDirection
    exact ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hsDirection⟩
  have hconditionsSet : {s | conditions s} ∈ nhds (0, base) := hconditions
  have hzero := hpersist {s | conditions s}
    (by simpa [base] using hconditionsSet)
  have hall : ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      ∃ q : Fin 3 → ℂ,
        conditions (tau, q) ∧
        eCNineXChartRescaledPerturbation initialMap remainder (tau, q) = 0 ∧
        tau ≠ 0 := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with tau htau htauMem
    obtain ⟨q, hcondition, hzeroAt⟩ := htau
    refine ⟨q, hcondition, hzeroAt, ?_⟩
    simpa using htauMem
  obtain ⟨tau, q, hcondition, hzeroAt, htau⟩ := hall.exists
  obtain ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hqDirection⟩ :=
    hcondition
  have hvalues :
      representative
          (weightedRadialSource 1 tau (eCNineXChartFirstPoint q)) =
        representative
          (weightedRadialSource 1 tau (eCNineXChartSecondPoint q)) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative
            (weightedRadialSource 1 tau (eCNineXChartFirstPoint q)) i -
          representative
            (weightedRadialSource 1 tau (eCNineXChartSecondPoint q)) i =
        tau ^ degrees i *
          eCNineXChartRescaledPerturbation initialMap remainder
            (tau, q) i :=
          representative_difference_eq_eCNineXChartRescaledPerturbation
            degrees initialMap representative remainder tau q
              hfirstAt hsecondAt i
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      weightedRadialSource 1 tau (eCNineXChartFirstPoint q) ≠
        weightedRadialSource 1 tau (eCNineXChartSecondPoint q) := by
    intro hequal
    have hfirstCoordinate := congrArg Prod.fst hequal
    simp only [weightedRadialSource, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, pow_one, mul_one] at hfirstCoordinate
    have hqOne : q 1 = 1 := by
      apply mul_left_cancel₀ htau
      simpa using hfirstCoordinate.symm
    exact hqDirection hqOne
  exact hsourcesNe
    (hsourceInjective hfirstMem hsecondMem hvalues)

theorem eCNine_direction_ne_one_of_distinct
    {t z T : ℂ} (hequations : ECNineEquations 1 t z T)
    (hdistinct : (1, t) ≠ (z, T)) : z ≠ 1 := by
  intro hz
  subst z
  have hfirst := hequations.1
  have hsecond := hequations.2
  change 12 * t ^ 3 + (1 - 1) *
    ((1 : ℂ) ^ 2 + 2 * 1 * 1 + 3 * 1 ^ 2) = 0 at hfirst
  change 12 * T ^ 3 - (1 - 1) *
    (3 * (1 : ℂ) ^ 2 + 2 * 1 * 1 + 1 ^ 2) = 0 at hsecond
  have htCube : t ^ 3 = 0 := by
    linear_combination (1 / 12) * hfirst
  have hTCube : T ^ 3 = 0 := by
    linear_combination (1 / 12) * hsecond
  have ht : t = 0 := (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp htCube
  have hT : T = 0 := (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hTCube
  exact hdistinct (by rw [ht, hT])

/-- An affine C9 collision with nonzero determinant norm excludes an
injective representative. -/
theorem eCNineCollision_not_hasInjectiveRepresentative
    (R : Form ℂ) (N : ℕ) (t z T : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hequations : ECNineEquations 1 t z T)
    (hz : z ≠ 1)
    (hcollision :
      weightedPolynomialMap (eInvariantPolynomialMap R) (1, t) =
        weightedPolynomialMap (eInvariantPolynomialMap R) (z, T))
    (hfirst : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (1, t))
    (hsecond : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (z, T)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_eCNineWeightedZeros
    (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder t z T hz hfirst hsecond
  intro U hU
  apply eventually_exists_eCNineZero_mem_nhds
    R t z T remainder hnorm hequations hz
      hfirst.remainder_analyticAt hsecond.remainder_analyticAt
  · apply sub_eq_zero.mpr
    simpa [eCNineXChartFirstPoint, eCNineXChartSecondPoint] using hcollision
  · exact hU

/-- Weighted order tails with a hard C9 initial form exclude an injective
representative. -/
theorem eCNineHardWeightedOrderTails_not_hasInjectiveRepresentative
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hhomogeneous :
      (eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eInvariantPolynomialMap
              (eSourceCubeSubstitutionForm Rzero +
                MvPolynomial.C coefficient * formT ^ N) i) ∈
        Germ.weightedOrderIdeal 1 (eInvariantDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  let hardForm := eSourceCubeSubstitutionForm Rzero +
    MvPolynomial.C coefficient * formT ^ N
  have hnorm : eCNineUnitDifferenceNorm hardForm ≠ 0 :=
    eCNineUnitDifferenceNorm_ne_zero homega hardForm Rzero coefficient N
      rfl hc hnotdiv
  obtain ⟨z, t, T, hequations, hdistinct, hcollision⟩ :=
    eCNineHardNorm_gives_initial_collision homega Rzero coefficient N
      hhomogeneous hc hnotdiv
  have hz : z ≠ 1 :=
    eCNine_direction_ne_one_of_distinct hequations hdistinct
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      1 (by simp) (eInvariantDegrees N) (eInvariantPolynomialMap hardForm)
        (eInvariantPolynomialMap_isWeightedHomogeneous hardForm N
          hhomogeneous) representative hanalytic (by
            intro i
            simpa [hardForm] using htail i)
  exact eCNineCollision_not_hasInjectiveRepresentative
    hardForm N t z T representative remainder hanalytic hzero hnorm
      hequations hz (by simpa [hardForm] using hcollision)
        (hexpansion (1, t)) (hexpansion (z, T))

/-- Ordinary maximal ideal tails with a hard C9 initial form exclude an
injective representative. -/
theorem eCNineHardMaximalIdealTails_not_hasInjectiveRepresentative
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hhomogeneous :
      (eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eInvariantPolynomialMap
              (eSourceCubeSubstitutionForm Rzero +
                MvPolynomial.C coefficient * formT ^ N) i) ∈
        Germ.maximalIdeal 2 ^ (eInvariantDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply eCNineHardWeightedOrderTails_not_hasInjectiveRepresentative
    homega Rzero coefficient N hhomogeneous hc hnotdiv representative
      hanalytic hzero
  intro i
  rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow]
  exact htail i

end OnLeConjecture.DThree
