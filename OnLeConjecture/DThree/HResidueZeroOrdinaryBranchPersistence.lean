/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddOrdinaryPersistence
public import OnLeConjecture.DThree.HResidueZeroInvariantContradiction

/-!
# Persistence of an H source branch after a power substitution

An ordinary source branch whose second coordinates are nonzero lifts through
the map `y ↦ y^a`. The lifted branch supplies the transverse data needed to
persist a collision through strict weighted tails.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The analytic function associated with the zero residue polynomial map.
-/
@[expose]
noncomputable def hResidueZeroInitialMap
    (a : ℕ) (R : Form ℂ) : ℂ × ℂ → Fin 3 → ℂ :=
  weightedPolynomialMap (hResidueZeroPolynomialMap a R)

/-- Source branch data for the power substitution of an ordinary `H` form.
-/
structure HResidueZeroSourceBranchData (a : ℕ) (R : Form ℂ) where
  firstX : ℂ → ℂ
  secondPoint : ℂ → Fin 2 → ℂ
  secondX : ℂ
  secondT : ℂ
  order : ℕ
  unit : ℂ → ℂ
  firstX_analyticAt : AnalyticAt ℂ firstX 0
  secondPoint_analyticAt : AnalyticAt ℂ secondPoint 0
  secondPoint_zero : secondPoint 0 = ![secondX, secondT]
  secondT_ne_zero : secondT ≠ 0
  chart_points_ne : (firstX 0, 1) ≠ (secondX, secondT)
  plane_zero : ∀ᶠ lambda in nhds 0,
    hCollisionPlaneDifference a firstX
      (lambda, secondPoint lambda) = 0
  order_pos : 0 < order
  unit_analyticAt : AnalyticAt ℂ unit 0
  unit_zero_ne : unit 0 ≠ 0
  third_factor : ∀ᶠ lambda in nhds 0,
    MvPolynomial.eval ![firstX lambda, 1] R -
        MvPolynomial.eval
          ![secondPoint lambda 0, secondPoint lambda 1 ^ a] R =
      lambda ^ order * unit lambda

/-- An ordinary source branch with nonzero second coordinates lifts through
the `a`th power map. -/
theorem exists_hResidueZeroSourceBranchData_of_ordinarySourceBranch
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (data : HHardOddOrdinarySourceBranchData R) :
    Nonempty (HResidueZeroSourceBranchData a R) := by
  let t : ℂ → ℂ := fun lambda ↦ data.secondPoint lambda 1
  have htAnalytic : AnalyticAt ℂ t 0 := by
    exact AnalyticAt.fun_comp
      (g := fun value : Fin 2 → ℂ ↦ value 1)
      (f := data.secondPoint)
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt
        (data.secondPoint 0)) data.secondPoint_analyticAt
  have htZero : t 0 = data.secondT := by
    simp [t, data.secondPoint_zero]
  have htNe : t 0 ≠ 0 := by
    rw [htZero]
    exact data.secondT_ne_zero
  obtain ⟨T, hT⟩ := IsAlgClosed.exists_pow_nat_eq data.secondT ha
  have hTNe : T ≠ 0 := by
    intro hzero
    apply data.secondT_ne_zero
    rw [← hT, hzero, zero_pow ha.ne']
  obtain ⟨root, hrootAnalytic, hrootZero, hrootPower⟩ :=
    exists_analyticAt_root_with_value t htAnalytic htNe
      a ha.ne' T (by simpa only [htZero] using hT)
  let secondPoint : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![data.secondPoint lambda 0, root lambda]
  have hsecondPointAnalytic : AnalyticAt ℂ secondPoint 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact AnalyticAt.fun_comp
        (g := fun value : Fin 2 → ℂ ↦ value 0)
        (f := data.secondPoint)
        ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt
          (data.secondPoint 0)) data.secondPoint_analyticAt
    · exact hrootAnalytic
  have hsecondPointZero : secondPoint 0 = ![data.secondX, T] := by
    funext i
    fin_cases i
    · simp [secondPoint, data.secondPoint_zero]
    · simp [secondPoint, hrootZero]
  have hchart : (data.firstX 0, 1) ≠ (data.secondX, T) := by
    intro hequal
    apply data.chart_points_ne
    have hfirst : data.firstX 0 = data.secondX :=
      congrArg (fun z : ℂ × ℂ ↦ z.1) hequal
    have hsecond : (1 : ℂ) = T :=
      congrArg (fun z : ℂ × ℂ ↦ z.2) hequal
    apply Prod.ext
    · exact hfirst
    · calc
        1 = 1 ^ a := by simp
        _ = T ^ a := congrArg (fun z : ℂ ↦ z ^ a) hsecond
        _ = data.secondT := hT
  have hplane : ∀ᶠ lambda in nhds 0,
      hCollisionPlaneDifference a data.firstX
        (lambda, secondPoint lambda) = 0 := by
    filter_upwards [data.plane_zero] with lambda hzero
    funext i
    have hpower : root lambda ^ (2 * a) = t lambda ^ 2 := by
      rw [Nat.mul_comm 2 a, pow_mul, hrootPower]
    fin_cases i
    · simpa [hCollisionPlaneDifference, secondPoint, t, hpower] using
        congrFun hzero 0
    · simpa [hCollisionPlaneDifference, secondPoint, t, hpower] using
        congrFun hzero 1
  have hthird : ∀ᶠ lambda in nhds 0,
      MvPolynomial.eval ![data.firstX lambda, 1] R -
          MvPolynomial.eval
            ![secondPoint lambda 0, secondPoint lambda 1 ^ a] R =
        lambda ^ data.order * data.unit lambda := by
    filter_upwards [data.third_factor] with lambda hfactor
    simpa [secondPoint, t, hrootPower] using hfactor
  exact ⟨
    { firstX := data.firstX
      secondPoint := secondPoint
      secondX := data.secondX
      secondT := T
      order := data.order
      unit := data.unit
      firstX_analyticAt := data.firstX_analyticAt
      secondPoint_analyticAt := hsecondPointAnalytic
      secondPoint_zero := hsecondPointZero
      secondT_ne_zero := hTNe
      chart_points_ne := hchart
      plane_zero := hplane
      order_pos := data.order_pos
      unit_analyticAt := data.unit_analyticAt
      unit_zero_ne := data.unit_zero_ne
      third_factor := hthird }⟩

/-- At radial parameter zero, the first two differences are the weighted
`H` fibre equations. -/
theorem hCollisionPlanePart_hResidueZeroInitialMap_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x : ℂ → ℂ) (lambda : ℂ) (point : Fin 2 → ℂ) :
    hCollisionPlanePart
        (weightedRescaledPerturbation
          (hResidueZeroInitialMap a R) remainder)
        x ((0, lambda), point) =
      hCollisionPlaneDifference a x (lambda, point) := by
  funext i
  fin_cases i
  · simp [hCollisionPlanePart, hCollisionReparametrization,
      hCollisionAffinePoint, hCollisionPlaneDifference,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      hResidueZeroInitialMap, weightedPolynomialMap,
      hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      weightedPowerSubstitutionForm, cubicForm, formX, formT, hP]
    all_goals ring_nf
    all_goals simp
  · simp [hCollisionPlanePart, hCollisionReparametrization,
      hCollisionAffinePoint, hCollisionPlaneDifference,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      hResidueZeroInitialMap, weightedPolynomialMap,
      hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      weightedPowerSubstitutionForm, quarticForm, formX, formT, hQ]
    all_goals ring_nf

/-- At radial parameter zero, the third difference evaluates the ordinary
form after the power substitution. -/
theorem hCollisionThirdPart_hResidueZeroInitialMap_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x : ℂ → ℂ) (lambda : ℂ) (point : Fin 2 → ℂ) :
    hCollisionThirdPart
        (weightedRescaledPerturbation
          (hResidueZeroInitialMap a R) remainder)
        x ((0, lambda), point) =
      MvPolynomial.eval ![x lambda, 1] R -
        MvPolynomial.eval ![point 0, point 1 ^ a] R := by
  rw [hCollisionThirdPart, hCollisionReparametrization,
    hCollisionAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint, hResidueZeroInitialMap]
  change
    MvPolynomial.eval ![x lambda, 1]
          (weightedPowerSubstitutionForm a R) -
        MvPolynomial.eval ![point 0, point 1]
          (weightedPowerSubstitutionForm a R) =
      MvPolynomial.eval ![x lambda, 1] R -
        MvPolynomial.eval ![point 0, point 1 ^ a] R
  have hfirst :
      MvPolynomial.eval ![x lambda, 1]
          (weightedPowerSubstitutionForm a R) =
        MvPolynomial.eval ![x lambda, 1 ^ a] R := by
    simpa using eval_weightedPowerSubstitutionForm a R (x lambda, 1)
  have hsecond :
      MvPolynomial.eval ![point 0, point 1]
          (weightedPowerSubstitutionForm a R) =
        MvPolynomial.eval ![point 0, point 1 ^ a] R := by
    simpa using eval_weightedPowerSubstitutionForm a R (point 0, point 1)
  rw [hfirst, hsecond]
  simp

/-- The lifted source branch persists through a weighted analytic
perturbation. -/
theorem eventually_exists_hResidueZeroBranchZero_mem_nhds
    (a : ℕ) (ha : 0 < a) (R : Form ℂ)
    (data : HResidueZeroSourceBranchData a R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder
      (0, (data.firstX 0, 1)))
    (hsecond : AnalyticAt ℂ remainder
      (0, (data.secondX, data.secondT)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds
      (0, ![data.firstX 0, data.secondX, data.secondT])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (hResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  let Phi := weightedRescaledPerturbation
    (hResidueZeroInitialMap a R) remainder
  have hPhi : AnalyticAt ℂ Phi
      (0, ![data.firstX 0, data.secondX, data.secondT]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (hResidueZeroPolynomialMap a R) _
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  exact eventually_exists_hCollisionZero_mem_nhds_of_explicit_branch
    Phi a ha data.firstX data.secondPoint data.secondX data.secondT
      data.firstX_analyticAt data.secondPoint_analyticAt
        data.secondPoint_zero data.secondT_ne_zero hPhi
      (hCollisionPlanePart_hResidueZeroInitialMap_zero
        a R remainder data.firstX)
      data.plane_zero
      (fun q : ℂ × (Fin 2 → ℂ) ↦
        MvPolynomial.eval ![data.firstX q.1, 1] R -
          MvPolynomial.eval ![q.2 0, q.2 1 ^ a] R)
      (hCollisionThirdPart_hResidueZeroInitialMap_zero
        a R remainder data.firstX)
      data.order data.unit data.order_pos data.unit_analyticAt
        data.unit_zero_ne data.third_factor U hU

/-- A lifted zero residue source branch excludes injectivity on every
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_hResidueZeroSourceBranch
    (a N : ℕ) (ha : 0 < a) (R : Form ℂ)
    (data : HResidueZeroSourceBranchData a R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N) (hResidueZeroInitialMap a R)
        representative remainder (data.firstX 0, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N) (hResidueZeroInitialMap a R)
        representative remainder (data.secondX, data.secondT)) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_chart
    a (hQuadraticWeightedDegrees a N) (hResidueZeroInitialMap a R)
      representative remainder (data.firstX 0) data.secondX
        data.secondT ha data.chart_points_ne hfirst hsecond
  intro U hU
  exact eventually_exists_hResidueZeroBranchZero_mem_nhds
    a ha R data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- Weighted tails exclude an injective representative when a lifted zero
residue source branch is available. -/
theorem hResidueZeroSourceBranchWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (R : Form ℂ)
    (hR : R.IsHomogeneous N)
    (data : HResidueZeroSourceBranchData a R)
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
  exact not_neighborhood_injective_of_hResidueZeroSourceBranch
    a N ha R data representative remainder
      (hexpansion (data.firstX 0, 1))
      (hexpansion (data.secondX, data.secondT))

/-- An ordinary source branch with nonzero second coordinates excludes an
injective representative after every positive power substitution. -/
theorem hOrdinarySourceBranchResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (R : Form ℂ)
    (hR : R.IsHomogeneous N)
    (data : HHardOddOrdinarySourceBranchData R)
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
    exists_hResidueZeroSourceBranchData_of_ordinarySourceBranch
      a ha R data
  exact hResidueZeroSourceBranchWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R hR lifted representative hanalytic hzero htail

end OnLeConjecture.DThree
