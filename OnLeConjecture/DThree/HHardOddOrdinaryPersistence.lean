/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNormalizedCollisionNoninjectivity
public import OnLeConjecture.DThree.HReflectionLineNoninjectivity
public import OnLeConjecture.DThree.OrdinaryOrderExpansion

/-!
# Persistence for an ordinary H collision branch

An analytic branch of fibres of the cubic and quartic forms is recorded
together with a positive finite order factorization of the third difference.
This supplies the precise local input needed to persist a collision through
ordinary maximal ideal tails.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Analytic source data for an ordinary H collision whose first point has
second coordinate one. -/
structure HHardOddOrdinarySourceBranchData
    (R : Form ℂ) where
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
    hCollisionPlaneDifference 1 firstX
      (lambda, secondPoint lambda) = 0
  order_pos : 0 < order
  unit_analyticAt : AnalyticAt ℂ unit 0
  unit_zero_ne : unit 0 ≠ 0
  third_factor : ∀ᶠ lambda in nhds 0,
    MvPolynomial.eval ![firstX lambda, 1] R -
        MvPolynomial.eval
          ![secondPoint lambda 0, secondPoint lambda 1] R =
      lambda ^ order * unit lambda

/-- At radial parameter zero, the first two ordinary H differences are the
two conic fibre equations. -/
theorem hCollisionPlanePart_hOrdinaryInitialMap_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x : ℂ → ℂ) (lambda : ℂ) (point : Fin 2 → ℂ) :
    hCollisionPlanePart
        (weightedRescaledPerturbation
          (hOrdinaryInitialMap R) remainder)
        x ((0, lambda), point) =
      hCollisionPlaneDifference 1 x (lambda, point) := by
  funext i
  fin_cases i
  all_goals simp [hCollisionPlanePart, hCollisionReparametrization,
    hCollisionAffinePoint, hCollisionPlaneDifference,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    hOrdinaryInitialMap, weightedPolynomialMap, hOrdinaryPolynomialMap,
    cubicForm, quarticForm, formX, formT, hP, hQ]
  all_goals ring

/-- At radial parameter zero, the third ordinary H difference is evaluation
of the homogeneous third form at the two chart points. -/
theorem hCollisionThirdPart_hOrdinaryInitialMap_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x : ℂ → ℂ) (lambda : ℂ) (point : Fin 2 → ℂ) :
    hCollisionThirdPart
        (weightedRescaledPerturbation
          (hOrdinaryInitialMap R) remainder)
        x ((0, lambda), point) =
      MvPolynomial.eval ![x lambda, 1] R -
        MvPolynomial.eval ![point 0, point 1] R := by
  simp [hCollisionThirdPart, hCollisionReparametrization,
    hCollisionAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint, hOrdinaryInitialMap,
    weightedPolynomialMap, hOrdinaryPolynomialMap]

/-- The rescaled perturbation has a zero in every neighborhood of an
ordinary H source branch. -/
theorem eventually_exists_hHardOddOrdinaryZero_mem_nhds
    (R : Form ℂ)
    (data : HHardOddOrdinarySourceBranchData R)
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
            (hOrdinaryInitialMap R) remainder (tau, point) = 0 := by
  let Phi := weightedRescaledPerturbation
    (hOrdinaryInitialMap R) remainder
  have hPhi : AnalyticAt ℂ Phi
      (0, ![data.firstX 0, data.secondX, data.secondT]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (hOrdinaryPolynomialMap R) _
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  exact eventually_exists_hCollisionZero_mem_nhds_of_explicit_branch
    Phi 1 (by norm_num) data.firstX data.secondPoint data.secondX
      data.secondT data.firstX_analyticAt data.secondPoint_analyticAt
        data.secondPoint_zero data.secondT_ne_zero hPhi
      (hCollisionPlanePart_hOrdinaryInitialMap_zero
        R remainder data.firstX)
      data.plane_zero
      (fun q : ℂ × (Fin 2 → ℂ) ↦
        MvPolynomial.eval ![data.firstX q.1, 1] R -
          MvPolynomial.eval ![q.2 0, q.2 1] R)
      (hCollisionThirdPart_hOrdinaryInitialMap_zero
        R remainder data.firstX)
      data.order data.unit data.order_pos data.unit_analyticAt
        data.unit_zero_ne data.third_factor U hU

/-- An ordinary H source branch excludes injectivity on every neighborhood
of the origin. -/
theorem not_neighborhood_injective_of_hHardOddOrdinarySourceBranch
    (R : Form ℂ) (N : ℕ)
    (data : HHardOddOrdinarySourceBranchData R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt 1
      (hOrdinaryDegrees N) (hOrdinaryInitialMap R)
        representative remainder (data.firstX 0, 1))
    (hsecond : HasWeightedRadialExpansionAt 1
      (hOrdinaryDegrees N) (hOrdinaryInitialMap R)
        representative remainder (data.secondX, data.secondT)) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_chart
    1 (hOrdinaryDegrees N) (hOrdinaryInitialMap R)
      representative remainder (data.firstX 0) data.secondX
        data.secondT (by norm_num) data.chart_points_ne hfirst hsecond
  intro U hU
  exact eventually_exists_hHardOddOrdinaryZero_mem_nhds
    R data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- Ordinary maximal ideal tails exclude an injective representative when
an ordinary H source branch is available. -/
theorem hHardOddOrdinarySourceBranchMaximalIdealTails_not_hasInjectiveRepresentative
    (R : Form ℂ) (N : ℕ) (hR : R.IsHomogeneous N)
    (data : HHardOddOrdinarySourceBranchData R)
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
  exact not_neighborhood_injective_of_hHardOddOrdinarySourceBranch
    R N data representative remainder
      (hexpansion (data.firstX 0, 1))
      (hexpansion (data.secondX, data.secondT))

end OnLeConjecture.DThree
