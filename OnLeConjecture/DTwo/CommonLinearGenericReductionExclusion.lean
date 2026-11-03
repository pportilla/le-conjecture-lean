/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CommonLinearGenericMember
public import OnLeConjecture.DTwo.CommonLinearNodeExclusion
public import OnLeConjecture.Analytic.GenericPointBasisOpenChoice
public import OnLeConjecture.Analytic.MatrixLinearCoordinates
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction

/-!
# Common-linear exclusion with a chosen general member

The reduction conclusions are supplied on a nonempty open set of target
coefficient vectors. The node condition and all recorded exact orders are
then imposed within that same open set. The analytic point basis and its
weak generators are reconstructed before the proved common-linear exclusion
is applied. No reduction theorem is asserted here.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- A coefficient vector with nonzero second coordinate can be selected as
the first target coordinate by a constructed invertible linear change. -/
theorem exists_target_first_linearCombination_of_second_coefficient_ne_zero
    (g : PointedMapGerm 2 3) (q : Fin 3 → ℂ) (hq : q 1 ≠ 0) :
    ∃ f : PointedMapGerm 2 3, g.RightLeftEquivalent f ∧
      f.1.component 0 = germLinearCombination g.1.component q ∧
      f.1.component 1 = g.1.component 0 ∧ f.1.component 2 = g.1.component 2 := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![q 0, q 1, q 2; 1, 0, 0; 0, 0, 1]
  have hA : A.det ≠ 0 := by simpa [A, Matrix.det_fin_three] using neg_ne_zero.mpr hq
  obtain ⟨T, hT⟩ := exists_equiv_linear_matrix A hA
  let f := T.forward.comp g
  have hf (i : Fin 3) : f.1.component i = ∑ j, constRingHom 2 (A i j) * g.1.component j := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← PointedMapGerm.pullback_coordinate,
      hT, map_sum]
    simp only [map_mul, PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_coordinate]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, T, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · rw [hf]
    change (∑ j, constRingHom 2 (A 0 j) * g.1.component j) = ∑ j, q j • g.1.component j
    apply Finset.sum_congr rfl
    intro j _
    have hrow : A 0 j = q j := by fin_cases j <;> rfl
    rw [hrow]
    rfl
  · simpa [A, Fin.sum_univ_succ] using hf 1
  · simpa [A, Fin.sum_univ_succ] using hf 2

/-- The common-linear case is impossible when the genuine maximal-component
and polar reduction data hold on a nonempty open set of coefficient choices.
The sum of squares is the point-basis expression for the image multiplicity.
Neither node branch count nor either point count occurs as an input. -/
theorem common_linear_excluded_of_open_general_member_reduction
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2)
    (hF0 : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hF1 : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (hF2 : d.generators c.root 2 ∈ maximalIdeal 2 ^ 3)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty)
    (hReduction : ∀ q ∈ U, ∃ h : Germ 2, ∃ t : ℕ,
      h ∈ maximalIdeal 2 ∧ Numerical.MultiplicityCounts.sum c.multiplicity ≤ t ∧
        h ^ (t - 1) ∣ jacobian (d.generators c.root 0) (d.generators c.root 1) ∧
        ∃ hfinite : PlaneCurve.HasFiniteIntersection h
            (germLinearCombination (d.generators c.root) q),
          PlaneCurve.intersectionMultiplicity h
              (germLinearCombination (d.generators c.root) q) hfinite * (t - 1) +
              Numerical.MultiplicityCounts.sum c.multiplicity +
              PlaneCurve.irreducibleBranchCount (germLinearCombination (d.generators c.root) q) ≤
            2 * Numerical.MultiplicityCounts.squareSum c.multiplicity) : False := by
  have hproj : (LinearMap.proj (1 : Fin 3) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) ≠ 0 := by
    intro hzero
    have hh := congrArg (fun L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ => L (fun _ => 1)) hzero
    norm_num at hh
  obtain ⟨q, hqU, hq, hcondition⟩ :=
    d.exists_coefficients_exact_orders_linear_conditions_mem_open
      (fun _ : Fin 1 => LinearMap.proj (1 : Fin 3)) (fun _ => hproj) U hU hUne
  have hq1 : q 1 ≠ 0 := hcondition 0
  let d' := d.weakDataOfLinearCombination q hq
  have hcharts' := rootWeakChartCompatibility_linearCombination d q hq hcharts
  have hcomplete' := d.finiteWeakBasepointCompleteness_linearCombination q hq hcomplete
  have hnode := common_linear_linearCombination_quadratic_tail
    (d.generators c.root) hF0 hF1 hF2 q
  obtain ⟨h, t, hh, hMt, hdiv, hfinite, hpolar⟩ := hReduction q hqU
  have hF2' : d'.generators c.root 2 -
      (constRingHom 2 0 * d'.generators c.root 0 + constRingHom 2 0 * d'.generators c.root 1) ∈
        maximalIdeal 2 ^ 3 := by
    simp only [map_zero, zero_mul, zero_add, sub_zero]
    change d.generators c.root 2 ∈ maximalIdeal 2 ^ 3
    exact hF2
  exact common_linear_node_excluded_of_complete_weak_point_basis d' hcharts' hcomplete'
    hroot hF0 hF1 0 0 hF2' (q 0) (q 1) hq1 hnode h hh t
    (Numerical.MultiplicityCounts.squareSum c.multiplicity) hMt rfl hdiv hfinite hpolar

end OnLeConjecture.DTwo
