/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisReconstruction
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization
public import OnLeConjecture.DTwo.CommonLinearQuadraticPointBasis

/-!
# Choosing a node member of the common-linear pencil

For weak generators with root jets `x²,xy,0`, one coefficient vector has
exactly the recorded orders at every center and has nonzero `xy` coefficient.
Its root member has two irreducible analytic branches. The construction does
not assert a polar inequality for a newly chosen member.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem common_linear_linearCombination_quadratic_tail
    (F : Fin 3 → Germ 2)
    (hF0 : F 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hF1 : F 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3)
    (hF2 : F 2 ∈ maximalIdeal 2 ^ 3) (q : Fin 3 → ℂ) :
    germLinearCombination F q - coordinate (0 : Fin 2) *
      (constRingHom 2 (q 0) * coordinate (0 : Fin 2) +
        constRingHom 2 (q 1) * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3 := by
  have hh := (maximalIdeal 2 ^ 3).add_mem
    ((maximalIdeal 2 ^ 3).add_mem
      ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 (q 0)) hF0)
      ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 (q 1)) hF1))
    ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 (q 2)) hF2)
  have hLC : germLinearCombination F q =
      constRingHom 2 (q 0) * F 0 + constRingHom 2 (q 1) * F 1 +
        constRingHom 2 (q 2) * F 2 := by
    change (∑ i, q i • F i) = _
    simp only [Fin.sum_univ_three]
    rfl
  rw [hLC]
  convert hh using 1
  ring

/-- The coefficient of `xy` is chosen nonzero simultaneously with every
recorded exact order. The reconstructed point basis has the same centers,
chart identities and multiplicities, and its root is an analytic node. -/
theorem exists_common_linear_node_point_basis_member
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hF0 : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hF1 : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (hF2 : d.generators c.root 2 ∈ maximalIdeal 2 ^ 3) :
    ∃ q : Fin 3 → ℂ, q 1 ≠ 0 ∧
      ∃ hq : ∀ p, germLinearCombination (d.generators p) q ∈
          maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1),
        let c' := d.pointBasisOfLinearCombination q hq
        c'.germ c'.root - coordinate (0 : Fin 2) *
          (constRingHom 2 (q 0) * coordinate (0 : Fin 2) +
            constRingHom 2 (q 1) * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3 ∧
          PlaneCurve.irreducibleBranchCount (c'.germ c'.root) = 2 := by
  have hproj : (LinearMap.proj (1 : Fin 3) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) ≠ 0 := by
    intro hzero
    have hh := congrArg (fun L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ => L (fun _ => 1)) hzero
    norm_num at hh
  obtain ⟨q, hq, hcondition⟩ :=
    d.exists_coefficients_exact_orders_and_linear_conditions
      (fun _ : Fin 1 => LinearMap.proj (1 : Fin 3)) (fun _ => hproj)
  have hq1 : q 1 ≠ 0 := hcondition 0
  have htail := common_linear_linearCombination_quadratic_tail
    (d.generators c.root) hF0 hF1 hF2 q
  exact ⟨q, hq1, hq, htail,
    ordinary_node_irreducibleBranchCount_eq_two
      (germLinearCombination (d.generators c.root) q) (q 0) (q 1) hq1 htail⟩

theorem rootWeakChartCompatibility_linearCombination
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (q : Fin 3 → ℂ)
    (hq : ∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
      germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1))
    (hcharts : RootWeakChartCompatibility d) :
    RootWeakChartCompatibility (d.weakDataOfLinearCombination q hq) := by
  constructor
  intro p hp
  exact hcharts.charts p hp

/-- For a complete weak-ideal point basis, the chosen node member retains
the chart compatibility and has the derived counts `A₂=1` and `A₁≥1`.
No polar inequality for the new member is asserted. -/
theorem exists_common_linear_node_member_with_complete_point_basis
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2)
    (hF0 : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hF1 : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (hF2 : d.generators c.root 2 ∈ maximalIdeal 2 ^ 3) :
    ∃ q : Fin 3 → ℂ, q 1 ≠ 0 ∧
      ∃ hq : ∀ p, germLinearCombination (d.generators p) q ∈
          maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1),
        let c' := d.pointBasisOfLinearCombination q hq
        let d' := d.weakDataOfLinearCombination q hq
        RootWeakChartCompatibility d' ∧ FiniteWeakBasepointCompleteness d' ∧
          PlaneCurve.irreducibleBranchCount (c'.germ c'.root) = 2 ∧
          Numerical.MultiplicityCounts.valueCount c'.multiplicity 2 = 1 ∧
          1 ≤ Numerical.MultiplicityCounts.valueCount c'.multiplicity 1 := by
  obtain ⟨q, hq1, hq, _, hbranch⟩ :=
    exists_common_linear_node_point_basis_member d hF0 hF1 hF2
  let d' := d.weakDataOfLinearCombination q hq
  have hcharts' := rootWeakChartCompatibility_linearCombination d q hq hcharts
  have hcomplete' := d.finiteWeakBasepointCompleteness_linearCombination q hq hcomplete
  have hF2' : d'.generators c.root 2 -
      (constRingHom 2 0 * d'.generators c.root 0 + constRingHom 2 0 * d'.generators c.root 1) ∈
        maximalIdeal 2 ^ 3 := by
    simp only [map_zero, zero_mul, zero_add, sub_zero]
    change d.generators c.root 2 ∈ maximalIdeal 2 ^ 3
    exact hF2
  obtain ⟨hcount2, hcount1, _, _⟩ := common_linear_complete_point_basis_counts
    d' hcharts' hcomplete' hroot hF0 hF1 0 0 hF2'
  exact ⟨q, hq1, hq, hcharts', hcomplete', hbranch, hcount2, hcount1⟩

end OnLeConjecture.DTwo
