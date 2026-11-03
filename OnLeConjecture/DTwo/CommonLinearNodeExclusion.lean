/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CommonLinearQuadraticPointBasis
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization

/-!
# Common-linear quadratic exclusion with the actual analytic branch count

The generic member is chosen with nonzero `xy` coefficient in the common
quadratic pencil. Its two analytic branches are constructed, so the polar
inequality uses the proved UFD branch count instead of a free natural
parameter. The generic choice itself and the reduction/resolution inputs
remain explicit.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The common-linear branch with both point-basis counts and the analytic
branch count derived. The nonzero pencil coefficient is the remaining
explicit generic-member choice. -/
theorem common_linear_node_excluded_of_complete_weak_point_basis
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2)
    (hf : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (α β : ℂ)
    (hw : d.generators c.root 2 -
      (constRingHom 2 α * d.generators c.root 0 + constRingHom 2 β * d.generators c.root 1) ∈
        maximalIdeal 2 ^ 3)
    (a b : ℂ) (hb : b ≠ 0)
    (hnode : c.germ c.root - coordinate (0 : Fin 2) *
      (constRingHom 2 a * coordinate (0 : Fin 2) +
        constRingHom 2 b * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2) (t i : ℕ)
    (hMt : Numerical.MultiplicityCounts.sum c.multiplicity ≤ t)
    (hNoether : i = Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hdiv : h ^ (t - 1) ∣ jacobian (d.generators c.root 0) (d.generators c.root 1))
    (hfinite : PlaneCurve.HasFiniteIntersection h (c.germ c.root))
    (hpolar : PlaneCurve.intersectionMultiplicity h (c.germ c.root) hfinite * (t - 1) +
      Numerical.MultiplicityCounts.sum c.multiplicity +
      PlaneCurve.irreducibleBranchCount (c.germ c.root) ≤ 2 * i) : False := by
  have hbranches := ordinary_node_irreducibleBranchCount_eq_two (c.germ c.root) a b hb hnode
  exact common_linear_quadratic_excluded_of_complete_weak_point_basis
    d hcharts hcomplete hroot hf hg α β hw h hh t
    (PlaneCurve.irreducibleBranchCount (c.germ c.root)) i (by omega)
    hMt hNoether hdiv hfinite hpolar

end OnLeConjecture.DTwo
