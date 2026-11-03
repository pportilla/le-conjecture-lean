/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupPointBasis
public import OnLeConjecture.Analytic.RawWeakBlowupSiblingSeparation
public import OnLeConjecture.Analytic.ProjectivePointBasisAtlas
import Mathlib.Tactic

/-!
# The projective atlas of the constructed point basis

Each edge is labeled by its literal projective chart. Distinct children
have distinct labels because the tree contains exactly one child tree at
each projective basepoint.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

@[expose] noncomputable def twoChartAtlas (T : RawProjectiveWeakBlowupTree F)
    (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    TopOrderTwoChartAtlas (T.pointBasis q hq) where
  chartPoint p := T.chartPoint (T.indexEquiv.symm p)
  coordinates p _ r _ := by
    change match T.chartPoint (T.indexEquiv.symm r) with
      | some ζ => projectiveChartCenter (T.chartPoint (T.indexEquiv.symm r)) = ζ ∧
          (projectiveChartSource (T.chartPoint (T.indexEquiv.symm r))).forward =
            PointedMapGerm.identity 2
      | none => projectiveChartCenter (T.chartPoint (T.indexEquiv.symm r)) = 0 ∧
          (projectiveChartSource (T.chartPoint (T.indexEquiv.symm r))).forward =
            (coordinateSwapPointedEquiv (1 : Fin 2)).forward
    cases T.chartPoint (T.indexEquiv.symm r) <;>
      simp [projectiveChartCenter, projectiveChartSource]
  separated p _ r s hr hs hchart := by
    apply T.indexEquiv.symm.injective
    apply T.eq_of_predecessor_eq_chartPoint_eq _ _ ?_ ?_ ?_ hchart
    · intro h
      apply hr.1
      exact (T.indexEquiv.eq_symm_apply.mp h.symm).symm
    · intro h
      apply hs.1
      exact (T.indexEquiv.eq_symm_apply.mp h.symm).symm
    · apply T.indexEquiv.injective
      exact hr.2.trans hs.2.symm

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
