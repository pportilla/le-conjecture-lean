/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupPointBasis
public import OnLeConjecture.Analytic.PointBlowupSmoothIntersection
public import OnLeConjecture.PlaneCurve.IrreducibleFiniteIntersection

/-!
# Exact-order members have no exceptional-axis component

At every nonroot vertex the member has nonzero restriction to the newest
exceptional divisor. If an older exceptional divisor is present on the
other coordinate axis, its restriction is also nonzero. The proof uses
the exact parent order, the actual weak-transform identity, and the
recursion defining the older-axis label.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

theorem member_firstAxisRestriction_ne_zero
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : T.Vertex) (hp : p ≠ T.root) :
    lineRestriction (firstCoordinateVector 1) (germLinearCombination (T.generators p) q) ≠ 0 := by
  have hmem := germLinearCombination_mem _ _ (T.generator_mem (T.predecessor p)) q
  have hnext : (projectiveChartSource (T.chartPoint p)).forward.pullbackRingHom
      (germLinearCombination (T.generators (T.predecessor p)) q) ∉
        maximalIdeal 2 ^ (T.multiplicity (T.predecessor p) + 1) := by
    intro h
    exact hq _ (((projectiveChartSource (T.chartPoint p)).pullback_mem_maximalIdeal_pow_iff _).mp h)
  have hne := pointBlowupTransform_exceptionalRestriction_ne_zero
    (projectiveChartCenter (T.chartPoint p)) (T.multiplicity (T.predecessor p))
    ((projectiveChartSource (T.chartPoint p)).forward.pullbackRingHom
      (germLinearCombination (T.generators (T.predecessor p)) q))
    (germLinearCombination (T.generators p) q)
    ((projectiveChartSource (T.chartPoint p)).forward.pullback_mem_maximalIdeal_pow hmem)
    hnext (T.linearCombination_transform q p hp)
  rwa [pointBlowupExceptionalLine_eq_lineGerm] at hne

/-- At the finite zero chart the old first-coordinate axis keeps its
parameter, and restriction removes the exceptional power. -/
theorem member_zero_chart_axis_identity
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (p : T.Vertex) (hp : p ≠ T.root) (hchart : T.chartPoint p = some 0) :
    hyperplaneRestriction 1 (germLinearCombination (T.generators (T.predecessor p)) q) =
      coordinate (0 : Fin 1) ^ T.multiplicity (T.predecessor p) *
        hyperplaneRestriction 1 (germLinearCombination (T.generators p) q) := by
  have h := T.linearCombination_transform q p hp
  simp only [hchart, projectiveChartCenter, projectiveChartSource,
    PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity,
    RingHom.id_apply] at h
  have hr := congrArg (hyperplaneRestriction 1) h
  simpa only [hyperplaneRestriction_pointBlowupChart_zero, map_mul, map_pow,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    hyperplaneRestriction_coordinate_succ] using hr

/-- In the complementary chart, the parent's newest exceptional line
becomes the child's older first-coordinate axis. -/
theorem member_complementary_chart_axis_identity
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (p : T.Vertex) (hp : p ≠ T.root) (hchart : T.chartPoint p = none) :
    lineRestriction (firstCoordinateVector 1)
        (germLinearCombination (T.generators (T.predecessor p)) q) =
      coordinate (0 : Fin 1) ^ T.multiplicity (T.predecessor p) *
        hyperplaneRestriction 1 (germLinearCombination (T.generators p) q) := by
  have h := T.linearCombination_transform q p hp
  simp only [hchart, projectiveChartCenter, projectiveChartSource] at h
  have hr := congrArg (hyperplaneRestriction 1) h
  rw [complementaryBlowupChart_secondAxisRestriction] at hr
  simpa only [map_mul, map_pow,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    hyperplaneRestriction_coordinate_succ] using hr

theorem member_oldAxisRestriction_ne_zero
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    {p a : T.Vertex} (haxis : T.rootedChartData.xAncestor p = some a) :
    hyperplaneRestriction 1 (germLinearCombination (T.generators p) q) ≠ 0 := by
  classical
  induction p using (measure T.generation).wf.induction generalizing a with
  | h p ih =>
      obtain ⟨hp, hparent, _⟩ := T.rootedChartData.xAncestor_predecessor_cases haxis
      change p ≠ T.root at hp
      change T.predecessor p ≠ T.root at hparent
      cases hc : T.chartPoint p with
      | none =>
          have hidentity := T.member_complementary_chart_axis_identity q p hp hc
          have hne := T.member_firstAxisRestriction_ne_zero q hq (T.predecessor p) hparent
          intro hz
          exact hne (by rw [hidentity, hz, mul_zero])
      | some ζ =>
          by_cases hζ : ζ = 0
          · subst ζ
            have haxisParent : T.rootedChartData.xAncestor (T.predecessor p) = some a := by
              rw [T.rootedChartData.xAncestor_zero p hp hc] at haxis
              exact haxis
            have hne := ih (T.predecessor p) (T.generation_decreases p hp) haxisParent
            have hidentity := T.member_zero_chart_axis_identity q p hp hc
            intro hz
            exact hne (by rw [hidentity, hz, mul_zero])
          · rw [T.rootedChartData.xAncestor_nonzero p hp ζ hζ hc] at haxis
            cases haxis

theorem member_hasFiniteIntersection_oldAxis
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    {p a : T.Vertex} (haxis : T.rootedChartData.xAncestor p = some a) :
    PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2))
      (germLinearCombination (T.generators p) q) :=
  PlaneCurve.hasFiniteIntersection_coordinate_of_restriction_ne_zero _
    (T.member_oldAxisRestriction_ne_zero q hq haxis)

theorem member_hasFiniteIntersection_newestAxis
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : T.Vertex) (hp : p ≠ T.root) :
    PlaneCurve.HasFiniteIntersection (coordinate (1 : Fin 2))
      (germLinearCombination (T.generators p) q) := by
  have hy : Irreducible (coordinate (1 : Fin 2)) := by
    apply (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq _
      (coordinate_mem_maximalIdeal 1) _).2
    intro hmem
    have hd := (mem_firstOrderIdeal_iff.mp (maximalIdeal_sq_le_firstOrderIdeal 2 hmem)).2
    have hv := congrArg (fun L : Source 2 →L[ℂ] ℂ => L (coordinateVector 1)) hd
    simp [coordinateVector] at hv
  apply PlaneCurve.hasFiniteIntersection_of_irreducible_not_dvd _ _ hy
  intro hdiv
  have hline := pointBlowupExceptionalLine.pullbackRingHom.map_dvd hdiv
  change pointBlowupExceptionalLine.pullbackRingHom (coordinate 1) ∣
    pointBlowupExceptionalLine.pullbackRingHom (germLinearCombination (T.generators p) q) at hline
  rw [pointBlowupExceptionalLine_pullback_one, zero_dvd_iff,
    pointBlowupExceptionalLine_eq_lineGerm] at hline
  exact T.member_firstAxisRestriction_ne_zero q hq p hp hline

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
