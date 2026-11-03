/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveFixedTangentGenericAvoidance
public import OnLeConjecture.DThree.MaximalCriticalFirstBlowup

/-!
# Cubic maximal critical intersection in either projective chart

The numerical estimates prove smoothness of the fixed critical equation.
Its tangent is then treated in the finite or complementary root chart.
Two-chart weak-basepoint completeness and fixed-tangent avoidance rule
out intersection four without a coordinate-derivative hypothesis.
-/

public section

namespace OnLeConjecture.DThree

open Analytic Analytic.Germ
open scoped BigOperators

theorem cubic_maximal_critical_intersection_eq_three_of_projective_first_blowup
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    {ι : Type*} [Fintype ι] (w : WeakTransformIdealData c ι)
    (hcomplete : RootTwoChartWeakBasepointCompleteness w)
    (q : ι → ℂ)
    (hmember : c.germ c.root = germLinearCombination (w.generators c.root) q)
    (hroot : c.multiplicity c.root = 3)
    (hdepth : ∀ p, c.ParentRelation p c.root →
      c.generation p = c.generation c.root + 1)
    (t : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ d.proximity.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (havoid : w.AvoidsRootProjectiveTangentCancellation q (criticalProjectiveTangent h))
    (hfinite : PlaneCurve.HasFiniteIntersection h (c.germ c.root))
    (hglobal : d.proximity.squareMultiplicity + d.proximity.totalMultiplicity ≤ 3 * t)
    (hpolar : PlaneCurve.intersectionMultiplicity h (c.germ c.root) hfinite * (t - 1) +
      d.proximity.totalMultiplicity + d.proximity.branchCount ≤
        2 * d.proximity.squareMultiplicity) :
    PlaneCurve.intersectionMultiplicity h (c.germ c.root) hfinite = 3 ∧
    differential h ≠ 0 ∧ Irreducible h := by
  let I := PlaneCurve.intersectionMultiplicity h (c.germ c.root) hfinite
  have hfinite' : PlaneCurve.HasFiniteIntersection (c.germ c.root) h :=
    (PlaneCurve.hasFiniteIntersection_comm _ _).mp hfinite
  have hinterComm := PlaneCurve.intersectionMultiplicity_comm h (c.germ c.root) hfinite
  have hglobal' : Numerical.MultiplicityCounts.squareSum c.multiplicity +
      (∑ p, c.multiplicity p) ≤ 3 * t := by
    simpa only [Numerical.ProximityCertificate.squareMultiplicity,
      Numerical.ProximityCertificate.totalMultiplicity, d.multiplicity_eq] using hglobal
  have hpolar' : PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite' * (t - 1) +
      (∑ p, c.multiplicity p) + d.proximity.branchCount ≤
        2 * Numerical.MultiplicityCounts.squareSum c.multiplicity := by
    rw [← hinterComm]
    simpa only [Numerical.ProximityCertificate.squareMultiplicity,
      Numerical.ProximityCertificate.totalMultiplicity, d.multiplicity_eq] using hpolar
  obtain ⟨hlower', hupper', hsmooth, hirred⟩ := c.maximal_critical_equation_smooth
    3 t d.proximity.branchCount (Or.inl rfl) hroot hb ht h hh hfinite' hglobal' hpolar'
  have hlower : 3 ≤ I := by simpa only [← hinterComm] using hlower'
  have hupper : I ≤ 4 := by simpa only [← hinterComm] using hupper'
  have hnotFour : I ≠ 4 := by
    intro hfour
    obtain ⟨V, hVfactor, hV, hVnext⟩ :=
      exists_smooth_first_transform_of_critical_intersection_succ
        3 (c.germ c.root) h (by simpa only [hroot] using c.germ_mem c.root)
        hh hsmooth hfinite hfour
    obtain ⟨p, hparent, hentry⟩ :=
      w.exists_root_child_entry_one_of_projective_tangent_avoidance
        hcomplete q (criticalProjectiveTangent h) hmember havoid V
        (by simpa only [hroot] using hVfactor) hV hVnext
    have hfree := d.not_satellite_of_first_depth p hparent (hdepth p hparent)
    have hresult := OnLeConjecture.DThree.ProximityCertificate.transverse_intersection_eq_three
      d.proximity t I
      (by simpa only [d.multiplicity_eq, d.root_eq] using hroot)
      (fun p ↦ by rw [d.multiplicity_eq]; exact c.multiplicity_pos p)
      (fun p ↦ by simpa only [d.multiplicity_eq, hroot] using c.multiplicity_le_root p)
      hb p (by simpa only [d.multiplicity_eq] using hentry) hfree
      (by omega) hlower hglobal hpolar
    omega
  exact ⟨by change I = 3; omega, hsmooth, hirred⟩

theorem exists_cubic_source_preparation_of_maximal_critical_projective_first_blowup
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (hcomponent : c.germ c.root = g.1.component 0)
    {ι : Type*} [Fintype ι] (w : WeakTransformIdealData c ι)
    (hcomplete : RootTwoChartWeakBasepointCompleteness w)
    (q : ι → ℂ)
    (hmember : c.germ c.root = germLinearCombination (w.generators c.root) q)
    (hroot : c.multiplicity c.root = 3)
    (hdepth : ∀ p, c.ParentRelation p c.root →
      c.generation p = c.generation c.root + 1)
    (t : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ d.proximity.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (havoid : w.AvoidsRootProjectiveTangentCancellation q (criticalProjectiveTangent h))
    (hfinite : PlaneCurve.HasFiniteIntersection h (c.germ c.root))
    (hglobal : d.proximity.squareMultiplicity + d.proximity.totalMultiplicity ≤ 3 * t)
    (hpolar : PlaneCurve.intersectionMultiplicity h (c.germ c.root) hfinite * (t - 1) +
      d.proximity.totalMultiplicity + d.proximity.branchCount ≤
        2 * d.proximity.squareMultiplicity) :
    Nonempty (SmoothReductionCoordinates g h 3) := by
  obtain ⟨hinter, hsmooth, _⟩ :=
    cubic_maximal_critical_intersection_eq_three_of_projective_first_blowup
      c d w hcomplete q hmember hroot hdepth t ht hb h hh havoid hfinite hglobal hpolar
  have hfinite' : PlaneCurve.HasFiniteIntersection h (g.1.component 0) := by
    simpa only [hcomponent] using hfinite
  apply exists_smoothReductionCoordinates g h hh hsmooth hfinite' 3 (Or.inl rfl)
  simpa only [hcomponent] using hinter

/-- The critical equation and all reduction inequalities are fixed on
the prescribed open set before choosing the coefficients. The resulting
member has the recorded exact orders and critical intersection three. -/
theorem exists_open_cubic_member_critical_intersection_three
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    {ι : Type*} [Fintype ι] (w : WeakTransformIdealData c ι)
    (hcomplete : RootTwoChartWeakBasepointCompleteness w)
    (hroot : c.multiplicity c.root = 3)
    (hdepth : ∀ p, c.ParentRelation p c.root →
      c.generation p = c.generation c.root + 1)
    (t : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ d.proximity.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hglobal : d.proximity.squareMultiplicity + d.proximity.totalMultiplicity ≤ 3 * t)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty)
    (hfinite : ∀ q ∈ U,
      PlaneCurve.HasFiniteIntersection h (germLinearCombination (w.generators c.root) q))
    (hpolar : ∀ q (hq : q ∈ U),
      PlaneCurve.intersectionMultiplicity h (germLinearCombination (w.generators c.root) q)
          (hfinite q hq) * (t - 1) +
        d.proximity.totalMultiplicity + d.proximity.branchCount ≤
          2 * d.proximity.squareMultiplicity) :
    ∃ q ∈ U, ∃ hq : ∀ p,
        germLinearCombination (w.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (w.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1),
      w.AvoidsRootProjectiveTangentCancellation q (criticalProjectiveTangent h) ∧
      ∃ hf : PlaneCurve.HasFiniteIntersection h
          ((w.pointBasisOfLinearCombination q hq).germ c.root),
        PlaneCurve.intersectionMultiplicity h
          ((w.pointBasisOfLinearCombination q hq).germ c.root) hf = 3 ∧
        differential h ≠ 0 ∧ Irreducible h := by
  obtain ⟨q, hqU, hq, havoid⟩ :=
    w.exists_coefficients_exact_orders_projective_tangent_avoidance_mem_open
      (fun _ : Unit => criticalProjectiveTangent h) U hU hUne
  refine ⟨q, hqU, hq, havoid (), hfinite q hqU, ?_⟩
  exact cubic_maximal_critical_intersection_eq_three_of_projective_first_blowup
    (w.pointBasisOfLinearCombination q hq) (w.proximityOfLinearCombination q hq d)
    (w.weakDataOfLinearCombination q hq)
    (w.rootTwoChartWeakBasepointCompleteness_linearCombination q hq hcomplete)
    q rfl hroot hdepth t ht hb h hh
    (w.avoidsRootProjectiveTangentCancellation_linearCombination q hq
      (criticalProjectiveTangent h) (havoid ()))
    (hfinite q hqU) hglobal (hpolar q hqU)

end OnLeConjecture.DThree
