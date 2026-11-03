/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Persistence of a multiple zero

The minimum modulus principle gives a zero in a disk when the norm at its
center is smaller than the norm on its boundary. This criterion yields
persistence under uniform convergence on the boundary.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

/-- A holomorphic function has a zero in a closed disk if its norm at the
center is smaller than a positive lower bound on the boundary. -/
theorem exists_zero_mem_closedBall_of_norm_lt_boundary
    (f : ℂ → ℂ) (r C : ℝ)
    (hr : 0 < r) (hC : 0 < C)
    (hf : DiffContOnCl ℂ f (ball 0 r))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) r, C ≤ ‖f z‖)
    (hcenter : ‖f 0‖ < C) :
    ∃ z ∈ closedBall (0 : ℂ) r, f z = 0 := by
  by_contra hzero
  push Not at hzero
  have hnonzero : ∀ z ∈ closure (ball (0 : ℂ) r), f z ≠ 0 := by
    rw [closure_ball _ hr.ne']
    exact hzero
  have hinverse : DiffContOnCl ℂ f⁻¹ (ball (0 : ℂ) r) :=
    hf.inv hnonzero
  have hboundaryInverse :
      ∀ z ∈ frontier (ball (0 : ℂ) r), ‖f⁻¹ z‖ ≤ C⁻¹ := by
    rw [frontier_ball _ hr.ne']
    intro z hz
    rw [Pi.inv_apply, norm_inv]
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hzero z (sphere_subset_closedBall hz))) hC).2
      (hboundary z hz)
  have hcenterInverse : ‖f⁻¹ 0‖ ≤ C⁻¹ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hinverse hboundaryInverse <| by
        rw [closure_ball _ hr.ne']
        exact mem_closedBall_self hr.le
  have hcenterLower : C ≤ ‖f 0‖ := by
    rw [Pi.inv_apply, norm_inv] at hcenterInverse
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hzero 0 (mem_closedBall_self hr.le))) hC).1
      hcenterInverse
  exact (not_le_of_gt hcenter) hcenterLower

/-- Zeros persist when a family converges uniformly on the boundary of a
disk, its values at the center converge to zero, and its members are
holomorphic on the disk. -/
theorem eventually_exists_zero_mem_closedBall_of_tendstoUniformlyOn
    {A : Type*} {l : Filter A}
    (F : A → ℂ → ℂ) (f : ℂ → ℂ) (r C : ℝ)
    (hr : 0 < r) (hC : 0 < C)
    (huniform : TendstoUniformlyOn F f l (sphere (0 : ℂ) r))
    (hslices : ∀ᶠ t in l, DiffContOnCl ℂ (F t) (ball 0 r))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) r, C ≤ ‖f z‖)
    (hcenter : Tendsto (fun t ↦ F t 0) l (nhds 0)) :
    ∀ᶠ t in l, ∃ z ∈ closedBall (0 : ℂ) r, F t z = 0 := by
  have hhalf : 0 < C / 2 := half_pos hC
  have huniform' :
      ∀ᶠ t in l, ∀ z ∈ sphere (0 : ℂ) r,
        dist (f z) (F t z) < C / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp huniform) (C / 2) hhalf
  have hcenter' : ∀ᶠ t in l, ‖F t 0‖ < C / 2 := by
    have ht := (Metric.tendsto_nhds.mp hcenter) (C / 2) hhalf
    simpa [dist_zero_right] using ht
  filter_upwards [hslices, huniform', hcenter'] with t ht htu htc
  apply exists_zero_mem_closedBall_of_norm_lt_boundary
      (F t) r (C / 2) hr hhalf ht
  · intro z hz
    have hdist : ‖f z - F t z‖ < C / 2 := by
      simpa [dist_eq_norm] using htu z hz
    have hnorm := norm_sub_norm_le (f z) (F t z)
    nlinarith [hboundary z hz]
  · exact htc

/-- A positive order zero of the special fiber persists in an arbitrarily
small disk for all sufficiently small values of the parameter. -/
theorem eventually_exists_zero_of_analyticAt_of_specialFiber_factorization_lt
    (Phi : ℂ × ℂ → ℂ) (m : ℕ) (u : ℂ → ℂ)
    (hm : 0 < m)
    (hPhi : AnalyticAt ℂ Phi (0, 0))
    (hu : AnalyticAt ℂ u 0)
    (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ z in nhds 0, Phi (0, z) = z ^ m * u z)
    (R : ℝ) (hR : 0 < R) :
    ∃ r > 0, r < R ∧ ∀ᶠ t in nhds 0,
      ∃ z ∈ closedBall (0 : ℂ) r, Phi (t, z) = 0 := by
  obtain ⟨Rjoint, hRjoint, hAnalyticJoint⟩ :=
    Metric.mem_nhds_iff.mp hPhi.eventually_analyticAt
  have huNorm : 0 < ‖u 0‖ := norm_pos_iff.mpr hu0
  have huClose :
      ∀ᶠ z in nhds 0, dist (u z) (u 0) < ‖u 0‖ / 2 :=
    (Metric.tendsto_nhds.mp hu.continuousAt) (‖u 0‖ / 2) (half_pos huNorm)
  have huLower : ∀ᶠ z in nhds 0, ‖u 0‖ / 2 < ‖u z‖ := by
    filter_upwards [huClose] with z hz
    rw [dist_eq_norm] at hz
    have htriangle : ‖u 0‖ - ‖u z‖ ≤ ‖u z - u 0‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le (u 0) (u z)
    nlinarith
  obtain ⟨Rfiber, hRfiber, hFiber⟩ :=
    Metric.mem_nhds_iff.mp (hfactor.and huLower)
  let r : ℝ := min (min Rjoint Rfiber) R / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrJoint : r < Rjoint := by
    dsimp [r]
    nlinarith [min_le_left (min Rjoint Rfiber) R,
      min_le_left Rjoint Rfiber, hRjoint]
  have hrFiber : r < Rfiber := by
    dsimp [r]
    nlinarith [min_le_left (min Rjoint Rfiber) R,
      min_le_right Rjoint Rfiber, hRfiber]
  have hrBound : r < R := by
    dsimp [r]
    nlinarith [min_le_right (min Rjoint Rfiber) R, hR]
  have hpairAnalytic
      {t z : ℂ} (ht : t ∈ closedBall 0 r) (hz : z ∈ closedBall 0 r) :
      AnalyticAt ℂ Phi (t, z) := by
    apply hAnalyticJoint
    rw [mem_ball, Prod.dist_eq]
    exact max_lt
      (lt_of_le_of_lt (by simpa [mem_closedBall] using ht) hrJoint)
      (lt_of_le_of_lt (by simpa [mem_closedBall] using hz) hrJoint)
  have hcontinuousJoint : ContinuousOn Phi
      (closedBall (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) := by
    intro s hs
    exact (hpairAnalytic hs.1 (sphere_subset_closedBall hs.2)).continuousAt.continuousWithinAt
  have huniformWithin :
      TendstoUniformlyOn (fun t z ↦ Phi (t, z)) (fun z ↦ Phi (0, z))
        (nhdsWithin 0 (closedBall (0 : ℂ) r)) (sphere (0 : ℂ) r) := by
    have hcompact : IsCompact
        (closedBall (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) :=
      (isCompact_closedBall (0 : ℂ) r).prod (isCompact_sphere (0 : ℂ) r)
    exact (hcompact.uniformContinuousOn_of_continuous hcontinuousJoint).tendstoUniformlyOn
      (mem_closedBall_self hr.le)
  have huniform :
      TendstoUniformlyOn (fun t z ↦ Phi (t, z)) (fun z ↦ Phi (0, z))
        (nhds 0) (sphere (0 : ℂ) r) := by
    rw [nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds 0 hr)] at huniformWithin
    exact huniformWithin
  have hslices :
      ∀ᶠ t in nhds 0, DiffContOnCl ℂ (fun z ↦ Phi (t, z)) (ball 0 r) := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr] with t ht
    apply DifferentiableOn.diffContOnCl
    intro z hz
    rw [closure_ball _ hr.ne'] at hz
    simpa [Function.comp_def] using
      ((hpairAnalytic ht hz).differentiableAt.comp z (by fun_prop)).differentiableWithinAt
  have hFiberOnSphere :
      ∀ z ∈ sphere (0 : ℂ) r,
        Phi (0, z) = z ^ m * u z ∧ ‖u 0‖ / 2 < ‖u z‖ := by
    intro z hz
    apply hFiber
    rw [mem_ball]
    exact lt_of_eq_of_lt (by simpa [mem_sphere] using hz) hrFiber
  let C : ℝ := r ^ m * (‖u 0‖ / 2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hboundary :
      ∀ z ∈ sphere (0 : ℂ) r, C ≤ ‖Phi (0, z)‖ := by
    intro z hz
    obtain ⟨hzFactor, hzUnit⟩ := hFiberOnSphere z hz
    rw [hzFactor, norm_mul, norm_pow]
    have hzNorm : ‖z‖ = r := by simpa [mem_sphere] using hz
    rw [hzNorm]
    dsimp [C]
    exact mul_le_mul_of_nonneg_left hzUnit.le (pow_nonneg hr.le m)
  have hbase : Phi (0, 0) = 0 := by
    have hzeroFiber := hFiber (mem_ball_self hRfiber : (0 : ℂ) ∈ ball 0 Rfiber)
    simpa [zero_pow hm.ne'] using hzeroFiber.1
  have hcenter : Tendsto (fun t ↦ Phi (t, 0)) (nhds 0) (nhds 0) := by
    have hembed : ContinuousAt (fun t : ℂ ↦ (t, (0 : ℂ))) 0 :=
      continuousAt_id.prodMk continuousAt_const
    have hc : ContinuousAt (fun t : ℂ ↦ Phi (t, 0)) 0 := by
      simpa [Function.comp_def] using
        hPhi.continuousAt.comp_of_eq hembed rfl
    change Tendsto (fun t : ℂ ↦ Phi (t, 0)) (nhds 0) (nhds (Phi (0, 0))) at hc
    simpa [hbase] using hc
  refine ⟨r, hr, hrBound, ?_⟩
  exact eventually_exists_zero_mem_closedBall_of_tendstoUniformlyOn
    (fun t z ↦ Phi (t, z)) (fun z ↦ Phi (0, z)) r C hr hC
      huniform hslices hboundary hcenter

/-- A positive order zero of the special fiber of a two variable analytic
function persists for all sufficiently small values of the parameter. -/
theorem eventually_exists_zero_of_analyticAt_of_specialFiber_factorization
    (Phi : ℂ × ℂ → ℂ) (m : ℕ) (u : ℂ → ℂ)
    (hm : 0 < m)
    (hPhi : AnalyticAt ℂ Phi (0, 0))
    (hu : AnalyticAt ℂ u 0)
    (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ z in nhds 0, Phi (0, z) = z ^ m * u z) :
    ∃ r > 0, ∀ᶠ t in nhds 0,
      ∃ z ∈ closedBall (0 : ℂ) r, Phi (t, z) = 0 := by
  obtain ⟨r, hr, -, hzero⟩ :=
    eventually_exists_zero_of_analyticAt_of_specialFiber_factorization_lt
      Phi m u hm hPhi hu hu0 hfactor 1 zero_lt_one
  exact ⟨r, hr, hzero⟩

end OnLeConjecture.Analytic
