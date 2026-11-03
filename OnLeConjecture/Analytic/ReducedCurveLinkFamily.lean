/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveBranches
public import OnLeConjecture.Analytic.PlaneBranchNormalizedLinkFamily

/-!
# Simultaneous normalized links of a reduced plane curve

Finite irreducible factorization and punctured separation provide one
radius interval on which all branch circles are disjoint. Their union is
the entire normalized sphere zero set of the original equation. Each
component depends smoothly on the squared radius.
-/

public noncomputable section

open Filter Set
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

/-- Circle parametrizations of all the normalized sphere zero sets of a
plane equation on one positive interval, with disjoint smooth components. -/
structure NormalizedPlaneCurveLinkFamily (H : Source 2 → ℂ) (ι : Type*) where
  radiusSq : ℝ
  radiusSq_pos : 0 < radiusSq
  component : ι → Metric.sphere (0 : ℂ) 1 × ℝ → EuclideanSpace ℂ (Fin 2)
  norm_eq_one : ∀ c ∈ Ioo 0 radiusSq, ∀ i u, ‖component i (u, c)‖ = 1
  smooth : ∀ c ∈ Ioo 0 radiusSq, ∀ i u,
    ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (component i) (u, c)
  closedEmbedding : ∀ c ∈ Ioo 0 radiusSq, ∀ i,
    Topology.IsClosedEmbedding (fun u => component i (u, c))
  differential_injective : ∀ c ∈ Ioo 0 radiusSq, ∀ i u,
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      (fun v => component i (v, c)) u)
  disjoint : ∀ c ∈ Ioo 0 radiusSq,
    Pairwise (fun i j => Disjoint (Set.range (fun u => component i (u, c)))
      (Set.range (fun u => component j (u, c))))
  range_eq : ∀ c ∈ Ioo 0 radiusSq,
    (⋃ i, Set.range (fun u => component i (u, c))) =
      (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ''
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt c) ∩
          {y | H ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0})

namespace Germ

/-- Finitely many irreducible representatives with a proved local union
and punctured separation give simultaneous disjoint smooth circle families. -/
theorem exists_normalized_link_family_of_separated_branches
    {ι : Type*} [Finite ι] (H : Source 2 → ℂ) (P : ι → Source 2 → ℂ)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0)
    (hirr : ∀ i, Irreducible (ofFunction (P i) (hP i)))
    (hcover : ∀ᶠ z in 𝓝 (0 : Source 2), H z = 0 ↔ ∃ i, P i z = 0)
    (hsep : ∀ᶠ z in 𝓝 (0 : Source 2),
      ∀ i j, i ≠ j → P i z = 0 → P j z = 0 → z = 0) :
    Nonempty (NormalizedPlaneCurveLinkFamily H ι) := by
  classical
  choose d hd K hK using fun i =>
    exists_normalized_smooth_zero_set_family_of_irreducible (P i) (hP i) (hirr i)
  have hsmall : ∀ᶠ c in 𝓝 (0 : ℝ), ∀ i, c < d i :=
    Filter.eventually_all.mpr fun i => Iio_mem_nhds (hd i)
  obtain ⟨a, ha, haall⟩ := Metric.mem_nhds_iff.mp hsmall
  have haeach (i : ι) : a / 2 < d i := by
    apply haall _ (i := i)
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos ha)]
    exact half_lt_self ha
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have he : Tendsto e (𝓝 (0 : EuclideanSpace ℂ (Fin 2))) (𝓝 0) := by
    simpa only [map_zero] using e.continuous.continuousAt.tendsto (x := 0)
  have hnear := he.eventually (hcover.and hsep)
  obtain ⟨r, hr, hrnear⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (a / 2) (r ^ 2)
  have hδ : 0 < δ := lt_min (half_pos ha) (sq_pos_of_pos hr)
  have hci (c : ℝ) (hc : c ∈ Ioo 0 δ) (i : ι) : c ∈ Ioo 0 (d i) :=
    ⟨hc.1, (hc.2.trans_le (min_le_left _ _)).trans (haeach i)⟩
  have hball (c : ℝ) (hc : c ∈ Ioo 0 δ)
      (y : EuclideanSpace ℂ (Fin 2)) (hy : y ∈ Metric.sphere 0 (Real.sqrt c)) :
      y ∈ Metric.ball 0 r := by
    have hsqrt : Real.sqrt c < r := by
      have hsq := Real.sq_sqrt hc.1.le
      have hlt := hc.2.trans_le (min_le_right (a / 2) (r ^ 2))
      nlinarith [Real.sqrt_nonneg c]
    simpa only [Metric.mem_ball, dist_zero_right,
      (show ‖y‖ = Real.sqrt c by simpa only [Metric.mem_sphere, dist_zero_right] using hy)]
      using hsqrt
  refine ⟨{
    radiusSq := δ
    radiusSq_pos := hδ
    component := K
    norm_eq_one := fun c hc i => (hK i c (hci c hc i)).1
    smooth := fun c hc i => (hK i c (hci c hc i)).2.1
    closedEmbedding := fun c hc i => (hK i c (hci c hc i)).2.2.1
    differential_injective := fun c hc i => (hK i c (hci c hc i)).2.2.2.1
    disjoint := ?_
    range_eq := ?_ }⟩
  · intro c hc i j hij
    rw [(hK i c (hci c hc i)).2.2.2.2, (hK j c (hci c hc j)).2.2.2.2]
    have hscale : Function.Injective
        (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) := by
      intro x y hxy
      have h := congrArg (fun z => Real.sqrt c • z) hxy
      simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc.1)), one_smul]
        using h
    rw [Set.disjoint_image_iff hscale]
    apply Set.disjoint_left.mpr
    intro y hi hj
    have hz : e y = 0 := (hrnear (hball c hc y hi.1)).2 i j hij hi.2 hj.2
    have hy0 : y = 0 := e.injective (hz.trans (map_zero e).symm)
    have hnorm : ‖y‖ = Real.sqrt c := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hi.1
    rw [hy0, norm_zero] at hnorm
    exact (ne_of_gt (Real.sqrt_pos.mpr hc.1)) hnorm.symm
  · intro c hc
    have heq : (⋃ i, Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt c) ∩
          {y | P i (e y) = 0}) =
        Metric.sphere 0 (Real.sqrt c) ∩ {y | H (e y) = 0} := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨i, hy, hi⟩
        exact ⟨hy, (hrnear (hball c hc y hy)).1.mpr ⟨i, hi⟩⟩
      · rintro ⟨hy, hHy⟩
        obtain ⟨i, hi⟩ := (hrnear (hball c hc y hy)).1.mp hHy
        exact ⟨i, hy, hi⟩
    calc
      (⋃ i, Set.range (fun u => K i (u, c))) =
          ⋃ i, (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ''
            (Metric.sphere 0 (Real.sqrt c) ∩ {y | P i (e y) = 0}) := by
        congr 1
        funext i
        exact (hK i c (hci c hc i)).2.2.2.2
      _ = (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ''
          (⋃ i, Metric.sphere 0 (Real.sqrt c) ∩ {y | P i (e y) = 0}) :=
        Set.image_iUnion.symm
      _ = _ := congrArg _ heq

/-- A reduced analytic plane equation constructs disjoint smooth branch
circles on one common radius interval, covering its entire sphere zero sets. -/
theorem exists_normalized_link_family_of_squarefree
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ s : Finset (Germ 2), Nonempty (NormalizedPlaneCurveLinkFamily H s) := by
  obtain ⟨s, P, hP, -, hirr, -, hcover, hsep⟩ :=
    exists_separated_branch_representatives_of_squarefree H hH hsq
  exact ⟨s, exists_normalized_link_family_of_separated_branches H P hP hirr hcover hsep⟩

end Germ

end OnLeConjecture.Analytic
