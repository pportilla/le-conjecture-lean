/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveRadialSubmersion
public import OnLeConjecture.Analytic.SectionNearbyPoints
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Algebra.Module.Projective

/-!
# The actual Milnor fibre of a reduced plane curve

Let `H : Source 2 → ℂ` be analytic at the origin with `H 0 = 0` and squarefree
germ. Using the Euclidean norm on `ℂ²` through `EuclideanSpace.equiv`, the
Milnor fibre of radius `ε` over `s` is the actual set
`F_{ε,s} = {z : ‖z‖ ≤ ε, H z = s}`.

For every sufficiently small radius `ε` and every inner radius `0 < ε₁ ≤ ε`
there is `δ > 0` such that for `0 < |s| < δ`:
* the fibre of radius `ε₁` is nonempty, so the fibre of radius `ε` is
  nonempty;
* the fibre is compact;
* the real differential of `H` is surjective at every point of the fibre;
* at every point of the fibre with `ε₁ ≤ ‖z‖`, the real differential of
  `z ↦ (H z, ‖z‖²)` is surjective. In particular the fibre is transverse to
  every sphere of radius in `[ε₁, ε]`, including the boundary sphere.

The last statement follows from the joint radial submersion along the zero
set and a compactness argument, using that surjectivity of a continuous linear
map between finite-dimensional spaces is an open condition.
-/

@[expose] public noncomputable section

open Filter Metric Set Function
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The surjective continuous linear maps between finite-dimensional real
normed spaces form an open set. -/
theorem isOpen_setOf_surjective_continuousLinearMap {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    IsOpen {L : V →L[ℝ] W | Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L₀ hL₀
  obtain ⟨g, hg⟩ := (L₀ : V →ₗ[ℝ] W).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL₀)
  let R : W →L[ℝ] V := LinearMap.toContinuousLinearMap g
  let Φ : (V →L[ℝ] W) → (W →L[ℝ] W) := fun L => L.comp R
  have hΦ : Continuous Φ := (ContinuousLinearMap.compL ℝ W V W).flip R |>.continuous
  have hΦ0 : Φ L₀ = 1 := by
    ext w
    change L₀ (g w) = w
    exact LinearMap.congr_fun hg w
  have hunit : Φ L₀ ∈ {x : W →L[ℝ] W | IsUnit x} := by
    change IsUnit (Φ L₀)
    rw [hΦ0]
    exact isUnit_one
  have hmem : Φ ⁻¹' {x : W →L[ℝ] W | IsUnit x} ∈ 𝓝 L₀ :=
    hΦ.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)
  filter_upwards [hmem] with L hL
  intro w
  obtain ⟨u, hu⟩ := hL
  refine ⟨R ((↑u⁻¹ : W →L[ℝ] W) w), ?_⟩
  have h := congrArg (fun T : W →L[ℝ] W => T w) u.mul_inv
  change (↑u : W →L[ℝ] W) ((↑u⁻¹ : W →L[ℝ] W) w) = w at h
  rw [hu] at h
  exact h

/-- The equation on the Euclidean model of `ℂ²`. -/
def euclideanEquation (H : Source 2 → ℂ) (z : EuclideanSpace ℂ (Fin 2)) : ℂ :=
  H ((EuclideanSpace.equiv (Fin 2) ℂ) z)

/-- The equation together with the squared Euclidean norm. -/
def radialPair (H : Source 2 → ℂ) (z : EuclideanSpace ℂ (Fin 2)) : ℂ × ℝ :=
  (euclideanEquation H z, ‖z‖ ^ 2)

/-- The actual Milnor fibre `{z : ‖z‖ ≤ ε, H z = s}`. -/
def milnorFibre (H : Source 2 → ℂ) (ε : ℝ) (s : ℂ) : Set (EuclideanSpace ℂ (Fin 2)) :=
  {z | ‖z‖ ≤ ε ∧ euclideanEquation H z = s}

/-- The part of the Milnor fibre on the boundary sphere. -/
def milnorFibreBoundary (H : Source 2 → ℂ) (ε : ℝ) (s : ℂ) : Set (EuclideanSpace ℂ (Fin 2)) :=
  {z | ‖z‖ = ε ∧ euclideanEquation H z = s}

theorem milnorFibreBoundary_eq (H : Source 2 → ℂ) (ε : ℝ) (s : ℂ) :
    milnorFibreBoundary H ε s = milnorFibre H ε s ∩ sphere 0 ε := by
  ext z
  simp only [milnorFibreBoundary, milnorFibre, mem_inter_iff, mem_ofPred_eq,
    mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.le, h2⟩, h1⟩
  · rintro ⟨⟨-, h2⟩, h1⟩
    exact ⟨h1, h2⟩

theorem milnorFibre_mono (H : Source 2 → ℂ) {ε ε' : ℝ} (h : ε ≤ ε') (s : ℂ) :
    milnorFibre H ε s ⊆ milnorFibre H ε' s :=
  fun _ hz => ⟨hz.1.trans h, hz.2⟩

/-- Pulling back an eventual property along the Euclidean equivalence. -/
theorem eventually_euclidean_of_eventually {P : Source 2 → Prop}
    (h : ∀ᶠ z in 𝓝 (0 : Source 2), P z) :
    ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)), P ((EuclideanSpace.equiv (Fin 2) ℂ) z) := by
  have he : Tendsto (EuclideanSpace.equiv (Fin 2) ℂ) (𝓝 (0 : EuclideanSpace ℂ (Fin 2)))
      (𝓝 0) := by
    simpa only [map_zero] using
      (EuclideanSpace.equiv (Fin 2) ℂ).continuous.continuousAt.tendsto (x := 0)
  exact he.eventually h

theorem analyticAt_euclideanEquation {H : Source 2 → ℂ} {z : EuclideanSpace ℂ (Fin 2)}
    (hH : AnalyticAt ℂ H ((EuclideanSpace.equiv (Fin 2) ℂ) z)) :
    AnalyticAt ℂ (euclideanEquation H) z :=
  hH.comp ((EuclideanSpace.equiv (Fin 2) ℂ).analyticAt z)

theorem contDiffAt_radialPair {H : Source 2 → ℂ} {z : EuclideanSpace ℂ (Fin 2)}
    (hH : AnalyticAt ℂ (euclideanEquation H) z) :
    ContDiffAt ℝ ⊤ (radialPair H) z :=
  ((hH.restrictScalars (𝕜 := ℝ)).contDiffAt).prodMk (contDiff_norm_sq ℝ).contDiffAt

/-- Surjectivity of the real differential of the euclidean equation at
nonzero points near the origin. -/
theorem eventually_euclidean_fderiv_surjective (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)), z ≠ 0 →
      Surjective (fderiv ℝ (euclideanEquation H) z) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  filter_upwards [eventually_euclidean_of_eventually
      (eventually_real_fderiv_surjective_of_squarefree H hH hH0 hsq),
    eventually_euclidean_of_eventually hH.eventually_analyticAt] with z hz ha hzn
  have hez : e z ≠ 0 := fun h0 => hzn (e.injective (h0.trans (map_zero e).symm))
  have hHa : DifferentiableAt ℝ H (e z) := ha.differentiableAt.restrictScalars ℝ
  have hcomp : fderiv ℝ (euclideanEquation H) z =
      (fderiv ℝ H (e z)).comp (e.toContinuousLinearMap.restrictScalars ℝ) :=
    (hHa.hasFDerivAt.comp z (e.hasFDerivAt.restrictScalars ℝ)).fderiv
  rw [hcomp]
  exact (hz hez).comp e.surjective

/-- **Milnor radii.** For every sufficiently small radius `ε` and every inner
radius `0 < ε₁ ≤ ε` there is `δ > 0` such that for `0 < |s| < δ` the fibre of
radius `ε₁` over `s` is nonempty, the fibre of radius `ε` is compact, the
equation is a submersion along it, and the equation together with the
squared norm is a submersion at its points of norm at least `ε₁`. -/
theorem exists_milnorFibre_radii (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ ε₁, 0 < ε₁ → ε₁ ≤ ε → ∃ δ > 0, ∀ s : ℂ, s ≠ 0 →
      ‖s‖ < δ →
        (milnorFibre H ε₁ s).Nonempty ∧ IsCompact (milnorFibre H ε s) ∧
        (∀ z ∈ milnorFibre H ε s,
          AnalyticAt ℂ (euclideanEquation H) z ∧ Surjective (fderiv ℝ (euclideanEquation H) z)) ∧
        (∀ z ∈ milnorFibre H ε s, ε₁ ≤ ‖z‖ → Surjective (fderiv ℝ (radialPair H) z)) := by
  classical
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have hE0 : euclideanEquation H 0 = 0 := by
    simp [euclideanEquation, hH0]
  have hEan : AnalyticAt ℂ (euclideanEquation H) 0 :=
    analyticAt_euclideanEquation (by simpa using hH)
  -- the good neighbourhood of the origin
  have hgood : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)),
      AnalyticAt ℂ (euclideanEquation H) z ∧
      (z ≠ 0 → Surjective (fderiv ℝ (euclideanEquation H) z)) ∧
      (z ≠ 0 → euclideanEquation H z = 0 → Surjective (fderiv ℝ (radialPair H) z)) := by
    filter_upwards [eventually_euclidean_of_eventually hH.eventually_analyticAt,
      eventually_euclidean_fderiv_surjective H hH hH0 hsq,
      Germ.eventually_joint_radial_fderiv_surjective_of_squarefree H hH hH0 hsq]
      with z ha hs hj
    exact ⟨analyticAt_euclideanEquation ha, hs, hj⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨ρ / 2, half_pos hρ, fun ε hε hερ ε₁ hε₁ hε₁ε => ?_⟩
  have hball : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ ≤ ε →
      z ∈ ball (0 : EuclideanSpace ℂ (Fin 2)) ρ :=
    fun z hz => mem_ball_zero_iff.mpr (lt_of_le_of_lt (hz.trans hερ) (half_lt_self hρ))
  -- nonemptiness from the open mapping theorem
  have hopen : 𝓝 (euclideanEquation H 0) ≤ map (euclideanEquation H) (𝓝 0) := by
    rcases hEan.eventually_constant_or_nhds_le_map_nhds with hc | hc
    · exfalso
      apply hsq.ne_zero
      rw [hE0] at hc
      have hc' : ∀ᶠ w in 𝓝 (0 : Source 2), H w = 0 := by
        have hes : Tendsto e.symm (𝓝 (0 : Source 2)) (𝓝 0) := by
          simpa only [map_zero] using e.symm.continuous.continuousAt.tendsto (x := 0)
        filter_upwards [hes.eventually hc] with w hw
        change H (e (e.symm w)) = 0 at hw
        rwa [e.apply_symm_apply] at hw
      rw [show (0 : Germ 2) = ofFunction (fun _ => (0 : ℂ)) analyticAt_const from rfl]
      apply Subtype.ext
      exact Filter.Germ.coe_eq.mpr hc'
    · exact hc
  have himg : euclideanEquation H '' ball 0 ε₁ ∈ 𝓝 (0 : ℂ) := by
    rw [← hE0]
    exact hopen (image_mem_map (ball_mem_nhds 0 hε₁))
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhds_iff.mp himg
  -- continuity of the joint differential on the closed ball
  have hJcont : ContinuousOn (fun z => fderiv ℝ (radialPair H) z) (closedBall 0 ε) := by
    intro z hz
    have ha := (hρsub (hball z (mem_closedBall_zero_iff.mp hz))).1
    exact ((contDiffAt_radialPair ha).fderiv_right (m := 0) (by norm_num)).continuousAt
      |>.continuousWithinAt
  have hEcont : ContinuousOn (euclideanEquation H) (closedBall 0 ε) := fun z hz =>
    (hρsub (hball z (mem_closedBall_zero_iff.mp hz))).1.continuousAt.continuousWithinAt
  -- the compact set of non-transverse points in the annulus
  set K := closedBall (0 : EuclideanSpace ℂ (Fin 2)) ε ∩ {z | ε₁ ≤ ‖z‖} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 ε).inter_right (isClosed_le continuous_const continuous_norm)
  set Bad := K ∩ (fun z => fderiv ℝ (radialPair H) z) ⁻¹'
    {L : EuclideanSpace ℂ (Fin 2) →L[ℝ] ℂ × ℝ | ¬ Surjective L} with hBad
  have hBadc : IsCompact Bad := by
    apply hKc.of_isClosed_subset _ inter_subset_left
    exact (hJcont.mono inter_subset_left).preimage_isClosed_of_isClosed hKc.isClosed
      isOpen_setOf_surjective_continuousLinearMap.isClosed_compl
  have hBadne : ∀ z ∈ Bad, euclideanEquation H z ≠ 0 := by
    rintro z ⟨⟨hz, hz₁⟩, hzbad⟩ h0
    have hzn : z ≠ 0 := by
      rintro rfl
      simp only [mem_ofPred_eq, norm_zero] at hz₁
      linarith
    exact hzbad ((hρsub (hball z (mem_closedBall_zero_iff.mp hz))).2.2 hzn h0)
  obtain ⟨δ₂, hδ₂, hδ₂bad⟩ : ∃ δ₂ > 0, ∀ z ∈ Bad, δ₂ ≤ ‖euclideanEquation H z‖ := by
    rcases Bad.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact hz.elim⟩
    · obtain ⟨zm, hzm, hmin⟩ := hBadc.exists_isMinOn hne
        ((hEcont.mono (fun z hz => hz.1.1)).norm)
      exact ⟨‖euclideanEquation H zm‖, norm_pos_iff.mpr (hBadne zm hzm), fun z hz => hmin hz⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs0 hsδ => ⟨?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨z, hz, hzs⟩ := hδ₁sub (mem_ball_zero_iff.mpr (lt_of_lt_of_le hsδ (min_le_left _ _)))
    exact ⟨z, (mem_ball_zero_iff.mp hz).le, hzs⟩
  · have hclosed : IsClosed (milnorFibre H ε s) := by
      have h := hEcont.preimage_isClosed_of_isClosed isClosed_closedBall
        (isClosed_singleton (x := s))
      convert h using 1
      ext z
      simp [milnorFibre]
    exact (isCompact_closedBall 0 ε).of_isClosed_subset hclosed
      (fun z hz => mem_closedBall_zero_iff.mpr hz.1)
  · intro z hz
    have hzn : z ≠ 0 := by
      rintro rfl
      exact hs0 (hz.2.symm.trans hE0)
    obtain ⟨ha, hsurj, -⟩ := hρsub (hball z hz.1)
    exact ⟨ha, hsurj hzn⟩
  · intro z hz hz₁
    by_contra hns
    have hzBad : z ∈ Bad := ⟨⟨mem_closedBall_zero_iff.mpr hz.1, hz₁⟩, hns⟩
    have h1 := hδ₂bad z hzBad
    rw [hz.2] at h1
    linarith [min_le_right δ₁ δ₂]

/-- **Transversality near the link.** For every sufficiently small radius `ε`
and inner radius `0 < ε₁ ≤ ε`, the equation is analytic on the ball of radius
`2 ε₀`, and there is `c > 0` such that the equation together with the squared
norm is a submersion at every point of the closed annulus `ε₁ ≤ ‖z‖ ≤ ε` where
the equation has modulus less than `c`. -/
theorem exists_radial_transverse_neighbourhood (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, (∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ < 2 * ε₀ →
        AnalyticAt ℂ (euclideanEquation H) z ∧
        (z ≠ 0 → Surjective (fderiv ℝ (euclideanEquation H) z))) ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ ε₁, 0 < ε₁ → ε₁ ≤ ε → ∃ c > 0, ∀ z : EuclideanSpace ℂ (Fin 2),
        ε₁ ≤ ‖z‖ → ‖z‖ ≤ ε → ‖euclideanEquation H z‖ < c →
          Surjective (fderiv ℝ (radialPair H) z) := by
  classical
  have hgood : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)),
      AnalyticAt ℂ (euclideanEquation H) z ∧
      (z ≠ 0 → Surjective (fderiv ℝ (euclideanEquation H) z)) ∧
      (z ≠ 0 → euclideanEquation H z = 0 → Surjective (fderiv ℝ (radialPair H) z)) := by
    filter_upwards [eventually_euclidean_of_eventually hH.eventually_analyticAt,
      eventually_euclidean_fderiv_surjective H hH hH0 hsq,
      Germ.eventually_joint_radial_fderiv_surjective_of_squarefree H hH hH0 hsq]
      with z ha hs hj
    exact ⟨analyticAt_euclideanEquation ha, hs, hj⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨ρ / 2, half_pos hρ, fun z hz => ?_, fun ε hε hερ ε₁ hε₁ hε₁ε => ?_⟩
  · have hz' : z ∈ ball (0 : EuclideanSpace ℂ (Fin 2)) ρ :=
      mem_ball_zero_iff.mpr (by linarith)
    exact ⟨(hρsub hz').1, (hρsub hz').2.1⟩
  have hball : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ ≤ ε →
      z ∈ ball (0 : EuclideanSpace ℂ (Fin 2)) ρ :=
    fun z hz => mem_ball_zero_iff.mpr (lt_of_le_of_lt (hz.trans hερ) (half_lt_self hρ))
  have hJcont : ContinuousOn (fun z => fderiv ℝ (radialPair H) z) (closedBall 0 ε) := by
    intro z hz
    have ha := (hρsub (hball z (mem_closedBall_zero_iff.mp hz))).1
    exact ((contDiffAt_radialPair ha).fderiv_right (m := 0) (by norm_num)).continuousAt
      |>.continuousWithinAt
  have hEcont : ContinuousOn (euclideanEquation H) (closedBall 0 ε) := fun z hz =>
    (hρsub (hball z (mem_closedBall_zero_iff.mp hz))).1.continuousAt.continuousWithinAt
  set K := closedBall (0 : EuclideanSpace ℂ (Fin 2)) ε ∩ {z | ε₁ ≤ ‖z‖} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 ε).inter_right (isClosed_le continuous_const continuous_norm)
  set Bad := K ∩ (fun z => fderiv ℝ (radialPair H) z) ⁻¹'
    {L : EuclideanSpace ℂ (Fin 2) →L[ℝ] ℂ × ℝ | ¬ Surjective L} with hBad
  have hBadc : IsCompact Bad := by
    apply hKc.of_isClosed_subset _ inter_subset_left
    exact (hJcont.mono inter_subset_left).preimage_isClosed_of_isClosed hKc.isClosed
      isOpen_setOf_surjective_continuousLinearMap.isClosed_compl
  have hBadne : ∀ z ∈ Bad, euclideanEquation H z ≠ 0 := by
    rintro z ⟨⟨hz, hz₁⟩, hzbad⟩ h0
    have hzn : z ≠ 0 := by
      rintro rfl
      simp only [mem_ofPred_eq, norm_zero] at hz₁
      linarith
    exact hzbad ((hρsub (hball z (mem_closedBall_zero_iff.mp hz))).2.2 hzn h0)
  obtain ⟨δ₂, hδ₂, hδ₂bad⟩ : ∃ δ₂ > 0, ∀ z ∈ Bad, δ₂ ≤ ‖euclideanEquation H z‖ := by
    rcases Bad.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact hz.elim⟩
    · obtain ⟨zm, hzm, hmin⟩ := hBadc.exists_isMinOn hne
        ((hEcont.mono (fun z hz => hz.1.1)).norm)
      exact ⟨‖euclideanEquation H zm‖, norm_pos_iff.mpr (hBadne zm hzm), fun z hz => hmin hz⟩
  refine ⟨δ₂, hδ₂, fun z hz₁ hzε hzc => ?_⟩
  by_contra hns
  have hzBad : z ∈ Bad := ⟨⟨mem_closedBall_zero_iff.mpr hzε, hz₁⟩, hns⟩
  linarith [hδ₂bad z hzBad]

end OnLeConjecture.Analytic
