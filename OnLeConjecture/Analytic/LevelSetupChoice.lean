/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupConnected

/-!
# Compactness choices for a fixed projection

Fix a radius `R`, a base coordinate `h` and a fibre coordinate `ζ` of the target. Write
`v = H₀`, `φ = h ∘ H` and `F = (v, φ)`. Suppose that `H` is analytic on `B̄_R`, that the origin is
the only common zero of `v` and `φ` on `B̄_R`, that the central curve `v = 0` is unramified over
`φ ≠ 0` in `B_R`, and that its points on the sphere `∂B_R` lie over `|φ| ≥ δ`. The compactness of
`B̄_R` gives the following radii, all independent of the later choice of the level.

* `exists_sphere_margin`: a margin `μ > 0` with `max (|v|, |φ|) ≥ μ` on the sphere `∂B_R`.
* `exists_annulus_regular`: for `0 < ρ₁ ≤ ρ₂ < δ`, a radius `ε > 0` of levels such that `F` has
  injective differential at the points of `B_R` with `|v| < ε` and `ρ₁ ≤ |φ| ≤ ρ₂`.
* `exists_separation`: for a compact set `T` of pairs (level, base value) over which `F` is proper
  and unramified, a uniform positive lower bound `κ` for the distance between the `ζ`-coordinates
  of distinct points of each fibre.
* `exists_small_roots`: for every `κ > 0`, a radius `m > 0` such that every point of `B̄_R` with
  `|v| < m` and `|φ| < m` has `|ζ ∘ H| < κ / 2`.

These are the choices "`η = min_{∂B_R} max(|v|, |h₀|) > 0`" and "Properness and a
convergent-subsequence argument therefore allow `ε₀` to be decreased so that this invertibility
holds on the annulus for all `|v| ≤ ε₀`" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`), together with the two quantitative inputs of the
connectedness argument of `LevelSetupConnected.lean`.
-/

@[expose] public noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

variable (A : ResolutionSectionAssembly g hd hi) {R : ℝ} {h : Source 3 →L[ℂ] ℂ}

theorem continuousOn_levelFunctions
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x) :
    ContinuousOn (fun x => A.H x 0) (closedBall (0 : Source 2) R) ∧
      ContinuousOn (fun x => h (A.H x)) (closedBall (0 : Source 2) R) := by
  have hH : ContinuousOn A.H (closedBall (0 : Source 2) R) := fun x hx =>
    (han x hx).continuousAt.continuousWithinAt
  exact ⟨(continuous_apply 0).comp_continuousOn hH, h.continuous.comp_continuousOn hH⟩

/-- **The margin on the sphere.** -/
theorem exists_sphere_margin (hR : 0 < R)
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x)
    (hiso : ∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 → h (A.H x) = 0 → x = 0) :
    ∃ μ > 0, ∀ x : Source 2, ‖x‖ = R → μ ≤ max ‖A.H x 0‖ ‖h (A.H x)‖ := by
  obtain ⟨hv, hφ⟩ := continuousOn_levelFunctions A (h := h) han
  have hS : IsCompact (sphere (0 : Source 2) R) := isCompact_sphere 0 R
  have hSsub : sphere (0 : Source 2) R ⊆ closedBall 0 R := sphere_subset_closedBall
  have hne : (sphere (0 : Source 2) R).Nonempty := by
    refine ⟨fun _ => (R : ℂ), ?_⟩
    rw [mem_sphere_zero_iff_norm]
    have : ‖(fun _ : Fin 2 => (R : ℂ))‖ = ‖(R : ℂ)‖ := by
      simp [pi_norm_const]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hf : ContinuousOn (fun x => max ‖A.H x 0‖ ‖h (A.H x)‖) (sphere (0 : Source 2) R) :=
    (ContinuousOn.sup' (continuous_norm.comp_continuousOn hv)
      (continuous_norm.comp_continuousOn hφ)).mono hSsub
  obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hf
  refine ⟨max ‖A.H x₀ 0‖ ‖h (A.H x₀)‖, ?_, fun x hx => hmin (mem_sphere_zero_iff_norm.mpr hx)⟩
  by_contra hle
  push Not at hle
  have h1 : ‖A.H x₀ 0‖ = 0 := le_antisymm ((le_max_left _ _).trans hle) (norm_nonneg _)
  have h2 : ‖h (A.H x₀)‖ = 0 := le_antisymm ((le_max_right _ _).trans hle) (norm_nonneg _)
  have h0 := hiso x₀ (hSsub hx₀) (norm_eq_zero.mp h1) (norm_eq_zero.mp h2)
  have := mem_sphere_zero_iff_norm.mp hx₀
  rw [h0, norm_zero] at this
  exact hR.ne this

/-- **Unramified annuli over all nearby levels.** -/
theorem exists_annulus_regular
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x) {δ : ℝ}
    (hbd : ∀ x : Source 2, ‖x‖ = R → A.H x 0 = 0 → δ ≤ ‖h (A.H x)‖)
    (hunr : ∀ x ∈ ball (0 : Source 2) R, A.H x 0 = 0 → h (A.H x) ≠ 0 →
      Injective (fderiv ℂ (levelBaseMap A h) x))
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : ρ₂ < δ) :
    ∃ ε > 0, ∀ x ∈ ball (0 : Source 2) R, ‖A.H x 0‖ < ε → ρ₁ ≤ ‖h (A.H x)‖ →
      ‖h (A.H x)‖ ≤ ρ₂ → Injective (fderiv ℂ (levelBaseMap A h) x) := by
  obtain ⟨hv, hφ⟩ := continuousOn_levelFunctions A (h := h) han
  set K : Set (Source 2) := closedBall (0 : Source 2) R ∩
    (fun x => ‖h (A.H x)‖) ⁻¹' Icc ρ₁ ρ₂ with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall (0 : Source 2) R).of_isClosed_subset
      ((continuous_norm.comp_continuousOn hφ).preimage_isClosed_of_isClosed isClosed_closedBall
        isClosed_Icc) inter_subset_left
  set I : Set (Source 2) :=
    {x | x ∈ ball (0 : Source 2) R ∧ Injective (fderiv ℂ (levelBaseMap A h) x)} with hIdef
  have hIo : IsOpen I := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hx, hxinj⟩
    have hHx : AnalyticAt ℂ A.H x := han x (ball_subset_closedBall hx)
    filter_upwards [isOpen_ball.mem_nhds hx,
      eventually_injective_fderiv (levelBaseMap_analyticAt A h hHx) hxinj] with y hy hyinj
    exact ⟨hy, hyinj⟩
  set Bad := K \ I with hBad
  have hBc : IsCompact Bad := hKc.diff hIo
  have hBv : ∀ x ∈ Bad, A.H x 0 ≠ 0 := by
    rintro x ⟨⟨hxB, hxφ⟩, hxI⟩ hx0
    rcases (mem_closedBall_zero_iff.mp hxB).lt_or_eq with hlt | heq
    · have hx : x ∈ ball (0 : Source 2) R := mem_ball_zero_iff.mpr hlt
      have hne : h (A.H x) ≠ 0 := fun h0 => by
        have h1 : ρ₁ ≤ ‖h (A.H x)‖ := hxφ.1
        rw [h0, norm_zero] at h1
        linarith
      exact hxI ⟨hx, hunr x hx hx0 hne⟩
    · have h1 := hbd x heq hx0
      linarith [hxφ.2]
  rcases Bad.eq_empty_or_nonempty with hBe | hBne
  · refine ⟨1, one_pos, fun x hx _ h1 h2 => ?_⟩
    by_contra hni
    have : x ∈ Bad := ⟨⟨ball_subset_closedBall hx, h1, h2⟩, fun hI => hni hI.2⟩
    rw [hBe] at this
    exact this
  · obtain ⟨x₀, hx₀, hmin⟩ := hBc.exists_isMinOn hBne
      ((continuous_norm.comp_continuousOn hv).mono fun x hx => hx.1.1)
    refine ⟨‖A.H x₀ 0‖, norm_pos_iff.mpr (hBv x₀ hx₀), fun x hx hxv h1 h2 => ?_⟩
    by_contra hni
    have hxB : x ∈ Bad := ⟨⟨ball_subset_closedBall hx, h1, h2⟩, fun hI => hni hI.2⟩
    exact absurd (hmin hxB) (not_le.mpr hxv)

/-- **Uniform separation of the roots** over a compact set of pairs (level, base value) over
which `F` is proper and unramified. -/
theorem exists_separation {ζ : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, h y, ζ y))
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x)
    (hinj : InjOn A.H (ball (0 : Source 2) R)) {T : Set (ℂ × ℂ)} (hT : IsCompact T)
    (hprop : ∀ p ∈ T, ∀ x ∈ closedBall (0 : Source 2) R, levelBaseMap A h x = p →
      x ∈ ball (0 : Source 2) R)
    (hreg : ∀ p ∈ T, ∀ x ∈ ball (0 : Source 2) R, levelBaseMap A h x = p →
      Injective (fderiv ℂ (levelBaseMap A h) x)) :
    ∃ κ > 0, ∀ p ∈ T, ∀ x ∈ ball (0 : Source 2) R, ∀ y ∈ ball (0 : Source 2) R,
      levelBaseMap A h x = p → levelBaseMap A h y = p → x ≠ y →
      κ ≤ ‖ζ (A.H x) - ζ (A.H y)‖ := by
  classical
  have hcont := continuousOn_levelBaseMap A h han
  -- the local separation at each pair
  have hloc : ∀ p ∈ T, ∃ κ > 0, ∀ᶠ q in 𝓝 p, ∀ x ∈ ball (0 : Source 2) R,
      ∀ y ∈ ball (0 : Source 2) R, levelBaseMap A h x = q → levelBaseMap A h y = q → x ≠ y →
        κ ≤ ‖ζ (A.H x) - ζ (A.H y)‖ := by
    intro p hp
    have hreg' : ∀ x ∈ ball (0 : Source 2) R, levelBaseMap A h x = p →
        ∃ f' : Source 2 ≃L[ℂ] ℂ × ℂ,
          HasStrictFDerivAt (levelBaseMap A h) (f' : Source 2 →L[ℂ] ℂ × ℂ) x := by
      intro x hx hxp
      obtain ⟨e, -, he⟩ := exists_hasStrictFDerivAt_equiv
        (levelBaseMap_analyticAt A h (han x (ball_subset_closedBall hx))) (hreg p hp x hx hxp)
      exact ⟨e, he⟩
    obtain ⟨Z, hZ, r, hr, G, hG0, hG⟩ := exists_localLabels (isCompact_closedBall 0 R)
      isOpen_ball ball_subset_closedBall hcont (hprop p hp) hreg'
    -- the minimal distance at `p`
    have hdist : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → ζ (A.H z) ≠ ζ (A.H w) := by
      intro z hz w hw hzw heq
      obtain ⟨hzB, hzp⟩ := (hZ z).mp hz
      obtain ⟨hwB, hwp⟩ := (hZ w).mp hw
      apply hzw
      apply hinj hzB hwB
      apply hcoord
      have h1 := congrArg Prod.fst (hzp.trans hwp.symm)
      have h2 := congrArg Prod.snd (hzp.trans hwp.symm)
      simp only [levelBaseMap] at h1 h2
      simp only [h1, h2, heq]
    obtain ⟨d, hd, hdle⟩ : ∃ d > 0, ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → d ≤ ‖ζ (A.H z) - ζ (A.H w)‖ := by
      set T := (Z ×ˢ Z).filter (fun q => q.1 ≠ q.2) with hT
      rcases T.eq_empty_or_nonempty with hTe | hTne
      · refine ⟨1, one_pos, fun z hz w hw hzw => ?_⟩
        have : (z, w) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hw⟩, hzw⟩
        rw [hTe] at this
        exact absurd this (Finset.notMem_empty _)
      · obtain ⟨q, hq, hqmin⟩ := T.exists_min_image (fun q => ‖ζ (A.H q.1) - ζ (A.H q.2)‖) hTne
        obtain ⟨hq12, hqne⟩ := Finset.mem_filter.mp hq
        obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq12
        refine ⟨‖ζ (A.H q.1) - ζ (A.H q.2)‖, norm_pos_iff.mpr (sub_ne_zero.mpr
          (hdist _ hq1 _ hq2 hqne)), fun z hz w hw hzw => ?_⟩
        exact hqmin (z, w) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hw⟩, hzw⟩)
    -- the labels move little near `p`
    have hnear : ∀ z ∈ Z, ∀ᶠ q in 𝓝 p, ‖ζ (A.H (G z q)) - ζ (A.H z)‖ < d / 4 := by
      intro z hz
      obtain ⟨h1, h2, -⟩ := hG0 z hz
      have hc : ContinuousAt (fun q => ζ (A.H (G z q))) p := by
        have hHz : ContinuousAt A.H (G z p) := by
          rw [h1]
          exact (han z (ball_subset_closedBall ((hZ z).mp hz).1)).continuousAt
        exact ζ.continuous.continuousAt.comp (hHz.comp (h2.continuousAt (ball_mem_nhds p hr)))
      have hball : ball (ζ (A.H (G z p))) (d / 4) ∈ 𝓝 (ζ (A.H (G z p))) :=
        ball_mem_nhds _ (by positivity)
      filter_upwards [hc.preimage_mem_nhds hball] with q hq
      rw [h1] at hq
      rw [mem_preimage, mem_ball, dist_eq_norm] at hq
      exact hq
    refine ⟨d / 2, by positivity, ?_⟩
    filter_upwards [(Filter.eventually_all_finset Z).mpr hnear, ball_mem_nhds p hr]
      with q hq hqr x hx y hy hxq hyq hxy
    obtain ⟨-, hsurj, -⟩ := hG q hqr
    obtain ⟨z, hz, rfl⟩ := hsurj x (ball_subset_closedBall hx) hxq
    obtain ⟨w, hw, rfl⟩ := hsurj y (ball_subset_closedBall hy) hyq
    have hzw : z ≠ w := fun h' => hxy (by rw [h'])
    have h1 := hdle z hz w hw hzw
    have h2 := hq z hz
    have h3 := hq w hw
    have htri : ‖ζ (A.H z) - ζ (A.H w)‖ ≤ ‖ζ (A.H (G z q)) - ζ (A.H (G w q))‖ +
        ‖ζ (A.H (G z q)) - ζ (A.H z)‖ + ‖ζ (A.H (G w q)) - ζ (A.H w)‖ := by
      have e : ζ (A.H z) - ζ (A.H w) = (ζ (A.H (G z q)) - ζ (A.H (G w q))) -
          (ζ (A.H (G z q)) - ζ (A.H z)) + (ζ (A.H (G w q)) - ζ (A.H w)) := by ring
      set a₁ := ζ (A.H (G z q)) - ζ (A.H (G w q))
      set a₂ := ζ (A.H (G z q)) - ζ (A.H z)
      set a₃ := ζ (A.H (G w q)) - ζ (A.H w)
      rw [e]
      calc ‖a₁ - a₂ + a₃‖ ≤ ‖a₁ - a₂‖ + ‖a₃‖ := norm_add_le _ _
        _ ≤ ‖a₁‖ + ‖a₂‖ + ‖a₃‖ := by gcongr; exact norm_sub_le _ _
    linarith
  -- a finite subcover
  choose! κf hκf hκev using hloc
  obtain ⟨t, htT, hcover⟩ := hT.elim_nhds_subcover (fun p => {q | ∀ x ∈ ball (0 : Source 2) R,
      ∀ y ∈ ball (0 : Source 2) R, levelBaseMap A h x = q → levelBaseMap A h y = q → x ≠ y →
        κf p ≤ ‖ζ (A.H x) - ζ (A.H y)‖}) (fun p hp => hκev p hp)
  obtain ⟨κ, hκ, hκle⟩ : ∃ κ > 0, ∀ p ∈ t, κ ≤ κf p := by
    rcases t.eq_empty_or_nonempty with hte | htne
    · exact ⟨1, one_pos, fun p hp => by rw [hte] at hp; exact absurd hp (Finset.notMem_empty _)⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := t.exists_min_image κf htne
      exact ⟨κf p₀, hκf p₀ (htT p₀ hp₀), hmin⟩
  refine ⟨κ, hκ, fun p hp x hx y hy hxp hyp hxy => ?_⟩
  obtain ⟨p₀, hp₀, hpU⟩ := mem_iUnion₂.mp (hcover hp)
  exact (hκle p₀ hp₀).trans (hpU x hx y hy hxp hyp hxy)

/-- **Small roots near the origin.** -/
theorem exists_small_roots {ζ : Source 3 →L[ℂ] ℂ}
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x)
    (hiso : ∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 → h (A.H x) = 0 → x = 0)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ m > 0, ∀ x ∈ closedBall (0 : Source 2) R, ‖A.H x 0‖ < m → ‖h (A.H x)‖ < m →
      ‖ζ (A.H x)‖ < κ / 2 := by
  obtain ⟨hv, hφ⟩ := continuousOn_levelFunctions A (h := h) han
  have hH : ContinuousOn A.H (closedBall (0 : Source 2) R) := fun x hx =>
    (han x hx).continuousAt.continuousWithinAt
  have hζ : ContinuousOn (fun x => ‖ζ (A.H x)‖) (closedBall (0 : Source 2) R) :=
    continuous_norm.comp_continuousOn (ζ.continuous.comp_continuousOn hH)
  set K := closedBall (0 : Source 2) R ∩ (fun x => ‖ζ (A.H x)‖) ⁻¹' Ici (κ / 2) with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (0 : Source 2) R).of_isClosed_subset
    (hζ.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Ici) inter_subset_left
  have hpos : ∀ x ∈ K, 0 < max ‖A.H x 0‖ ‖h (A.H x)‖ := by
    rintro x ⟨hxB, hxζ⟩
    by_contra hle
    push Not at hle
    have h1 : A.H x 0 = 0 :=
      norm_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hle) (norm_nonneg _))
    have h2 : h (A.H x) = 0 :=
      norm_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hle) (norm_nonneg _))
    have h0 := hiso x hxB h1 h2
    have hx' : ‖ζ (A.H x)‖ ≥ κ / 2 := hxζ
    rw [h0, A.H_zero, map_zero, norm_zero] at hx'
    linarith
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun x hx _ _ => ?_⟩
    by_contra hle
    push Not at hle
    have : x ∈ K := ⟨hx, hle⟩
    rw [hKe] at this
    exact this
  · obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hKne
      ((ContinuousOn.sup' (continuous_norm.comp_continuousOn hv)
      (continuous_norm.comp_continuousOn hφ)).mono
        inter_subset_left)
    refine ⟨max ‖A.H x₀ 0‖ ‖h (A.H x₀)‖, hpos x₀ hx₀, fun x hx h1 h2 => ?_⟩
    by_contra hle
    push Not at hle
    have hm := hmin (show x ∈ K from ⟨hx, hle⟩)
    simp only [mem_ofPred_eq] at hm
    exact absurd hm (not_le.mpr (max_lt h1 h2))

end OnLeConjecture.Analytic
