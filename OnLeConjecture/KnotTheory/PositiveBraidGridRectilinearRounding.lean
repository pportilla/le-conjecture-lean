/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinear
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Relative smooth rounding with a recovered parameter

Only the two scalar rise functions are approximated. Their linear progress is
retained exactly, so injectivity and nonzero velocity follow independently of
any derivative estimate on the approximations. The approximation equals the
polygon away from a prescribed neighborhood of its six corner parameters.
This local construction does not identify the global grid link.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

/-- The six parameter values at which either moving strand has a corner. -/
def positiveGridRectilinearCornerTimes : Set ℝ :=
  {1 / 6, 5 / 12, 7 / 12, 5 / 6, 1 / 4, 3 / 4}

theorem positiveGridRectilinearCornerTimes_isClosed :
    IsClosed positiveGridRectilinearCornerTimes := by
  have hfin : positiveGridRectilinearCornerTimes.Finite := by
    unfold positiveGridRectilinearCornerTimes
    simp
  exact hfin.isClosed

private theorem ramp_contDiffAt {h x : ℝ} (hh : 0 < h) (hx₀ : x ≠ 0) (hxh : x ≠ h) :
    ContDiffAt ℝ ∞ (positiveGridRectilinearRamp h) x := by
  rcases lt_or_gt_of_ne hx₀ with hx | hx
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact positiveGridRectilinearRamp_of_nonpos hy.le
  · rcases lt_or_gt_of_ne hxh with hxh | hxh
    · apply (contDiffAt_id : ContDiffAt ℝ ∞ (fun y : ℝ => y) x).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hx hxh] with y hy
      exact positiveGridRectilinearRamp_of_le hy.1.le hy.2.le
    · apply (contDiffAt_const (c := h)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hxh] with y hy
      exact positiveGridRectilinearRamp_of_ge hh.le hy.le

/-- The lower rise is smooth at every parameter other than the listed corners. -/
theorem positiveGridRectilinearLowerRise_contDiffAt {t : ℝ}
    (ht : t ∉ positiveGridRectilinearCornerTimes) :
    ContDiffAt ℝ ∞ positiveGridRectilinearLowerRise t := by
  simp only [positiveGridRectilinearCornerTimes, mem_insert_iff, mem_singleton_iff,
    not_or] at ht
  unfold positiveGridRectilinearLowerRise
  apply ContDiffAt.add
  · exact (ramp_contDiffAt (by norm_num : (0 : ℝ) < 1 / 2)
      (by intro h; exact ht.1 (by linarith))
      (by intro h; exact ht.2.1 (by linarith))).comp t
        ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)
  · exact (ramp_contDiffAt (by norm_num : (0 : ℝ) < 1 / 2)
      (by intro h; exact ht.2.2.1 (by linarith))
      (by intro h; exact ht.2.2.2.1 (by linarith))).comp t
        ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)

/-- The upper drop is smooth at every parameter other than the listed corners. -/
theorem positiveGridRectilinearUpperDrop_contDiffAt {t : ℝ}
    (ht : t ∉ positiveGridRectilinearCornerTimes) :
    ContDiffAt ℝ ∞ positiveGridRectilinearUpperDrop t := by
  simp only [positiveGridRectilinearCornerTimes, mem_insert_iff, mem_singleton_iff,
    not_or] at ht
  unfold positiveGridRectilinearUpperDrop
  exact (ramp_contDiffAt (by norm_num : (0 : ℝ) < 1)
    (by intro h; exact ht.2.2.2.2.1 (by linarith))
    (by intro h; exact ht.2.2.2.2.2 (by linarith))).comp t
      ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)

/-- Both rises admit arbitrarily close smooth replacements, with exact equality
outside any prescribed open neighborhood of the actual corners. -/
theorem exists_positiveGridRectilinear_smooth_rises {ε : ℝ} (hε : 0 < ε)
    {U : Set ℝ} (hU : IsOpen U) (hcorners : positiveGridRectilinearCornerTimes ⊆ U) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε) ∧
      (∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise Uᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop Uᶜ := by
  have hn : positiveGridRectilinearCornerTimesᶜ ∈ 𝓝ˢ Uᶜ :=
    positiveGridRectilinearCornerTimes_isClosed.isOpen_compl.mem_nhdsSet.mpr
      (compl_subset_compl.mpr hcorners)
  obtain ⟨l, hl, hla, hle, -⟩ :=
    positiveGridRectilinearLowerRise_continuous.exists_contDiff_approx_and_eqOn (⊤ : ℕ∞)
      continuous_const (fun _ => hε) hU.isClosed_compl hn
      (fun _ ht => (positiveGridRectilinearLowerRise_contDiffAt ht).contDiffWithinAt)
  obtain ⟨u, hu, hua, hue, -⟩ :=
    positiveGridRectilinearUpperDrop_continuous.exists_contDiff_approx_and_eqOn (⊤ : ℕ∞)
      continuous_const (fun _ => hε) hU.isClosed_compl hn
      (fun _ ht => (positiveGridRectilinearUpperDrop_contDiffAt ht).contDiffWithinAt)
  exact ⟨l, u, hl, hu, hla, hua, hle, hue⟩

/-- Smooth strictly increasing progress, agreeing with `t` before the crossing
and `t+1` after it. -/
def positiveGridRoundingProgress (t : ℝ) : ℝ := t + Real.smoothTransition t

theorem positiveGridRoundingProgress_contDiff : ContDiff ℝ ∞ positiveGridRoundingProgress :=
  contDiff_id.add Real.smoothTransition.contDiff

theorem positiveGridRoundingProgress_strictMono : StrictMono positiveGridRoundingProgress := by
  intro t u htu
  exact add_lt_add_of_lt_of_le htu (Real.smoothTransition.monotone htu.le)

theorem positiveGridRoundingProgress_deriv_pos (t : ℝ) :
    0 < deriv positiveGridRoundingProgress t := by
  have hd := (hasDerivAt_id t).add
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have he : deriv positiveGridRoundingProgress t = 1 + deriv Real.smoothTransition t := hd.deriv
  rw [he]
  linarith [Real.smoothTransition.monotone.deriv_nonneg (x := t)]

/-- The rise of each moving strand throughout the smooth deformation. -/
def positiveGridRoundingRise (f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (1 - s) * Real.smoothTransition t + s * f (positiveGridRoundingProgress t / 2)

/-- The local deformation preserves linear progress while replacing the two rises. -/
def positiveGridRoundedDeformation {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  if k = adjacentLower i then
    (positiveGridRoundingProgress t - positiveGridRoundingRise l s t,
      (((i.val : ℝ) + positiveGridRoundingRise l s t : ℝ) : ℂ) - Complex.I)
  else if k = adjacentUpper i then
    (positiveGridRoundingProgress t - positiveGridRoundingRise u s t,
      (((i.val : ℝ) + 1 - positiveGridRoundingRise u s t : ℝ) : ℂ) + Complex.I)
  else (t, (k.val : ℂ))

private theorem rounding_lower_ne_upper {m : ℕ} (i : Fin (m - 1)) :
    adjacentLower i ≠ adjacentUpper i := by
  intro h
  have he := congrArg Fin.val h
  change i.val = i.val + 1 at he
  omega

/-- Joint smoothness requires only the proved smoothness of the two scalar replacements. -/
theorem positiveGridRoundedDeformation_contDiff {m : ℕ} (i : Fin (m - 1))
    {l u : ℝ → ℝ} (hl : ContDiff ℝ ∞ l) (hu : ContDiff ℝ ∞ u) (k : Fin m) :
    ContDiff ℝ ∞ (fun st : ℝ × ℝ => positiveGridRoundedDeformation i l u k st.1 st.2) := by
  have hp : ContDiff ℝ ∞ (fun st : ℝ × ℝ => positiveGridRoundingProgress st.2) :=
    positiveGridRoundingProgress_contDiff.comp contDiff_snd
  have hr (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (fun st : ℝ × ℝ => positiveGridRoundingRise f st.1 st.2) :=
    ((contDiff_const.sub contDiff_fst).mul
      (Real.smoothTransition.contDiff.comp contDiff_snd)).add
        (contDiff_fst.mul (hf.comp (hp.div_const 2)))
  unfold positiveGridRoundedDeformation
  split_ifs
  · exact (hp.sub (hr l hl)).prodMk
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.add (hr l hl))).sub contDiff_const)
  · exact (hp.sub (hr u hu)).prodMk
      ((Complex.ofRealCLM.contDiff.comp ((contDiff_const.add contDiff_const).sub
        (hr u hu))).add contDiff_const)
  · exact contDiff_snd.prodMk contDiff_const

@[simp] theorem positiveGridRoundedDeformation_im {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (k : Fin m) (s t : ℝ) :
    (positiveGridRoundedDeformation i l u k s t).2.im = positiveGridRectilinearDepth i k := by
  unfold positiveGridRoundedDeformation positiveGridRectilinearDepth
  split_ifs <;> simp

/-- The lower linear coordinate recovers exactly the same strictly increasing progress. -/
theorem positiveGridRoundedDeformation_lower_progress {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (s t : ℝ) :
    (positiveGridRoundedDeformation i l u (adjacentLower i) s t).1 +
      (positiveGridRoundedDeformation i l u (adjacentLower i) s t).2.re - i.val =
        positiveGridRoundingProgress t := by
  simp [positiveGridRoundedDeformation]

/-- The upper linear coordinate recovers the same progress with the opposite row sign. -/
theorem positiveGridRoundedDeformation_upper_progress {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (s t : ℝ) :
    (positiveGridRoundedDeformation i l u (adjacentUpper i) s t).1 -
      (positiveGridRoundedDeformation i l u (adjacentUpper i) s t).2.re + (i.val + 1) =
        positiveGridRoundingProgress t := by
  simp only [positiveGridRoundedDeformation, if_neg (rounding_lower_ne_upper i).symm,
    ite_true, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
  ring

/-- All other strands stay fixed. -/
theorem positiveGridRoundedDeformation_fixed {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (k : Fin m) (hk₀ : k ≠ adjacentLower i) (hk₁ : k ≠ adjacentUpper i)
    (s t : ℝ) : positiveGridRoundedDeformation i l u k s t = (t, (k.val : ℂ)) := by
  simp [positiveGridRoundedDeformation, hk₀, hk₁]

/-- Constant depths distinguish the moving labels; fixed labels retain distinct real heights. -/
theorem positiveGridRoundedDeformation_label_eq {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (k k' : Fin m) (s t t' : ℝ)
    (he : positiveGridRoundedDeformation i l u k s t =
      positiveGridRoundedDeformation i l u k' s t') : k = k' := by
  have hd := congrArg (fun p : ℝ × ℂ => p.2.im) he
  simp only [positiveGridRoundedDeformation_im] at hd
  by_cases hk₀ : k = adjacentLower i
  · subst k
    exact ((positiveGridRectilinearDepth_eq_neg_one_iff i k').mp
      (hd.symm.trans (positiveGridRectilinearDepth_lower i))).symm
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    exact ((positiveGridRectilinearDepth_eq_one_iff i k').mp
      (hd.symm.trans (positiveGridRectilinearDepth_upper i))).symm
  have hk'₀ : k' ≠ adjacentLower i := by
    intro h
    exact hk₀ ((positiveGridRectilinearDepth_eq_neg_one_iff i k).mp (by simpa [h] using hd))
  have hk'₁ : k' ≠ adjacentUpper i := by
    intro h
    exact hk₁ ((positiveGridRectilinearDepth_eq_one_iff i k).mp (by simpa [h] using hd))
  rw [positiveGridRoundedDeformation_fixed i l u k hk₀ hk₁,
    positiveGridRoundedDeformation_fixed i l u k' hk'₀ hk'₁] at he
  exact Fin.ext (Nat.cast_injective (congrArg Prod.snd he))

/-- Every slice is injective for any replacements, since linear progress is retained exactly. -/
theorem positiveGridRoundedDeformation_injective {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (s : ℝ) :
    Function.Injective (fun p : Fin m × ℝ => positiveGridRoundedDeformation i l u p.1 s p.2) := by
  rintro ⟨k, t⟩ ⟨k', t'⟩ he
  have hkk := positiveGridRoundedDeformation_label_eq i l u k k' s t t' he
  subst k'
  suffices t = t' by simp [this]
  by_cases hk₀ : k = adjacentLower i
  · subst k
    apply positiveGridRoundingProgress_strictMono.injective
    simpa only [positiveGridRoundedDeformation_lower_progress] using
      congrArg (fun p : ℝ × ℂ => p.1 + p.2.re - i.val) he
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    apply positiveGridRoundingProgress_strictMono.injective
    simpa only [positiveGridRoundedDeformation_upper_progress] using
      congrArg (fun p : ℝ × ℂ => p.1 - p.2.re + (i.val + 1)) he
  simpa only [positiveGridRoundedDeformation_fixed i l u k hk₀ hk₁] using congrArg Prod.fst he

private theorem deriv_ne_zero_of_progress {F : ℝ → ℝ × ℂ}
    (hF : Differentiable ℝ F) (L : (ℝ × ℂ) →L[ℝ] ℝ) (c : ℝ)
    (h : ∀ t, L (F t) = positiveGridRoundingProgress t + c) (t : ℝ) : deriv F t ≠ 0 := by
  intro hz
  have hd := L.hasFDerivAt.comp_hasDerivAt t (hF t).hasDerivAt
  have hp : HasDerivAt positiveGridRoundingProgress 0 t := by
    simpa only [Function.comp_apply, h, add_sub_cancel_right, hz, map_zero] using hd.sub_const c
  have he := hp.deriv
  linarith [positiveGridRoundingProgress_deriv_pos t]

/-- Smooth replacements give nonzero velocity on every strand and at every deformation time. -/
theorem positiveGridRoundedDeformation_deriv_ne_zero {m : ℕ} (i : Fin (m - 1))
    {l u : ℝ → ℝ} (hl : ContDiff ℝ ∞ l) (hu : ContDiff ℝ ∞ u)
    (k : Fin m) (s t : ℝ) : deriv (positiveGridRoundedDeformation i l u k s) t ≠ 0 := by
  have hF : Differentiable ℝ (positiveGridRoundedDeformation i l u k s) :=
    ((positiveGridRoundedDeformation_contDiff i hl hu k).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  by_cases hk₀ : k = adjacentLower i
  · subst k
    apply deriv_ne_zero_of_progress hF
      (ContinuousLinearMap.fst ℝ ℝ ℂ + Complex.reCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℂ))
      (i.val : ℝ) _ t
    intro v
    have hp := positiveGridRoundedDeformation_lower_progress i l u s v
    change (positiveGridRoundedDeformation i l u (adjacentLower i) s v).1 +
      (positiveGridRoundedDeformation i l u (adjacentLower i) s v).2.re = _
    linarith
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    apply deriv_ne_zero_of_progress hF
      (ContinuousLinearMap.fst ℝ ℝ ℂ - Complex.reCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℂ))
      (-(i.val + 1) : ℝ) _ t
    intro v
    have hp := positiveGridRoundedDeformation_upper_progress i l u s v
    change (positiveGridRoundedDeformation i l u (adjacentUpper i) s v).1 -
      (positiveGridRoundedDeformation i l u (adjacentUpper i) s v).2.re = _
    linarith
  have he : positiveGridRoundedDeformation i l u k s = fun v => (v, (k.val : ℂ)) :=
    funext (positiveGridRoundedDeformation_fixed i l u k hk₀ hk₁ s)
  rw [he]
  have hd : HasDerivAt (fun v : ℝ => (v, (k.val : ℂ))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (k.val : ℂ))
  intro h
  have hh := congrArg Prod.fst (hd.deriv.symm.trans h)
  norm_num at hh

/-- The initial slice is exactly the already constructed smooth crossing at constant depths. -/
theorem positiveGridRoundedDeformation_zero {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (k : Fin m) (t : ℝ) :
    positiveGridRoundedDeformation i l u k 0 t =
      (t, positiveAdjacentHeight i (positiveGridRectilinearDepth i) k t) := by
  unfold positiveGridRoundedDeformation
  split_ifs with hk₀ hk₁
  · subst k
    simp [positiveGridRoundingRise, positiveGridRoundingProgress,
      positiveAdjacentHeight, positiveAdjacentReal_lower, positiveGridRectilinearDepth,
      Complex.ofReal_add, sub_eq_add_neg]
  · subst k
    simp [positiveGridRoundingRise, positiveGridRoundingProgress,
      positiveAdjacentHeight, positiveAdjacentReal_upper, positiveGridRectilinearDepth,
      (rounding_lower_ne_upper i).symm]
  · simp [positiveAdjacentHeight, positiveAdjacentReal_fixed i k hk₀ hk₁,
      positiveGridRectilinearDepth, hk₀, hk₁]

/-- Away from the chosen corner neighborhood, the rounded terminal slice is exactly
on the original polygon, with the explicit increasing reparametrization. -/
theorem positiveGridRoundedDeformation_one_eq_polygon {m : ℕ} (i : Fin (m - 1))
    {l u : ℝ → ℝ} {U : Set ℝ}
    (hl : EqOn l positiveGridRectilinearLowerRise Uᶜ)
    (hu : EqOn u positiveGridRectilinearUpperDrop Uᶜ)
    (k : Fin m) {t : ℝ} (ht : positiveGridRoundingProgress t / 2 ∉ U)
    (hk : k = adjacentLower i ∨ k = adjacentUpper i) :
    positiveGridRoundedDeformation i l u k 1 t =
      positiveGridRectilinear i k (positiveGridRoundingProgress t / 2) := by
  rcases hk with rfl | rfl
  · simp [positiveGridRoundedDeformation, positiveGridRoundingRise, hl ht,
      positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
      positiveGridRectilinearDepth, sub_eq_add_neg]
    ring
  · simp [positiveGridRoundedDeformation, positiveGridRoundingRise, hu ht,
      positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
      positiveGridRectilinearDepth, (rounding_lower_ne_upper i).symm]
    ring

/-- Restricting any smooth slice to the finite compact tangle gives a closed embedding. -/
theorem positiveGridRoundedDeformation_isClosedEmbedding {m : ℕ} (i : Fin (m - 1))
    {l u : ℝ → ℝ} (hl : ContDiff ℝ ∞ l) (hu : ContDiff ℝ ∞ u) (s : ℝ) :
    Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) 1 =>
      positiveGridRoundedDeformation i l u p.1 s p.2) := by
  have hc : Continuous (fun p : Fin m × Icc (0 : ℝ) 1 =>
      positiveGridRoundedDeformation i l u p.1 s p.2) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact ((positiveGridRoundedDeformation_contDiff i hl hu k).continuous.comp
      (continuous_const.prodMk continuous_subtype_val))
  apply hc.isClosedEmbedding
  intro p q hpq
  have he := positiveGridRoundedDeformation_injective i l u s
    (a₁ := (p.1, p.2.val)) (a₂ := (q.1, q.2.val)) hpq
  have hk : p.1 = q.1 := congrArg (fun z : Fin m × ℝ => z.1) he
  have ht : p.2.val = q.2.val := congrArg (fun z : Fin m × ℝ => z.2) he
  exact Prod.ext hk (Subtype.ext ht)

/-- A corner neighborhood contained in the crossing interval leaves the entire
initial and terminal straight portions unchanged throughout the deformation. -/
theorem positiveGridRoundedDeformation_outside {m : ℕ} (i : Fin (m - 1))
    {l u : ℝ → ℝ} {U : Set ℝ}
    (hl : EqOn l positiveGridRectilinearLowerRise Uᶜ)
    (hu : EqOn u positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    positiveGridRoundedDeformation i l u k s t =
      (t, positiveAdjacentHeight i (positiveGridRectilinearDepth i) k t) := by
  have hq : positiveGridRoundingProgress t / 2 ∉ U := by
    intro h
    have hh := hU h
    rcases ht with ht | ht
    · simp only [positiveGridRoundingProgress, Real.smoothTransition.zero_of_nonpos ht,
        add_zero] at hh
      linarith [hh.1]
    · simp only [positiveGridRoundingProgress, Real.smoothTransition.one_of_one_le ht] at hh
      linarith [hh.2]
  have hl' : l (positiveGridRoundingProgress t / 2) = Real.smoothTransition t := by
    rw [hl hq]
    rcases ht with ht | ht
    · rw [Real.smoothTransition.zero_of_nonpos ht]
      apply positiveGridRectilinearLowerRise_first
      simp only [positiveGridRoundingProgress, Real.smoothTransition.zero_of_nonpos ht, add_zero]
      linarith
    · rw [Real.smoothTransition.one_of_one_le ht]
      apply positiveGridRectilinearLowerRise_fifth
      simp only [positiveGridRoundingProgress, Real.smoothTransition.one_of_one_le ht]
      linarith
  have hu' : u (positiveGridRoundingProgress t / 2) = Real.smoothTransition t := by
    rw [hu hq]
    rcases ht with ht | ht
    · rw [Real.smoothTransition.zero_of_nonpos ht]
      apply positiveGridRectilinearUpperDrop_first
      simp only [positiveGridRoundingProgress, Real.smoothTransition.zero_of_nonpos ht, add_zero]
      linarith
    · rw [Real.smoothTransition.one_of_one_le ht]
      apply positiveGridRectilinearUpperDrop_third
      simp only [positiveGridRoundingProgress, Real.smoothTransition.one_of_one_le ht]
      linarith
  have he : positiveGridRoundedDeformation i l u k s t =
      positiveGridRoundedDeformation i l u k 0 t := by
    unfold positiveGridRoundedDeformation positiveGridRoundingRise
    split_ifs <;> simp only [hl', hu', sub_zero, one_mul, zero_mul, add_zero] <;>
      congr 1 <;> push_cast <;> ring
  exact he.trans (positiveGridRoundedDeformation_zero i l u k t)

/-- The smooth rounding and its deformation are obtained from the polygon itself.
No injectivity, regularity, or derivative bound is supplied as an assumption. -/
theorem exists_positiveGridRectilinear_regular_rounding {m : ℕ} (i : Fin (m - 1))
    {ε : ℝ} (hε : 0 < ε) {U : Set ℝ} (hU : IsOpen U)
    (hcorners : positiveGridRectilinearCornerTimes ⊆ U) (hU' : U ⊆ Ioo (0 : ℝ) 1) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε) ∧
      (∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise Uᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop Uᶜ ∧
      (∀ k, ContDiff ℝ ∞ (fun st : ℝ × ℝ =>
        positiveGridRoundedDeformation i l u k st.1 st.2)) ∧
      (∀ s, Function.Injective (fun p : Fin m × ℝ =>
        positiveGridRoundedDeformation i l u p.1 s p.2)) ∧
      (∀ k s t, deriv (positiveGridRoundedDeformation i l u k s) t ≠ 0) ∧
      (∀ s, Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) 1 =>
        positiveGridRoundedDeformation i l u p.1 s p.2)) ∧
      (∀ k s t, t ≤ 0 ∨ 1 ≤ t → positiveGridRoundedDeformation i l u k s t =
        (t, positiveAdjacentHeight i (positiveGridRectilinearDepth i) k t)) := by
  obtain ⟨l, u, hl, hu, hla, hua, hle, hue⟩ :=
    exists_positiveGridRectilinear_smooth_rises hε hU hcorners
  exact ⟨l, u, hl, hu, hla, hua, hle, hue,
    positiveGridRoundedDeformation_contDiff i hl hu,
    positiveGridRoundedDeformation_injective i l u,
    positiveGridRoundedDeformation_deriv_ne_zero i hl hu,
    positiveGridRoundedDeformation_isClosedEmbedding i hl hu,
    fun k s _ ht => positiveGridRoundedDeformation_outside i hle hue hU' k s ht⟩

end OnLeConjecture.KnotTheory
