/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidEventModel

/-! # Separation between a braid event and its smooth word model

Distinct real clusters retain their projected order throughout the word model.
Within each cluster, the original imaginary coordinates remain separated near
the event and agree in order with the fixed model heights. A regular interval
before the event supplies the required order of the real clusters.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory

/-- An initial sorting permutation on a regular left interval becomes monotone
at its limiting event. Equal real coordinates at the event are allowed. -/
theorem strand_sortingPerm_monotone_at_event
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    {left θ : ℝ} (hlt : left < θ) (before : Equiv.Perm (Fin a))
    (hsort : StrictMono (fun j => (K (before j) left).re))
    (hreg : ∀ t ∈ Ico left θ, Function.Injective (fun k => (K k t).re)) :
    Monotone (fun j => (K (before j) θ).re) := by
  intro j k hjk
  have hs : Ico left θ ⊆ {t | (K (before j) t).re ≤ (K (before k) t).re} := by
    intro t ht
    have hsortt := strand_sortingPerm_on_regular_interval hcont
      (u := left) (v := t)
      (fun s hs => hreg s ⟨hs.1, hs.2.trans_lt ht.2⟩)
      (show left ∈ Icc left t from ⟨le_rfl, ht.1⟩)
      (show t ∈ Icc left t from ⟨ht.1, le_rfl⟩) hsort
    exact hsortt.monotone hjk
  have hc : IsClosed {t | (K (before j) t).re ≤ (K (before k) t).re} :=
    isClosed_le (Complex.continuous_re.comp (hcont _))
      (Complex.continuous_re.comp (hcont _))
  exact closure_minimal hs hc (by rw [closure_Ico hlt.ne]; exact ⟨hlt.le, le_rfl⟩)

/-- Coincident real coordinates of distinct event sheets have different imaginary heights. -/
theorem IsPositiveBraidEventWord.coincident_im_ne
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    {k l : Fin a} (hkl : k ≠ l) (hr : (K k θ).re = (K l θ).re) :
    (K k θ).im ≠ (K l θ).im := by
  have hn : after.symm k ≠ after.symm l := fun he => hkl (after.symm.injective he)
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hp := (h.2.2.1 (after.symm k) (after.symm l)).mpr
      ⟨hlt, by simpa only [Equiv.apply_symm_apply] using hr⟩
    have hh := h.2.2.2.1 _ _ hp
    simpa only [Equiv.apply_symm_apply] using hh.ne.symm
  · have hp := (h.2.2.1 (after.symm l) (after.symm k)).mpr
      ⟨hgt, by simpa only [Equiv.apply_symm_apply] using hr.symm⟩
    have hh := h.2.2.2.1 _ _ hp
    simpa only [Equiv.apply_symm_apply] using hh.ne

/-- A strict order between distinct real clusters is retained for all model times. -/
theorem IsPositiveBraidEventWord.model_lt_of_event_lt
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (horder : Monotone (fun j => (K (before j) θ).re))
    {k l : Fin a} (hkl : (K k θ).re < (K l θ).re) (τ : ℝ) :
    (planeBranchBraidEventModel K θ before w k τ).re <
      (planeBranchBraidEventModel K θ before w l τ).re := by
  have hn : k ≠ l := by rintro rfl; exact lt_irrefl _ hkl
  have hp : before.symm k < before.symm l := by
    by_contra hnot
    have hh := horder (le_of_not_gt hnot)
    simp only [Equiv.apply_symm_apply] at hh
    exact not_le_of_gt hkl hh
  have hzero : (planeBranchBraidEventModel K θ before w k 0).re <
      (planeBranchBraidEventModel K θ before w l 0).re := by
    simp only [planeBranchBraidEventModel_zero, Complex.add_re, Complex.natCast_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, zero_mul, sub_self, add_zero]
    exact_mod_cast hp
  have hc (q : Fin a) : Continuous (fun t => (planeBranchBraidEventModel K θ before w q t).re) :=
    Complex.continuous_re.comp (planeBranchBraidEventModel_contDiff K θ before w q).continuous
  apply (lt_iff_of_continuousOn_ne_on_preconnected isPreconnected_univ
    (hc k).continuousOn (hc l).continuousOn
    (fun t _ he => hkl.ne (h.model_coincidence_original hn he))
    (mem_univ 0) (mem_univ τ)).mp hzero

/-- Original and model real differences have the same strict sign for pairs
belonging to different real clusters at the event. -/
theorem IsPositiveBraidEventWord.model_real_product_pos
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (horder : Monotone (fun j => (K (before j) θ).re))
    {k l : Fin a} (hr : (K k θ).re ≠ (K l θ).re) (τ : ℝ) :
    0 < (K k θ - K l θ).re *
      (planeBranchBraidEventModel K θ before w k τ -
        planeBranchBraidEventModel K θ before w l τ).re := by
  simp only [Complex.sub_re]
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt)
      (sub_neg.mpr (h.model_lt_of_event_lt horder hlt τ))
  · exact mul_pos (sub_pos.mpr hgt)
      (sub_pos.mpr (h.model_lt_of_event_lt horder hgt τ))

/-- One neighborhood of the event separates every pair from every model time
in either the real or imaginary coordinate. The model time is unrestricted. -/
theorem IsPositiveBraidEventWord.exists_radius_model_separation
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (hcont : ∀ k, ContinuousAt (K k) θ)
    (horder : Monotone (fun j => (K (before j) θ).re)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ ball θ ρ, ∀ τ : ℝ, ∀ k l : Fin a, k ≠ l →
      0 < (K k s - K l s).re *
          (planeBranchBraidEventModel K θ before w k τ -
            planeBranchBraidEventModel K θ before w l τ).re ∨
        0 < (K k s - K l s).im *
          (planeBranchBraidEventModel K θ before w k τ -
            planeBranchBraidEventModel K θ before w l τ).im := by
  have hp (k l : Fin a) : ∀ᶠ s in 𝓝 θ, ∀ τ : ℝ, k ≠ l →
      0 < (K k s - K l s).re *
          (planeBranchBraidEventModel K θ before w k τ -
            planeBranchBraidEventModel K θ before w l τ).re ∨
        0 < (K k s - K l s).im *
          (planeBranchBraidEventModel K θ before w k τ -
            planeBranchBraidEventModel K θ before w l τ).im := by
    by_cases hkl : k = l
    · exact Filter.Eventually.of_forall fun _ _ hn => (hn hkl).elim
    by_cases hr : (K k θ).re = (K l θ).re
    · have hn : (K k θ - K l θ).im ≠ 0 := by
        simpa only [Complex.sub_im, sub_ne_zero] using h.coincident_im_ne hkl hr
      have hc : ContinuousAt (fun s => (K k s - K l s).im * (K k θ - K l θ).im) θ :=
        (Complex.continuous_im.continuousAt.comp ((hcont k).sub (hcont l))).mul_const _
      have he := continuousAt_const.eventually_lt hc (mul_self_pos.mpr hn)
      filter_upwards [he] with s hs τ _
      right
      simpa only [Complex.sub_im, planeBranchBraidEventModel_im] using hs
    · have hn : (K k θ - K l θ).re ≠ 0 := by
        simpa only [Complex.sub_re, sub_ne_zero] using hr
      have hc : ContinuousAt (fun s => (K k s - K l s).re * (K k θ - K l θ).re) θ :=
        (Complex.continuous_re.continuousAt.comp ((hcont k).sub (hcont l))).mul_const _
      have he := continuousAt_const.eventually_lt hc (mul_self_pos.mpr hn)
      filter_upwards [he] with s hs τ _
      left
      have hm := h.model_real_product_pos horder hr τ
      rcases mul_pos_iff.mp hs with hs | hs <;> rcases mul_pos_iff.mp hm with hm | hm
      · exact mul_pos hs.1 hm.2
      · exact (not_lt_of_gt hs.2 hm.1).elim
      · exact (not_lt_of_gt hm.1 hs.2).elim
      · exact mul_pos_of_neg_of_neg hs.1 hm.2
  have hall := Filter.eventually_all.mpr fun k => Filter.eventually_all.mpr (hp k)
  obtain ⟨ρ, hρ, hρspec⟩ := Metric.eventually_nhds_iff.mp hall
  exact ⟨ρ, hρ, fun s hs τ k l hkl => hρspec hs k l τ hkl⟩

/-- The data of an actual isolated event block supplies the real-cluster order
and hence the uniform separation from its model. No order or separation
hypothesis is added to the block data. -/
theorem exists_radius_braid_event_block_model_separation
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    (E : Finset ℝ) {b d left θ right : ℝ}
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re)
    (hbl : b ≤ left) (hlθ : left < θ) (hθr : θ < right) (hrd : right ≤ d)
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (hsort : StrictMono (fun j => (K (before j) left).re))
    (hisolate : ∀ t ∈ Icc left right, t ∈ E ↔ t = θ)
    (hevent : IsPositiveBraidEventWord K θ before after w) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ ball θ ρ, ∀ τ : ℝ, ∀ k l : Fin a, k ≠ l →
      0 < (K k s - K l s).re *
          (planeBranchBraidEventModel K θ before w k τ -
            planeBranchBraidEventModel K θ before w l τ).re ∨
        0 < (K k s - K l s).im *
          (planeBranchBraidEventModel K θ before w k τ -
            planeBranchBraidEventModel K θ before w l τ).im := by
  have hreg : ∀ t ∈ Ico left θ, Function.Injective (fun k => (K k t).re) := by
    intro t ht k l he
    by_contra hkl
    have htE := (hE t).mpr
      ⟨⟨hbl.trans ht.1, ht.2.le.trans (hθr.le.trans hrd)⟩, k, l, hkl, he⟩
    have htθ := (hisolate t ⟨ht.1, ht.2.le.trans hθr.le⟩).mp htE
    exact ht.2.ne htθ
  exact hevent.exists_radius_model_separation (fun k => (hcont k).continuousAt)
    (strand_sortingPerm_monotone_at_event hcont hlθ before hsort hreg)

end OnLeConjecture.Analytic
