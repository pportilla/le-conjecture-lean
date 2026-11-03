/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCrossingOrder
public import OnLeConjecture.Analytic.PlaneBranchBraidChambers
public import OnLeConjecture.KnotTheory.PositivePermutationWords
public import OnLeConjecture.KnotTheory.PositiveWordSequence

/-! # Positive words assigned to projected braid events

Each word retains the event time and the two sorting permutations. Its
crossed pairs are the coincident pairs at that event, expressed in final
position labels. No geometric realization of the word is asserted.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory

/-- Positive transverse pair crossings are isolated simultaneously for a finite set of strands. -/
theorem eventually_strand_projection_injective_off_event
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    (hcont : ∀ k, ContinuousAt (K k) θ)
    (hpos : ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im) :
    ∀ᶠ t in 𝓝 θ, t ≠ θ → Function.Injective (fun k => (K k t).re) := by
  have hpair (k l : Fin a) : ∀ᶠ t in 𝓝 θ,
      t ≠ θ → k ≠ l → (K k t).re ≠ (K l t).re := by
    by_cases hkl : k = l
    · exact Filter.Eventually.of_forall fun _ _ h => (h hkl).elim
    by_cases hz : (K k θ).re = (K l θ).re
    · have hd : deriv (fun t => (K k t - K l t).re) θ ≠ 0 := by
        intro hd
        have h := hpos k l hkl hz
        simp only [hd, neg_zero, zero_mul, lt_self_iff_false] at h
      have hh := (differentiableAt_of_deriv_ne_zero hd).hasDerivAt.eventually_ne hd (c := 0)
      have hh' : ∀ᶠ t in 𝓝 θ, t ≠ θ → (K k t - K l t).re ≠ 0 := by
        simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hh
      filter_upwards [hh'] with t ht hne _
      simpa only [Complex.sub_re, sub_ne_zero] using ht hne
    · have hc : ContinuousAt (fun t => (K k t - K l t).re) θ :=
        Complex.continuous_re.continuousAt.comp ((hcont k).sub (hcont l))
      have hh := hc.eventually_ne (show (K k θ - K l θ).re ≠ 0 by
        simpa only [Complex.sub_re, sub_ne_zero] using hz)
      filter_upwards [hh] with t ht _ _
      simpa only [Complex.sub_re, sub_ne_zero] using ht
  have hall := Filter.eventually_all.mpr fun k => Filter.eventually_all.mpr (hpair k)
  filter_upwards [hall] with t ht hne k l heq
  by_contra hkl
  exact ht k l hne hkl heq

/-- One event determines a positive word between every sufficiently close pair
of regular samples on its two sides. The recorded pairs are exactly the
coincident pairs, each once, and their heights have the prescribed positive order. -/
theorem exists_positive_braid_event_word_neighborhood
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    (hcont : ∀ k, ContinuousAt (K k) θ)
    (hpos : ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im) :
    ∃ η : ℝ, 0 < η ∧ ∀ l ∈ ball θ η, l < θ →
      ∀ r ∈ ball θ η, θ < r →
        ∃ (before after : Equiv.Perm (Fin a)) (w : PositiveAdjacentWord a),
          StrictMono (fun j => (K (before j) l).re) ∧
          StrictMono (fun j => (K (after j) r).re) ∧
          before * w.toSigned.permutation = after ∧
          w.crossingPairs.Nodup ∧
          (∀ x y : Fin a, (x, y) ∈ w.crossingPairs ↔
            x < y ∧ (K (after x) θ).re = (K (after y) θ).re) ∧
          (∀ x y : Fin a, (x, y) ∈ w.crossingPairs →
            (K (after y) θ).im < (K (after x) θ).im) ∧
          w.length = (Finset.univ.filter fun p : Fin a × Fin a =>
            p.1 < p.2 ∧ (K (after p.1) θ).re = (K (after p.2) θ).re).card := by
  classical
  have horder := eventually_strand_orders_of_positive_crossings hcont hpos
  have hregular := eventually_strand_projection_injective_off_event hcont hpos
  obtain ⟨η, hη, hηspec⟩ := Metric.eventually_nhds_iff.mp (horder.and hregular)
  refine ⟨η, hη, ?_⟩
  intro l hl hlθ r hr hθr
  obtain ⟨hleft, hli⟩ := hηspec hl
  obtain ⟨hright, hri⟩ := hηspec hr
  obtain ⟨before, hbefore, _⟩ := exists_unique_sortingPerm
    (fun k => (K k l).re) (hli hlθ.ne)
  obtain ⟨after, hafter, _⟩ := exists_unique_sortingPerm
    (fun k => (K k r).re) (hri hθr.ne')
  obtain ⟨w, hw, _hlen, hnodup, hpairs⟩ := exists_positive_order_transition_word before after
  have hlabels {x y : Fin a} (hxy : x < y) : after x ≠ after y :=
    fun he => hxy.ne (after.injective he)
  have hheight {x y : Fin a} (hxy : x < y)
      (heq : (K (after x) θ).re = (K (after y) θ).re) :
      (K (after y) θ).im < (K (after x) θ).im := by
    have hh := ((hright (after x) (after y) (hlabels hxy)).2 heq).mp (hafter hxy)
    rcases hh with hh | hh
    · exact (not_lt_of_gt hθr hh.1).elim
    · exact hh.2
  have hpairiff (x y : Fin a) : (x, y) ∈ w.crossingPairs ↔
      x < y ∧ (K (after x) θ).re = (K (after y) θ).re := by
    rw [hpairs]
    constructor
    · rintro ⟨hxy, hbeforexy⟩
      refine ⟨hxy, ?_⟩
      by_contra hne
      have hθxy := ((hright (after x) (after y) (hlabels hxy)).1 hne).mp (hafter hxy)
      have hlxy : (K (after y) l).re < (K (after x) l).re := by
        simpa only [Equiv.apply_symm_apply] using hbefore hbeforexy
      have hθyx := ((hleft (after y) (after x) (hlabels hxy).symm).1 (Ne.symm hne)).mp hlxy
      exact (not_lt_of_gt hθxy hθyx)
    · rintro ⟨hxy, heq⟩
      refine ⟨hxy, ?_⟩
      have hlxy : (K (after y) l).re < (K (after x) l).re :=
        ((hleft (after y) (after x) (hlabels hxy).symm).2 heq.symm).mpr
          (Or.inl ⟨hlθ, hheight hxy heq⟩)
      have hb := hbefore.lt_iff_lt (a := before.symm (after y)) (b := before.symm (after x))
      exact hb.mp (by simpa only [Equiv.apply_symm_apply] using hlxy)
  refine ⟨before, after, w, hbefore, hafter, hw, hnodup, hpairiff,
    fun x y h => hheight (hpairiff x y |>.mp h).1 (hpairiff x y |>.mp h).2, ?_⟩
  have hset : w.crossingPairs.toFinset = Finset.univ.filter
      (fun p : Fin a × Fin a => p.1 < p.2 ∧ (K (after p.1) θ).re = (K (after p.2) θ).re) := by
    ext p
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpairiff p.1 p.2
  rw [← hset, List.toFinset_card_of_nodup hnodup, PositiveAdjacentWord.crossingPairs_length]

/-- Exact agreement between one word and the projected pairs at its assigned event. -/
def IsPositiveBraidEventWord {a : ℕ} (K : Fin a → ℝ → ℂ) (θ : ℝ)
    (before after : Equiv.Perm (Fin a)) (w : PositiveAdjacentWord a) : Prop :=
  before * w.toSigned.permutation = after ∧
  w.crossingPairs.Nodup ∧
  (∀ x y : Fin a, (x, y) ∈ w.crossingPairs ↔
    x < y ∧ (K (after x) θ).re = (K (after y) θ).re) ∧
  (∀ x y : Fin a, (x, y) ∈ w.crossingPairs →
    (K (after y) θ).im < (K (after x) θ).im) ∧
  w.length = (Finset.univ.filter fun p : Fin a × Fin a =>
    p.1 < p.2 ∧ (K (after p.1) θ).re = (K (after p.2) θ).re).card

/-- Sorting is constant on an interval with no projected coincidences. -/
theorem strand_sortingPerm_on_regular_interval
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    {u v : ℝ} (hregular : ∀ t ∈ Icc u v, Function.Injective (fun k => (K k t).re))
    {s t : ℝ} (hs : s ∈ Icc u v) (ht : t ∈ Icc u v)
    {σ : Equiv.Perm (Fin a)} (hσ : StrictMono (fun j => (K (σ j) s).re)) :
    StrictMono (fun j => (K (σ j) t).re) := by
  intro j k hjk
  apply (lt_iff_of_continuousOn_ne_on_preconnected isPreconnected_Icc
    (Complex.continuous_re.comp (hcont (σ j))).continuousOn
    (Complex.continuous_re.comp (hcont (σ k))).continuousOn _ hs ht).mp (hσ hjk)
  intro q hq heq
  exact hjk.ne (σ.injective (hregular q hq heq))

/-- The ordered finite event set is realized by compatible positive word blocks.
Each block retains regular samples on its two sides and the exact crossing pairs.
The first and last sorting permutations sort the specified interval endpoints. -/
theorem exists_finite_positive_braid_event_blocks
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    (E : Finset ℝ) (b d : ℝ) (hbd : b < d)
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re)
    (hb : b ∉ E) (hd : d ∉ E)
    (hpos : ∀ θ ∈ E, ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im) :
    ∃ (N : ℕ) (event left right : Fin N → ℝ)
      (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a),
      List.ofFn event = E.sort (· ≤ ·) ∧
      StrictMono (fun j => (K (σ 0 j) b).re) ∧
      StrictMono (fun j => (K (σ (Fin.last N) j) d).re) ∧
      ∀ j : Fin N,
        b ≤ left j ∧ left j < event j ∧ event j < right j ∧ right j ≤ d ∧
        StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
        StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
        (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
        IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j) := by
  classical
  induction E using Finset.strongInductionOn generalizing b d with
  | _ E ih =>
    have hreg (t : ℝ) (ht : t ∈ Icc b d) (hnt : t ∉ E) :
        Function.Injective (fun k => (K k t).re) := by
      intro k l heq
      by_contra hkl
      exact hnt ((hE t).mpr ⟨ht, k, l, hkl, heq⟩)
    by_cases hne : E.Nonempty
    · let θ := E.min' hne
      have hθ : θ ∈ E := E.min'_mem hne
      have hθbd := ((hE θ).mp hθ).1
      have hbθ : b < θ := lt_of_le_of_ne hθbd.1 (fun he => hb (he ▸ hθ))
      have hθd : θ < d := lt_of_le_of_ne hθbd.2 (fun he => hd (he ▸ hθ))
      obtain ⟨η, hη, hlocal⟩ := exists_positive_braid_event_word_neighborhood
        (fun k => (hcont k).continuousAt) (hpos θ hθ)
      have hav : ∀ᶠ t in 𝓝 θ, t ∉ E.erase θ :=
        (E.erase θ).isClosed.isOpen_compl.mem_nhds (Finset.notMem_erase _ _)
      have he : ∀ᶠ t in 𝓝 θ, t ∈ Ioo b d := isOpen_Ioo.mem_nhds ⟨hbθ, hθd⟩
      obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.mp (hav.and he)
      let ε := min η δ
      have hε : 0 < ε := lt_min hη hδ
      let l := θ - ε / 2
      let r := θ + ε / 2
      have hlθ : l < θ := by dsimp [l]; linarith
      have hθr : θ < r := by dsimp [r]; linarith
      have hlball : l ∈ ball θ ε := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        dsimp [l]
        constructor <;> linarith
      have hrball : r ∈ ball θ ε := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        dsimp [r]
        constructor <;> linarith
      have hlδ := hδspec (ball_subset_ball (min_le_right η δ) hlball)
      have hrδ := hδspec (ball_subset_ball (min_le_right η δ) hrball)
      obtain ⟨before, after, word, hbefore, hafter, hword⟩ :=
        hlocal l (ball_subset_ball (min_le_left η δ) hlball) hlθ
          r (ball_subset_ball (min_le_left η δ) hrball) hθr
      have hbeforeb : StrictMono (fun j => (K (before j) b).re) := by
        apply strand_sortingPerm_on_regular_interval hcont (u := b) (v := l) _
          ⟨hlδ.2.1.le, le_rfl⟩ ⟨le_rfl, hlδ.2.1.le⟩ hbefore
        intro t ht
        apply hreg t ⟨ht.1, ht.2.trans hlδ.2.2.le⟩
        intro htE
        have hmin : θ ≤ t := E.min'_le t htE
        linarith [ht.2]
      have hE' : ∀ t, t ∈ E.erase θ ↔ t ∈ Icc r d ∧
          ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re := by
        intro t
        constructor
        · intro ht
          obtain ⟨htθ, htE⟩ := Finset.mem_erase.mp ht
          obtain ⟨htbd, hpair⟩ := (hE t).mp htE
          refine ⟨⟨?_, htbd.2⟩, hpair⟩
          by_contra hrt
          have htr : t < r := lt_of_not_ge hrt
          have hθt : θ ≤ t := E.min'_le t htE
          have htd : t ∈ ball θ δ := by
            rw [mem_ball, Real.dist_eq, abs_lt]
            have hεδ : ε ≤ δ := min_le_right η δ
            dsimp [r] at htr
            constructor <;> linarith
          exact (hδspec htd).1 ht
        · rintro ⟨ht, hpair⟩
          exact Finset.mem_erase.mpr ⟨(hθr.trans_le ht.1).ne',
            (hE t).mpr ⟨⟨hrδ.2.1.le.trans ht.1, ht.2⟩, hpair⟩⟩
      obtain ⟨N, event, left, right, σ, w, hevent, hσ0, hσlast, hblocks⟩ :=
        ih (E.erase θ) (Finset.erase_ssubset hθ) r d hrδ.2.2 hE' hrδ.1
          (fun h => hd (Finset.mem_of_mem_erase h))
          (fun t ht => hpos t (Finset.mem_of_mem_erase ht))
      have hσafter : σ 0 = after :=
        sortingPerm_unique (hreg r ⟨hrδ.2.1.le, hrδ.2.2.le⟩ (by
          intro hrE
          exact hrδ.1 (Finset.mem_erase.mpr ⟨hθr.ne', hrE⟩))) hσ0 hafter
      have hfirstIsolation : ∀ t ∈ Icc l r, t ∈ E ↔ t = θ := by
        intro t ht
        have htd : t ∈ ball θ δ := by
          rw [mem_ball, Real.dist_eq, abs_lt]
          have hεδ : ε ≤ δ := min_le_right η δ
          dsimp [l, r] at ht
          constructor <;> linarith [ht.1, ht.2]
        constructor
        · intro htE
          by_contra hne
          exact (hδspec htd).1 (Finset.mem_erase.mpr ⟨hne, htE⟩)
        · rintro rfl
          exact hθ
      refine ⟨N + 1, Fin.cons θ event, Fin.cons l left, Fin.cons r right,
        Fin.cons before σ, Fin.cons word w, ?_, ?_, ?_, ?_⟩
      · rw [List.ofFn_cons, hevent]
        have hs := Finset.sort_insert (s := E.erase θ) (a := θ) (· ≤ ·)
          (fun t ht => E.min'_le t (Finset.mem_of_mem_erase ht)) (Finset.notMem_erase _ _)
        simpa only [Finset.insert_erase hθ] using hs.symm
      · simpa only [Fin.cons_zero] using hbeforeb
      · simpa only [show Fin.last (N + 1) = (Fin.last N).succ from rfl,
          Fin.cons_succ] using hσlast
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, hσafter] using
            (show b ≤ l ∧ l < θ ∧ θ < r ∧ r ≤ d ∧
              StrictMono (fun k => (K (before k) l).re) ∧
              StrictMono (fun k => (K (after k) r).re) ∧
              (∀ t ∈ Icc l r, t ∈ E ↔ t = θ) ∧
              IsPositiveBraidEventWord K θ before after word from
              ⟨hlδ.2.1.le, hlθ, hθr, hrδ.2.2.le, hbefore, hafter, hfirstIsolation, hword⟩)
        · obtain ⟨hrl, hlt, htr, hrd, hL, hR, hisol, hmatch⟩ := hblocks j
          have hbl : b ≤ left j := hrδ.2.1.le.trans hrl
          have hisol' : ∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j := by
            intro t ht
            have htθ : t ≠ θ := (hθr.trans_le (hrl.trans ht.1)).ne'
            have he : t ∈ E ↔ t ∈ E.erase θ :=
              ⟨fun h => Finset.mem_erase.mpr ⟨htθ, h⟩, Finset.mem_of_mem_erase⟩
            exact he.trans (hisol t ht)
          simpa only [Fin.cons_succ, Fin.castSucc_succ] using
            (show b ≤ left j ∧ left j < event j ∧ event j < right j ∧ right j ≤ d ∧
              StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
              StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
              (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
              IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j) from
              ⟨hbl, hlt, htr, hrd, hL, hR, hisol', hmatch⟩)
    · have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst E
      obtain ⟨σ, hσ, _⟩ := exists_unique_sortingPerm
        (fun k => (K k b).re) (hreg b ⟨le_rfl, hbd.le⟩ hb)
      have hσd : StrictMono (fun j => (K (σ j) d).re) := by
        apply strand_sortingPerm_on_regular_interval hcont
          (fun t ht => hreg t ht (by simp)) ⟨le_rfl, hbd.le⟩ ⟨hbd.le, le_rfl⟩ hσ
      exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun _ => σ, Fin.elim0,
        by simp, hσ, hσd, fun j => Fin.elim0 j⟩

/-- Ordered event words concatenate to the exact endpoint order transition.
The total length is the sum of the coincident unordered-pair counts at the
individual events. The counts use the final sorting of each event block. -/
theorem exists_finite_positive_braid_event_words
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    (E : Finset ℝ) (b d : ℝ) (hbd : b < d)
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re)
    (hb : b ∉ E) (hd : d ∉ E)
    (hpos : ∀ θ ∈ E, ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im) :
    ∃ (N : ℕ) (event left right : Fin N → ℝ)
      (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a),
      N = E.card ∧ List.ofFn event = E.sort (· ≤ ·) ∧ StrictMono event ∧
      StrictMono (fun j => (K (σ 0 j) b).re) ∧
      StrictMono (fun j => (K (σ (Fin.last N) j) d).re) ∧
      (∀ j : Fin N,
        b ≤ left j ∧ left j < event j ∧ event j < right j ∧ right j ≤ d ∧
        StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
        StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
        (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
        IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
      σ 0 * (PositiveAdjacentWord.toSigned ((List.ofFn w).flatten)).permutation =
        σ (Fin.last N) ∧
      (List.ofFn w).flatten.length = ∑ j : Fin N,
        (Finset.univ.filter fun p : Fin a × Fin a =>
          p.1 < p.2 ∧ (K (σ j.succ p.1) (event j)).re =
            (K (σ j.succ p.2) (event j)).re).card := by
  classical
  obtain ⟨N, event, left, right, σ, w, hevent, hσ0, hσlast, hblocks⟩ :=
    exists_finite_positive_braid_event_blocks hcont E b d hbd hE hb hd hpos
  have hn : N = E.card := by
    simpa only [List.length_ofFn, Finset.length_sort] using congrArg List.length hevent
  have hmono : StrictMono event := List.pairwise_ofFn.mp (by
    rw [hevent]
    exact E.sortedLT_sort.pairwise)
  have hword (j : Fin N) := (hblocks j).2.2.2.2.2.2.2
  refine ⟨N, event, left, right, σ, w, hn, hevent, hmono, hσ0, hσlast, hblocks,
    positiveWordSequence_permutation σ w (fun j => (hword j).1), ?_⟩
  rw [positiveWordSequence_length]
  exact Finset.sum_congr rfl (fun j _ => (hword j).2.2.2.2)

end OnLeConjecture.Analytic
