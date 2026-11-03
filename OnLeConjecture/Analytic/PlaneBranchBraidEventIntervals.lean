/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidEventWord

/-! # Strictly separated intervals for projected braid events

The samples may be moved toward their events without changing any event word
or chamber sorting permutation. A uniform sufficiently small radius produces
strict gaps between all the resulting closed intervals.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory

/-- Finitely many strictly ordered points admit smaller sample intervals with
strict gaps, inside any prescribed intervals around the individual points. -/
theorem exists_capped_strictly_separated_event_samples {N : ℕ}
    (event left right : Fin N → ℝ) (b d : ℝ) (hmono : StrictMono event)
    (cap : Fin N → ℝ) (hcap : ∀ j, 0 < cap j)
    (hlocal : ∀ j, b ≤ left j ∧ left j < event j ∧ event j < right j ∧ right j ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ j, ε < cap j) ∧
      (∀ j, b < event j - ε ∧ left j < event j - ε ∧ event j - ε < event j ∧
        event j < event j + ε ∧ event j + ε < right j ∧ event j + ε < d) ∧
      (∀ j k, j < k → event j + ε < event k - ε) ∧
      (∀ j, Icc (event j - ε) (event j + ε) ⊆ ball (event j) (cap j)) := by
  have hs (j : Fin N) : ∀ᶠ ε : ℝ in 𝓝 0,
      left j < event j - ε ∧ event j + ε < right j := by
    have hL := (continuousAt_const : ContinuousAt (fun _ : ℝ => left j) 0).eventually_lt
      (continuousAt_const.sub continuousAt_id) (by simpa using (hlocal j).2.1)
    have hR := (continuousAt_const.add continuousAt_id :
      ContinuousAt (fun ε : ℝ => event j + ε) 0).eventually_lt
      continuousAt_const (by simpa using (hlocal j).2.2.1)
    exact hL.and hR
  have hp (j k : Fin N) : ∀ᶠ ε : ℝ in 𝓝 0,
      j < k → event j + ε < event k - ε := by
    by_cases hjk : j < k
    · have h := (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun ε : ℝ => event j + ε) 0).eventually_lt
        (continuousAt_const.sub continuousAt_id) (by simpa using hmono hjk)
      exact h.mono fun _ ht _ => ht
    · exact Filter.Eventually.of_forall fun _ h => (hjk h).elim
  have hc (j : Fin N) : ∀ᶠ ε : ℝ in 𝓝 0, ε < cap j :=
    continuousAt_id.eventually_lt continuousAt_const (hcap j)
  have hall := (Filter.eventually_all.mpr hs).and
    ((Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr (hp j)).and
      (Filter.eventually_all.mpr hc))
  obtain ⟨δ, hδ, hspec⟩ := Metric.eventually_nhds_iff.mp hall
  have hhalf : δ / 2 ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hspecL, hspecP, hspecC⟩ := hspec hhalf
  refine ⟨δ / 2, by positivity, hspecC, ?_, hspecP, ?_⟩
  · intro j
    obtain ⟨hbl, hle, her, hrd⟩ := hlocal j
    obtain ⟨hL, hR⟩ := hspecL j
    exact ⟨hbl.trans_lt hL, hL, by linarith, by linarith, hR, hR.trans_le hrd⟩
  · intro j t ht
    rw [mem_ball, Real.dist_eq, abs_lt]
    have hj := hspecC j
    constructor <;> linarith [ht.1, ht.2]

/-- The uncapped sample refinement, retaining its original interface. -/
theorem exists_strictly_separated_event_samples {N : ℕ}
    (event left right : Fin N → ℝ) (b d : ℝ) (hmono : StrictMono event)
    (hlocal : ∀ j, b ≤ left j ∧ left j < event j ∧ event j < right j ∧ right j ≤ d) :
    ∃ l r : Fin N → ℝ,
      (∀ j, b < l j ∧ left j < l j ∧ l j < event j ∧
        event j < r j ∧ r j < right j ∧ r j < d) ∧
      (∀ j k, j < k → r j < l k) := by
  obtain ⟨ε, _hε, _hcap, hlocal', hsep, _hball⟩ :=
    exists_capped_strictly_separated_event_samples event left right b d hmono
      (fun _ => 1) (fun _ => one_pos) hlocal
  exact ⟨fun j => event j - ε, fun j => event j + ε, hlocal', hsep⟩

/-- Refine the sample intervals of fixed event blocks. The event enumeration,
sorting permutations, and positive words are unchanged. -/
theorem refine_positive_braid_event_intervals_capped
    {a N : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    (E : Finset ℝ) (b d : ℝ)
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re)
    (event left right : Fin N → ℝ) (hmono : StrictMono event)
    (cap : Fin N → ℝ) (hcap : ∀ j, 0 < cap j)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hblocks : ∀ j : Fin N,
      b ≤ left j ∧ left j < event j ∧ event j < right j ∧ right j ≤ d ∧
      StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
      StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
      (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
      IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) :
    ∃ l r : Fin N → ℝ,
      (∀ j, left j < l j ∧ r j < right j) ∧
      (∀ j : Fin N,
        b < l j ∧ l j < event j ∧ event j < r j ∧ r j < d ∧
        StrictMono (fun k => (K (σ j.castSucc k) (l j)).re) ∧
        StrictMono (fun k => (K (σ j.succ k) (r j)).re) ∧
        (∀ t ∈ Icc (l j) (r j), t ∈ E ↔ t = event j) ∧
        IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
      (∀ j k, j < k → r j < l k) ∧
      (∀ j, Icc (l j) (r j) ⊆ ball (event j) (cap j)) := by
  obtain ⟨ε, _hε, _hcap, hlocal, hsep, hball⟩ :=
    exists_capped_strictly_separated_event_samples event left right b d hmono cap hcap
      (fun j => ⟨(hblocks j).1, (hblocks j).2.1, (hblocks j).2.2.1, (hblocks j).2.2.2.1⟩)
  let l : Fin N → ℝ := fun j => event j - ε
  let r : Fin N → ℝ := fun j => event j + ε
  refine ⟨l, r, fun j => ⟨(hlocal j).2.1, (hlocal j).2.2.2.2.1⟩, ?_, hsep, hball⟩
  intro j
  obtain ⟨hbl, hll, hle, her, hrr, hrd⟩ := hlocal j
  obtain ⟨hbL, hLe, heR, hRd, hσL, hσR, hiso, hword⟩ := hblocks j
  have hreg (t : ℝ) (ht : t ∈ Icc (left j) (right j)) (hne : t ≠ event j) :
      Function.Injective (fun k => (K k t).re) := by
    intro k l heq
    by_contra hkl
    have hmem : t ∈ E := (hE t).mpr ⟨⟨hbL.trans ht.1, ht.2.trans hRd⟩, k, l, hkl, heq⟩
    exact hne ((hiso t ht).mp hmem)
  have hsortL : StrictMono (fun k => (K (σ j.castSucc k) (l j)).re) := by
    apply strand_sortingPerm_on_regular_interval hcont
      (u := left j) (v := l j) ?_ ⟨le_rfl, hll.le⟩ ⟨hll.le, le_rfl⟩ hσL
    intro t ht
    exact hreg t ⟨ht.1, ht.2.trans (hle.trans heR).le⟩ (ne_of_lt (ht.2.trans_lt hle))
  have hsortR : StrictMono (fun k => (K (σ j.succ k) (r j)).re) := by
    apply strand_sortingPerm_on_regular_interval hcont
      (u := r j) (v := right j) ?_ ⟨hrr.le, le_rfl⟩ ⟨le_rfl, hrr.le⟩ hσR
    intro t ht
    exact hreg t ⟨(hLe.trans her).le.trans ht.1, ht.2⟩ (ne_of_gt (her.trans_le ht.1))
  refine ⟨hbl, hle, her, hrd, hsortL, hsortR, ?_, hword⟩
  intro t ht
  exact hiso t ⟨hll.le.trans ht.1, ht.2.trans hrr.le⟩

/-- Refine the sample intervals of fixed event blocks. The event enumeration,
sorting permutations, and positive words are unchanged. -/
theorem refine_positive_braid_event_intervals
    {a N : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    (E : Finset ℝ) (b d : ℝ)
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re)
    (event left right : Fin N → ℝ) (hmono : StrictMono event)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hblocks : ∀ j : Fin N,
      b ≤ left j ∧ left j < event j ∧ event j < right j ∧ right j ≤ d ∧
      StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
      StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
      (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
      IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) :
    ∃ l r : Fin N → ℝ,
      (∀ j, left j < l j ∧ r j < right j) ∧
      (∀ j : Fin N,
        b < l j ∧ l j < event j ∧ event j < r j ∧ r j < d ∧
        StrictMono (fun k => (K (σ j.castSucc k) (l j)).re) ∧
        StrictMono (fun k => (K (σ j.succ k) (r j)).re) ∧
        (∀ t ∈ Icc (l j) (r j), t ∈ E ↔ t = event j) ∧
        IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
      (∀ j k, j < k → r j < l k) := by
  obtain ⟨l, r, hsub, hnew, hsep, _hball⟩ := refine_positive_braid_event_intervals_capped
    hcont E b d hE event left right hmono (fun _ => 1) (fun _ => one_pos) σ w hblocks
  exact ⟨l, r, hsub, hnew, hsep⟩

/-- Ordered event words with strictly separated closed sample intervals.
This preserves the exact concatenated permutation and eventwise length formula. -/
theorem exists_strict_finite_positive_braid_event_words
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
        b < left j ∧ left j < event j ∧ event j < right j ∧ right j < d ∧
        StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
        StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
        (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
        IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
      (∀ j k, j < k → right j < left k) ∧
      σ 0 * (PositiveAdjacentWord.toSigned ((List.ofFn w).flatten)).permutation =
        σ (Fin.last N) ∧
      (List.ofFn w).flatten.length = ∑ j : Fin N,
        (Finset.univ.filter fun p : Fin a × Fin a =>
          p.1 < p.2 ∧ (K (σ j.succ p.1) (event j)).re =
            (K (σ j.succ p.2) (event j)).re).card := by
  classical
  obtain ⟨N, event, left, right, σ, w, hN, hevent, hmono, hσ0, hσlast, hblocks,
      hperm, hlength⟩ := exists_finite_positive_braid_event_words hcont E b d hbd hE hb hd hpos
  obtain ⟨l, r, _hsub, hnew, hsep⟩ := refine_positive_braid_event_intervals hcont E b d hE
    event left right hmono σ w hblocks
  exact ⟨N, event, l, r, σ, w, hN, hevent, hmono, hσ0, hσlast, hnew, hsep, hperm, hlength⟩

end OnLeConjecture.Analytic
