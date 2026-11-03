/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedVerticalArcs

/-! # Rounding profiles supported only near their own vertices

The lower strand has four vertices and the upper strand has two. Separate
relative approximations leave the other strand's interior edge points unchanged.
Both profiles still satisfy the common-neighborhood hypotheses of the released
native circle and ambient deformation theorems.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

/-- The four vertices on the lower moving strand. -/
def positiveGridLowerVertexTimes : Set ℝ := {1 / 6, 5 / 12, 7 / 12, 5 / 6}

/-- The two vertices on the upper moving strand. -/
def positiveGridUpperVertexTimes : Set ℝ := {1 / 4, 3 / 4}

/-- The prescribed neighborhoods of only the lower strand's own vertices. -/
def positiveGridLowerVertexNeighborhood (δ : ℝ) : Set ℝ :=
  {t | ∃ c ∈ positiveGridLowerVertexTimes, |t - c| < δ}

/-- The prescribed neighborhoods of only the upper strand's own vertices. -/
def positiveGridUpperVertexNeighborhood (δ : ℝ) : Set ℝ :=
  {t | ∃ c ∈ positiveGridUpperVertexTimes, |t - c| < δ}

private theorem ramp_contDiffAt' {h x : ℝ} (hh : 0 < h) (hx₀ : x ≠ 0) (hxh : x ≠ h) :
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

theorem positiveGridLowerRise_contDiffAt_of_not_vertex {t : ℝ}
    (ht : t ∉ positiveGridLowerVertexTimes) :
    ContDiffAt ℝ ∞ positiveGridRectilinearLowerRise t := by
  simp only [positiveGridLowerVertexTimes, mem_insert_iff, mem_singleton_iff, not_or] at ht
  unfold positiveGridRectilinearLowerRise
  apply ContDiffAt.add
  · exact (ramp_contDiffAt' (by norm_num : (0 : ℝ) < 1 / 2)
      (by intro h; exact ht.1 (by linarith))
      (by intro h; exact ht.2.1 (by linarith))).comp t
        ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)
  · exact (ramp_contDiffAt' (by norm_num : (0 : ℝ) < 1 / 2)
      (by intro h; exact ht.2.2.1 (by linarith))
      (by intro h; exact ht.2.2.2 (by linarith))).comp t
        ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)

theorem positiveGridUpperDrop_contDiffAt_of_not_vertex {t : ℝ}
    (ht : t ∉ positiveGridUpperVertexTimes) :
    ContDiffAt ℝ ∞ positiveGridRectilinearUpperDrop t := by
  simp only [positiveGridUpperVertexTimes, mem_insert_iff, mem_singleton_iff, not_or] at ht
  unfold positiveGridRectilinearUpperDrop
  exact (ramp_contDiffAt' (by norm_num : (0 : ℝ) < 1)
    (by intro h; exact ht.1 (by linarith))
    (by intro h; exact ht.2 (by linarith))).comp t
      ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)

private theorem vertex_neighborhood_isOpen (S : Set ℝ) (δ : ℝ) :
    IsOpen {t : ℝ | ∃ c ∈ S, |t - c| < δ} := by
  have he : {t : ℝ | ∃ c ∈ S, |t - c| < δ} =
      ⋃ c ∈ S, {t : ℝ | |t - c| < δ} := by ext t; simp
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    isOpen_lt (continuous_id.sub continuous_const).abs continuous_const

theorem positiveGridLowerVertexNeighborhood_isOpen (δ : ℝ) :
    IsOpen (positiveGridLowerVertexNeighborhood δ) := vertex_neighborhood_isOpen _ _

theorem positiveGridUpperVertexNeighborhood_isOpen (δ : ℝ) :
    IsOpen (positiveGridUpperVertexNeighborhood δ) := vertex_neighborhood_isOpen _ _

theorem positiveGridLowerVertexNeighborhood_subset (δ : ℝ) :
    positiveGridLowerVertexNeighborhood δ ⊆ positiveGridRoundingCornerNeighborhood δ := by
  rintro t ⟨c, hc, hct⟩
  refine ⟨c, ?_, hct⟩
  simp only [positiveGridLowerVertexTimes, mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [positiveGridRectilinearCornerTimes]

theorem positiveGridUpperVertexNeighborhood_subset (δ : ℝ) :
    positiveGridUpperVertexNeighborhood δ ⊆ positiveGridRoundingCornerNeighborhood δ := by
  rintro t ⟨c, hc, hct⟩
  refine ⟨c, ?_, hct⟩
  simp only [positiveGridUpperVertexTimes, mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl <;> simp [positiveGridRectilinearCornerTimes]

private theorem exists_vertex_profile {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ}
    (hS : IsClosed S) (hfs : ∀ t ∉ S, ContDiffAt ℝ ∞ f t)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ (∀ t, dist (p t) (f t) < ε) ∧
      EqOn p f {t : ℝ | ∃ c ∈ S, |t - c| < δ}ᶜ := by
  let U := {t : ℝ | ∃ c ∈ S, |t - c| < δ}
  have hSU : S ⊆ U := fun t ht => ⟨t, ht, by simpa using hδ⟩
  have hn : Sᶜ ∈ 𝓝ˢ Uᶜ := hS.isOpen_compl.mem_nhdsSet.mpr (compl_subset_compl.mpr hSU)
  obtain ⟨p, hp, hpa, hpe, -⟩ := hf.exists_contDiff_approx_and_eqOn (⊤ : ℕ∞)
    continuous_const (fun _ => hε) (vertex_neighborhood_isOpen S δ).isClosed_compl hn
    (fun t ht => (hfs t ht).contDiffWithinAt)
  exact ⟨p, hp, hpa, hpe⟩

/-- Separate arbitrarily close smooth profiles agree with the polygon everywhere
outside neighborhoods of their OWN vertices. No interior edge exceptions are introduced. -/
theorem exists_positiveGrid_own_vertex_profiles {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε) ∧
      (∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridRoundingCornerNeighborhood δ)ᶜ := by
  have hL : IsClosed positiveGridLowerVertexTimes :=
    (by simp [positiveGridLowerVertexTimes] : positiveGridLowerVertexTimes.Finite).isClosed
  have hU : IsClosed positiveGridUpperVertexTimes :=
    (by simp [positiveGridUpperVertexTimes] : positiveGridUpperVertexTimes.Finite).isClosed
  obtain ⟨l, hls, hla, hl⟩ := exists_vertex_profile positiveGridRectilinearLowerRise_continuous hL
    (fun _ h => positiveGridLowerRise_contDiffAt_of_not_vertex h) hδ hε
  obtain ⟨u, hus, hua, hu⟩ := exists_vertex_profile positiveGridRectilinearUpperDrop_continuous hU
    (fun _ h => positiveGridUpperDrop_contDiffAt_of_not_vertex h) hδ hε
  exact ⟨l, u, hls, hus, hla, hua, hl, hu,
    hl.mono (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset δ)),
    hu.mono (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset δ))⟩

/-- The lower rounded strand is exactly the polygon outside its OWN vertex
neighborhood, even at parameter values near an upper-strand vertex. -/
theorem positiveGridRoundedDeformation_lower_eq_polygon_own_vertices {m : ℕ}
    (i : Fin (m - 1)) {l : ℝ → ℝ} (u : ℝ → ℝ) {δ t : ℝ}
    (hl : EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (ht : positiveGridRoundingProgress t / 2 ∉ positiveGridLowerVertexNeighborhood δ) :
    positiveGridRoundedDeformation i l u (adjacentLower i) 1 t =
      positiveGridRectilinear i (adjacentLower i) (positiveGridRoundingProgress t / 2) := by
  simp [positiveGridRoundedDeformation, positiveGridRoundingRise, hl ht,
    positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
    positiveGridRectilinearDepth, sub_eq_add_neg]
  ring

/-- The upper rounded strand is exactly the polygon outside its OWN two vertex
neighborhoods; the lower strand's four vertex times impose no restriction. -/
theorem positiveGridRoundedDeformation_upper_eq_polygon_own_vertices {m : ℕ}
    (i : Fin (m - 1)) (l : ℝ → ℝ) {u : ℝ → ℝ} {δ t : ℝ}
    (hu : EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (ht : positiveGridRoundingProgress t / 2 ∉ positiveGridUpperVertexNeighborhood δ) :
    positiveGridRoundedDeformation i l u (adjacentUpper i) 1 t =
      positiveGridRectilinear i (adjacentUpper i) (positiveGridRoundingProgress t / 2) := by
  have hne : adjacentUpper i ≠ adjacentLower i := by
    intro h
    have he := congrArg Fin.val h
    change i.val + 1 = i.val at he
    omega
  simp [positiveGridRoundedDeformation, positiveGridRoundingRise, hu ht,
    positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
    positiveGridRectilinearDepth, hne]
  ring

/-- In the complete retained word, each moving strand agrees exactly with its
polygonal letter outside only that strand's own vertex neighborhoods. The prefix
label and the original progress parameter are unchanged. -/
theorem positiveRoundedWord_letter_eq_polygon_own_vertices {m : ℕ}
    (w : PositiveAdjacentWord m) {l u : Fin w.length → ℝ → ℝ} {δ : ℝ}
    (hδ : δ ≤ 1 / 48)
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise
      (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop
      (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hout :
      ((positiveWordPrefix w j.val).symm k = adjacentLower w[j.val] ∧
        positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉
          positiveGridLowerVertexNeighborhood δ) ∨
      ((positiveWordPrefix w j.val).symm k = adjacentUpper w[j.val] ∧
        positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉
          positiveGridUpperVertexNeighborhood δ)) :
    positiveRoundedWord w l u k 1 t =
      let p := positiveGridRectilinear w[j.val] ((positiveWordPrefix w j.val).symm k)
        (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)
      (2 * (j.val : ℝ) + 1 + p.1, p.2) := by
  have hU : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hh := positiveGridRoundingCornerNeighborhood_subset hδ hx
    constructor <;> linarith [hh.1, hh.2]
  have hlc (j) := (hl j).mono (compl_subset_compl.mpr
    (positiveGridLowerVertexNeighborhood_subset δ))
  have huc (j) := (hu j).mono (compl_subset_compl.mpr
    (positiveGridUpperVertexNeighborhood_subset δ))
  rw [positiveRoundedWord_letter w hlc huc hU k 1 j ht]
  rcases hout with ⟨hk, hout⟩ | ⟨hk, hout⟩
  · rw [hk, positiveGridRoundedDeformation_lower_eq_polygon_own_vertices w[j.val] (u j)
      (hl j) hout]
  · rw [hk, positiveGridRoundedDeformation_upper_eq_polygon_own_vertices w[j.val] (l j)
      (hu j) hout]

end OnLeConjecture.KnotTheory
