/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Order.Filter.Finite
public import Mathlib.Analysis.Complex.Basic

/-!
# Local labels of a regular fibre of a proper map

Let `f : X → Y` be continuous on a compact set `K` of a complex Banach space, let `Ω ⊆ K` be
open, and let `y₀ ∈ Y` be a value that is not taken on `K \ Ω`. Suppose that `f` is strictly
differentiable with invertible derivative at every point of `Ω` over `y₀`. Then
(`exists_localLabels`):

* the fibre `Z = {x ∈ Ω | f x = y₀}` is finite;
* there are `r > 0` and maps `g z`, `z ∈ Z`, continuous on the ball `B(y₀, r)`, differentiable
  at `y₀`, with `g z y₀ = z`, such that for every `y ∈ B(y₀, r)` the points `g z y` lie in `Ω`
  over `y`, are pairwise distinct, and exhaust the points of `K` over `y`.

The proof is the inverse function theorem at each point of the fibre, with pairwise disjoint
neighbourhoods, together with the compactness of `K` minus these neighbourhoods. Finiteness of
the fibre follows from compactness, because the inverse function theorem isolates its points.

`IsPreconnected.eq_of_eventually_eq` records that a function to `ℕ` that is locally constant
on a preconnected set is constant there.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace OnLeConjecture.Analytic

/-- A compact set each of whose points has an open neighbourhood meeting the set only in that
point is finite. -/
theorem finite_of_isCompact_of_isolated {X : Type*} [TopologicalSpace X] {Z : Set X}
    (hZ : IsCompact Z) (hiso : ∀ z ∈ Z, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ Z ∩ U ⊆ {z}) :
    Z.Finite := by
  classical
  choose! U hUo hzU hZU using hiso
  obtain ⟨t, htZ, htfin, hcover⟩ := hZ.elim_finite_subcover_image (b := Z) (c := U)
    (fun z hz => hUo z hz) (fun z hz => mem_biUnion hz (hzU z hz))
  refine htfin.subset fun z hz => ?_
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcover hz)
  have h := hZU i (htZ hi) ⟨hz, hzi⟩
  rw [mem_singleton_iff] at h
  rw [h]
  exact hi

/-- A function to `ℕ` that is locally constant on a preconnected set is constant there. -/
theorem IsPreconnected.eq_of_eventually_eq {α : Type*} [TopologicalSpace α] {s : Set α}
    (hs : IsPreconnected s) {f : α → ℕ} (hf : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, f y = f x)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  refine hs.constant (fun z hz => ?_) hx hy
  rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
  exact hf z hz

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Local labels of a regular fibre of a proper map.** -/
theorem exists_localLabels {f : X → Y} {K Ω : Set X} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hΩK : Ω ⊆ K) (hf : ContinuousOn f K) {y₀ : Y}
    (hfr : ∀ x ∈ K, f x = y₀ → x ∈ Ω)
    (hreg : ∀ x ∈ Ω, f x = y₀ → ∃ f' : X ≃L[ℂ] Y, HasStrictFDerivAt f (f' : X →L[ℂ] Y) x) :
    ∃ Z : Finset X, (∀ x, x ∈ Z ↔ x ∈ Ω ∧ f x = y₀) ∧ ∃ r > 0, ∃ g : X → Y → X,
      (∀ z ∈ Z, g z y₀ = z ∧ ContinuousOn (g z) (ball y₀ r) ∧ DifferentiableAt ℂ (g z) y₀) ∧
      ∀ y ∈ ball y₀ r, (∀ z ∈ Z, g z y ∈ Ω ∧ f (g z y) = y) ∧
        (∀ x ∈ K, f x = y → ∃ z ∈ Z, g z y = x) ∧ InjOn (fun z => g z y) Z := by
  classical
  choose f' hf' using hreg
  set Zs : Set X := {x | x ∈ Ω ∧ f x = y₀} with hZsdef
  have hZsK : Zs = K ∩ f ⁻¹' {y₀} := by
    ext x
    exact ⟨fun hx => ⟨hΩK hx.1, hx.2⟩, fun hx => ⟨hfr x hx.1 hx.2, hx.2⟩⟩
  have hZsc : IsCompact Zs := by
    rw [hZsK]
    exact hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  -- the inverse function theorem isolates the points of the fibre
  have hiso : ∀ z ∈ Zs, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ Zs ∩ U ⊆ {z} := by
    intro z hz
    let e := (hf' z hz.1 hz.2).toOpenPartialHomeomorph f
    refine ⟨e.source, e.open_source, (hf' z hz.1 hz.2).mem_toOpenPartialHomeomorph_source,
      fun x hx => ?_⟩
    have hxz : e x = e z := by
      change f x = f z
      rw [hx.1.2, hz.2]
    exact e.injOn hx.2 (hf' z hz.1 hz.2).mem_toOpenPartialHomeomorph_source hxz
  have hZfin : Zs.Finite := finite_of_isCompact_of_isolated hZsc hiso
  set Z : Finset X := hZfin.toFinset with hZdef
  have hmemZ : ∀ x, x ∈ Z ↔ x ∈ Ω ∧ f x = y₀ := fun x => by
    rw [hZdef, Set.Finite.mem_toFinset]
    rfl
  -- the local inverses
  let g : X → Y → X := fun z y =>
    if hz : z ∈ Ω ∧ f z = y₀ then ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).symm y else z
  have hg : ∀ z (hz : z ∈ Ω ∧ f z = y₀),
      g z = ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).symm := by
    intro z hz
    funext y
    simp only [g, dif_pos hz]
  -- pairwise disjoint neighbourhoods
  obtain ⟨D, hD, hdisj⟩ := hZfin.t2_separation
  let U : X → Set X := fun z =>
    if hz : z ∈ Ω ∧ f z = y₀ then
      ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).source ∩ D z ∩ Ω
    else ∅
  have hU : ∀ z (hz : z ∈ Ω ∧ f z = y₀),
      U z = ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).source ∩ D z ∩ Ω := by
    intro z hz
    simp only [U, dif_pos hz]
  have hUopen : ∀ z, IsOpen (U z) := by
    intro z
    by_cases hz : z ∈ Ω ∧ f z = y₀
    · rw [hU z hz]
      exact (((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).open_source.inter (hD z).2).inter hΩ
    · simp only [U, dif_neg hz]
      exact isOpen_empty
  -- the part of `K` away from the neighbourhoods is compact and misses `y₀`
  set K' : Set X := K \ ⋃ z ∈ Z, U z with hK'def
  have hK'c : IsCompact K' := hK.diff (isOpen_biUnion fun z _ => hUopen z)
  have hK'y₀ : y₀ ∉ f '' K' := by
    rintro ⟨x, hx, hfx⟩
    have hxZ : x ∈ Z := (hmemZ x).mpr ⟨hfr x hx.1 hfx, hfx⟩
    apply hx.2
    refine mem_biUnion hxZ ?_
    have hz : x ∈ Ω ∧ f x = y₀ := (hmemZ x).mp hxZ
    rw [hU x hz]
    exact ⟨⟨(hf' x hz.1 hz.2).mem_toOpenPartialHomeomorph_source, (hD x).1⟩, hz.1⟩
  have hev₁ : ∀ᶠ y in 𝓝 y₀, y ∉ f '' K' :=
    (hK'c.image_of_continuousOn (hf.mono sdiff_subset)).isClosed.isOpen_compl.mem_nhds hK'y₀
  have hev₂ : ∀ z ∈ Z, ∀ᶠ y in 𝓝 y₀, ∀ hz : z ∈ Ω ∧ f z = y₀,
      y ∈ ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).target ∧ g z y ∈ U z := by
    intro z hzZ
    have hz := (hmemZ z).mp hzZ
    set e := (hf' z hz.1 hz.2).toOpenPartialHomeomorph f with he
    have hy₀ : y₀ ∈ e.target := by
      rw [← hz.2]
      exact (hf' z hz.1 hz.2).image_mem_toOpenPartialHomeomorph_target
    have hzs : z ∈ e.source := (hf' z hz.1 hz.2).mem_toOpenPartialHomeomorph_source
    have hsymm : e.symm y₀ = z := by
      rw [← hz.2]
      exact e.left_inv hzs
    have hUz : U z ∈ 𝓝 z := by
      apply (hUopen z).mem_nhds
      rw [hU z hz]
      exact ⟨⟨hzs, (hD z).1⟩, hz.1⟩
    have hcont : ∀ᶠ y in 𝓝 y₀, e.symm y ∈ U z :=
      (e.continuousAt_symm hy₀).preimage_mem_nhds (by rw [hsymm]; exact hUz)
    filter_upwards [e.open_target.mem_nhds hy₀, hcont] with y hy1 hy2
    intro _
    refine ⟨hy1, ?_⟩
    rw [hg z hz]
    exact hy2
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.mp
    (hev₁.and ((Filter.eventually_all_finset Z).mpr hev₂))
  refine ⟨Z, hmemZ, r, hr, g, ?_, ?_⟩
  · intro z hzZ
    have hz := (hmemZ z).mp hzZ
    set e := (hf' z hz.1 hz.2).toOpenPartialHomeomorph f with he
    have hzs : z ∈ e.source := (hf' z hz.1 hz.2).mem_toOpenPartialHomeomorph_source
    refine ⟨?_, ?_, ?_⟩
    · rw [hg z hz]
      exact (congrArg e.symm hz.2).symm.trans (e.left_inv hzs)
    · rw [hg z hz]
      refine e.continuousOn_symm.mono fun y hy => ?_
      exact ((hrball (mem_ball.mp hy)).2 z hzZ hz).1
    · have h := (hf' z hz.1 hz.2).to_localInverse
      rw [HasStrictFDerivAt.localInverse_def] at h
      rw [hg z hz]
      convert h.hasFDerivAt.differentiableAt using 1
      exact hz.2.symm
  · intro y hy
    obtain ⟨hyK, hyU⟩ := hrball (mem_ball.mp hy)
    have hgood : ∀ z ∈ Z, g z y ∈ U z ∧ f (g z y) = y := by
      intro z hzZ
      have hz := (hmemZ z).mp hzZ
      obtain ⟨htarget, hgU⟩ := hyU z hzZ hz
      refine ⟨hgU, ?_⟩
      rw [hg z hz]
      exact ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).right_inv htarget
    refine ⟨fun z hzZ => ⟨?_, (hgood z hzZ).2⟩, ?_, ?_⟩
    · have hz := (hmemZ z).mp hzZ
      have h := (hgood z hzZ).1
      rw [hU z hz] at h
      exact h.2
    · intro x hxK hfx
      have hxU : x ∈ ⋃ z ∈ Z, U z := by
        by_contra hxU
        exact hyK ⟨x, ⟨hxK, hxU⟩, hfx⟩
      obtain ⟨z, hzZ, hxz⟩ := mem_iUnion₂.mp hxU
      have hz := (hmemZ z).mp hzZ
      refine ⟨z, hzZ, ?_⟩
      rw [hU z hz] at hxz
      rw [hg z hz]
      have hex : ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f) x = y := hfx
      rw [← hex]
      exact ((hf' z hz.1 hz.2).toOpenPartialHomeomorph f).left_inv hxz.1.1
    · intro z hzZ z' hz'Z hzz
      by_contra hne
      have h1 := (hgood z hzZ).1
      have h2 := (hgood z' hz'Z).1
      rw [hU z ((hmemZ z).mp hzZ)] at h1
      rw [hU z' ((hmemZ z').mp hz'Z)] at h2
      have hd := hdisj (hZfin.mem_toFinset.mp hzZ) (hZfin.mem_toFinset.mp hz'Z) hne
      exact Set.disjoint_left.mp hd h1.1.2 (by simpa only [hzz] using h2.1.2)

end OnLeConjecture.Analytic
