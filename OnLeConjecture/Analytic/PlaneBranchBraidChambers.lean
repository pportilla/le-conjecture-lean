/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCrossingFinite
public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Projected sheet orders between crossing events

On an open angle interval containing no projected coincidence, continuity
keeps every pair of projected coordinates in the same strict order.
Sorting the finite image gives a unique permutation of the sheet labels.
Regular sample angles in the same interval determine the same permutation.
No order is assigned at a crossing event where projected coordinates tie.
-/

@[expose] public noncomputable section

open Set Metric

namespace OnLeConjecture.Analytic

/-- A finite injective real-valued function has one sorting permutation,
which sends each position to the label occupying that position. -/
theorem exists_unique_sortingPerm {a : ℕ} (f : Fin a → ℝ)
    (hf : Function.Injective f) :
    ∃! σ : Equiv.Perm (Fin a), StrictMono (fun j => f (σ j)) := by
  classical
  let s : Finset ℝ := Finset.univ.image f
  have hs : s.card = a := by
    change (Finset.univ.image f).card = a
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let e : Fin a ≃ s := Equiv.ofBijective
    (fun k => ⟨f k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩) (by
      constructor
      · intro k l h
        exact hf (congrArg Subtype.val h)
      · rintro ⟨x, hx⟩
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hx
        exact ⟨k, Subtype.ext hk⟩)
  let σ : Equiv.Perm (Fin a) := (s.orderIsoOfFin hs).toEquiv.trans e.symm
  have hval (j : Fin a) : f (σ j) = s.orderEmbOfFin hs j := by
    exact congrArg Subtype.val (e.apply_symm_apply (s.orderIsoOfFin hs j))
  have hσ : StrictMono (fun j => f (σ j)) := by
    simpa only [hval] using (s.orderEmbOfFin hs).strictMono
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  have hu := Finset.orderEmbOfFin_unique hs
    (fun j => Finset.mem_image.mpr ⟨τ j, Finset.mem_univ _, rfl⟩) hτ
  apply Equiv.ext
  intro j
  exact hf ((congrFun hu j).trans (hval j).symm)

theorem sortingPerm_unique {a : ℕ} {f : Fin a → ℝ} (hf : Function.Injective f)
    {σ τ : Equiv.Perm (Fin a)}
    (hσ : StrictMono (fun j => f (σ j))) (hτ : StrictMono (fun j => f (τ j))) :
    σ = τ :=
  (exists_unique_sortingPerm f hf).unique hσ hτ

/-- Two continuous functions without coincidences on a connected set keep
the same strict order throughout that set. -/
theorem lt_iff_of_continuousOn_ne_on_preconnected
    {f g : ℝ → ℝ} {J : Set ℝ} (hJ : IsPreconnected J)
    (hf : ContinuousOn f J) (hg : ContinuousOn g J)
    (hne : ∀ θ ∈ J, f θ ≠ g θ) {θ φ : ℝ} (hθ : θ ∈ J) (hφ : φ ∈ J) :
    f θ < g θ ↔ f φ < g φ := by
  constructor
  · intro h
    by_contra h'
    obtain ⟨t, ht, heq⟩ := hJ.intermediate_value₂ hθ hφ hf hg h.le (le_of_not_gt h')
    exact hne t ht heq
  · intro h
    by_contra h'
    obtain ⟨t, ht, heq⟩ := hJ.intermediate_value₂ hφ hθ hf hg h.le (le_of_not_gt h')
    exact hne t ht heq

/-- The real coordinate of each labelled sheet in a fixed projection. -/
def planeBranchBraidProjection (F : ℂ → Source 2) (i : Fin 2) (a : ℕ)
    (r : ℝ) (c : ℂ) (θ : ℝ) (k : Fin a) : ℝ :=
  (c * planeBranchBraidSheet F i a r k θ).re

theorem planeBranchBraidProjection_continuous
    {F : ℂ → Source 2} {R : ℝ} (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (i : Fin 2) (a : ℕ) {r : ℝ} (hr : 0 < r) (hrR : r < R) (c : ℂ) (k : Fin a) :
    Continuous (fun θ => planeBranchBraidProjection F i a r c θ k) := by
  have hparam : Continuous (planeBranchBraidParameter a r k) :=
    (continuous_iff_continuousAt.mpr fun θ =>
      (planeBranchAngularParameter_hasDerivAt a r θ).continuousAt).comp
        (continuous_id.add continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hz : planeBranchBraidParameter a r k θ ∈ ball 0 R := by
    simpa only [mem_ball, dist_zero_right, planeBranchBraidParameter_norm,
      abs_of_pos hr] using hrR
  have hc := (continuous_apply i.rev).continuousAt.comp
    ((hF _ hz).continuousAt.comp hparam.continuousAt)
  exact Complex.continuous_re.continuousAt.comp (hc.const_mul c)

theorem planeBranchBraidProjection_injective_of_not_mem_event
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (c : ℂ) {u v θ : ℝ}
    (hθ : θ ∈ Icc u v)
    (hne : θ ∉ planeBranchProjectedCrossingTimes F i a r c u v) :
    Function.Injective (planeBranchBraidProjection F i a r c θ) := by
  intro k l h
  by_contra hkl
  apply hne
  exact (mem_planeBranchProjectedCrossingTimes_iff F i a r c u v θ).mpr
    ⟨hθ, k, l, hkl, h⟩

/-- Strict pairwise order is constant on any open interval avoiding the
finite event set for the actual analytic sheets. -/
theorem planeBranchBraidProjection_lt_iff_on_chamber
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R)) {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (c : ℂ) {b d u v : ℝ} (E : Finset ℝ)
    (hE : ∀ θ, θ ∈ E ↔ θ ∈ planeBranchProjectedCrossingTimes F i a r c b d)
    (hsub : Ioo u v ⊆ Icc b d) (hfree : ∀ θ ∈ Ioo u v, θ ∉ E)
    {θ φ : ℝ} (hθ : θ ∈ Ioo u v) (hφ : φ ∈ Ioo u v) (k l : Fin a) :
    planeBranchBraidProjection F i a r c θ k < planeBranchBraidProjection F i a r c θ l ↔
      planeBranchBraidProjection F i a r c φ k < planeBranchBraidProjection F i a r c φ l := by
  by_cases hkl : k = l
  · simp only [hkl, lt_self_iff_false]
  · apply lt_iff_of_continuousOn_ne_on_preconnected isPreconnected_Ioo
      (planeBranchBraidProjection_continuous hF i a hr hrR c k).continuousOn
      (planeBranchBraidProjection_continuous hF i a hr hrR c l).continuousOn _ hθ hφ
    intro t ht heq
    have hinj := planeBranchBraidProjection_injective_of_not_mem_event F i a r c (hsub ht)
      (fun he => hfree t ht ((hE t).mpr he))
    exact hkl (hinj heq)

/-- Every nonempty event-free interval has one sorting permutation valid
at every angle of that interval. -/
theorem exists_unique_planeBranchBraid_chamber_sortingPerm
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R)) {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (c : ℂ) {b d u v : ℝ} (E : Finset ℝ)
    (hE : ∀ θ, θ ∈ E ↔ θ ∈ planeBranchProjectedCrossingTimes F i a r c b d)
    (hsub : Ioo u v ⊆ Icc b d) (hfree : ∀ θ ∈ Ioo u v, θ ∉ E) (huv : u < v) :
    ∃! σ : Equiv.Perm (Fin a), ∀ θ ∈ Ioo u v,
      StrictMono (fun j => planeBranchBraidProjection F i a r c θ (σ j)) := by
  have hm : (u + v) / 2 ∈ Ioo u v := by constructor <;> linarith
  have hinj := planeBranchBraidProjection_injective_of_not_mem_event F i a r c (hsub hm)
    (fun he => hfree _ hm ((hE _).mpr he))
  obtain ⟨σ, hσ, hu⟩ := exists_unique_sortingPerm
    (planeBranchBraidProjection F i a r c ((u + v) / 2)) hinj
  refine ⟨σ, ?_, ?_⟩
  · intro θ hθ j k hjk
    exact (planeBranchBraidProjection_lt_iff_on_chamber hF hr hrR c E hE hsub hfree
      hm hθ (σ j) (σ k)).mp (hσ hjk)
  · intro τ hτ
    exact hu τ (hτ _ hm)

/-- The sorting permutations at two regular sample angles in one chamber
agree. The sample angles may be endpoints of a smaller closed interval. -/
theorem planeBranchBraid_chamber_sortingPerm_eq
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R)) {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (c : ℂ) {b d u v : ℝ} (E : Finset ℝ)
    (hE : ∀ θ, θ ∈ E ↔ θ ∈ planeBranchProjectedCrossingTimes F i a r c b d)
    (hsub : Ioo u v ⊆ Icc b d) (hfree : ∀ θ ∈ Ioo u v, θ ∉ E)
    {θ φ : ℝ} (hθ : θ ∈ Ioo u v) (hφ : φ ∈ Ioo u v)
    {σ τ : Equiv.Perm (Fin a)}
    (hσ : StrictMono (fun j => planeBranchBraidProjection F i a r c θ (σ j)))
    (hτ : StrictMono (fun j => planeBranchBraidProjection F i a r c φ (τ j))) :
    σ = τ := by
  have hinj := planeBranchBraidProjection_injective_of_not_mem_event F i a r c (hsub hφ)
    (fun he => hfree _ hφ ((hE _).mpr he))
  apply sortingPerm_unique hinj _ hτ
  intro j k hjk
  exact (planeBranchBraidProjection_lt_iff_on_chamber hF hr hrR c E hE hsub hfree
    hθ hφ (σ j) (σ k)).mp (hσ hjk)

/-- Any finite collection of regular sample angles has a unique collection
of sorting permutations. No strict order at an event time is requested. -/
theorem exists_unique_planeBranchBraid_sample_permutations
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (c : ℂ)
    {b d : ℝ} (E : Finset ℝ)
    (hE : ∀ θ, θ ∈ E ↔ θ ∈ planeBranchProjectedCrossingTimes F i a r c b d)
    {N : ℕ} (sample : Fin N → ℝ)
    (hsample : ∀ j, sample j ∈ Icc b d ∧ sample j ∉ E) :
    ∃! σ : Fin N → Equiv.Perm (Fin a), ∀ j,
      StrictMono (fun k => planeBranchBraidProjection F i a r c (sample j) (σ j k)) := by
  have hsort (j : Fin N) : ∃! σ : Equiv.Perm (Fin a),
      StrictMono (fun k => planeBranchBraidProjection F i a r c (sample j) (σ k)) := by
    apply exists_unique_sortingPerm
    exact planeBranchBraidProjection_injective_of_not_mem_event F i a r c (hsample j).1
      (fun he => (hsample j).2 ((hE _).mpr he))
  choose σ hσ huniq using hsort
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  funext j
  exact huniq j (τ j) (hτ j)

end OnLeConjecture.Analytic
