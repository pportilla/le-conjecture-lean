/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.UnitSphereSmoothEmbedding
public import OnLeConjecture.External.TauCeti.Geometry.Manifold.SmoothIsotopy.Basic

/-!
# Smooth isotopies from families on the unit sphere

A jointly smooth family of embedded immersed maps on an open interval
restricts along the affine path between any two levels to a smooth isotopy
through embeddings. The codomain is the fixed unit sphere. No extension
to an ambient isotopy is asserted here.
-/

public noncomputable section

open Manifold Set
open scoped ContDiff Manifold

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [IsManifold I ∞ M] {δ : ℝ} (K : M × ℝ → E)
  (hnorm : ∀ c ∈ Ioo 0 δ, ∀ x, ‖K (x, c)‖ = 1)
  (hsmooth : ∀ c ∈ Ioo 0 δ, ∀ x, ContMDiffAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ K (x, c))
  (hd : ∀ c ∈ Ioo 0 δ, ∀ x,
    Function.Injective (mfderiv I 𝓘(ℝ, E) (fun y => K (y, c)) x))
  (he : ∀ c ∈ Ioo 0 δ, Topology.IsEmbedding (fun x => K (x, c)))

include hsmooth in
omit [CompleteSpace V] [I.Boundaryless] [IsManifold I ∞ M] in
/-- Each slice of a jointly smooth family is smooth. -/
theorem unitSphereFamily_slice_contMDiff {c : ℝ} (hc : c ∈ Ioo 0 δ) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x => K (x, c)) := by
  intro x
  exact (hsmooth c hc x).comp x (contMDiffAt_id.prodMk contMDiffAt_const)

/-- A positive-level slice, bundled as a smooth embedding in the unit sphere. -/
@[expose] def unitSphereFamilySlice (c : ℝ) (hc : c ∈ Ioo 0 δ) :
    TauCeti.SmoothEmbedding I (𝓡 n) ∞ M (Metric.sphere (0 : E) 1) :=
  TauCeti.SmoothEmbedding.ofIsSmoothEmbedding
    (Set.codRestrict (fun x => K (x, c)) (Metric.sphere (0 : E) 1)
      (fun x => by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm c hc x))
    (isSmoothEmbedding_codRestrict_unit_sphere
      (unitSphereFamily_slice_contMDiff K hsmooth hc) _ (hd c hc) (he c hc))

/-- The bundled slice retains the given ambient formula. -/
@[simp] theorem unitSphereFamilySlice_coe_apply (c : ℝ) (hc : c ∈ Ioo 0 δ) (x : M) :
    (unitSphereFamilySlice (n := n) K hnorm hsmooth hd he c hc x : E) = K (x, c) := by
  simp [unitSphereFamilySlice]

/-- The affine path between two positive levels stays in the same open interval. -/
theorem affine_level_mem_Ioo {c₀ c₁ δ : ℝ}
    (h₀ : c₀ ∈ Ioo 0 δ) (h₁ : c₁ ∈ Ioo 0 δ) (t : unitInterval) :
    c₀ + (t : ℝ) * (c₁ - c₀) ∈ Ioo 0 δ := by
  have h := (convex_Ioo (0 : ℝ) δ) h₀ h₁ (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  convert h using 1
  simp only [smul_eq_mul]
  ring

/-- Any two slices of the given family are joined by a smooth isotopy
through embeddings in the unit sphere. -/
def unitSphereFamilySmoothIsotopy (c₀ c₁ : ℝ)
    (h₀ : c₀ ∈ Ioo 0 δ) (h₁ : c₁ ∈ Ioo 0 δ) :
    TauCeti.SmoothIsotopy
      (unitSphereFamilySlice (n := n) K hnorm hsmooth hd he c₀ h₀).toContMDiffMap
      (unitSphereFamilySlice (n := n) K hnorm hsmooth hd he c₁ h₁).toContMDiffMap := by
  let level : unitInterval → ℝ := fun t => c₀ + (t : ℝ) * (c₁ - c₀)
  have hlevel (t : unitInterval) : level t ∈ Ioo 0 δ := affine_level_mem_Ioo h₀ h₁ t
  let motion : unitInterval × M → E := fun p => K (p.2, level p.1)
  have hAff : ContDiff ℝ ∞ (fun t : ℝ => c₀ + t * (c₁ - c₀)) :=
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hlevelSmooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ level :=
    hAff.contMDiff.comp (contMDiff_subtypeVal_Icc (x := 0) (y := 1))
  have hm : ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ, E) ∞ motion := by
    intro p
    exact (hsmooth _ (hlevel p.1) p.2).comp p
      (contMDiffAt_snd.prodMk (hlevelSmooth.contMDiffAt.comp p contMDiffAt_fst))
  have hmem (p : unitInterval × M) : motion p ∈ Metric.sphere (0 : E) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm _ (hlevel p.1) p.2
  refine {
    toContMDiffMap := ⟨Set.codRestrict motion (Metric.sphere (0 : E) 1) hmem,
      hm.codRestrict_sphere (n := n) hmem⟩
    map_zero_left := ?_
    map_one_left := ?_
    isSmoothEmbedding := ?_ }
  · intro x
    apply Subtype.ext
    simp [motion, level, unitSphereFamilySlice]
  · intro x
    apply Subtype.ext
    simp [motion, level, unitSphereFamilySlice]
  · intro t
    convert! (unitSphereFamilySlice (n := n) K hnorm hsmooth hd he _
      (hlevel t)).isSmoothEmbedding using 1
    ext x
    simp [unitSphereFamilySlice, motion]

end OnLeConjecture.Analytic
