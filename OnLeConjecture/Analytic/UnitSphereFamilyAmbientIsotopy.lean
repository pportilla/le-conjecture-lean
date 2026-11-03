/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.UnitSphereFamilyIsotopy
public import OnLeConjecture.DifferentialTopology.CompactMotionVelocity
public import OnLeConjecture.DifferentialTopology.SmoothEvolution

/-!
# Ambient isotopy between slices of a smooth sphere family

A smooth transition makes the given motion stationary outside the unit
time interval. Its velocity is extended from the embedded track, projected
tangent to the sphere, and integrated using the constructed global flow.
The resulting ambient isotopy carries the initial embedding pointwise to
the final embedding.
-/

public noncomputable section

open Set Manifold OnLeConjecture.DifferentialTopology
open scoped Topology ContDiff Manifold

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [IsManifold I ∞ M] [CompactSpace M] {δ : ℝ} (K : M × ℝ → E)
  (hnorm : ∀ c ∈ Ioo 0 δ, ∀ x, ‖K (x, c)‖ = 1)
  (hsmooth : ∀ c ∈ Ioo 0 δ, ∀ x, ContMDiffAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ K (x, c))
  (hd : ∀ c ∈ Ioo 0 δ, ∀ x,
    Function.Injective (mfderiv I 𝓘(ℝ, E) (fun y => K (y, c)) x))
  (he : ∀ c ∈ Ioo 0 δ, Topology.IsEmbedding (fun x => K (x, c)))

/-- Any two slices of the smooth family are related by an actual ambient
isotopy of the unit sphere, constructed from the motion's velocity. -/
theorem exists_unitSphereFamilyDiffeotopy (c₀ c₁ : ℝ)
    (h₀ : c₀ ∈ Ioo 0 δ) (h₁ : c₁ ∈ Ioo 0 δ) :
    ∃ Φ : TauCeti.Diffeotopy (𝓡 n) ∞ (Metric.sphere (0 : E) 1), ∀ x,
      Φ.final (unitSphereFamilySlice (n := n) K hnorm hsmooth hd he c₀ h₀ x) =
        unitSphereFamilySlice (n := n) K hnorm hsmooth hd he c₁ h₁ x := by
  let level : ℝ → ℝ := fun t => c₀ + Real.smoothTransition t * (c₁ - c₀)
  have hlevel (t : ℝ) : level t ∈ Ioo 0 δ := affine_level_mem_Ioo h₀ h₁
    ⟨Real.smoothTransition t, Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hls : ContDiff ℝ ∞ level := by fun_prop
  let G : ℝ × M → E := fun p => K (p.2, level p.1)
  have hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G := by
    intro p
    exact (hsmooth _ (hlevel p.1) p.2).comp p
      (contMDiffAt_snd.prodMk (hls.contMDiff.contMDiffAt.comp p contMDiffAt_fst))
  have hGi : ∀ t, Function.Injective (fun x => G (t, x)) :=
    fun t => (he _ (hlevel t)).injective
  have hGd : ∀ t x, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun y => G (t, y)) x) :=
    fun t x => hd _ (hlevel t) x
  have ha : ∀ t ≤ 0, ∀ x, G (t, x) = G (0, x) := by
    intro t ht x
    simp only [G, level, Real.smoothTransition.zero_of_nonpos ht, Real.smoothTransition.zero]
  have hb : ∀ t, 1 ≤ t → ∀ x, G (t, x) = G (1, x) := by
    intro t ht x
    simp only [G, level, Real.smoothTransition.one_of_one_le ht, Real.smoothTransition.one]
  obtain ⟨X, hX, hcX, hderiv⟩ := exists_compact_motion_velocity hG hGi hGd ha hb
  obtain ⟨Φ, hΦ⟩ := exists_sphereDiffeotopy_of_velocity_extension
    (n := n) hX hcX (fun t x => G (t, x))
    (fun t x => hnorm _ (hlevel t) x) hderiv
  refine ⟨Φ, fun x => Subtype.ext ?_⟩
  have h := hΦ 1 x
  simpa [TauCeti.Diffeotopy.final_apply, unitSphereFamilySlice,
    Set.codRestrict, G, level] using h

/-- Forgetting the smooth structure of the constructed diffeotopy gives
an ambient isotopy with the same endpoint transport. -/
theorem exists_unitSphereFamilyAmbientIsotopy (c₀ c₁ : ℝ)
    (h₀ : c₀ ∈ Ioo 0 δ) (h₁ : c₁ ∈ Ioo 0 δ) :
    ∃ Φ : TauCeti.AmbientIsotopy (Metric.sphere (0 : E) 1), ∀ x,
      Φ.final (unitSphereFamilySlice (n := n) K hnorm hsmooth hd he c₀ h₀ x) =
        unitSphereFamilySlice (n := n) K hnorm hsmooth hd he c₁ h₁ x := by
  obtain ⟨Φ, hΦ⟩ := exists_unitSphereFamilyDiffeotopy (n := n) K hnorm hsmooth hd he c₀ c₁ h₀ h₁
  exact ⟨Φ.toAmbientIsotopy, fun x => (Φ.toAmbientIsotopy_final_apply _).trans (hΦ x)⟩

end OnLeConjecture.Analytic
