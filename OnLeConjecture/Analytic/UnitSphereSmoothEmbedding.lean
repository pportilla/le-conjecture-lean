/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Immersion.FiniteDimensional
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smooth embeddings with image on the unit sphere

An ambient smooth map with injective differential and embedded image
remains a smooth embedding when its codomain is restricted to the unit
sphere. The chain rule transfers differential injectivity to the sphere.
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
  [IsManifold I ∞ M] {f : M → E}

/-- Restricting a smooth ambient embedding to the unit sphere preserves
the native smooth-embedding predicate. -/
theorem isSmoothEmbedding_codRestrict_unit_sphere
    (hf : ContMDiff I 𝓘(ℝ, E) ∞ f)
    (hmem : ∀ x, f x ∈ Metric.sphere (0 : E) 1)
    (hd : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) f x))
    (he : Topology.IsEmbedding f) :
    IsSmoothEmbedding I (𝓡 n) ∞ (Set.codRestrict f (Metric.sphere (0 : E) 1) hmem) := by
  have hs := hf.codRestrict_sphere (n := n) hmem
  apply hs.isSmoothEmbedding_of_injective_mfderiv (by simp)
  · intro x v w hvw
    apply hd x
    have hcoe := (contMDiff_coe_sphere (E := E) (n := n) (m := ∞)).mdifferentiableAt
      (by simp) (x := Set.codRestrict f (Metric.sphere (0 : E) 1) hmem x)
    have hx := hs.mdifferentiableAt (by simp) (x := x)
    have hchain := mfderiv_comp x hcoe hx
    change mfderiv I 𝓘(ℝ, E) f x = _ at hchain
    rw [hchain]
    exact congrArg (mfderiv (𝓡 n) 𝓘(ℝ, E)
      (Subtype.val : Metric.sphere (0 : E) 1 → E) _) hvw
  · exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp he

end OnLeConjecture.Analytic
