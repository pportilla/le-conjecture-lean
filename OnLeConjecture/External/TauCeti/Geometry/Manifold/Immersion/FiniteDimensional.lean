/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Immersion.ManifoldDifferentialForward
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# A common complement for immersions into finite dimensions

Selective port of TauCeti's complement comparison from
`Analysis/Normed/Module/FiniteDimension.lean` and the pointwise immersion
criterion from `Geometry/Manifold/Immersion/Basic.lean`, both at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`. The final corollaries combine
these with the differential criterion in the preceding module.
-/

public noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti

/-- Two complements of the same space in a finite-dimensional space are
continuously linearly equivalent. -/
theorem nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {V W F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [AddCommGroup V] [TopologicalSpace V] [Module 𝕜 V]
    [AddCommGroup W] [TopologicalSpace W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (e : (V × F) ≃L[𝕜] W) (e' : (V × F') ≃L[𝕜] W) : Nonempty (F ≃L[𝕜] F') := by
  have : FiniteDimensional 𝕜 (V × F) := e.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 (V × F') := e'.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 F :=
    .of_injective (LinearMap.inr 𝕜 V F) LinearMap.inr_injective
  have : FiniteDimensional 𝕜 F' :=
    .of_injective (LinearMap.inr 𝕜 V F') LinearMap.inr_injective
  have : FiniteDimensional 𝕜 V :=
    .of_injective (LinearMap.inl 𝕜 V F) LinearMap.inl_injective
  apply FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
  have h := e.toLinearEquiv.finrank_eq.trans e'.toLinearEquiv.finrank_eq.symm
  rw [Module.finrank_prod, Module.finrank_prod] at h
  omega

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- The immersion complements can be chosen uniformly for a
finite-dimensional target model. -/
theorem isImmersion_iff_forall_isImmersionAt :
    IsImmersion I J n f ↔ ∀ x, IsImmersionAt I J n f x := by
  refine ⟨fun h x => h.isImmersionAt x, fun h => ?_⟩
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact IsImmersionOfComplement.isImmersion (F := E') fun x => isEmptyElim x
  refine IsImmersionOfComplement.isImmersion (F := (h x₀).complement) fun x => ?_
  obtain ⟨e⟩ := nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv
    (h x).isImmersionAtOfComplement_complement.equiv
    (h x₀).isImmersionAtOfComplement_complement.equiv
  exact (h x).isImmersionAtOfComplement_complement.trans_F e

end TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E'] [FiniteDimensional 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
  {f : M → N}

/-- A smooth map with injective differential is an immersion into a
finite-dimensional boundaryless target. -/
theorem ContMDiff.isImmersion_of_injective_mfderiv
    (hf : ContMDiff I J n f) (hn : 1 ≤ n)
    (hdf : ∀ x, Function.Injective (mfderiv I J f x)) : IsImmersion I J n f := by
  apply TauCeti.isImmersion_iff_forall_isImmersionAt.mpr
  intro x
  exact hf.contMDiffOn.isImmersionAt_of_injective_mfderiv isOpen_univ (Set.mem_univ x) hn (hdf x)

/-- Smoothness, an injective differential, and a topological embedding
give the native smooth embedding predicate. -/
theorem ContMDiff.isSmoothEmbedding_of_injective_mfderiv
    (hf : ContMDiff I J n f) (hn : 1 ≤ n)
    (hdf : ∀ x, Function.Injective (mfderiv I J f x))
    (hemb : Topology.IsEmbedding f) : IsSmoothEmbedding I J n f :=
  ⟨hf.isImmersion_of_injective_mfderiv hn hdf, hemb⟩

end
