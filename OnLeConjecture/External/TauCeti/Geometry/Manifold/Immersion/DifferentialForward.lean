/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import OnLeConjecture.External.TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Immersion normal forms from an injective differential

Selective port of the Euclidean forward implication in TauCeti
`Geometry/Manifold/Immersion/Differential.lean`, commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`.
The retained proof constructs actual charts using a closed complement and
the smooth inverse function theorem. The finite-dimensional corollary uses
Mathlib's continuous linear left inverse theorem.
-/

public noncomputable section

open Set Function Topology Manifold
open scoped ContDiff Manifold

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {n : ℕ∞ω} {f : E → F} {s : Set E} {x : E}

/-- A smooth map with a split differential has actual immersion charts. -/
theorem ContDiffOn.isImmersionAt_of_hasLeftInverse
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hdf : (fderiv 𝕜 f x).HasLeftInverse) :
    IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f x := by
  -- Adjoin the closed complement so that the augmented derivative is invertible.
  let G := hdf.complement
  have : CompleteSpace G := hdf.isClosed_complement.completeSpace_coe
  let e : (E × G) ≃L[𝕜] F :=
    (fderiv 𝕜 f x).coprodSubtypeLEquivOfIsCompl hdf.isCompl_complement
      (LinearMap.ker_eq_bot.mpr hdf.injective)
  let g : E × G → F := fun p => f p.1 + (p.2 : F)
  let t : Set (E × G) := Prod.fst ⁻¹' s
  have ht : IsOpen t := hs.preimage continuous_fst
  have hg : ContDiffOn 𝕜 n g t :=
    (hf.comp contDiffOn_fst (fun _ hp => hp)).add
      (G.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hderiv : HasFDerivAt g (e : (E × G) →L[𝕜] F) (x, 0) := by
    convert! (((hf.contDiffAt (hs.mem_nhds hx)).differentiableAt hn0).hasFDerivAt.comp
      (x, (0 : G)) (hasFDerivAt_fst)).add
      (G.subtypeL.hasFDerivAt.comp (x, 0) (hasFDerivAt_snd)) using 1
  obtain ⟨Θ, hΘ, hxΘ, hsub, hinv⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hg ht hx hn hderiv.fderiv.symm
  have hforward : ContDiffOn 𝕜 n Θ Θ.source := hΘ ▸ hg.mono hsub
  -- The inverse chart straightens the image; the source chart restricts the identity.
  let ψ := Θ.symm.transHomeomorph e.toHomeomorph
  let u : Set E := (fun y => (y, (0 : G))) ⁻¹' Θ.source
  have hu : IsOpen u := Θ.open_source.preimage (continuous_id.prodMk continuous_const)
  let φ := (OpenPartialHomeomorph.refl E).restrOpen u hu
  have hφsource : φ.source = u := by simp [φ]
  have hφtarget : (φ.extend 𝓘(𝕜, E)).target = u := by simp [φ, mfld_simps]
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) n F := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiffOn_iff_contDiffOn.mpr (e.contDiff.comp_contDiffOn hinv)
    · exact contMDiffOn_iff_contDiffOn.mpr
        (hforward.comp e.symm.contDiff.contDiffOn (fun _ hy => hy))
  refine IsImmersionAt.mk_of_charts e φ ψ (hφsource.symm ▸ hxΘ) ?_
    (φ.mem_maximalAtlas_of_contMDiffOn contMDiffOn_id contMDiffOn_id) hψ ?_ ?_
  · have h := Θ.map_source hxΘ
    simpa [ψ, hΘ, g] using h
  · intro y hy
    have h := Θ.map_source (hφsource ▸ hy)
    simpa [φ, ψ, hΘ, g] using h
  · intro y hy
    have h := Θ.left_inv (hφtarget ▸ hy)
    simpa [φ, ψ, hΘ, g, mfld_simps] using congrArg e h


/-- In finite-dimensional target spaces an injective differential supplies
the required splitting and hence the immersion normal form. -/
theorem ContDiffOn.isImmersionAt_of_injective_fderiv [FiniteDimensional 𝕜 F]
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hdf : Function.Injective (fderiv 𝕜 f x)) :
    IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f x :=
  hf.isImmersionAt_of_hasLeftInverse hs hx hn
    (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hdf)

end

