/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Immersion.DifferentialForward
public import OnLeConjecture.External.TauCeti.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Immersion charts on boundaryless manifolds

Selective forward implications from TauCeti's immersion differential
criterion at commit `eb4dd2412a1cd62f73128361bfd3cb422df32e37`.
The chart transport and splitting argument retain their original proofs.
The finite-dimensional corollary uses Mathlib's continuous linear splitting.
-/

public noncomputable section

open Set Function Topology Manifold
open scoped ContDiff Manifold

namespace Manifold.IsImmersionAtOfComplement

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- An immersion normal form of a map between boundaryless manifolds, read in the preferred
extended charts, is an immersion normal form of the map itself, with the same complement. -/
theorem of_writtenInExtChartAt [I.Boundaryless] [J.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] (hf : ContinuousAt f x)
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n (writtenInExtChartAt I J x f)
      (extChartAt I x x)) :
    IsImmersionAtOfComplement F I J n f x := by
  -- The charts of the normal form in the model spaces, read through the preferred charts.
  let φ : OpenPartialHomeomorph M H :=
    (((chartAt H x).transHomeomorph I.toHomeomorph).trans h.domChart).transHomeomorph
      I.toHomeomorph.symm
  let ψ : OpenPartialHomeomorph N G :=
    (((chartAt G (f x)).transHomeomorph J.toHomeomorph).trans h.codChart).transHomeomorph
      J.toHomeomorph.symm
  refine mk_of_continuousAt hf h.equiv φ ψ ?_ ?_ ?_ ?_ ?_
  · simpa [φ] using h.mem_domChart_source
  · simpa [ψ, writtenInExtChartAt] using h.mem_codChart_source
  · exact TauCeti.conj_chartAt_mem_maximalAtlas x h.domChart_mem_maximalAtlas
  · exact TauCeti.conj_chartAt_mem_maximalAtlas (f x) h.codChart_mem_maximalAtlas
  · intro u hu
    have hI : ∀ u, I (I.symm u) = u := fun u => I.right_inv (by simp [I.range_eq_univ])
    have hJ : ∀ u, J (J.symm u) = u := fun u => J.right_inv (by simp [J.range_eq_univ])
    have k1 : (φ.extend I).symm u = (chartAt H x).symm (I.symm (h.domChart.symm u)) := by
      simp [φ, hI, OpenPartialHomeomorph.extend]
    have k2 : ∀ z, ψ.extend J z = h.codChart (J (chartAt G (f x) z)) := by
      intro z
      simp [ψ, hJ, OpenPartialHomeomorph.extend]
    have hu' : (∃ y, I y = u) ∧ u ∈ h.domChart.target ∧
        I.symm (h.domChart.symm u) ∈ (chartAt H x).target := by
      simpa [φ, hI, OpenPartialHomeomorph.extend] using hu
    have := h.writtenInCharts (by simpa [OpenPartialHomeomorph.extend] using hu'.2.1)
    simp only [Function.comp_apply, k1, k2] at this ⊢
    simpa [OpenPartialHomeomorph.extend, writtenInExtChartAt, extChartAt] using this

end Manifold.IsImmersionAtOfComplement

section Manifold

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M} {x : M}

/-- A `C^n` map on an open subset of a boundaryless manifold, with values in a boundaryless
manifold, is an immersion at any point where its manifold derivative admits a continuous linear
left inverse. -/
theorem ContMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv
    (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hdf : (mfderiv I J f x).HasLeftInverse) :
    IsImmersionAt I J n f x := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hfx : ContMDiffAt I J n f x := hf.contMDiffAt (hs.mem_nhds hx)
  -- Read `f` in the preferred extended charts, on an open set around the chart image of `x`.
  let t := (extChartAt I x).target ∩
    (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt J (f x)).source)
  have ht : IsOpen t :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      (hf.continuousOn.isOpen_inter_preimage hs (isOpen_extChartAt_source (f x)))
  have hxt : extChartAt I x x ∈ t := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    simp [hx]
  have hft : ContDiffOn 𝕜 n (writtenInExtChartAt I J x f) t :=
    (contMDiffOn_iff.mp hf).2 x (f x)
  -- On a boundaryless model the manifold derivative is literally the derivative in charts.
  have hderiv : fderiv 𝕜 (writtenInExtChartAt I J x f) (extChartAt I x x) =
      mfderiv I J f x := by
    simp only [mfderiv, hfx.mdifferentiableAt hn0, I.range_eq_univ, fderivWithin_univ]
    rfl
  have h := hft.isImmersionAt_of_hasLeftInverse ht hxt hn (hderiv ▸ hdf)
  exact (IsImmersionAtOfComplement.of_writtenInExtChartAt hfx.continuousAt
    h.isImmersionAtOfComplement_complement).isImmersionAt


/-- An injective manifold differential gives actual immersion charts when
the target model is finite dimensional. -/
theorem ContMDiffOn.isImmersionAt_of_injective_mfderiv [FiniteDimensional 𝕜 E']
    (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hdf : Function.Injective (mfderiv I J f x)) : IsImmersionAt I J n f x :=
  hf.isImmersionAt_of_hasLeftInverse_mfderiv hs hx hn
    (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
      (f := (show E →L[𝕜] E' from mfderiv I J f x)) hdf)

end Manifold
end

