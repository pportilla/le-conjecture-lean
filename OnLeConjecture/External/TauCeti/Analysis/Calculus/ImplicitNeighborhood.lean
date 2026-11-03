/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import OnLeConjecture.External.TauCeti.Analysis.Calculus.InverseFunctionTheorem
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth implicit functions on an open parameter neighborhood

This selective port retains the open-neighborhood theorem for product domains.

Source: https://github.com/TauCetiProject/TauCeti/blob/eb4dd2412a1cd62f73128361bfd3cb422df32e37/TauCeti/Analysis/Calculus/ImplicitFunctionTheorem.lean
Retrieved 2026-10-29. Retain only ContDiffOn.exists_isOpen_contDiffOn_implicitFunction and its
variables. Omit complemented-kernel and slice-chart sections. Proof unchanged.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace ContDiffOn

variable {𝕜 E₁ E₂ F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- A `C^n` equation on an open subset of a product whose derivative in the second variable is
invertible has an implicit function which is `C^n` on one open neighbourhood of the base parameter.

Mathlib proves smoothness at the base point. The local inverse used in that proof is smooth on its
whole open target, so restricting that target to the slice through the equation value gives a
single neighbourhood on which the implicit function is smooth. This distinction matters at
infinite regularity, where pointwise smoothness need not provide one neighbourhood valid for all
finite orders. -/
theorem exists_isOpen_contDiffOn_implicitFunction {u : E₁ × E₂} {f : E₁ × E₂ → F}
    {s : Set (E₁ × E₂)} {n : ℕ∞ω} (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hu : u ∈ s) (hn : n ≠ 0)
    (hi : (fderiv 𝕜 f u ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible) :
    ∃ U : Set E₁, IsOpen U ∧ u.1 ∈ U ∧
      ContDiffOn 𝕜 n ((hf.contDiffAt (hs.mem_nhds hu)).implicitFunction hn hi) U := by
  let hfu : ContDiffAt 𝕜 n f u := hf.contDiffAt (hs.mem_nhds hu)
  let hstrict := hfu.hasStrictFDerivAt hn
  let φ := hstrict.implicitFunctionDataOfProdDomain hi
  let e₀ := φ.hasStrictFDerivAt.toOpenPartialHomeomorph φ.prodFun
  let e := e₀.restrOpen s hs
  let U : Set E₁ := (fun x ↦ (f u, x)) ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hue : u ∈ e.source := by
    -- Restricting `e₀` to `s` replaces its source by `e₀.source ∩ s`.
    change u ∈ e₀.source ∩ s
    refine ⟨?_, hu⟩
    simpa only [e₀, φ, HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain] using
      φ.hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
  have huU : u.1 ∈ U := by
    -- Membership in `U` unfolds to membership of the corresponding slice point in `e.target`.
    change (f u, u.1) ∈ e.target
    simpa only [e, OpenPartialHomeomorph.coe_restrOpen, e₀, φ,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe, ImplicitFunctionData.prodFun_apply,
      HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
      HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain,
      HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain] using e.map_source hue
  have hinv : ContDiffOn 𝕜 n e.symm e.target := by
    intro y hy
    have hxe : e.symm y ∈ e.source := e.map_target hy
    have hxe₀ : e.symm y ∈ e₀.source := hxe.1
    have hxS : e.symm y ∈ s := hxe.2
    have hy₀ : y ∈ e₀.target := by
      rw [← e.right_inv hy]
      exact e₀.map_source hxe₀
    have hprodAt : ContDiffAt 𝕜 n φ.prodFun (e₀.symm y) := by
      have hfAt : ContDiffAt 𝕜 n f (e₀.symm y) := by
        apply hf.contDiffAt (hs.mem_nhds ?_)
        simpa only [e, OpenPartialHomeomorph.coe_restrOpen_symm] using hxS
      convert hfAt.prodMk contDiffAt_fst using 1
      funext x
      simp only [ImplicitFunctionData.prodFun_apply, φ,
        HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
        HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain]
    have hiAt : ContDiffAt 𝕜 n e₀.symm y :=
      φ.hasStrictFDerivAt.contDiffAt_toOpenPartialHomeomorph_symm hy₀ hprodAt
    simpa only [e, OpenPartialHomeomorph.coe_restrOpen_symm] using hiAt.contDiffWithinAt
  refine ⟨U, hU, huU, ?_⟩
  have hcomp : ContDiffOn 𝕜 n (fun x ↦ (e.symm (f u, x)).2) U :=
    (hinv.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hx ↦ hx).snd
  simpa only [hfu, hstrict, φ, e₀, e, U, ContDiffAt.implicitFunction_def,
    HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
    ImplicitFunctionData.implicitFunction_def, Function.curry_apply,
    OpenPartialHomeomorph.coe_restrOpen_symm] using hcomp

end ContDiffOn
