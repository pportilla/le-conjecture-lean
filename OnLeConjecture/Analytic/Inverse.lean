/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Equivalence
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# The analytic inverse function theorem for pointed germs

An analytic self map whose differential at the origin is a continuous linear
equivalence determines an invertible pointed analytic germ.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- An analytic self map that fixes the origin and has invertible differential
determines a pointed analytic equivalence germ. -/
theorem exists_pointedEquivGerm_of_fderiv_eq {n : ℕ}
    (f : Source n → Source n) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (i : Source n ≃L[ℂ] Source n)
    (hfi : fderiv ℂ f 0 = (i : Source n →L[ℂ] Source n)) :
    ∃ e : PointedEquivGerm n,
      e.forward = PointedMapGerm.ofFunction f hf hf0 := by
  have hstrict :
      HasStrictFDerivAt f (i : Source n →L[ℂ] Source n) 0 := by
    simpa only [hfi] using hf.hasStrictFDerivAt
  let R : OpenPartialHomeomorph (Source n) (Source n) :=
    hstrict.toOpenPartialHomeomorph f
  have hzeroSource : (0 : Source n) ∈ R.source :=
    hstrict.mem_toOpenPartialHomeomorph_source
  have hzeroTarget : (0 : Source n) ∈ R.target := by
    simpa only [R, hf0] using hstrict.image_mem_toOpenPartialHomeomorph_target
  have hRanalytic : AnalyticAt ℂ R.symm 0 := by
    have h := R.analyticAt_symm' hzeroSource hf hfi
    have hRapply : R 0 = 0 := by
      change f 0 = 0
      exact hf0
    rw [hRapply] at h
    exact h
  have hRzero : R.symm 0 = 0 := by
    have h := R.left_inv hzeroSource
    have hRapply : R 0 = 0 := by
      change f 0 = 0
      exact hf0
    rw [hRapply] at h
    exact h
  let forward : PointedMapGerm n n :=
    PointedMapGerm.ofFunction f hf hf0
  let inverse : PointedMapGerm n n :=
    PointedMapGerm.ofFunction R.symm hRanalytic hRzero
  have hforwardInverse :
      forward.comp inverse = PointedMapGerm.identity n := by
    dsimp only [forward, inverse]
    rw [PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [R.open_target.mem_nhds hzeroTarget] with y hy
    exact R.right_inv hy
  have hinverseForward :
      inverse.comp forward = PointedMapGerm.identity n := by
    dsimp only [forward, inverse]
    rw [PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [R.open_source.mem_nhds hzeroSource] with x hx
    exact R.left_inv hx
  let e : PointedEquivGerm n :=
    {
      forward := forward
      inverse := inverse
      forward_inverse := hforwardInverse
      inverse_forward := hinverseForward
    }
  exact ⟨e, rfl⟩

/-- A pointed analytic self map germ whose differential is a continuous linear
equivalence is an invertible pointed germ. -/
theorem PointedMapGerm.exists_pointedEquivGerm_of_differential_eq {n : ℕ}
    (f : PointedMapGerm n n) (i : Source n ≃L[ℂ] Source n)
    (hfi : f.differential = (i : Source n →L[ℂ] Source n)) :
    ∃ e : PointedEquivGerm n, e.forward = f := by
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      rw [isAnalyticMapGerm_ofFun] at hf
      change f 0 = 0 at hf0
      change fderiv ℂ f 0 = (i : Source n →L[ℂ] Source n) at hfi
      obtain ⟨e, he⟩ :=
        exists_pointedEquivGerm_of_fderiv_eq f hf hf0 i hfi
      refine ⟨e, ?_⟩
      rw [he]
      rfl

/-- A pointed analytic self map germ with bijective differential is the
forward map of an invertible pointed analytic germ. -/
theorem PointedMapGerm.exists_pointedEquivGerm_of_differential_bijective
    {n : ℕ} (f : PointedMapGerm n n)
    (hfi : Function.Bijective f.differential) :
    ∃ e : PointedEquivGerm n, e.forward = f := by
  let i : Source n ≃L[ℂ] Source n :=
    ContinuousLinearEquiv.ofBijective f.differential
      (LinearMap.ker_eq_bot.mpr hfi.1)
      (LinearMap.range_eq_top.mpr hfi.2)
  exact f.exists_pointedEquivGerm_of_differential_eq i rfl

end OnLeConjecture.Analytic
