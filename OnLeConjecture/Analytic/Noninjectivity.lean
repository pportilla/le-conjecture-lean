/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MapGerm
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Local noninjectivity of analytic map germs

An analytic representative that is not injective on any neighborhood of the
origin cannot represent a germ with an injective representative. Eventual
equality transfers injectivity between representatives.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Set
open scoped Topology

/-- If an analytic function is not injective on any neighborhood of the
origin, then its pointed map germ has no injective representative. -/
theorem PointedMapGerm.not_hasInjectiveRepresentative_ofFunction
    {n m : ℕ} (f : Source n → Source m)
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0)
    (hnot : ¬ ∃ s ∈ 𝓝 (0 : Source n), Set.InjOn f s) :
    ¬ (PointedMapGerm.ofFunction f hf h0).HasInjectiveRepresentative := by
  intro hinjective
  obtain ⟨q, hq, hq0, heq, s, hs, hqInjective⟩ := hinjective
  have hunderlying := congrArg
    (fun g : PointedMapGerm n m => g.1.1) heq
  have heventual : f =ᶠ[𝓝 (0 : Source n)] q := by
    apply Filter.Germ.coe_eq.mp
    simpa only [PointedMapGerm.ofFunction, MapGerm.ofFunction] using hunderlying
  apply hnot
  refine ⟨s ∩ {x | f x = q x}, inter_mem hs heventual, ?_⟩
  intro x hx y hy hfxy
  apply hqInjective hx.1 hy.1
  calc
    q x = f x := hx.2.symm
    _ = f y := hfxy
    _ = q y := hy.2

/-- Noninjectivity on every neighborhood is preserved when a function on a
product is written in the two coordinate function space. -/
theorem not_neighborhood_injective_comp_finTwoArrow
    {m : ℕ} (f : ℂ × ℂ → Source m)
    (hnot : ¬ ∃ s ∈ 𝓝 (0 : ℂ × ℂ), Set.InjOn f s) :
    ¬ ∃ s ∈ 𝓝 (0 : Source 2),
      Set.InjOn
        (fun z => f (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z)) s := by
  intro hinjective
  obtain ⟨s, hs, hsInjective⟩ := hinjective
  let e : Source 2 ≃L[ℂ] ℂ × ℂ :=
    ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  have heZero : e.symm (0 : ℂ × ℂ) = 0 := map_zero e.symm
  have hpre : e.symm ⁻¹' s ∈ 𝓝 (0 : ℂ × ℂ) := by
    have hs' : s ∈ 𝓝 (e.symm (0 : ℂ × ℂ)) := by
      simpa [heZero] using hs
    exact e.symm.continuousAt hs'
  apply hnot
  refine ⟨e.symm ⁻¹' s, hpre, ?_⟩
  intro x hx y hy hfxy
  apply e.symm.injective
  apply hsInjective hx hy
  simpa [e] using hfxy

/-- An analytic function on a product defines a pointed map germ after the
standard identification with the two coordinate function space. -/
@[expose]
noncomputable def PointedMapGerm.ofPairFunction
    {m : ℕ} (f : ℂ × ℂ → Source m)
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) : PointedMapGerm 2 m := by
  change AnalyticAt ℂ f ((0, 0) : ℂ × ℂ) at hf
  change f ((0, 0) : ℂ × ℂ) = 0 at h0
  let e : Source 2 ≃L[ℂ] ℂ × ℂ :=
    ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  have hfAt : AnalyticAt ℂ f (e (0 : Source 2)) := by
    simpa [e] using hf
  have hcomp : AnalyticAt ℂ (fun z => f (e z)) 0 :=
    hfAt.fun_comp (e.toContinuousLinearMap.analyticAt 0)
  have hcompZero : (fun z => f (e z)) 0 = 0 := by
    simpa [e] using h0
  exact PointedMapGerm.ofFunction (fun z => f (e z)) hcomp hcompZero

/-- A function on a product with collisions in every neighborhood defines a
pointed map germ without an injective representative. -/
theorem PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
    {m : ℕ} (f : ℂ × ℂ → Source m)
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0)
    (hnot : ¬ ∃ s ∈ 𝓝 (0 : ℂ × ℂ), Set.InjOn f s) :
    ¬ (PointedMapGerm.ofPairFunction f hf h0).HasInjectiveRepresentative := by
  change f ((0, 0) : ℂ × ℂ) = 0 at h0
  rw [PointedMapGerm.ofPairFunction]
  apply PointedMapGerm.not_hasInjectiveRepresentative_ofFunction
  · simpa using h0
  exact not_neighborhood_injective_comp_finTwoArrow f hnot

end OnLeConjecture.Analytic
