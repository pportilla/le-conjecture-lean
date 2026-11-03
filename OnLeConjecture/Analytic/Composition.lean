/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MapGerm
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Composition of pointed analytic map germs

An outer germ at the origin can be composed with an inner germ that maps the
origin to the origin. This file defines that composition and proves the chain
rule for its differential.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- The identity pointed analytic map germ. -/
@[expose] noncomputable def PointedMapGerm.identity (n : ℕ) :
    PointedMapGerm n n :=
  PointedMapGerm.ofFunction id analyticAt_id rfl

@[simp]
theorem PointedMapGerm.differential_identity (n : ℕ) :
    (PointedMapGerm.identity n).differential =
      ContinuousLinearMap.id ℂ (Source n) := by
  exact fderiv_id

/-- An analytic map germ tends to its value at the origin. -/
theorem MapGerm.tendsto_valueAtOrigin {n m : ℕ} (g : MapGerm n m) :
    g.1.Tendsto (𝓝 g.valueAtOrigin) := by
  rcases g with ⟨g, hg⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [Filter.Germ.coe_tendsto]
      rw [isAnalyticMapGerm_ofFun] at hg
      exact hg.continuousAt

/-- A pointed analytic map germ tends to the origin. -/
theorem PointedMapGerm.tendsto_origin {n m : ℕ}
    (g : PointedMapGerm n m) :
    g.1.1.Tendsto (𝓝 (0 : Source m)) := by
  have hnhds : 𝓝 (0 : Source m) = 𝓝 g.1.valueAtOrigin :=
    congrArg 𝓝 g.2.symm
  rw [hnhds]
  exact g.1.tendsto_valueAtOrigin

/-- Composition of an analytic map germ with a pointed analytic map germ. -/
@[expose] noncomputable def MapGerm.compPointed {l n m : ℕ}
    (g : MapGerm n m) (h : PointedMapGerm l n) : MapGerm l m := by
  refine ⟨g.1.compTendsto' h.1.1 h.tendsto_origin, ?_⟩
  rcases g with ⟨g, hg⟩
  rcases h with ⟨⟨h, hh⟩, h0⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      induction h using Filter.Germ.inductionOn with
      | _ k =>
          rw [isAnalyticMapGerm_ofFun] at hg hh
          change k 0 = 0 at h0
          have hkT : Tendsto k (𝓝 0) (𝓝 0) := by
            have hkc := hh.continuousAt
            change Tendsto k (𝓝 0) (𝓝 (k 0)) at hkc
            rw [h0] at hkc
            exact hkc
          change IsAnalyticMapGerm
            ((f : FunctionMapGerm n m).compTendsto'
              (k : FunctionMapGerm l n) hkT.germ_tendsto)
          rw [Filter.Germ.coe_compTendsto']
          rw [Filter.Germ.map_coe]
          rw [isAnalyticMapGerm_ofFun]
          have hgf : AnalyticAt ℂ f (k 0) := by
            simpa only [h0] using hg
          exact hgf.comp hh

@[simp]
theorem MapGerm.compPointed_ofFunction {l n m : ℕ}
    (f : Source n → Source m) (hf : AnalyticAt ℂ f 0)
    (k : Source l → Source n) (hk : AnalyticAt ℂ k 0) (hk0 : k 0 = 0) :
    MapGerm.compPointed (MapGerm.ofFunction f hf)
      (PointedMapGerm.ofFunction k hk hk0) =
        MapGerm.ofFunction (f ∘ k) (by
          have hfk : AnalyticAt ℂ f (k 0) := by simpa only [hk0] using hf
          exact hfk.comp hk) := by
  apply Subtype.ext
  have hkT : Tendsto k (𝓝 0) (𝓝 0) := by
    have hkc := hk.continuousAt
    change Tendsto k (𝓝 0) (𝓝 (k 0)) at hkc
    rw [hk0] at hkc
    exact hkc
  change
    (f : FunctionMapGerm n m).compTendsto'
      (k : FunctionMapGerm l n) hkT.germ_tendsto =
        ((f ∘ k) : FunctionMapGerm l m)
  rw [Filter.Germ.coe_compTendsto']
  exact Filter.Germ.map_coe _ _

/-- Composition of two pointed analytic map germs. -/
@[expose] noncomputable def PointedMapGerm.comp {l n m : ℕ}
    (g : PointedMapGerm n m) (h : PointedMapGerm l n) :
    PointedMapGerm l m := by
  refine ⟨g.1.compPointed h, ?_⟩
  rcases g with ⟨g, hg0⟩
  rcases h with ⟨h, hh0⟩
  rcases g with ⟨g, hg⟩
  rcases h with ⟨h, hh⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      induction h using Filter.Germ.inductionOn with
      | _ k =>
          change f (k 0) = 0
          change f 0 = 0 at hg0
          change k 0 = 0 at hh0
          simpa [hh0] using hg0

@[simp]
theorem PointedMapGerm.comp_ofFunction {l n m : ℕ}
    (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (k : Source l → Source n) (hk : AnalyticAt ℂ k 0) (hk0 : k 0 = 0) :
    (PointedMapGerm.ofFunction f hf hf0).comp
      (PointedMapGerm.ofFunction k hk hk0) =
        PointedMapGerm.ofFunction (f ∘ k)
          (by
            have hfk : AnalyticAt ℂ f (k 0) := by simpa only [hk0] using hf
            exact hfk.comp hk)
          (by simp only [Function.comp_apply, hk0, hf0]) := by
  apply Subtype.ext
  exact MapGerm.compPointed_ofFunction f hf k hk hk0

/-- The chain rule for composition of pointed analytic map germs. -/
theorem PointedMapGerm.differential_comp {l n m : ℕ}
    (g : PointedMapGerm n m) (h : PointedMapGerm l n) :
    (g.comp h).differential = g.differential ∘L h.differential := by
  rcases g with ⟨⟨g, hg⟩, hg0⟩
  rcases h with ⟨⟨h, hh⟩, hh0⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      induction h using Filter.Germ.inductionOn with
      | _ k =>
          rw [isAnalyticMapGerm_ofFun] at hg hh
          change f 0 = 0 at hg0
          change k 0 = 0 at hh0
          change fderiv ℂ (f ∘ k) 0 =
            fderiv ℂ f 0 ∘L fderiv ℂ k 0
          have hgf : DifferentiableAt ℂ f (k 0) := by
            simpa only [hh0] using hg.differentiableAt
          simpa only [hh0] using
            (fderiv_comp 0 hgf hh.differentiableAt)

/-- Composition of pointed analytic map germs is associative. -/
theorem PointedMapGerm.comp_assoc {k l n m : ℕ}
    (f : PointedMapGerm n m) (g : PointedMapGerm l n)
    (h : PointedMapGerm k l) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  rcases g with ⟨⟨g, hg⟩, hg0⟩
  rcases h with ⟨⟨h, hh⟩, hh0⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
          induction h using Filter.Germ.inductionOn with
          | _ h =>
              rw [isAnalyticMapGerm_ofFun] at hf hg hh
              change f 0 = 0 at hf0
              change g 0 = 0 at hg0
              change h 0 = 0 at hh0
              have hfeq :
                  (⟨⟨(f : FunctionMapGerm n m),
                    (isAnalyticMapGerm_ofFun f).2 hf⟩, hf0⟩ :
                      PointedMapGerm n m) =
                    PointedMapGerm.ofFunction f hf hf0 := by
                apply Subtype.ext
                apply Subtype.ext
                rfl
              have hgeq :
                  (⟨⟨(g : FunctionMapGerm l n),
                    (isAnalyticMapGerm_ofFun g).2 hg⟩, hg0⟩ :
                      PointedMapGerm l n) =
                    PointedMapGerm.ofFunction g hg hg0 := by
                apply Subtype.ext
                apply Subtype.ext
                rfl
              have hheq :
                  (⟨⟨(h : FunctionMapGerm k l),
                    (isAnalyticMapGerm_ofFun h).2 hh⟩, hh0⟩ :
                      PointedMapGerm k l) =
                    PointedMapGerm.ofFunction h hh hh0 := by
                apply Subtype.ext
                apply Subtype.ext
                rfl
              rw [hfeq, hgeq, hheq]
              rw [PointedMapGerm.comp_ofFunction,
                PointedMapGerm.comp_ofFunction,
                PointedMapGerm.comp_ofFunction,
                PointedMapGerm.comp_ofFunction]
              apply Subtype.ext
              apply Subtype.ext
              rfl

/-- The identity germ is a left identity for composition. -/
theorem PointedMapGerm.identity_comp {n m : ℕ}
    (f : PointedMapGerm n m) :
    (PointedMapGerm.identity m).comp f = f := by
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      rw [isAnalyticMapGerm_ofFun] at hf
      change f 0 = 0 at hf0
      have hfeq :
          (⟨⟨(f : FunctionMapGerm n m),
            (isAnalyticMapGerm_ofFun f).2 hf⟩, hf0⟩ :
              PointedMapGerm n m) =
            PointedMapGerm.ofFunction f hf hf0 := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [hfeq, PointedMapGerm.identity,
        PointedMapGerm.comp_ofFunction]
      apply Subtype.ext
      apply Subtype.ext
      rfl

/-- The identity germ is a right identity for composition. -/
theorem PointedMapGerm.comp_identity {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.comp (PointedMapGerm.identity n) = f := by
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      rw [isAnalyticMapGerm_ofFun] at hf
      change f 0 = 0 at hf0
      have hfeq :
          (⟨⟨(f : FunctionMapGerm n m),
            (isAnalyticMapGerm_ofFun f).2 hf⟩, hf0⟩ :
              PointedMapGerm n m) =
            PointedMapGerm.ofFunction f hf hf0 := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [hfeq, PointedMapGerm.identity,
        PointedMapGerm.comp_ofFunction]
      apply Subtype.ext
      apply Subtype.ext
      rfl

end OnLeConjecture.Analytic
