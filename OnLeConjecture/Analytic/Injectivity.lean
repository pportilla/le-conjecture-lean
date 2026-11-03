/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Equivalence

/-!
# Local injectivity of invertible analytic germs

This file proves that a pointed analytic map germ with a left inverse germ has
an injective representative near the origin.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Set
open scoped Topology

/-- A pointed analytic map germ with a left inverse germ has an injective
representative on a neighborhood of the origin. -/
theorem PointedMapGerm.hasInjectiveRepresentative_of_leftInverse
    {n m : ℕ} (f : PointedMapGerm n m) (r : PointedMapGerm m n)
    (hleft : r.comp f = PointedMapGerm.identity n) :
    f.HasInjectiveRepresentative := by
  rcases f with ⟨⟨f, hf⟩, hf0⟩
  rcases r with ⟨⟨r, hr⟩, hr0⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      induction r using Filter.Germ.inductionOn with
      | _ r =>
          have hfan : AnalyticAt ℂ f 0 := by
            rw [isAnalyticMapGerm_ofFun] at hf
            exact hf
          have hran : AnalyticAt ℂ r 0 := by
            rw [isAnalyticMapGerm_ofFun] at hr
            exact hr
          have hfzero : f 0 = 0 := by
            change f 0 = 0 at hf0
            exact hf0
          have hrzero : r 0 = 0 := by
            change r 0 = 0 at hr0
            exact hr0
          have hfeq :
              (⟨⟨(f : FunctionMapGerm n m),
                (isAnalyticMapGerm_ofFun f).2 hfan⟩, hfzero⟩ :
                  PointedMapGerm n m) =
                PointedMapGerm.ofFunction f hfan hfzero := by
            apply Subtype.ext
            apply Subtype.ext
            rfl
          have hreq :
              (⟨⟨(r : FunctionMapGerm m n),
                (isAnalyticMapGerm_ofFun r).2 hran⟩, hrzero⟩ :
                  PointedMapGerm m n) =
                PointedMapGerm.ofFunction r hran hrzero := by
            apply Subtype.ext
            apply Subtype.ext
            rfl
          have hcomposition :
              (PointedMapGerm.ofFunction r hran hrzero).comp
                  (PointedMapGerm.ofFunction f hfan hfzero) =
                PointedMapGerm.identity n := by
            simpa only [hfeq, hreq] using hleft
          rw [PointedMapGerm.comp_ofFunction] at hcomposition
          have hunderlying := congrArg
            (fun q : PointedMapGerm n n ↦ q.1.1) hcomposition
          have heventual : (r ∘ f) =ᶠ[𝓝 0] id := by
            apply Filter.Germ.coe_eq.mp
            simpa only [PointedMapGerm.identity, PointedMapGerm.ofFunction,
              MapGerm.ofFunction] using hunderlying
          change ∃ (q : Source n → Source m)
              (hq : AnalyticAt ℂ q 0) (hq0 : q 0 = 0),
            (⟨⟨(f : FunctionMapGerm n m), hf⟩, hf0⟩ :
                PointedMapGerm n m) =
                PointedMapGerm.ofFunction q hq hq0 ∧
              ∃ s ∈ 𝓝 (0 : Source n), Set.InjOn q s
          refine ⟨f, hfan, hfzero, ?_,
            {z : Source n | r (f z) = z}, heventual, ?_⟩
          · exact hfeq
          · intro x hx y hy hxy
            calc
              x = r (f x) := hx.symm
              _ = r (f y) := congrArg r hxy
              _ = y := hy

/-- Both directions of an invertible pointed analytic germ have injective
representatives. -/
theorem PointedEquivGerm.forward_hasInjectiveRepresentative {n : ℕ}
    (e : PointedEquivGerm n) :
    e.forward.HasInjectiveRepresentative :=
  e.forward.hasInjectiveRepresentative_of_leftInverse e.inverse
    e.inverse_forward

theorem PointedEquivGerm.inverse_hasInjectiveRepresentative {n : ℕ}
    (e : PointedEquivGerm n) :
    e.inverse.HasInjectiveRepresentative :=
  e.inverse.hasInjectiveRepresentative_of_leftInverse e.forward
    e.forward_inverse

/-- Composition preserves the existence of an injective analytic
representative near the origin. -/
theorem PointedMapGerm.comp_hasInjectiveRepresentative {l n m : ℕ}
    (g : PointedMapGerm n m) (h : PointedMapGerm l n)
    (hg : g.HasInjectiveRepresentative)
    (hh : h.HasInjectiveRepresentative) :
    (g.comp h).HasInjectiveRepresentative := by
  rcases hg with ⟨G, hGan, hG0, hgerm, s, hs, hGinj⟩
  rcases hh with ⟨H, hHan, hH0, hherm, t, ht, hHinj⟩
  have hGatH0 : AnalyticAt ℂ G (H 0) := by
    simpa only [hH0] using hGan
  have hcompAnalytic : AnalyticAt ℂ (G ∘ H) 0 := hGatH0.comp hHan
  have hcompZero : (G ∘ H) 0 = 0 := by
    simp only [Function.comp_apply, hH0, hG0]
  have hpre : H ⁻¹' s ∈ 𝓝 (0 : Source l) := by
    have hsH0 : s ∈ 𝓝 (H 0) := by simpa only [hH0] using hs
    exact hHan.continuousAt hsH0
  change ∃ (q : Source l → Source m)
      (hq : AnalyticAt ℂ q 0) (hq0 : q 0 = 0),
    g.comp h = PointedMapGerm.ofFunction q hq hq0 ∧
      ∃ u ∈ 𝓝 (0 : Source l), Set.InjOn q u
  refine ⟨G ∘ H, hcompAnalytic, hcompZero, ?_,
    t ∩ H ⁻¹' s, inter_mem ht hpre, ?_⟩
  · rw [hgerm, hherm]
    exact PointedMapGerm.comp_ofFunction G hGan hG0 H hHan hH0
  · intro x hx y hy hxy
    have hHxy : H x = H y :=
      hGinj hx.2 hy.2 hxy
    exact hHinj hx.1 hy.1 hHxy

/-- A right left coordinate change preserves the existence of an injective
representative in the forward direction. -/
theorem PointedMapGerm.RightLeftEquivalent.hasInjectiveRepresentative
    {n m : ℕ} {f g : PointedMapGerm n m}
    (hfg : f.RightLeftEquivalent g)
    (hf : f.HasInjectiveRepresentative) :
    g.HasInjectiveRepresentative := by
  rw [PointedMapGerm.RightLeftEquivalent.eq_1] at hfg
  rcases hfg with ⟨source, target, rfl⟩
  apply PointedMapGerm.comp_hasInjectiveRepresentative
  · exact target.forward_hasInjectiveRepresentative
  · apply PointedMapGerm.comp_hasInjectiveRepresentative
    · exact hf
    · exact source.forward_hasInjectiveRepresentative

/-- Right left equivalent germs have simultaneously injective
representatives near the origin. -/
theorem PointedMapGerm.RightLeftEquivalent.hasInjectiveRepresentative_iff
    {n m : ℕ} {f g : PointedMapGerm n m}
    (hfg : f.RightLeftEquivalent g) :
    g.HasInjectiveRepresentative ↔ f.HasInjectiveRepresentative := by
  constructor
  · exact hfg.symm.hasInjectiveRepresentative
  · exact hfg.hasInjectiveRepresentative

end OnLeConjecture.Analytic
