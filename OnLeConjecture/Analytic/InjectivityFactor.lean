/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Injectivity
public import OnLeConjecture.Analytic.PairRepresentative

/-!
# Local injectivity and factorization

If a composite analytic germ has an injective representative, then its inner
factor has an injective representative. This is the germ version of the
elementary fact that injectivity of `G ∘ H` implies injectivity of `H`.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Set
open scoped Topology

/-- Local injectivity of a composite descends to its inner factor. -/
theorem PointedMapGerm.hasInjectiveRepresentative_of_comp
    {l n m : ℕ} (g : PointedMapGerm n m) (h : PointedMapGerm l n)
    (hcomp : (g.comp h).HasInjectiveRepresentative) :
    h.HasInjectiveRepresentative := by
  obtain ⟨G, hG, hG0, hgerm⟩ := g.exists_ofFunction
  obtain ⟨H, hH, hH0, hherm⟩ := h.exists_ofFunction
  obtain ⟨F, hF, hF0, hfgerm, s, hs, hFinjective⟩ := hcomp
  have hGH : AnalyticAt ℂ (G ∘ H) 0 := by
    have hGAt : AnalyticAt ℂ G (H 0) := by
      simpa only [hH0] using hG
    exact hGAt.comp hH
  have hGH0 : (G ∘ H) 0 = 0 := by
    simp only [Function.comp_apply, hH0, hG0]
  have hcomposition : g.comp h =
      PointedMapGerm.ofFunction (G ∘ H) hGH hGH0 := by
    rw [hgerm, hherm]
    exact PointedMapGerm.comp_ofFunction G hG hG0 H hH hH0
  have hunderlying := congrArg
    (fun q : PointedMapGerm l m ↦ q.1.1)
    (hcomposition.symm.trans hfgerm)
  have heventual : (G ∘ H) =ᶠ[nhds (0 : Source l)] F := by
    apply Filter.Germ.coe_eq.mp
    simpa only [PointedMapGerm.ofFunction, MapGerm.ofFunction] using hunderlying
  refine ⟨H, hH, hH0, hherm, s ∩ {x | (G ∘ H) x = F x},
    inter_mem hs heventual, ?_⟩
  intro x hx y hy hHxy
  apply hFinjective hx.1 hy.1
  calc
    F x = (G ∘ H) x := hx.2.symm
    _ = (G ∘ H) y := by simp only [Function.comp_apply, hHxy]
    _ = F y := hy.2

end OnLeConjecture.Analytic
