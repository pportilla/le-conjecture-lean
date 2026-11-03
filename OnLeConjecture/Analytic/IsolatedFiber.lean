/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Injectivity

/-!
# The zero fibre of a pointed analytic map germ

Local injectivity implies that the inverse image of the origin is isolated at
the origin. This is the topological input needed before applying the local
analytic finiteness theorem.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Set
open scoped Topology

/-- A pointed analytic map germ has an isolated zero fibre when it admits a
representative whose inverse image of the origin contains no other point in a
neighborhood of the origin. -/
@[expose] def PointedMapGerm.HasIsolatedZeroRepresentative {n m : ℕ}
    (g : PointedMapGerm n m) : Prop :=
  ∃ (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0),
    g = PointedMapGerm.ofFunction f hf h0 ∧
      ∃ s ∈ 𝓝 (0 : Source n),
        ∀ x ∈ s, f x = 0 → x = 0

/-- A locally injective pointed analytic map germ has an isolated zero
fibre. -/
theorem PointedMapGerm.HasInjectiveRepresentative.hasIsolatedZeroRepresentative
    {n m : ℕ} {g : PointedMapGerm n m}
    (hinjective : g.HasInjectiveRepresentative) :
    g.HasIsolatedZeroRepresentative := by
  rcases hinjective with ⟨f, hf, h0, hgf, s, hs, hinj⟩
  refine ⟨f, hf, h0, hgf, s, hs, ?_⟩
  have hzero : (0 : Source n) ∈ s := mem_of_mem_nhds hs
  intro x hx hfx
  apply hinj hx hzero
  simpa only [h0] using hfx

/-- A germ with an injective representative cannot have a nonisolated zero
fibre. -/
theorem PointedMapGerm.hasIsolatedZeroRepresentative_of_injective
    {n m : ℕ} (g : PointedMapGerm n m)
    (hinjective : g.HasInjectiveRepresentative) :
    g.HasIsolatedZeroRepresentative :=
  hinjective.hasIsolatedZeroRepresentative

end OnLeConjecture.Analytic
