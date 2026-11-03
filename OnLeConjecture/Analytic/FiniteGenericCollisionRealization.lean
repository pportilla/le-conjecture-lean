/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteCoordinatePresentation
public import OnLeConjecture.Analytic.SimpleZeroCollision

/-!
# Collision realization for generic embeddings

The proposition in this file isolates the analytic realization theorem still
needed after the generic field reduction. It asks that two distinct generic
embeddings of a finite plane map produce two source paths converging to the
origin whose images agree and which are distinct away from the parameter
origin.

No realization theorem is asserted here. The proved implication records that
this proposition is sufficient for uniqueness of the generic embedding of an
injective plane map germ.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Distinct generic embeddings of a finite plane map can be realized by
nearby collision paths for every analytic representative. -/
@[expose] def GenericEmbeddingCollisionRealization (m : ℕ) : Prop :=
  ∀ (f : PointedMapGerm 2 m) (_hfinite : f.IsFiniteAtOrigin),
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∀ (sigma tau : Field.Emb (FractionRing f.ImageRing)
        (FractionRing (Germ 2))),
      sigma ≠ tau →
      ∀ (representative : Source 2 → Source m)
        (hrepresentative : AnalyticAt ℂ representative 0)
        (hrepresentativeZero : representative 0 = 0),
        f = PointedMapGerm.ofFunction representative
          hrepresentative hrepresentativeZero →
        ∃ first second : ℂ → Source 2,
          Tendsto first (nhds 0) (nhds 0) ∧
          Tendsto second (nhds 0) (nhds 0) ∧
          (∀ᶠ parameter in nhds 0,
            representative (first parameter) =
              representative (second parameter)) ∧
          ∀ᶠ parameter in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
            first parameter ≠ second parameter

/-- Collision realization implies uniqueness of the generic embedding for
every injective plane map germ. -/
theorem planeInjectiveImpliesUniqueGenericEmbedding_of_collisionRealization
    {m : ℕ} (hrealization : GenericEmbeddingCollisionRealization m) :
    PlaneInjectiveImpliesUniqueGenericEmbedding m := by
  intro f hinjective
  have hfinite : f.IsFiniteAtOrigin :=
    f.injective_isFiniteAtOrigin_two hinjective
  apply
    (f.isBirationalAtOrigin_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
      hfinite).mp
  by_contra hnot
  obtain ⟨sigma, tau, hne⟩ :=
    f.exists_distinct_generic_embeddings_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
      hfinite hnot
  obtain ⟨representative, hrepresentative,
    hrepresentativeZero, hf, s, hs, hsInjective⟩ := hinjective
  obtain ⟨first, second, hfirst, hsecond, hequal, hdistinct⟩ :=
    hrealization f hfinite sigma tau hne representative
      hrepresentative hrepresentativeZero hf
  exact
    (not_neighborhood_injective_of_tendsto_collision_branches
      representative first second hfirst hsecond hequal hdistinct)
      ⟨s, hs, hsInjective⟩

end PointedMapGerm

end OnLeConjecture.Analytic
