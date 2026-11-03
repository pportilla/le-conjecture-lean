/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.Intersection

/-!
# Changes of a generator of a plane intersection ideal

This file records invariance of local intersection multiplicity when one
generator is changed by a multiple of the other generator.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- Subtracting a multiple of the first generator from the second generator
does not change their pair ideal. -/
theorem pairIdeal_sub_mul_right
    (g u q : Germ 2) :
    pairIdeal g (u - g * q) = pairIdeal g u := by
  rw [pairIdeal_eq_span, pairIdeal_eq_span]
  simpa only [mul_comm] using
    (Ideal.span_pair_sub_mul_left (x := g) (y := u) (z := q))

/-- Equality of pair ideals transports finite intersection. -/
theorem HasFiniteIntersection.of_pairIdeal_eq
    {g u v : Germ 2} (hfinite : HasFiniteIntersection g u)
    (hideal : pairIdeal g u = pairIdeal g v) :
    HasFiniteIntersection g v := by
  rw [HasFiniteIntersection, ← hideal]
  exact hfinite

/-- Intersection multiplicity depends only on the pair ideal. -/
theorem intersectionMultiplicity_eq_of_pairIdeal_eq
    {g u v : Germ 2} (hfinite : HasFiniteIntersection g u)
    (hfinite' : HasFiniteIntersection g v)
    (hideal : pairIdeal g u = pairIdeal g v) :
    intersectionMultiplicity g u hfinite =
      intersectionMultiplicity g v hfinite' := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ pairIdeal g u) := hfinite
  let _ : Module.Finite ℂ (Germ 2 ⧸ pairIdeal g v) := hfinite'
  change Module.finrank ℂ (Germ 2 ⧸ pairIdeal g u) =
    Module.finrank ℂ (Germ 2 ⧸ pairIdeal g v)
  rw [hideal]

/-- Subtracting a multiple of the first generator preserves finite
intersection. -/
theorem HasFiniteIntersection.sub_mul_right
    {g u q : Germ 2} (hfinite : HasFiniteIntersection g u) :
    HasFiniteIntersection g (u - g * q) := by
  exact hfinite.of_pairIdeal_eq (pairIdeal_sub_mul_right g u q).symm

/-- Subtracting a multiple of the first generator preserves intersection
multiplicity. -/
theorem intersectionMultiplicity_sub_mul_right
    {g u q : Germ 2} (hfinite : HasFiniteIntersection g u) :
    intersectionMultiplicity g (u - g * q) hfinite.sub_mul_right =
      intersectionMultiplicity g u hfinite := by
  exact intersectionMultiplicity_eq_of_pairIdeal_eq
    hfinite.sub_mul_right hfinite (pairIdeal_sub_mul_right g u q)

end OnLeConjecture.PlaneCurve
