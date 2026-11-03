/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PreparedTopOrderCoordinates
public import OnLeConjecture.Analytic.SmoothReductionCoordinates

/-!
# Map germs in the constructed point-basis preparation coordinates

The first member's prepared equation is matched to the transformed map,
and source equivalence transports ordinary orders, finite intersection,
squarefreeness, and every specified Jacobian divisor.
-/

public section

namespace OnLeConjecture.Analytic.PreparedTopOrderCoordinates

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} (d : PreparedTopOrderCoordinates c)
    (g : PointedMapGerm 2 3)

@[expose] noncomputable def map : PointedMapGerm 2 3 := g.comp d.source.forward

theorem component (j : Fin 3) :
    (d.map g).1.component j = d.source.forward.pullbackRingHom (g.1.component j) :=
  g.component_comp_general d.source.forward j

theorem rightLeftEquivalent : g.RightLeftEquivalent (d.map g) := by
  refine ⟨d.source, PointedEquivGerm.identity 3, ?_⟩
  rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  rfl

theorem component_mem_pow (j : Fin 3) (m : ℕ)
    (horder : g.1.component j ∈ maximalIdeal 2 ^ m) :
    (d.map g).1.component j ∈ maximalIdeal 2 ^ m := by
  rw [d.component]
  exact d.source.forward.pullback_mem_maximalIdeal_pow horder

theorem first_squarefree (hfree : Squarefree (g.1.component 0)) :
    Squarefree ((d.map g).1.component 0) := by
  rw [d.component]
  exact d.source.squarefree_pullback _ hfree

theorem first_prepared (hfirst : c.germ c.root = g.1.component 0) :
    (d.map g).1.component 0 = d.multiplier * firstCoordinatePolynomialEvaluation d.polynomial := by
  rw [d.component, ← hfirst, ← d.root_germ, d.prepared, mul_comm]

theorem pair_finite
    (hf : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1)) :
    PlaneCurve.HasFiniteIntersection ((d.map g).1.component 0) ((d.map g).1.component 1) := by
  simpa only [d.component, PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply] using hf.pullback d.source

theorem intersection_eq
    (hf : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1)) :
    PlaneCurve.intersectionMultiplicity ((d.map g).1.component 0) ((d.map g).1.component 1)
      (d.pair_finite g hf) =
    PlaneCurve.intersectionMultiplicity (g.1.component 0) (g.1.component 1) hf := by
  simpa only [d.component, PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply] using
      (PlaneCurve.intersectionMultiplicity_pullback d.source hf).symm

theorem jacobian_divisor (i j : Fin 3) (t : ℕ)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (g.1.component i) (g.1.component j)) :
    coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian ((d.map g).1.component i) ((d.map g).1.component j) := by
  rw [d.component, d.component]
  exact d.source.coordinate_pow_dvd_jacobian_of_pullback_equation (coordinate (1 : Fin 2))
    _ _ (t - 1) d.source_preserves_y hdiv

end OnLeConjecture.Analytic.PreparedTopOrderCoordinates

