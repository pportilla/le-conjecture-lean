/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.DepressedPreparedSourceCoordinates
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction
public import OnLeConjecture.Analytic.Injectivity
public import OnLeConjecture.PlaneCurve.Intersection

/-!
# Source coordinates for the cubic and quartic reduction inputs

The reduction supplies the first member's reducedness, ordinary component
orders, finite first pair, and its numerical intersection estimates. The
local multiplicity cases must additionally identify a smooth critical
component whose intersection with that member equals its multiplicity.
From these analytic data the construction below produces the depressed
monic preparation, preserving the given component and every Jacobian
divisor supported on it.

No principalization or compatible blowup atlas is constructed here. In
particular, transporting an abstract record of local charts to these
coordinates requires commuting chart identities and cannot be inferred
from numerical proximity alone.
-/

public section

namespace OnLeConjecture.Analytic

/-- Constructed coordinates adapted to a specified smooth critical
equation. The point-basis and proximity data are not part of this object. -/
structure SmoothReductionCoordinates (g : PointedMapGerm 2 3) (h : Germ 2) (m : ℕ) where
  source : PointedEquivGerm 2
  polynomial : _root_.Polynomial (Germ 1)
  multiplier : Germ 2
  branch_coordinate : source.forward.pullbackRingHom h = Germ.coordinate (1 : Fin 2)
  monic : polynomial.Monic
  degree : polynomial.natDegree = m
  depressed : polynomial.coeff (m - 1) = 0
  distinguished : ∀ j, j < m → polynomial.coeff j ∈ Germ.maximalIdeal 1
  multiplier_unit : IsUnit multiplier
  first_prepared : source.forward.pullbackRingHom (g.1.component 0) =
    Germ.firstCoordinatePolynomialEvaluation polynomial * multiplier

namespace SmoothReductionCoordinates

variable {g : PointedMapGerm 2 3} {h : Germ 2} {m : ℕ}
    (d : SmoothReductionCoordinates g h m)

/-- The full original map in the constructed source coordinates. -/
@[expose] noncomputable def map : PointedMapGerm 2 3 := g.comp d.source.forward

theorem component (j : Fin 3) :
    d.map.1.component j = d.source.forward.pullbackRingHom (g.1.component j) :=
  g.component_comp_general d.source.forward j

theorem rightLeftEquivalent : g.RightLeftEquivalent d.map := by
  refine ⟨d.source, PointedEquivGerm.identity 3, ?_⟩
  rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  rfl

theorem component_mem_pow (j : Fin 3)
    (horder : g.1.coordinateIdeal ≤ Germ.maximalIdeal 2 ^ m) :
    d.map.1.component j ∈ Germ.maximalIdeal 2 ^ m := by
  rw [d.component]
  exact d.source.forward.pullback_mem_maximalIdeal_pow
    (horder (g.1.component_mem_coordinateIdeal j))

theorem first_squarefree (hfree : Squarefree (g.1.component 0)) :
    Squarefree (d.map.1.component 0) := by
  rw [d.component]
  exact d.source.squarefree_pullback _ hfree

theorem pair_finite
    (hf : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1)) :
    PlaneCurve.HasFiniteIntersection (d.map.1.component 0) (d.map.1.component 1) := by
  simpa only [d.component, PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply] using hf.pullback d.source

theorem intersection_eq
    (hf : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1)) :
    PlaneCurve.intersectionMultiplicity (d.map.1.component 0) (d.map.1.component 1)
        (d.pair_finite hf) =
      PlaneCurve.intersectionMultiplicity (g.1.component 0) (g.1.component 1) hf := by
  simpa only [d.component, PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply] using
      (PlaneCurve.intersectionMultiplicity_pullback d.source hf).symm

theorem common_jacobian_divisors (t : ℕ)
    (hdiv : ∀ i j : Fin 3, i < j → h ^ (t - 1) ∣
      Germ.jacobian (g.1.component i) (g.1.component j)) :
    ∀ i j : Fin 3, i < j → Germ.coordinate (1 : Fin 2) ^ (t - 1) ∣
      Germ.jacobian (d.map.1.component i) (d.map.1.component j) := by
  intro i j hij
  rw [d.component, d.component]
  exact d.source.coordinate_pow_dvd_jacobian_of_pullback_equation h _ _ (t - 1)
    d.branch_coordinate (hdiv i j hij)

/-- The prepared polynomial is squarefree up to its retained analytic
unit, and the ordinary orders of all other components are unchanged. -/
theorem prepared_first_squarefree (hfree : Squarefree (g.1.component 0)) :
    Squarefree (d.multiplier * Germ.firstCoordinatePolynomialEvaluation d.polynomial) := by
  rw [mul_comm, ← d.first_prepared]
  exact d.source.squarefree_pullback _ hfree

end SmoothReductionCoordinates

/-- Construction from a smooth equation and the actual intersection
order, for both multiplicities. Reducedness and ordinary-order bounds
are subsequently transported by the preceding methods. -/
theorem exists_smoothReductionCoordinates
    (g : PointedMapGerm 2 3) (h : Germ 2)
    (hh : h ∈ Germ.maximalIdeal 2) (hdh : Germ.differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h (g.1.component 0))
    (m : ℕ) (hm : m = 3 ∨ m = 4)
    (hinter : PlaneCurve.intersectionMultiplicity h (g.1.component 0) hfinite = m) :
    Nonempty (SmoothReductionCoordinates g h m) := by
  obtain ⟨e, P, U, he, hP, hdegree, hdepressed, hcoeff, hU, hfactor⟩ :=
    Germ.exists_smooth_second_coordinate_depressed_preparation
      h (g.1.component 0) hh hdh hfinite m hm hinter
  exact ⟨{
    source := e
    polynomial := P
    multiplier := U
    branch_coordinate := he
    monic := hP
    degree := hdegree
    depressed := hdepressed
    distinguished := hcoeff
    multiplier_unit := hU
    first_prepared := hfactor }⟩

end OnLeConjecture.Analytic
