/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothCriticalNodeNormalization
public import OnLeConjecture.DTwo.OrbitCubicPreparation

/-!
# Orbit exclusion before choosing critical-curve coordinates

The analytic source equivalence is constructed from the transverse node
and its intersection with the specified smooth critical curve. Its unit
multiple of the critical equation transports the minor divisibility.
The cubic orbit coefficient and the final target changes are then supplied
by the orbit preparation theorem.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The rank-one node branch is excluded using the actual critical curve
and intersection multiplicities, without an aligned coordinate or orbit
endpoint assumption. The two intersection equalities remain explicit
inputs supplied by the numerical reduction. -/
theorem smooth_critical_node_intersection_six_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) (h f g : Germ 2)
    (hfactor : F.1.component 0 = f * g)
    (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g))
    (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfiniteCritical : PlaneCurve.HasFiniteIntersection h (F.1.component 0))
    (hcritical : PlaneCurve.intersectionMultiplicity h (F.1.component 0) hfiniteCritical = 2)
    (hsecond : F.1.component 1 ∈ maximalIdeal 2 ^ 3)
    (hthird : F.1.component 2 ∈ maximalIdeal 2 ^ 3)
    (hfinitePair : PlaneCurve.HasFiniteIntersection (F.1.component 0) (F.1.component 1))
    (hpair : PlaneCurve.intersectionMultiplicity
      (F.1.component 0) (F.1.component 1) hfinitePair = 6)
    (hminor12 : h ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 1))
    (hminor13 : h ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 2)) :
    ¬ F.HasInjectiveRepresentative := by
  obtain ⟨e, U, _hU, he0, heh⟩ := exists_smooth_critical_node_normalization
    (F.1.component 0) h f g hfactor hf hg hjac hh hdh hfiniteCritical hcritical
  let G := F.comp e.forward
  have hcomponent (i : Fin 3) :
      G.1.component i = e.forward.pullbackRingHom (F.1.component i) :=
    PointedMapGerm.component_comp_eq_pullback _ _ _
  have hfirst : G.1.component 0 =
      coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) := by
    rw [hcomponent, he0]
    simp only [orbitPolynomialPhi, orbitPolynomialS, orbitPolynomialLambda, map_sub,
      map_pow, coordinatePolynomialAlgHom_X]
  have hsecondG : G.1.component 1 ∈ maximalIdeal 2 ^ 3 := by
    rw [hcomponent]
    exact e.forward.pullback_mem_maximalIdeal_pow hsecond
  have hthirdG : G.1.component 2 ∈ maximalIdeal 2 ^ 3 := by
    rw [hcomponent]
    exact e.forward.pullback_mem_maximalIdeal_pow hthird
  have hfiniteG : PlaneCurve.HasFiniteIntersection (G.1.component 0) (G.1.component 1) := by
    rw [hcomponent, hcomponent]
    exact hfinitePair.pullback e
  have hiG : PlaneCurve.intersectionMultiplicity
      (G.1.component 0) (G.1.component 1) hfiniteG = 6 := by
    simp only [hcomponent]
    exact (PlaneCurve.intersectionMultiplicity_pullback e hfinitePair).symm.trans hpair
  have hminorG (i : Fin 3)
      (hi : h ^ 3 ∣ jacobian (F.1.component 0) (F.1.component i)) :
      coordinate (1 : Fin 2) ^ 3 ∣ jacobian (G.1.component 0) (G.1.component i) := by
    rw [hcomponent, hcomponent]
    exact e.coordinate_pow_dvd_jacobian_of_pullback_multiple h
      (F.1.component 0) (F.1.component i) U 3 heh hi
  have hFG : F.RightLeftEquivalent G := by
    refine ⟨e, PointedEquivGerm.identity 3, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  intro hF
  exact aligned_node_intersection_six_not_hasInjectiveRepresentative G hfirst hsecondG hthirdG
    hfiniteG hiG (hminorG 1 hminor12) (hminorG 2 hminor13)
    (hFG.hasInjectiveRepresentative hF)

end OnLeConjecture.DTwo
