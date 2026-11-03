/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.SquareJetMaximalCritical
public import OnLeConjecture.DTwo.ProximityNumericalAssembly
public import OnLeConjecture.PlaneCurve.MorseBranchCount
public import OnLeConjecture.Analytic.RightLeftRelation

/-!
# Simultaneous square-jet preparation and numerical alternatives

The first quadratic power form is chosen independently of the critical
component. Its actual branch count and Milnor number connect the supplied
resolution identities to that power. The maximal critical intersection
is then proved to be two, permitting a simultaneous coordinate change.
Milnor invariance proves that this second change retains the same power.
Finally the analytic recurrence and proximity bounds leave the two even
numerical alternatives.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ Numerical PlaneCurve

theorem exists_square_jet_prepared_numerical_alternative
    (F : PointedMapGerm 2 3) {N : ℕ}
    (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (k : ℕ) (hk : 3 ≤ k) (hfirst : F.1.component 0 = morseCurve k)
    (hreduced : Squarefree (F.1.component 0)) (hdifferential : F.differential = 0)
    (hbranches : c.branchCount = irreducibleBranchCount (F.1.component 0))
    (hvcritical : HasIsolatedCriticalPoint (F.1.component 0))
    (hgenus : 2 * c.multiplicityCount 2 + 1 =
      milnorNumber (F.1.component 0) hvcritical + c.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hfiniteCritical : HasFiniteIntersection (F.1.component 0) h)
    (t : ℕ) (htransverse : c.totalMultiplicity ≤ t)
    (hpolar : intersectionMultiplicity (F.1.component 0) h hfiniteCritical * (t - 1) +
      c.totalMultiplicity + c.branchCount ≤ 2 * c.squareMultiplicity)
    (hminors : ∀ i : Fin 2, h ^ (t - 1) ∣ jacobian (F.1.component 0) (F.1.component i.succ))
    (selected : Fin 2)
    (hfinitePair : HasFiniteIntersection (F.1.component 0) (F.1.component selected.succ))
    (hpair : intersectionMultiplicity
      (F.1.component 0) (F.1.component selected.succ) hfinitePair = c.squareMultiplicity) :
    ∃ G : PointedMapGerm 2 3, F.RightLeftEquivalent G ∧ G.differential = 0 ∧
      G.1.component 0 = morseCurve k ∧
      (∀ i : Fin 2, coordinate (1 : Fin 2) ^ (t - 1) ∣
        jacobian (G.1.component 0) (G.1.component i.succ)) ∧
      (∀ i : Fin 2, coordinate (1 : Fin 2) ^ (k - 1) ∣
        jacobian (G.1.component 0) (G.1.component i.succ)) ∧
      Even k ∧
      ((c.multiplicityCount 1 = 0 ∧ t = k) ∨
        (c.multiplicityCount 1 = k ∧ t = 2 * k)) ∧
      ∃ hfinite : HasFiniteIntersection (G.1.component 0) (G.1.component selected.succ),
        intersectionMultiplicity
          (G.1.component 0) (G.1.component selected.succ) hfinite = c.squareMultiplicity := by
  have hb : c.branchCount = Nat.gcd 2 k := by
    rw [hbranches, hfirst]
    exact irreducibleBranchCount_morseCurve k (by omega)
  have hmu : milnorNumber (F.1.component 0) hvcritical = k - 1 := by
    simpa only [hfirst] using milnorNumber_morseCurve k (by omega)
  have hgenusK : 2 * c.multiplicityCount 2 + 2 = k + c.branchCount := by
    rw [hmu] at hgenus
    omega
  have hfiniteCritical' : HasFiniteIntersection
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) h := by
    simpa only [hfirst, morseCurve] using hfiniteCritical
  have hpolar' : intersectionMultiplicity
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) h hfiniteCritical' * (t - 1) +
        c.totalMultiplicity + c.branchCount ≤ 2 * c.squareMultiplicity := by
    simpa only [hfirst, morseCurve] using hpolar
  obtain ⟨hI2, hdh, _hirred⟩ := square_jet_maximal_critical_intersection_eq_two c generation
    hdecrease hroot hpositive k hk hb hgenusK h hh hfiniteCritical' t htransverse hpolar'
  have hI2' : intersectionMultiplicity (F.1.component 0) h hfiniteCritical = 2 := by
    simpa only [hfirst, morseCurve] using hI2
  have hfiniteh : HasFiniteIntersection h (F.1.component 0) :=
    (hasFiniteIntersection_comm _ _).mp hfiniteCritical
  have hIh : intersectionMultiplicity h (F.1.component 0) hfiniteh = 2 :=
    (intersectionMultiplicity_comm _ _ hfiniteCritical).symm.trans hI2'
  have hv2 : F.1.component 0 ∈ maximalIdeal 2 ^ 2 := by
    rw [hfirst, morseCurve]
    exact (maximalIdeal 2 ^ 2).add_mem (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
      ((Ideal.pow_le_pow_right (by omega : 2 ≤ k))
        (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) k))
  obtain ⟨l, hl, e, U, _hU, hev, heh⟩ := exists_smooth_critical_quadratic_normalization
    (F.1.component 0) h hv2 hreduced hh hdh hfiniteh hIh
  obtain ⟨_hv, hmul⟩ := isolatedCriticalPoint_and_milnorNumber_of_quadratic_power_coordinates
    (F.1.component 0) e l hl hev
  have hlk : l = k := by omega
  subst l
  let G := F.comp e.forward
  have hcomponent (i : Fin 3) : G.1.component i = e.pullbackAlgEquiv (F.1.component i) :=
    PointedMapGerm.component_comp_eq_pullback _ _ _
  have hFG : F.RightLeftEquivalent G := by
    refine ⟨e, PointedEquivGerm.identity 3, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  have hGdiff : G.differential = 0 :=
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff hFG).mpr hdifferential
  have hGfirst : G.1.component 0 = morseCurve k := (hcomponent 0).trans hev
  have hGminors (i : Fin 2) : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (G.1.component 0) (G.1.component i.succ) := by
    rw [hcomponent, hcomponent]
    exact e.coordinate_pow_dvd_jacobian_of_pullback_multiple h _ _ U (t - 1) heh (hminors i)
  have hGfinite : HasFiniteIntersection (G.1.component 0) (G.1.component selected.succ) := by
    rw [hcomponent, hcomponent]
    exact hfinitePair.pullback e
  have hGpair : intersectionMultiplicity
      (G.1.component 0) (G.1.component selected.succ) hGfinite = c.squareMultiplicity := by
    simp only [hcomponent]
    exact (intersectionMultiplicity_pullback e hfinitePair).symm.trans hpair
  have hconnected := c.root_reachable_of_generation generation hdecrease
  have hbounded (p : Fin N) : c.multiplicity p ≤ 2 := by
    simpa only [hroot] using c.multiplicity_le_root hconnected p
  have hsum := c.totalMultiplicity_eq_two_mul_count_two_add_count_one hpositive hbounded
  have hsquares := c.squareMultiplicity_eq_four_mul_count_two_add_count_one hpositive hbounded
  have hpolarK : 2 * (t - 1) + Nat.gcd 2 k ≤
      6 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
    rw [hI2'] at hpolar
    omega
  have hbranchPos : 0 < c.branchCount := by
    rw [hb]
    exact Nat.gcd_pos_of_pos_left k (by decide)
  have hkt : k ≤ t := (quadratic_exponent_le_totalMultiplicity
    c hconnected hroot hpositive k hbranchPos hgenusK).trans htransverse
  have alternatives := PointedMapGerm.numerical_alternatives_of_proximity_curveInvariants
    G c hconnected hroot hpositive hk (by simpa only [hb] using hgenusK) htransverse hpolarK
    hGfirst hGminors hGdiff selected hGfinite hGpair
  have heven : Even k ∧ ((c.multiplicityCount 1 = 0 ∧ t = k) ∨
      (c.multiplicityCount 1 = k ∧ t = 2 * k)) := by
    rcases alternatives with hodd | heven
    · obtain ⟨_, _, ht⟩ := hodd
      omega
    · exact heven
  refine ⟨G, hFG, hGdiff, hGfirst, hGminors, ?_, heven.1, heven.2, hGfinite, hGpair⟩
  intro i
  exact (pow_dvd_pow (coordinate (1 : Fin 2)) (Nat.sub_le_sub_right hkt 1)).trans (hGminors i)

end OnLeConjecture.DTwo
