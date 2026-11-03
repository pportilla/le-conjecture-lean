/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneUniqueFactorization
public import OnLeConjecture.Analytic.WeightedPrincipalClosure
public import OnLeConjecture.PlaneCurve.Intersection
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Topology.Separation.Basic

/-!
# Reduced members of a finite analytic pencil

A repeated irreducible factor of `f + c g` divides `J(f,g)`. A nonzero
Jacobian has only finitely many irreducible factors up to association.
Finite intersection of `f` and `g` ensures that any nonunit factor divides
at most one member of the pencil. Consequently only finitely many complex
coefficients give a nonreduced member, and every nonempty open coefficient
set contains a reduced member.

The nonzero Jacobian is an explicit hypothesis. No generic reduced-member
assertion, principalization existence, or reduction estimate is assumed.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic

/-- A finite plane intersection has no common nonunit analytic divisor. -/
theorem HasFiniteIntersection.isUnit_of_common_divisor
    {f g : Germ 2} (hfinite : HasFiniteIntersection f g)
    (p : Germ 2) (hpf : p ∣ f) (hpg : p ∣ g) : IsUnit p := by
  by_contra hunit
  have hp : p ∈ Analytic.Germ.maximalIdeal 2 := by
    rw [Analytic.Germ.mem_maximalIdeal_iff]
    by_contra hvalue
    exact hunit (Analytic.Germ.isUnit_of_valueRingHom_ne_zero hvalue)
  apply Analytic.Germ.not_maximalIdeal_pow_le_span_singleton p hp
  obtain ⟨N, hN⟩ := (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f g).mp hfinite
  refine ⟨N, hN.trans ?_⟩
  rw [pairIdeal, Ideal.span_le]
  rintro _ (rfl | rfl)
  · exact Ideal.mem_span_singleton.mpr hpf
  · exact Ideal.mem_span_singleton.mpr hpg

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic.Germ

open PlaneCurve UniqueFactorizationMonoid
open scoped BigOperators

/-- A square factor of the first equation divides its Jacobian with
every second equation, by the product rule. -/
theorem dvd_jacobian_of_square_dvd_left
    (p F G : Germ 2) (hfactor : p * p ∣ F) : p ∣ jacobian F G := by
  obtain ⟨u, rfl⟩ := hfactor
  refine ⟨p * jacobian u G + 2 * u * jacobian p G, ?_⟩
  simp only [jacobian_eq, partialDerivative_mul]
  ring

/-- Adding a constant multiple of the second equation leaves the
Jacobian unchanged. -/
theorem jacobian_pencil_member (f g : Germ 2) (c : ℂ) :
    jacobian (f + constRingHom 2 c * g) g = jacobian f g := by
  simp only [jacobian_add_left, jacobian_mul_left, jacobian_self,
    jacobian_const_left, mul_zero, add_zero]

theorem pencil_member_ne_zero_of_jacobian_ne_zero
    (f g : Germ 2) (hJ : jacobian f g ≠ 0) (c : ℂ) :
    f + constRingHom 2 c * g ≠ 0 := by
  intro hz
  have h := jacobian_pencil_member f g c
  rw [hz] at h
  have hzero : jacobian (0 : Germ 2) g = 0 := by
    simpa only [map_zero] using jacobian_const_left 0 g
  exact hJ (h.symm.trans hzero)

/-- A nonunit analytic divisor can occur in at most one member of a
pencil whose generators have finite intersection. -/
theorem pencil_coefficients_eq_of_common_nonunit_divisor
    (f g : Germ 2) (hfinite : HasFiniteIntersection f g)
    (p : Germ 2) (hp : ¬ IsUnit p) (c d : ℂ)
    (hc : p ∣ f + constRingHom 2 c * g)
    (hd : p ∣ f + constRingHom 2 d * g) : c = d := by
  by_contra hcd
  have hsub : p ∣ constRingHom 2 (c - d) * g := by
    have h := dvd_sub hc hd
    convert h using 1
    rw [map_sub]
    ring
  have hu : IsUnit (constRingHom 2 (c - d)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hcd)).map (constRingHom 2)
  have hpg : p ∣ g := hu.dvd_mul_left.mp hsub
  have hpf : p ∣ f := by
    have h := dvd_sub hc (dvd_mul_of_dvd_right hpg (constRingHom 2 c))
    simpa using h
  exact hp (hfinite.isUnit_of_common_divisor p hpf hpg)

/-- Every nonreduced pencil member is divisible by one of finitely many
irreducible factors of the fixed Jacobian. -/
theorem exists_jacobian_factor_dvd_of_not_squarefree_pencil
    (f g : Germ 2) (hJ : jacobian f g ≠ 0) (c : ℂ)
    (hbad : ¬ Squarefree (f + constRingHom 2 c * g)) :
    ∃ p ∈ factors (jacobian f g), p ∣ f + constRingHom 2 c * g := by
  have hne := pencil_member_ne_zero_of_jacobian_ne_zero f g hJ c
  obtain ⟨p, hp, hpsq⟩ : ∃ p : Germ 2, Irreducible p ∧
      p * p ∣ f + constRingHom 2 c * g := by
    by_contra hnot
    apply hbad
    rw [squarefree_iff_no_irreducibles hne]
    intro p hp hpsq
    exact hnot ⟨p, hp, hpsq⟩
  have hpJ : p ∣ jacobian f g := by
    rw [← jacobian_pencil_member f g c]
    exact dvd_jacobian_of_square_dvd_left p _ g hpsq
  obtain ⟨r, hr, hpr⟩ := exists_mem_factors_of_dvd hJ hp hpJ
  exact ⟨r, hr, hpr.dvd_iff_dvd_left.mp ((dvd_mul_right p p).trans hpsq)⟩

/-- There are only finitely many nonreduced members of the analytic
pencil when its generators have finite intersection and nonzero Jacobian. -/
theorem finite_not_squarefree_pencil
    (f g : Germ 2) (hfinite : HasFiniteIntersection f g) (hJ : jacobian f g ≠ 0) :
    {c : ℂ | ¬ Squarefree (f + constRingHom 2 c * g)}.Finite := by
  classical
  let K := (factors (jacobian f g)).toFinset
  have hK : (⋃ p ∈ (K : Set (Germ 2)),
      {c : ℂ | p ∣ f + constRingHom 2 c * g}).Finite := by
    apply K.finite_toSet.biUnion
    intro p hp
    apply Set.Subsingleton.finite
    intro c hc d hd
    have hpirr : Irreducible p := irreducible_of_factor p (by simpa only [K,
      Finset.mem_coe, Multiset.mem_toFinset] using hp)
    exact pencil_coefficients_eq_of_common_nonunit_divisor f g hfinite p hpirr.not_isUnit c d hc hd
  apply hK.subset
  intro c hc
  obtain ⟨p, hp, hpc⟩ := exists_jacobian_factor_dvd_of_not_squarefree_pencil f g hJ c hc
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
    ⟨by simpa only [K, Finset.mem_coe, Multiset.mem_toFinset] using hp, hpc⟩⟩

/-- Reducedness holds outside a finite set of coefficients. -/
theorem eventually_cofinite_squarefree_pencil
    (f g : Germ 2) (hfinite : HasFiniteIntersection f g) (hJ : jacobian f g ≠ 0) :
    ∀ᶠ c : ℂ in Filter.cofinite, Squarefree (f + constRingHom 2 c * g) :=
  Filter.eventually_cofinite.mpr (finite_not_squarefree_pencil f g hfinite hJ)

/-- A reduced pencil member can be chosen in any prescribed nonempty
open subset of the complex coefficient line. -/
theorem exists_squarefree_pencil_member_mem_open
    (f g : Germ 2) (hfinite : HasFiniteIntersection f g) (hJ : jacobian f g ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ c ∈ U, Squarefree (f + constRingHom 2 c * g) := by
  obtain ⟨z, hz⟩ := hne
  have hinfinite : U.Infinite := infinite_of_mem_nhds z (hU.mem_nhds hz)
  obtain ⟨c, hcU, hc⟩ := hinfinite.exists_notMem_finite
    (finite_not_squarefree_pencil f g hfinite hJ)
  exact ⟨c, hcU, not_not.mp hc⟩

/-- The reduced members form a dense open subset of the coefficient line. -/
theorem isOpen_dense_squarefree_pencil
    (f g : Germ 2) (hfinite : HasFiniteIntersection f g) (hJ : jacobian f g ≠ 0) :
    IsOpen {c : ℂ | Squarefree (f + constRingHom 2 c * g)} ∧
      Dense {c : ℂ | Squarefree (f + constRingHom 2 c * g)} := by
  constructor
  · simpa only [Set.compl_ofPred, not_not] using
      (finite_not_squarefree_pencil f g hfinite hJ).isClosed.isOpen_compl
  · rw [dense_iff_inter_open]
    intro U hU hne
    obtain ⟨c, hcU, hc⟩ := exists_squarefree_pencil_member_mem_open f g hfinite hJ U hU hne
    exact ⟨c, hcU, hc⟩

end OnLeConjecture.Analytic.Germ
