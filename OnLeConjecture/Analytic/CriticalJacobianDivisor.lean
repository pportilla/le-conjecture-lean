/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CriticalJacobianNonzero
public import OnLeConjecture.Analytic.PlaneUniqueFactorization
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# The common divisor of the coordinate Jacobians

The three ordered coordinate minors have a greatest common divisor in the
plane analytic germ ring. Factoring it gives distinct irreducible germs
with positive orders. The integers defined by adding one to these orders
are used below. Identifying them with transverse curve multiplicities
requires a separate geometric argument.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ
open scoped BigOperators

/-- Factorization of a greatest common divisor of all coordinate minors.
The support may be empty, in which case the common divisor is a unit. -/
structure CriticalJacobianFactorization (g : PointedMapGerm 2 3) where
  support : Finset (Germ 2)
  order : Germ 2 → ℕ
  irreducible : ∀ p ∈ support, Irreducible p
  order_pos : ∀ p ∈ support, 0 < order p
  component_mem : ∀ p ∈ support, p ∈ maximalIdeal 2
  pairwise_not_associated : (support : Set (Germ 2)).Pairwise fun p q => ¬Associated p q
  common_dvd_iff : ∀ d : Germ 2,
    d ∣ ∏ p ∈ support, p ^ order p ↔
      ∀ j k : Fin 3, d ∣ jacobian (g.1.component j) (g.1.component k)
  order_maximal : ∀ p ∈ support, ∀ n : ℕ,
    (∀ j k : Fin 3, p ^ n ∣ jacobian (g.1.component j) (g.1.component k)) ↔
      n ≤ order p

namespace PointedMapGerm

/-- Ordered pairs indexing the three coordinate minors. -/
def coordinateMinorPairs : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter fun ij => ij.1 < ij.2

/-- Unique factorization constructs the common coordinate Jacobian divisor
whenever at least one coordinate Jacobian is nonzero. -/
@[expose] noncomputable def criticalJacobianFactorizationOfNonzero
    (g : PointedMapGerm 2 3)
    (hne : ∃ j k, jacobian (g.1.component j) (g.1.component k) ≠ 0) :
    CriticalJacobianFactorization g := by
  classical
  let _ : StrongNormalizationMonoid (Germ 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : NormalizedGCDMonoid (Germ 2) :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid (Germ 2)
  let J : Fin 3 × Fin 3 → Germ 2 := fun ij =>
    jacobian (g.1.component ij.1) (g.1.component ij.2)
  let d : Germ 2 := coordinateMinorPairs.gcd J
  have hnonzero : d ≠ 0 := by
    apply Finset.gcd_ne_zero_iff.mpr
    obtain ⟨j, k, hjk⟩ := hne
    rcases lt_trichotomy j k with hlt | heq | hgt
    · exact ⟨(j, k), by simp [coordinateMinorPairs, hlt], hjk⟩
    · subst k
      exact (hjk (jacobian_self _)).elim
    · refine ⟨(k, j), by simp [coordinateMinorPairs, hgt], ?_⟩
      change jacobian (g.1.component k) (g.1.component j) ≠ 0
      rw [jacobian_swap]
      exact neg_ne_zero.mpr hjk
  have hdvd (a : Germ 2) : a ∣ d ↔
      ∀ j k : Fin 3, a ∣ jacobian (g.1.component j) (g.1.component k) := by
    rw [Finset.dvd_gcd_iff]
    constructor
    · intro ha j k
      rcases lt_trichotomy j k with hlt | heq | hgt
      · exact ha (j, k) (by simp [coordinateMinorPairs, hlt])
      · subst k
        rw [jacobian_self]
        exact dvd_zero _
      · rw [jacobian_swap]
        exact dvd_neg.mpr (ha (k, j) (by simp [coordinateMinorPairs, hgt]))
    · intro ha ij _
      exact ha ij.1 ij.2
  let factors := UniqueFactorizationMonoid.normalizedFactors d
  have hfactor : Associated (∏ p ∈ factors.toFinset, p ^ factors.count p) d := by
    rw [← Finset.prod_multiset_count]
    exact UniqueFactorizationMonoid.prod_normalizedFactors hnonzero
  refine {
    support := factors.toFinset
    order := factors.count
    irreducible := ?_
    order_pos := ?_
    component_mem := ?_
    pairwise_not_associated := ?_
    common_dvd_iff := ?_
    order_maximal := ?_ }
  · intro p hp
    exact UniqueFactorizationMonoid.irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp hp)
  · intro p hp
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
  · intro p hp
    apply mem_maximalIdeal_iff.mpr
    apply Classical.byContradiction
    intro hvalue
    exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp hp)).not_isUnit (isUnit_of_valueRingHom_ne_zero hvalue)
  · intro p hp q hq hne hpq
    exact hne (UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
      (Multiset.mem_toFinset.mp hp) (Multiset.mem_toFinset.mp hq) hpq)
  · intro a
    exact hfactor.dvd_iff_dvd_right.trans (hdvd a)
  · intro p hp n
    have hpmem := Multiset.mem_toFinset.mp hp
    have hpirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hpmem
    rw [← hdvd (p ^ n), pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hpirr hnonzero,
      UniqueFactorizationMonoid.normalize_normalized_factor p hpmem]
    exact ENat.natCast_le_natCast

/-- An injective representative supplies the nonzero Jacobian required by
the common-divisor factorization. -/
@[expose] noncomputable def criticalJacobianFactorization
    (g : PointedMapGerm 2 3) (hinjective : g.HasInjectiveRepresentative) :
    CriticalJacobianFactorization g :=
  g.criticalJacobianFactorizationOfNonzero (g.exists_jacobian_ne_zero_of_injective hinjective)

end PointedMapGerm

namespace CriticalJacobianFactorization

variable {g : PointedMapGerm 2 3} (D : CriticalJacobianFactorization g)

/-- The product of the irreducible common factors with their full orders. -/
@[expose] noncomputable def divisor : Germ 2 :=
  ∏ p ∈ D.support, p ^ D.order p

theorem divisor_ne_zero : D.divisor ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (D.irreducible p hp).ne_zero

theorem divisor_dvd (j k : Fin 3) :
    D.divisor ∣ jacobian (g.1.component j) (g.1.component k) :=
  (D.common_dvd_iff D.divisor).mp dvd_rfl j k

theorem pow_dvd_minors (p : Germ 2) (hp : p ∈ D.support) (j k : Fin 3) :
    p ^ D.order p ∣ jacobian (g.1.component j) (g.1.component k) :=
  (Finset.dvd_prod_of_mem (fun p => p ^ D.order p) hp).trans (D.divisor_dvd j k)

/-- The largest common-factor order plus one, with value zero for empty
support. This definition does not assert a transverse geometric meaning. -/
@[expose] noncomputable def maxMultiplicity : ℕ :=
  D.support.sup fun p => D.order p + 1

theorem support_nonempty_of_maxMultiplicity_pos (hpos : 0 < D.maxMultiplicity) :
    D.support.Nonempty := by
  by_contra h
  have hempty : D.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [maxMultiplicity, hempty] at hpos

theorem exists_order_add_one_eq_maxMultiplicity (hpos : 0 < D.maxMultiplicity) :
    ∃ p ∈ D.support, D.order p + 1 = D.maxMultiplicity := by
  obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup D.support
    (D.support_nonempty_of_maxMultiplicity_pos hpos) (fun p => D.order p + 1)
  exact ⟨p, hp, heq.symm⟩

/-- Every nonunit common divisor contains one of the irreducibles in the
constructed support. -/
theorem exists_mem_support_dvd_of_not_isUnit
    (h : Germ 2) (hunit : ¬IsUnit h)
    (hdiv : ∀ j k : Fin 3, h ∣ jacobian (g.1.component j) (g.1.component k)) :
    ∃ p ∈ D.support, p ∣ h := by
  classical
  have hhD : h ∣ D.divisor := (D.common_dvd_iff h).mpr hdiv
  have hhne := ne_zero_of_dvd_ne_zero D.divisor_ne_zero hhD
  obtain ⟨p, hp, hph⟩ := WfDvdMonoid.exists_irreducible_factor hunit hhne
  have hpD : p ∣ ∏ q ∈ D.support, q ^ D.order q := hph.trans hhD
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpD
  have hassoc := hp.associated_of_dvd (D.irreducible q hq) (hp.prime.dvd_of_dvd_pow hpq)
  exact ⟨q, hq, hassoc.dvd'.trans hph⟩

/-- A nonunit equation whose `(t - 1)`st power divides every coordinate
minor gives a lower bound for the maximal common-factor order plus one.
The equation need not be irreducible. -/
theorem le_maxMultiplicity_of_nonunit_pow_dvd
    (h : Germ 2) (hunit : ¬IsUnit h) (t : ℕ) (ht : 2 ≤ t)
    (hdiv : ∀ j k : Fin 3, h ^ (t - 1) ∣
      jacobian (g.1.component j) (g.1.component k)) :
    t ≤ D.maxMultiplicity := by
  have hpos : t - 1 ≠ 0 := by omega
  obtain ⟨p, hp, hph⟩ := D.exists_mem_support_dvd_of_not_isUnit h hunit
    (fun j k => (dvd_pow_self h hpos).trans (hdiv j k))
  have horder : t - 1 ≤ D.order p := (D.order_maximal p hp (t - 1)).mp
    (fun j k => (pow_dvd_pow_of_dvd hph (t - 1)).trans (hdiv j k))
  have hmax : D.order p + 1 ≤ D.maxMultiplicity :=
    Finset.le_sup (f := fun p => D.order p + 1) hp
  omega

/-- The maximum depends only on the coordinate minors, not on a choice of
normalization or representatives for their common irreducible factors. -/
theorem maxMultiplicity_eq (E : CriticalJacobianFactorization g) :
    D.maxMultiplicity = E.maxMultiplicity := by
  have hle (A B : CriticalJacobianFactorization g) :
      A.maxMultiplicity ≤ B.maxMultiplicity := by
    apply Finset.sup_le
    intro p hp
    apply B.le_maxMultiplicity_of_nonunit_pow_dvd p (A.irreducible p hp).not_isUnit
      (A.order p + 1) (by have h := A.order_pos p hp; omega)
    intro j k
    simpa using A.pow_dvd_minors p hp j k
  exact le_antisymm (hle D E) (hle E D)

end CriticalJacobianFactorization

end OnLeConjecture.Analytic
