/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IntersectionAdditivity

/-!
# Intersection bounds for products of divisors

Finite product additivity converts a divisor of a polar equation into a
weighted sum of component intersections. All multiplicities are lengths
of the actual analytic local intersection algebras.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic
open scoped BigOperators

/-- Intersection multiplicity is monotone under divisibility of the
first equation, when both intersections are finite. -/
theorem intersectionMultiplicity_le_of_dvd_left
    (f g h : Germ 2) (hf : HasFiniteIntersection f h) (hg : HasFiniteIntersection g h)
    (hdiv : f ∣ g) : intersectionMultiplicity f h hf ≤ intersectionMultiplicity g h hg := by
  obtain ⟨a, rfl⟩ := hdiv
  have ha := ((hasFiniteIntersection_mul_left_iff f a h).mp hg).2
  rw [intersectionMultiplicity_mul_left f a h hf ha hg]
  omega

/-- A positive power does not change the finite-intersection condition. -/
theorem HasFiniteIntersection.pow_left {f g : Germ 2}
    (hfinite : HasFiniteIntersection f g) (n : ℕ) : HasFiniteIntersection (f ^ n) g := by
  induction n with
  | zero =>
      apply (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le _ _).mpr
      refine ⟨0, ?_⟩
      simp only [pow_zero]
      have htop : pairIdeal 1 g = ⊤ :=
        (pairIdeal 1 g).eq_top_of_isUnit_mem (Ideal.subset_span (by simp)) isUnit_one
      rw [htop]
      exact le_top
  | succ n ih =>
      rw [pow_succ]
      exact (hasFiniteIntersection_mul_left_iff _ _ _).mpr ⟨ih, hfinite⟩

/-- A power multiplies its local intersection number by the exponent. -/
theorem intersectionMultiplicity_pow_left
    (f g : Germ 2) (n : ℕ) (hf : HasFiniteIntersection f g)
    (hpow : HasFiniteIntersection (f ^ n) g) :
    intersectionMultiplicity (f ^ n) g hpow = n * intersectionMultiplicity f g hf := by
  induction n with
  | zero =>
      have h1 : HasFiniteIntersection 1 g := by simpa only [pow_zero] using hpow
      simpa only [pow_zero, zero_mul] using
        intersectionMultiplicity_eq_zero_of_isUnit_left 1 g isUnit_one h1
  | succ n ih =>
      have hprev := hf.pow_left n
      have hmul : HasFiniteIntersection (f ^ n * f) g := by simpa only [pow_succ] using hpow
      have heq := intersectionMultiplicity_mul_left _ _ _ hprev hf hmul
      rw [ih hprev] at heq
      simpa only [pow_succ, Nat.succ_mul] using heq

/-- Arbitrary finite products satisfy intersection additivity. -/
theorem intersectionMultiplicity_finset_prod_left
    {ι : Type*} (s : Finset ι) (F : ι → Germ 2) (g : Germ 2)
    (hF : ∀ i, HasFiniteIntersection (F i) g)
    (hprod : HasFiniteIntersection (∏ i ∈ s, F i) g) :
    intersectionMultiplicity (∏ i ∈ s, F i) g hprod =
      ∑ i ∈ s, intersectionMultiplicity (F i) g (hF i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using intersectionMultiplicity_eq_zero_of_isUnit_left 1 g isUnit_one hprod
  | @insert i s hi ih =>
      have hmul : HasFiniteIntersection (F i * ∏ j ∈ s, F j) g := by
        simpa only [Finset.prod_insert hi] using hprod
      have hs := ((hasFiniteIntersection_mul_left_iff _ _ _).mp hmul).2
      have heq := intersectionMultiplicity_mul_left _ _ _ (hF i) hs hmul
      rw [ih hs] at heq
      simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using heq

/-- A product of powered equations dividing a finite-intersection
equation contributes at most the latter's intersection number. -/
theorem weighted_intersection_sum_le_of_product_pow_dvd
    {ι : Type*} [Fintype ι] (F : ι → Germ 2) (n : ι → ℕ) (g J : Germ 2)
    (hF : ∀ i, HasFiniteIntersection (F i) g) (hJ : HasFiniteIntersection J g)
    (hdiv : (∏ i, F i ^ n i) ∣ J) :
    (∑ i, intersectionMultiplicity (F i) g (hF i) * n i) ≤
      intersectionMultiplicity J g hJ := by
  classical
  have hprod : HasFiniteIntersection (∏ i, F i ^ n i) g := by
    obtain ⟨a, ha⟩ := hdiv
    rw [ha] at hJ
    exact ((hasFiniteIntersection_mul_left_iff _ _ _).mp hJ).1
  have hsum := intersectionMultiplicity_finset_prod_left Finset.univ
    (fun i => F i ^ n i) g (fun i => (hF i).pow_left (n i)) hprod
  have heq : intersectionMultiplicity (∏ i, F i ^ n i) g hprod =
      ∑ i, intersectionMultiplicity (F i) g (hF i) * n i := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    exact (intersectionMultiplicity_pow_left _ _ _ (hF i) _).trans (Nat.mul_comm _ _)
  rw [← heq]
  exact intersectionMultiplicity_le_of_dvd_left _ _ _ hprod hJ hdiv

end OnLeConjecture.PlaneCurve
