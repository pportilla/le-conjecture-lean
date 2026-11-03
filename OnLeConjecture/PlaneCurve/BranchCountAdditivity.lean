/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.BranchCountInvariance
public import OnLeConjecture.PlaneCurve.Intersection
public import OnLeConjecture.Analytic.WeightedPrincipalClosure
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Additivity of the number of analytic branches

Finite intersection forces every common divisor of two plane germs to
be a unit. The principal ideal theorem in the analytic plane proves
this assertion. Their irreducible associate classes are therefore
disjoint, and branch counts add in the product. The statements include
zero and unit germs and do not require squarefreeness.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ UniqueFactorizationMonoid

/-- A finite plane intersection has no common nonunit analytic factor. -/
theorem isRelPrime_of_hasFiniteIntersection
    (f g : Germ 2) (hfinite : HasFiniteIntersection f g) : IsRelPrime f g := by
  intro a haf hag
  by_contra hunit
  have ha : a ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    by_contra hvalue
    exact hunit (isUnit_of_valueRingHom_ne_zero hvalue)
  apply not_maximalIdeal_pow_le_span_singleton a ha
  obtain ⟨n, hn⟩ := (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f g).mp hfinite
  refine ⟨n, hn.trans ?_⟩
  change Ideal.span ({f, g} : Set (Germ 2)) ≤ Ideal.span {a}
  rw [Ideal.span_le]
  intro x hx
  rcases hx with rfl | hx
  · exact Ideal.mem_span_singleton.mpr haf
  · rcases hx with rfl
    exact Ideal.mem_span_singleton.mpr hag

theorem irreducibleBranchCount_eq_zero_of_isUnit
    (f : Germ 2) (hf : IsUnit f) : irreducibleBranchCount f = 0 := by
  rw [irreducibleBranchCount_eq_of_associated (associated_one_iff_isUnit.mpr hf)]
  exact irreducibleBranchCount_one

/-- A product of relatively prime analytic equations has the sum of
their branch counts. Repeated factors within an equation are ignored. -/
theorem irreducibleBranchCount_mul_of_isRelPrime
    (f g : Germ 2) (hrel : IsRelPrime f g) :
    irreducibleBranchCount (f * g) = irreducibleBranchCount f + irreducibleBranchCount g := by
  classical
  by_cases hf : f = 0
  · subst f
    have hg := isRelPrime_zero_left.mp hrel
    simp only [zero_mul, irreducibleBranchCount_zero,
      irreducibleBranchCount_eq_zero_of_isUnit g hg, add_zero]
  by_cases hg : g = 0
  · subst g
    have hfunit := isRelPrime_zero_right.mp hrel
    simp only [mul_zero, irreducibleBranchCount_zero,
      irreducibleBranchCount_eq_zero_of_isUnit f hfunit, add_zero]
  have hfmk : Associates.mk f ≠ 0 := by simpa using hf
  have hgmk : Associates.mk g ≠ 0 := by simpa using hg
  have hdisjoint : Disjoint (normalizedFactors (Associates.mk f)).toFinset
      (normalizedFactors (Associates.mk g)).toFinset :=
    Multiset.disjoint_toFinset.mpr
      (disjoint_normalizedFactors (Associates.mk_isRelPrime_iff.mpr hrel))
  rw [irreducibleBranchCount, ← Associates.mk_mul_mk,
    normalizedFactors_mul hfmk hgmk, Multiset.toFinset_add,
    Finset.card_union_of_disjoint hdisjoint]
  rfl

/-- Finiteness is the geometric hypothesis excluding a shared branch.
No separate disjointness or coprimality certificate is required. -/
theorem irreducibleBranchCount_mul_of_hasFiniteIntersection
    (f g : Germ 2) (hfinite : HasFiniteIntersection f g) :
    irreducibleBranchCount (f * g) = irreducibleBranchCount f + irreducibleBranchCount g :=
  irreducibleBranchCount_mul_of_isRelPrime f g (isRelPrime_of_hasFiniteIntersection f g hfinite)

/-- Branch-count additivity for a finite collection of analytic factors
whose distinct pairs have finite intersection. -/
theorem irreducibleBranchCount_prod_of_pairwise_finite
    {ι : Type*} (s : Finset ι) (f : ι → Germ 2)
    (hfinite : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → HasFiniteIntersection (f i) (f j)) :
    irreducibleBranchCount (∏ i ∈ s, f i) = ∑ i ∈ s, irreducibleBranchCount (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hpair (i) (hi : i ∈ s) : IsRelPrime (f a) (f i) :=
      isRelPrime_of_hasFiniteIntersection _ _
        (hfinite a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact ha hi))
    rw [Finset.prod_insert ha, irreducibleBranchCount_mul_of_isRelPrime
      _ _ (IsRelPrime.prod_right hpair), Finset.sum_insert ha]
    congr 1
    exact ih (fun i hi j hj hij =>
      hfinite i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)

end OnLeConjecture.PlaneCurve
