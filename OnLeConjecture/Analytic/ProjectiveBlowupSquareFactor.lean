/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveExceptionalIntersectionExact
public import OnLeConjecture.Analytic.RegularIrreducibleFactorization

/-!
# Persistence of repeated factors under point blowup

Exact ordinary orders add under multiplication. A nonunit repeated
factor has a nonunit strict transform at some projective point, and its
square still divides the strict transform of the original equation.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The product of two germs of exact ordinary orders `m` and `n` has
exact ordinary order `m + n`. -/
theorem exact_maximalIdeal_order_mul
    (m n : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hfn : f ∉ maximalIdeal 2 ^ (m + 1))
    (hg : g ∈ maximalIdeal 2 ^ n) (hgn : g ∉ maximalIdeal 2 ^ (n + 1)) :
    f * g ∈ maximalIdeal 2 ^ (m + n) ∧
      f * g ∉ maximalIdeal 2 ^ (m + n + 1) := by
  constructor
  · simpa only [pow_add] using Ideal.mul_mem_mul hf hg
  · intro hprod
    obtain ⟨P, hP, htail⟩ := exists_weightedHomogeneous_coordinatePolynomial_mod_succ
      1 m (by decide) f (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf)
    have hPne : P ≠ 0 := by
      intro hz
      apply hfn
      simpa only [hz, map_zero, sub_zero, weightedOrderIdeal_one_eq_maximalIdeal_pow] using htail
    apply hgn
    have h := mem_weightedOrderIdeal_of_mul_mem 1 m (n + 1) (by decide)
      P hP hPne f g htail (by
        simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow, Nat.add_assoc] using hprod)
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using h

/-- A germ has a unique exact ordinary order. -/
theorem exact_maximalIdeal_order_unique
    (m n : ℕ) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hfn : f ∉ maximalIdeal 2 ^ (m + 1))
    (hg : f ∈ maximalIdeal 2 ^ n) (hgn : f ∉ maximalIdeal 2 ^ (n + 1)) : m = n := by
  apply le_antisymm
  · by_contra h
    exact hgn (Ideal.pow_le_pow_right (by omega : n + 1 ≤ m) hf)
  · by_contra h
    exact hfn (Ideal.pow_le_pow_right (by omega : m + 1 ≤ n) hg)

/-- Dividing the total ordinary order from a product commutes with the
projective strict transform. -/
theorem projectiveStrictTransform_mul
    (m n : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfg : f * g ∈ maximalIdeal 2 ^ (m + n)) (t : Option ℂ) :
    projectiveStrictTransform (m + n) (f * g) hfg t =
      projectiveStrictTransform m f hf t * projectiveStrictTransform n g hg t := by
  apply pointBlowupTransform_unique _ _ _ _ _ (pointBlowupTransform_factor _ _ _ _)
  simp only [map_mul]
  rw [pointBlowupTransform_factor (projectiveChartCenter t) m
      ((projectiveChartSource t).forward.pullbackRingHom f)
      ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hf),
    pointBlowupTransform_factor (projectiveChartCenter t) n
      ((projectiveChartSource t).forward.pullbackRingHom g)
      ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hg), pow_add]
  dsimp only [projectiveStrictTransform]
  ring

/-- A positive-order equation has a nonunit strict transform somewhere
on the projective exceptional divisor. -/
theorem exists_nonunit_projectiveStrictTransform
    (m : ℕ) (hm : 0 < m) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hfn : f ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ t : Option ℂ, ¬ IsUnit (projectiveStrictTransform m f hf t) := by
  classical
  obtain ⟨s, _, hsum⟩ := exists_projective_exceptional_orders_sum_eq m f hf hfn
  by_contra hnot
  push Not at hnot
  have hz : ∑ t ∈ s, projectiveExceptionalIntersectionOrder m f hf t = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact projectiveExceptionalIntersectionOrder_eq_zero_of_isUnit m f hf t (hnot t)
  omega

/-- A nonreduced nonzero equation has a nonreduced projective strict
transform. That transform has ordinary order at least two. -/
theorem exists_nonreduced_projectiveStrictTransform
    (m : ℕ) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hfn : f ∉ maximalIdeal 2 ^ (m + 1))
    (hbad : ¬ Squarefree f) :
    ∃ t : Option ℂ, ¬ Squarefree (projectiveStrictTransform m f hf t) ∧
      projectiveStrictTransform m f hf t ∈ maximalIdeal 2 ^ 2 := by
  classical
  have hfne : f ≠ 0 := by
    intro hz
    exact hfn (hz ▸ Ideal.zero_mem _)
  obtain ⟨p, hp, hpsq⟩ : ∃ p : Germ 2, Irreducible p ∧ p * p ∣ f := by
    by_contra hnot
    apply hbad
    rw [squarefree_iff_no_irreducibles hfne]
    intro p hp hpsq
    exact hnot ⟨p, hp, hpsq⟩
  obtain ⟨r, hfactor⟩ := hpsq
  have hrne : r ≠ 0 := by
    intro hz
    exact hfne (by rw [hfactor, hz, mul_zero])
  obtain ⟨n, hpn, hpnext⟩ := exists_exact_maximalIdeal_order_of_ne_zero p hp.ne_zero
  obtain ⟨k, hrk, hrnext⟩ := exists_exact_maximalIdeal_order_of_ne_zero r hrne
  have hn : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    rw [hnzero, zero_add, pow_one, mem_maximalIdeal_iff] at hpnext
    exact hp.not_isUnit (isUnit_of_valueRingHom_ne_zero hpnext)
  obtain ⟨hpp, hppnext⟩ := exact_maximalIdeal_order_mul n n p p hpn hpnext hpn hpnext
  obtain ⟨hpph, hpphnext⟩ := exact_maximalIdeal_order_mul (n + n) k (p * p) r
    hpp hppnext hrk hrnext
  have hm : m = (n + n) + k := exact_maximalIdeal_order_unique m ((n + n) + k) f
    hf hfn (hfactor ▸ hpph) (hfactor ▸ hpphnext)
  obtain ⟨t, ht⟩ := exists_nonunit_projectiveStrictTransform n hn p hpn hpnext
  have hpt : projectiveStrictTransform n p hpn t ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    by_contra hvalue
    exact ht (isUnit_of_valueRingHom_ne_zero hvalue)
  have htransform : projectiveStrictTransform m f hf t =
      (projectiveStrictTransform n p hpn t * projectiveStrictTransform n p hpn t) *
        projectiveStrictTransform k r hrk t := by
    subst m
    subst f
    rw [projectiveStrictTransform_mul (n + n) k (p * p) r hpp hrk hf t,
      projectiveStrictTransform_mul n n p p hpn hpn hpp t]
  refine ⟨t, ?_, ?_⟩
  · intro hsq
    exact ht (hsq _ ⟨projectiveStrictTransform k r hrk t, htransform⟩)
  · rw [htransform]
    apply (maximalIdeal 2 ^ 2).mul_mem_right
    simpa only [pow_two] using Ideal.mul_mem_mul hpt hpt

end OnLeConjecture.Analytic.Germ
