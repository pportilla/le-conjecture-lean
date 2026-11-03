/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddNorm
public import OnLeConjecture.DThree.HHardOddHomogeneous

/-!
# Local order of the odd H norm

The two summands in the hard norm have orders of opposite parity at either
point over `X = 1`. Their difference therefore has the smaller of the two
orders. This bounds the local order of the norm in terms of the order of the
descended conic difference.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

/-- The first squared expression in the odd norm. -/
@[expose]
noncomputable def hHardOddMiddle
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    RatFunc ℂ :=
  hConicDifference Rzero ^ 2 +
    algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
      (hConicParamW ^ N - hConicParamCapitalW ^ N)

/-- The second squared expression in the odd norm. -/
@[expose]
noncomputable def hHardOddRight
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    RatFunc ℂ :=
  algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
    hConicDifference Rzero ^ 2 * hConicParamW ^ N

theorem hHardOddNorm_eq_middle_sq_sub_right
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    hHardOddNorm Rzero coefficient N =
      hHardOddMiddle Rzero coefficient N ^ 2 -
        hHardOddRight Rzero coefficient N := by
  rfl

private theorem valuation_inverse_sub_eq_one_of
    {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    [Inv Γ₀] (v : Valuation R Γ₀) {f g : R}
    (hne : (v.toMonoidWithZeroHom f)⁻¹ ≠
      (v.toMonoidWithZeroHom g)⁻¹) :
    (v.toMonoidWithZeroHom (f - g))⁻¹ =
        (v.toMonoidWithZeroHom f)⁻¹ ∨
      (v.toMonoidWithZeroHom (f - g))⁻¹ =
        (v.toMonoidWithZeroHom g)⁻¹ := by
  have hv : v f ≠ v g := by
    intro hequal
    apply hne
    exact congrArg Inv.inv hequal
  have hvaluation : v (f - g) = max (v f) (v g) := by
    rw [sub_eq_add_neg, v.map_add_of_distinct_val]
    · rw [v.map_neg]
    · rwa [v.map_neg]
  rcases le_total (v f) (v g) with hle | hle
  · right
    exact congrArg Inv.inv
      (hvaluation.trans (max_eq_right hle))
  · left
    exact congrArg Inv.inv
      (hvaluation.trans (max_eq_left hle))

/-- Under subtraction, a conventional finite order equals one of two
distinct input orders. -/
theorem h_finite_order_sub_eq_one_of_ne
    {K : Type*} [Field K] (a : K) {f g : RatFunc K}
    (hne : hFiniteOrderAt a f ≠ hFiniteOrderAt a g) :
    hFiniteOrderAt a (f - g) = hFiniteOrderAt a f ∨
      hFiniteOrderAt a (f - g) = hFiniteOrderAt a g := by
  simp only [hFiniteOrderAt, MonoidWithZeroHom.comp_apply,
    MonoidWithZero.inverse_apply, Ring.inverse_eq_inv] at hne ⊢
  exact valuation_inverse_sub_eq_one_of
    ((hParameterPrime K a).valuation (RatFunc K)) hne

private theorem valuation_inverse_sub_eq_left_of_exp_lt
    {R : Type*} [Ring R]
    (v : Valuation R ℤᵐ⁰) {f g : R} {m n : ℤ}
    (hf : (v.toMonoidWithZeroHom f)⁻¹ = WithZero.exp m)
    (hg : (v.toMonoidWithZeroHom g)⁻¹ = WithZero.exp n)
    (hmn : m < n) :
    (v.toMonoidWithZeroHom (f - g))⁻¹ = WithZero.exp m := by
  have hvf : v f = WithZero.exp (-m) := by
    have hinverse := congrArg Inv.inv hf
    simpa only [Valuation.toMonoidWithZeroHom_coe_eq_coe,
      inv_inv, WithZero.exp_neg] using hinverse
  have hvg : v g = WithZero.exp (-n) := by
    have hinverse := congrArg Inv.inv hg
    simpa only [Valuation.toMonoidWithZeroHom_coe_eq_coe,
      inv_inv, WithZero.exp_neg] using hinverse
  have hcomparison : v g < v f := by
    rw [hvf, hvg, WithZero.exp_lt_exp]
    omega
  have hvaluation := v.map_sub_eq_of_lt_left hcomparison
  have hinverse := congrArg Inv.inv hvaluation
  exact hinverse.trans hf

/-- If two finite orders have strictly increasing integer exponents, the
order of their difference is the first exponent. -/
theorem h_finite_order_sub_eq_left_of_exp_lt
    {K : Type*} [Field K] (a : K) {f g : RatFunc K} {m n : ℤ}
    (hf : hFiniteOrderAt a f = WithZero.exp m)
    (hg : hFiniteOrderAt a g = WithZero.exp n)
    (hmn : m < n) :
    hFiniteOrderAt a (f - g) = WithZero.exp m := by
  simp only [hFiniteOrderAt, MonoidWithZeroHom.comp_apply,
    MonoidWithZero.inverse_apply, Ring.inverse_eq_inv] at hf hg ⊢
  exact valuation_inverse_sub_eq_left_of_exp_lt
    ((hParameterPrime K a).valuation (RatFunc K)) hf hg hmn

/-- If the second finite order exponent is smaller, subtraction has that
second order. -/
theorem h_finite_order_sub_eq_right_of_exp_lt
    {K : Type*} [Field K] (a : K) {f g : RatFunc K} {m n : ℤ}
    (hf : hFiniteOrderAt a f = WithZero.exp m)
    (hg : hFiniteOrderAt a g = WithZero.exp n)
    (hnm : n < m) :
    hFiniteOrderAt a (f - g) = WithZero.exp n := by
  simp only [hFiniteOrderAt, MonoidWithZeroHom.comp_apply,
    MonoidWithZero.inverse_apply, Ring.inverse_eq_inv] at hf hg ⊢
  let v := (hParameterPrime K a).valuation (RatFunc K)
  have hreverse := valuation_inverse_sub_eq_left_of_exp_lt
    v hg hf hnm
  have hswap := v.map_sub_swap f g
  have hinverse := congrArg Inv.inv hswap
  exact hinverse.trans hreverse

/-- A nonzero scalar rational function has finite order zero. -/
theorem h_finite_order_scalar
    {K : Type*} [Field K] (a c : K) (hc : c ≠ 0) :
    hFiniteOrderAt a (algebraMap K (RatFunc K) c) = 1 := by
  rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C]
  exact h_finite_order_polynomial_of_eval_ne_zero a (C c) (by simpa)

/-- A nonzero rational function regular at a finite point has a
nonnegative integer order there. -/
theorem exists_h_finite_order_of_regular
    {K : Type*} [Field K] (a : K) (f : RatFunc K)
    (hf : f ≠ 0) (hregular : HRatFuncRegularAt a f) :
    ∃ k : ℕ, hFiniteOrderAt a f = WithZero.exp (k : ℤ) := by
  refine ⟨f.num.rootMultiplicity a, ?_⟩
  rw [h_finite_order_eq_rootMultiplicity_sub a f hf]
  have hdenominator : f.denom.rootMultiplicity a = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    simpa [HRatFuncRegularAt, Polynomial.IsRoot] using hregular
  rw [hdenominator]
  simp

/-- The middle expression in the hard norm is regular at either point over
`X = 1`. -/
theorem hHardOddMiddle_regular_at_one
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient a : ℂ) (N : ℕ)
    (ha : a ^ 2 + 2 * a + 4 = 0) :
    HRatFuncRegularAt a (hHardOddMiddle Rzero coefficient N) := by
  have hlinear := h_conic_param_one_root_add_one_ne_zero ha
  have hden : hConicParamDenominator.eval a ≠ 0 := by
    simpa [hConicParamDenominator] using
      h_conic_param_denominator_at_one_root_ne_zero ha
  obtain ⟨_hx, hw, hW⟩ := h_conic_param_regular_at a hlinear hden
  have hA := hConicDifference_regular_at Rzero a hlinear hden
  let cTwo : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)
  have hcTwo : HRatFuncRegularAt a cTwo := by
    change HRatFuncRegularAt a (RatFunc.C (coefficient ^ 2))
    exact hRatFuncRegularAt_C a (coefficient ^ 2)
  change HRatFuncRegularAt a
    (hConicDifference Rzero ^ 2 + cTwo *
      (hConicParamW ^ N - hConicParamCapitalW ^ N))
  exact hRatFuncRegularAt_add
    (hRatFuncRegularAt_pow hA 2)
    (hRatFuncRegularAt_mul hcTwo
      (hRatFuncRegularAt_sub
        (hRatFuncRegularAt_pow hw N)
        (hRatFuncRegularAt_pow hW N)))

/-- At a point over `X = 1`, the right summand in the hard norm has order
`2k+N` when the conic difference has order `k`. -/
theorem hHardOddNorm_right_order_at_one
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient a : ℂ)
    (N k : ℕ) (hcoefficient : coefficient ≠ 0)
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hAorder : hFiniteOrderAt a (hConicDifference Rzero) =
      WithZero.exp (k : ℤ)) :
    hFiniteOrderAt a
        (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
          hConicDifference Rzero ^ 2 * hConicParamW ^ N) =
      WithZero.exp ((2 * k + N : ℕ) : ℤ) := by
  have hscalar : (4 : ℂ) * coefficient ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hcoefficient)
  rw [map_mul, map_mul, map_pow, map_pow,
    h_finite_order_scalar a _ hscalar, hAorder,
    h_conic_param_w_order_at_one ha]
  simp

/-- The local order of the odd norm at either point over `X = 1` is at most
`2k+N`, where `k` is the local order of the descended difference. -/
theorem exists_hHardOddNorm_order_at_one_le
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient a : ℂ)
    (N k : ℕ) (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hAorder : hFiniteOrderAt a (hConicDifference Rzero) =
      WithZero.exp (k : ℤ)) :
    ∃ r : ℕ,
      hFiniteOrderAt a (hHardOddNorm Rzero coefficient N) =
          WithZero.exp (r : ℤ) ∧
        r ≤ 2 * k + N := by
  obtain ⟨j, rfl⟩ := hNodd
  let middle := hHardOddMiddle Rzero coefficient (2 * j + 1)
  let right := hHardOddRight Rzero coefficient (2 * j + 1)
  have hright : hFiniteOrderAt a right =
      WithZero.exp ((2 * k + (2 * j + 1) : ℕ) : ℤ) := by
    exact hHardOddNorm_right_order_at_one
      Rzero coefficient a (2 * j + 1) k hcoefficient ha hAorder
  by_cases hmiddleZero : middle = 0
  · refine ⟨2 * k + (2 * j + 1), ?_, le_rfl⟩
    rw [hHardOddNorm_eq_middle_sq_sub_right]
    change hFiniteOrderAt a (middle ^ 2 - right) = _
    rw [hmiddleZero, zero_pow (by norm_num : 2 ≠ 0), zero_sub]
    rw [show -right = algebraMap ℂ (RatFunc ℂ) (-1) * right by
      simp, map_mul, h_finite_order_scalar a (-1) (by norm_num), hright,
      one_mul]
  · obtain ⟨ell, hell⟩ := exists_h_finite_order_of_regular
      a middle hmiddleZero
        (by simpa only [middle] using
          hHardOddMiddle_regular_at_one Rzero coefficient a (2 * j + 1) ha)
    have hleft : hFiniteOrderAt a (middle ^ 2) =
        WithZero.exp ((2 * ell : ℕ) : ℤ) := by
      rw [map_pow, hell]
      simp
    have hexponentsNe :
        ((2 * ell : ℕ) : ℤ) ≠
          ((2 * k + (2 * j + 1) : ℕ) : ℤ) := by
      omega
    rcases lt_or_gt_of_ne hexponentsNe with hless | hgreater
    · refine ⟨2 * ell, ?_, by omega⟩
      rw [hHardOddNorm_eq_middle_sq_sub_right]
      change hFiniteOrderAt a (middle ^ 2 - right) = _
      exact h_finite_order_sub_eq_left_of_exp_lt
        a hleft hright hless
    · refine ⟨2 * k + (2 * j + 1), ?_, le_rfl⟩
      rw [hHardOddNorm_eq_middle_sq_sub_right]
      change hFiniteOrderAt a (middle ^ 2 - right) = _
      exact h_finite_order_sub_eq_right_of_exp_lt
        a hleft hright hgreater

end OnLeConjecture.DThree
