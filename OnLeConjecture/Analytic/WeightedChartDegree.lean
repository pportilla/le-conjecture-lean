/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm
public import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# Ordinary order and the degree of a weighted chart polynomial

For weights `(a,1)`, a homogeneous polynomial of degree `a k` whose chart
polynomial has degree `k` has a nonzero pure first-coordinate term.
Restriction to the parametrized axis `(t^a,0)` identifies its order as
`a k`. An analytic germ with that initial form and ordinary order at least
`m` therefore satisfies `m ≤ k`.

Divisibility of a weighted homogeneous polynomial by `y^T` also bounds the
degree of its chart polynomial by `(D-T)/a`.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

/-- In degree `a k`, the coefficient of `x^k` in the chart polynomial is
the value at the first coordinate axis point `(1,0)`. -/
theorem eval_first_axis_eq_weighted_chart_coeff
    (a k : ℕ) (ha : 0 < a) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] (a * k)) :
    MvPolynomial.eval (![1, 0] : Fin 2 → ℂ) P =
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).coeff k := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
      rw [MvPolynomial.eval_add, map_add, coeff_add, ihP, ihQ]
  | monomial d c hd =>
      have hdegree : a * d 0 + d 1 = a * k := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
      by_cases hd0 : d 0 = k
      · have hd1 : d 1 = 0 := by rw [hd0] at hdegree; omega
        simp [MvPolynomial.monomial_fin_two, hd0, hd1]
      · have hd1 : d 1 ≠ 0 := by
          intro hzero
          apply hd0
          nlinarith
        simp [MvPolynomial.monomial_fin_two, hd1, coeff_X_pow, Ne.symm hd0]

/-- A nonzero weighted homogeneous polynomial whose chart reaches degree
`k` in weighted degree `a k` does not vanish at `(1,0)`. -/
theorem eval_first_axis_ne_zero_of_weighted_chart_degree
    (a k : ℕ) (ha : 0 < a) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] (a * k)) (hPzero : P ≠ 0)
    (hdegree : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).natDegree = k) :
    MvPolynomial.eval (![1, 0] : Fin 2 → ℂ) P ≠ 0 := by
  have hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P ≠ 0 := by
    intro hzero
    have hk : k = 0 := by simpa [hzero] using hdegree.symm
    have hPdegreeZero : P.IsWeightedHomogeneous ![a, 1] 0 := by
      simpa [hk] using hP
    have hweights : ∀ i : Fin 2, ![a, 1] i ≠ 0 := by
      intro i
      fin_cases i
      · exact ha.ne'
      · exact one_ne_zero
    have hconstant : P = MvPolynomial.C (MvPolynomial.coeff 0 P) :=
      (MvPolynomial.weightedHomogeneousComponent_eq_self hPdegreeZero).symm.trans
        (MvPolynomial.weightedHomogeneousComponent_zero P hweights)
    have hc : MvPolynomial.coeff 0 P = 0 := by
      rw [hconstant] at hzero
      have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 0) hzero
      simpa using hcoeff
    exact hPzero (by rw [hconstant, hc, map_zero])
  rw [eval_first_axis_eq_weighted_chart_coeff a k ha P hP, ← hdegree]
  rw [coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr hchart

private theorem second_exponent_ge_of_second_power_dvd
    (T : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hdiv : MvPolynomial.X (1 : Fin 2) ^ T ∣ P)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support) :
    T ≤ d 1 := by
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at hcoeff
  simp only [Finsupp.single_le_iff] at hcoeff
  by_contra hnot
  simp [hnot] at hcoeff

/-- A second-coordinate power divisor bounds the degree of the chart of
a weighted homogeneous polynomial. The zero polynomial is allowed. -/
theorem weighted_chart_natDegree_le_of_second_power_dvd
    (a D T : ℕ) (ha : 0 < a) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (hdiv : MvPolynomial.X (1 : Fin 2) ^ T ∣ P) :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).natDegree ≤ (D - T) / a := by
  classical
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [P.as_sum, map_sum, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro d hd
  have hweight : a * d 0 + d 1 = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using
      hP (MvPolynomial.mem_support_iff.mp hd)
  have hT := second_exponent_ge_of_second_power_dvd T P hdiv d hd
  have hdBound : d 0 ≤ (D - T) / a := by
    apply (Nat.le_div_iff_mul_le ha).mpr
    nlinarith [Nat.sub_add_cancel (show T ≤ D by omega)]
  have hdn : n ≠ d 0 := by omega
  simp [MvPolynomial.monomial_fin_two, coeff_X_pow, hdn]

/-- For a nonzero weighted homogeneous polynomial, the second-coordinate
divisor and the chart degree satisfy the corresponding linear inequality. -/
theorem weighted_chart_degree_inequality_of_second_power_dvd
    (a D T : ℕ) (ha : 0 < a) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) (hPzero : P ≠ 0)
    (hdiv : MvPolynomial.X (1 : Fin 2) ^ T ∣ P) :
    a * (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).natDegree + T ≤ D := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hPzero
  have hweight : a * d 0 + d 1 = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using
      hP (MvPolynomial.mem_support_iff.mp hd)
  have hT := second_exponent_ge_of_second_power_dvd T P hdiv d hd
  have hdegree := (Nat.le_div_iff_mul_le ha).mp
    (weighted_chart_natDegree_le_of_second_power_dvd a D T ha P hP hdiv)
  nlinarith [Nat.sub_add_cancel (show T ≤ D by omega)]

end OnLeConjecture.Polynomial

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- On the parametrized axis `(t^a,0)`, an ordinary order of at least `m`
gives one-variable order at least `a m`. -/
theorem weighted_first_axis_pullback_mem_maximalIdeal_pow
    (a m : ℕ) (ha : 0 < a) (f : Germ 2)
    (hf : f ∈ Germ.maximalIdeal 2 ^ m) :
    (Germ.weightedLineMapGerm a ha ![1, 0]).pullbackRingHom f ∈
      Germ.maximalIdeal 1 ^ (a * m) := by
  let gamma := Germ.weightedLineMapGerm a ha (![1, 0] : Source 2)
  have hmap : Ideal.map gamma.pullbackRingHom (Germ.maximalIdeal 2) ≤
      Germ.maximalIdeal 1 ^ a := by
    rw [gamma.map_maximalIdeal_eq_coordinateIdeal, MapGerm.coordinateIdeal_le]
    intro i
    rw [← PointedMapGerm.pullback_coordinate]
    change (Germ.weightedLineMapGerm a ha ![1, 0]).pullbackRingHom
      (Germ.coordinate i) ∈ _
    rw [Germ.weightedLineMapGerm_pullback_coordinate]
    fin_cases i
    · simpa using Ideal.pow_mem_pow (Germ.coordinate_mem_maximalIdeal (0 : Fin 1)) a
    · simp
  have hmapPow : Ideal.map gamma.pullbackRingHom (Germ.maximalIdeal 2 ^ m) ≤
      Germ.maximalIdeal 1 ^ (a * m) := by
    rw [Ideal.map_pow, pow_mul]
    exact pow_le_pow_left' hmap m
  exact hmapPow (Ideal.mem_map_of_mem gamma.pullbackRingHom hf)

/-- The ordinary order of an analytic germ does not exceed the chart
degree when its weighted initial form contains the pure first-coordinate
term of that degree. -/
theorem maximalIdeal_order_le_weighted_chart_degree
    (a m k : ℕ) (ha : 0 < a) (f : Germ 2)
    (hf : f ∈ Germ.maximalIdeal 2 ^ m)
    (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] (a * k)) (hPzero : P ≠ 0)
    (hdegree :
      (MvPolynomial.aeval (![_root_.Polynomial.X, 1] : Fin 2 → ℂ[X]) P).natDegree = k)
    (htail : f - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (a * k + 1)) :
    m ≤ k := by
  by_contra hmk
  have hthreshold : a * k + 1 ≤ a * m := by nlinarith
  let gamma := Germ.weightedLineMapGerm a ha (![1, 0] : Source 2)
  have hfAxis : gamma.pullbackRingHom f ∈ Germ.maximalIdeal 1 ^ (a * k + 1) :=
    Ideal.pow_le_pow_right hthreshold
      (Germ.weighted_first_axis_pullback_mem_maximalIdeal_pow a m ha f hf)
  have htailAxis := Germ.weightedLineMapGerm_pullback_mem_maximalIdeal_pow
    a (a * k + 1) ha (![1, 0] : Source 2) htail
  have hPaxis : gamma.pullbackRingHom (Germ.coordinatePolynomialAlgHom 2 P) ∈
      Germ.maximalIdeal 1 ^ (a * k + 1) := by
    have hsub := (Germ.maximalIdeal 1 ^ (a * k + 1)).sub_mem hfAxis htailAxis
    simpa only [gamma, map_sub, sub_sub_cancel] using hsub
  have hvalue := OnLeConjecture.Polynomial.eval_first_axis_ne_zero_of_weighted_chart_degree
    a k ha P hP hPzero hdegree
  have hunit : IsUnit (Germ.constRingHom 1 (MvPolynomial.eval ![1, 0] P)) := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    simpa using hvalue
  have horder : Germ.vanishingOrder
      (gamma.pullbackRingHom (Germ.coordinatePolynomialAlgHom 2 P)) = a * k := by
    rw [Germ.weightedLineMapGerm_pullback_coordinatePolynomial a (a * k) ha _ hP]
    exact Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hunit rfl
  have hbound := Germ.mem_maximalIdeal_one_pow_iff.mp hPaxis
  rw [horder] at hbound
  have hbad : a * k + 1 ≤ a * k := by exact_mod_cast hbound
  omega

end OnLeConjecture.Analytic.Germ
