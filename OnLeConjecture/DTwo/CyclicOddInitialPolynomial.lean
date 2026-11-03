/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.HomogeneousEqualizerPolynomialDescent
public import OnLeConjecture.DTwo.PreparedPrimitiveChartIdentity

/-!
# The odd part of a cyclic weighted initial polynomial

The odd projection in the first variable is constructed from the polynomial.
For weights `(L,2)` and odd degree multiplier `N`, its monomials are precisely
of the form `x^(N-2h)*y^(L*h)`. This supplies a polynomial in normalized
variables of weights `(1,2)` without assuming a prepared coefficient formula.
-/

public section

namespace OnLeConjecture.DTwo

open scoped BigOperators

@[expose] noncomputable def reflectFirstPolynomial :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval ![-MvPolynomial.X 0, MvPolynomial.X 1]

@[expose] noncomputable def oddFirstPolynomial (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C (1 / 2 : ℂ) * (P - reflectFirstPolynomial P)

theorem eval_reflectFirstPolynomial (P : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    MvPolynomial.eval ![x, y] (reflectFirstPolynomial P) =
      MvPolynomial.eval ![-x, y] P := by
  have h : (MvPolynomial.aeval ![x, y]).comp reflectFirstPolynomial =
      MvPolynomial.aeval ![-x, y] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [reflectFirstPolynomial]
  exact DFunLike.congr_fun h P

theorem eval_oddFirstPolynomial (P : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    MvPolynomial.eval ![x, y] (oddFirstPolynomial P) =
      (MvPolynomial.eval ![x, y] P - MvPolynomial.eval ![-x, y] P) / 2 := by
  simp only [oddFirstPolynomial, map_mul, MvPolynomial.eval_C, map_sub,
    eval_reflectFirstPolynomial]
  ring

theorem oddFirstPolynomial_add (P Q : MvPolynomial (Fin 2) ℂ) :
    oddFirstPolynomial (P + Q) = oddFirstPolynomial P + oddFirstPolynomial Q := by
  simp only [oddFirstPolynomial, map_add]
  ring

theorem reflectFirstPolynomial_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) :
    reflectFirstPolynomial (MvPolynomial.monomial d c) =
      MvPolynomial.C ((-1 : ℂ) ^ d 0) * MvPolynomial.monomial d c := by
  rw [MvPolynomial.monomial_fin_two]
  simp only [reflectFirstPolynomial, map_mul, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, MvPolynomial.algebraMap_eq,
    map_neg, map_one]
  rw [neg_pow]
  ring

theorem oddFirstPolynomial_monomial_even (d : Fin 2 →₀ ℕ) (c : ℂ) (hd : Even (d 0)) :
    oddFirstPolynomial (MvPolynomial.monomial d c) = 0 := by
  rw [oddFirstPolynomial, reflectFirstPolynomial_monomial, hd.neg_one_pow]
  simp

theorem oddFirstPolynomial_monomial_odd (d : Fin 2 →₀ ℕ) (c : ℂ) (hd : Odd (d 0)) :
    oddFirstPolynomial (MvPolynomial.monomial d c) = MvPolynomial.monomial d c := by
  rw [oddFirstPolynomial, reflectFirstPolynomial_monomial, hd.neg_one_pow]
  simp only [map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add]
  calc
    _ = (MvPolynomial.C (1 / 2 : ℂ) + MvPolynomial.C (1 / 2 : ℂ)) *
      MvPolynomial.monomial d c := by ring
    _ = _ := by rw [← map_add]; norm_num

theorem oddFirstPolynomial_isWeightedHomogeneous {L D : ℕ}
    {P : MvPolynomial (Fin 2) ℂ} (hP : P.IsWeightedHomogeneous ![L, 2] D) :
    (oddFirstPolynomial P).IsWeightedHomogeneous ![L, 2] D := by
  have href : (reflectFirstPolynomial P).IsWeightedHomogeneous ![L, 2] D := by
    apply OnLeConjecture.Polynomial.isWeightedHomogeneous_aeval ![L, 2] ![L, 2] _ _ hP
    intro i
    fin_cases i
    · exact (MvPolynomial.isWeightedHomogeneous_X ℂ ![L, 2] 0).neg
    · exact MvPolynomial.isWeightedHomogeneous_X ℂ ![L, 2] 1
  simpa only [oddFirstPolynomial, zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C ![L, 2] (1 / 2 : ℂ)).mul (hP.sub href)

private theorem odd_weight_exponents {L N a b : ℕ} (hL : 0 < L)
    (hN : Odd N) (ha : Odd a) (hweight : L * a + 2 * b = L * N) :
    ∃ h : ℕ, a + 2 * h = N ∧ b = L * h := by
  have haN : a ≤ N := by nlinarith
  obtain ⟨n, hn⟩ := hN
  obtain ⟨q, hq⟩ := ha
  refine ⟨n - q, ?_, ?_⟩
  · omega
  · have h : a + 2 * (n - q) = N := by omega
    nlinarith

/-- The odd projection has an actual polynomial preimage in the normalized
variables `x,T=τ*y^L`, and this preimage has weights `(1,2)` and degree `N`. -/
theorem exists_normalized_odd_polynomial {L N : ℕ} (hL : 0 < L) (hN : Odd N)
    (τ : ℂ) (hτ : τ ≠ 0) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![L, 2] (L * N)) :
    ∃ H : MvPolynomial (Fin 2) ℂ, H.IsWeightedHomogeneous ![1, 2] N ∧
      oddFirstPolynomial P = MvPolynomial.aeval
        ![MvPolynomial.X 0, MvPolynomial.C τ * MvPolynomial.X 1 ^ L] H := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0, MvPolynomial.isWeightedHomogeneous_zero ℂ _ _, by simp [oddFirstPolynomial]⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨H, hH, heqH⟩ := ihp
    obtain ⟨K, hK, heqK⟩ := ihq
    exact ⟨H + K, hH.add hK, by rw [oddFirstPolynomial_add, heqH, heqK, map_add]⟩
  | monomial d c hd =>
    rcases Nat.even_or_odd (d 0) with heven | hodd
    · exact ⟨0, MvPolynomial.isWeightedHomogeneous_zero ℂ _ _, by
        rw [oddFirstPolynomial_monomial_even d c heven, map_zero]⟩
    have hweight : L * d 0 + 2 * d 1 = L * N := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
    obtain ⟨h, ha, hb⟩ := odd_weight_exponents hL hN hodd hweight
    let e : Fin 2 →₀ ℕ := Finsupp.single 0 (d 0) + Finsupp.single 1 h
    refine ⟨MvPolynomial.monomial e (c / τ ^ h), ?_, ?_⟩
    · apply MvPolynomial.isWeightedHomogeneous_monomial
      simpa [e, Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using ha
    · rw [oddFirstPolynomial_monomial_odd d c hodd]
      rw [MvPolynomial.monomial_fin_two d c, MvPolynomial.monomial_fin_two e]
      simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, MvPolynomial.algebraMap_eq]
      have he0 : e 0 = d 0 := by simp [e]
      have he1 : e 1 = h := by simp [e]
      rw [he0, he1, hb, mul_pow, ← map_pow]
      have hc : c / τ ^ h * τ ^ h = c := div_mul_cancel₀ _ (pow_ne_zero h hτ)
      calc
        _ = (MvPolynomial.C (c / τ ^ h * τ ^ h) : MvPolynomial (Fin 2) ℂ) * MvPolynomial.X 0 ^ d 0 *
            MvPolynomial.X 1 ^ (L * h) := by rw [hc]
        _ = _ := by simp only [map_mul, pow_mul]; ring

/-- Taking the odd part preserves the primitive comparison when `N` is odd. -/
theorem oddFirstPolynomial_primitive_chart {N : ℕ} (hN : Odd N)
    (P : MvPolynomial (Fin 2) ℂ) (C ζ cD : ℂ)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + C →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = cD * (s - S) ^ N) :
    ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + C →
      MvPolynomial.eval ![s, 1] (oddFirstPolynomial P) -
        MvPolynomial.eval ![S, ζ] (oddFirstPolynomial P) = cD * (s - S) ^ N := by
  intro s S hS hpoint
  have hpos := hchart s S hS hpoint
  have hneg := hchart (-s) (-S) (neg_ne_zero.mpr hS) (by simpa using hpoint)
  rw [show -s - -S = -(s - S) by ring, hN.neg_pow, mul_neg] at hneg
  simp only [eval_oddFirstPolynomial]
  linear_combination (hpos - hneg) / 2

theorem evenFirstPolynomial_zero_chart {N : ℕ} (hN : Odd N)
    (P : MvPolynomial (Fin 2) ℂ) (C ζ cD : ℂ)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + C →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = cD * (s - S) ^ N) :
    ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + C →
      MvPolynomial.eval ![s, 1] (P - oddFirstPolynomial P) -
        MvPolynomial.eval ![S, ζ] (P - oddFirstPolynomial P) = 0 := by
  intro s S hS hpoint
  have hodd := oddFirstPolynomial_primitive_chart hN P C ζ cD hchart s S hS hpoint
  have h := hchart s S hS hpoint
  simp only [map_sub]
  linear_combination h - hodd

private theorem eval_normalized_substitution (τ : ℂ) (L : ℕ)
    (H : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    MvPolynomial.eval ![x, y]
      (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C τ * MvPolynomial.X 1 ^ L] H) =
      MvPolynomial.eval ![x, τ * y ^ L] H := by
  have h : (MvPolynomial.aeval ![x, y]).comp
      (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C τ * MvPolynomial.X 1 ^ L]) =
      MvPolynomial.aeval ![x, τ * y ^ L] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact DFunLike.congr_fun h H

private theorem eval_weighted_scale_two {H : MvPolynomial (Fin 2) ℂ}
    {w : Fin 2 → ℕ} {D : ℕ} (hH : H.IsWeightedHomogeneous w D)
    (t : ℂ) (z : Fin 2 → ℂ) :
    MvPolynomial.eval (fun i => t ^ w i * z i) H = t ^ D * MvPolynomial.eval z H := by
  induction hH using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [MvPolynomial.eval_add, ihp, ihq, mul_add]
  | monomial d c hd =>
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
      Finsupp.prod_pow, Finsupp.prod_pow]
    simp_rw [mul_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hsum : ∑ i, w i * d i = D := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
    rw [hsum]
    ring

/-- A square root of `τ` changes the primitive comparison to the normalized
chart `T=1`. Its scaling factor cancels because both sides have degree `N`. -/
theorem normalized_odd_polynomial_primitive_chart {k j N : ℕ} (hN : Odd N)
    {τ ζ cD : ℂ} (hτ : τ ≠ 0) (hζ : ζ ^ k = 1)
    (P H : MvPolynomial (Fin 2) ℂ) (hH : H.IsWeightedHomogeneous ![1, 2] N)
    (hPH : oddFirstPolynomial P =
      MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C τ * MvPolynomial.X 1 ^ (k + j)] H)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + τ * (1 - ζ ^ j) →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = cD * (s - S) ^ N) :
    ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (1 - ζ ^ j) →
      MvPolynomial.eval ![s, 1] H - MvPolynomial.eval ![S, ζ ^ j] H = cD * (s - S) ^ N := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq τ (by omega : 0 < (2 : ℕ))
  have ht0 : t ≠ 0 := fun h => hτ (by simpa [h] using ht.symm)
  have hζL : ζ ^ (k + j) = ζ ^ j := by rw [pow_add, hζ, one_mul]
  intro s S hS hpoint
  have hscaled : (t * S) ^ 2 = (t * s) ^ 2 + τ * (1 - ζ ^ j) := by
    rw [mul_pow, mul_pow, ht, hpoint]; ring
  have h := oddFirstPolynomial_primitive_chart hN P _ ζ cD hchart
    (t * s) (t * S) (mul_ne_zero ht0 hS) hscaled
  rw [hPH, eval_normalized_substitution, eval_normalized_substitution] at h
  simp only [one_pow, mul_one, hζL] at h
  have heval (x T : ℂ) : MvPolynomial.eval ![t * x, τ * T] H =
      t ^ N * MvPolynomial.eval ![x, T] H := by
    convert eval_weighted_scale_two hH t ![x, T] using 1
    congr 2
    funext i
    fin_cases i <;> simp [ht]
  have heval1 : MvPolynomial.eval ![t * s, τ] H =
      t ^ N * MvPolynomial.eval ![s, 1] H := by simpa using heval s 1
  rw [heval1, heval,
    show t * s - t * S = t * (s - S) by ring, mul_pow] at h
  apply (mul_left_cancel₀ (pow_ne_zero N ht0))
  linear_combination h

theorem eval_second_zero_of_normalized_homogeneous {N : ℕ}
    (H : MvPolynomial (Fin 2) ℂ) (hH : H.IsWeightedHomogeneous ![1, 2] N) (x : ℂ) :
    MvPolynomial.eval ![x, 0] H = preparedCoefficient N H 0 * x ^ N := by
  have h := congrArg (MvPolynomial.eval ![x, 0])
    (eq_preparedOddBivariatePolynomial_of_isWeightedHomogeneous hH)
  rw [h]
  simp only [preparedOddBivariatePolynomial, map_sum, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    simp [zero_pow hi0]
  · simp

/-- The primitive comparison itself proves that the leading coefficient
is nonzero. Evaluation on `T=0, X=-x` gives its exact scalar relation. -/
theorem leading_coefficient_ne_zero_of_primitive_chart {N : ℕ} (hN : Odd N)
    (χ cD : ℂ) (hχ : χ ≠ 1) (hcD : cD ≠ 0)
    (H : MvPolynomial (Fin 2) ℂ) (hH : H.IsWeightedHomogeneous ![1, 2] N)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (1 - χ) →
      MvPolynomial.eval ![s, 1] H - MvPolynomial.eval ![S, χ] H = cD * (s - S) ^ N) :
    preparedCoefficient N H 0 ≠ 0 := by
  have h := cyclicInitial_primitive_identity_of_chart 1 N (1 - χ) χ cD
    (sub_ne_zero.mpr hχ.symm) H (by simpa using hH) hchart
    (-1 : ℂ) (1 : ℂ) (0 : ℂ) (by norm_num)
  change MvPolynomial.eval ![1, 0] H - MvPolynomial.eval ![-1, χ * 0] H =
    cD * (1 - -1) ^ N at h
  rw [mul_zero, eval_second_zero_of_normalized_homogeneous H hH,
    eval_second_zero_of_normalized_homogeneous H hH, one_pow, hN.neg_one_pow] at h
  intro hzero
  rw [hzero] at h
  have : cD * (2 : ℂ) ^ N = 0 := by simpa using h.symm
  exact mul_ne_zero hcD (pow_ne_zero N (by norm_num)) this

/-- The normalized polynomial and its primitive comparison construct a
prepared odd family after an explicitly justified nonzero scalar division. -/
theorem exists_scaled_prepared_model_of_normalized_chart {N : ℕ}
    (hN : 3 ≤ N) (hodd : Odd N) (χ cD : ℂ) (hχ : χ ≠ 1) (hcD : cD ≠ 0)
    (H : MvPolynomial (Fin 2) ℂ) (hH : H.IsWeightedHomogeneous ![1, 2] N)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (1 - χ) →
      MvPolynomial.eval ![s, 1] H - MvPolynomial.eval ![S, χ] H = cD * (s - S) ^ N) :
    χ = -1 ∧ ∃ a : ℂ, a ≠ 0 ∧ ∃ Ψ : PreparedOddFamily N, ∃ model : Ψ.BivariateModel,
      H = MvPolynomial.C a * model.polynomial ∧
      PreparedPrimitiveComponentIdentity N χ (a⁻¹ * cD)
        (preparedCoefficient N model.polynomial) := by
  let a := preparedCoefficient N H 0
  have ha : a ≠ 0 := leading_coefficient_ne_zero_of_primitive_chart hodd χ cD hχ hcD H hH hchart
  let K := MvPolynomial.C a⁻¹ * H
  have hK : K.IsWeightedHomogeneous ![1, 2] N := by
    simpa only [K, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C ![1, 2] a⁻¹).mul hH
  have hzero : preparedCoefficient N K 0 = 1 := by
    change MvPolynomial.coeff (preparedExponent N 0) (MvPolynomial.C a⁻¹ * H) = 1
    rw [MvPolynomial.coeff_C_mul]
    exact inv_mul_cancel₀ ha
  have hKchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (1 - χ) →
      MvPolynomial.eval ![s, 1] K - MvPolynomial.eval ![S, χ] K =
        (a⁻¹ * cD) * (s - S) ^ N := by
    intro s S hS hpoint
    simp only [K, map_mul, MvPolynomial.eval_C]
    rw [← mul_sub, hchart s S hS hpoint]
    ring
  obtain ⟨hnext, hchar, Ψ, model, hmodel⟩ :=
    exists_preparedOddFamily_model_of_homogeneous_chart N hN hodd χ (a⁻¹ * cD)
      hχ K hK hzero hKchart
  refine ⟨hchar, a, ha, Ψ, model, ?_, ?_⟩
  · rw [hmodel]
    change H = MvPolynomial.C a * (MvPolynomial.C a⁻¹ * H)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  · rw [hmodel]
    exact (preparedPrimitiveComponentIdentity_of_homogeneous_chart N χ (a⁻¹ * cD)
      hχ K hK hKchart).2

/-- An actual weighted initial polynomial with primitive affine comparison
supplies the prepared odd model, its component identity, and the polynomial
target correction removing its even part. All coefficient formulas and
normalizing scalars are constructed from `P`. -/
theorem exists_cyclic_prepared_model_of_primitive_weighted_chart
    {k j N : ℕ} (hk : 0 < k) (hN : 3 ≤ N) (hodd : Odd N)
    {b c ζ cD : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hcD : cD ≠ 0)
    (hζ : IsPrimitiveRoot ζ k) (hchar : ζ ^ j ≠ 1)
    (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![k + j, 2] ((k + j) * N))
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (-b / c) * (1 - ζ ^ j) →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = cD * (s - S) ^ N) :
    ζ ^ j = -1 ∧ ∃ a : ℂ, a ≠ 0 ∧ ∃ Ψ : PreparedOddFamily N, ∃ model : Ψ.BivariateModel,
      (P - MvPolynomial.C a *
          MvPolynomial.aeval
            ![MvPolynomial.X 0, MvPolynomial.C (-b / c) * MvPolynomial.X 1 ^ (k + j)]
            model.polynomial) ∈
        Set.range (MvPolynomial.aeval
          ![MvPolynomial.X 1 ^ k,
            -MvPolynomial.C c * MvPolynomial.X 0 ^ 2 +
              MvPolynomial.C b * MvPolynomial.X 1 ^ (k + j)] :
          MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
      PreparedPrimitiveComponentIdentity N (ζ ^ j) (a⁻¹ * cD)
        (preparedCoefficient N model.polynomial) := by
  have hτ : -b / c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) hc
  obtain ⟨H, hH, hPH⟩ := exists_normalized_odd_polynomial (by omega : 0 < k + j)
    hodd (-b / c) hτ P hP
  have hHchart := normalized_odd_polynomial_primitive_chart hodd hτ hζ.pow_eq_one
    P H hH hPH hchart
  obtain ⟨hminus, a, ha, Ψ, model, hmodel, hidentity⟩ :=
    exists_scaled_prepared_model_of_normalized_chart hN hodd (ζ ^ j) cD hchar hcD H hH hHchart
  have hevenHomogeneous := hP.sub (oddFirstPolynomial_isWeightedHomogeneous hP)
  have hevenChart := evenFirstPolynomial_zero_chart hodd P _ ζ cD hchart
  obtain ⟨R, hR⟩ := exists_initial_pair_polynomial_of_weighted_chart hk hb hc hζ hchar
    (P - oddFirstPolynomial P) hevenHomogeneous hevenChart
  refine ⟨hminus, a, ha, Ψ, model, ⟨R, ?_⟩, hidentity⟩
  rw [hR, hPH, hmodel, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

end OnLeConjecture.DTwo
