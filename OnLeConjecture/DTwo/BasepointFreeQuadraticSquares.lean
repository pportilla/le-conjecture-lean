/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticJetAlgebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Two independent squares in a quadratic pencil

After normalizing the first leading coefficient and subtracting it from
the second member, a pencil has the form `x²+bxy+cy²`, `exy+fy²`.
The absence of a common projective zero produces two independent squares.
Both the source and the target coefficient determinants are nonzero.
-/

public section

namespace OnLeConjecture.DTwo

theorem exists_independent_squares_in_monic_quadratic_pencil
    (b c e f : ℂ) (hQ : e ≠ 0 ∨ f ≠ 0)
    (hno : ∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) →
      ¬ (x ^ 2 + b * x * y + c * y ^ 2 = 0 ∧ e * x * y + f * y ^ 2 = 0)) :
    ∃ r s t u a₁ b₁ a₂ b₂ : ℂ,
      r * u - s * t ≠ 0 ∧ a₁ * b₂ - b₁ * a₂ ≠ 0 ∧
      binaryLinearForm r s ^ 2 =
        MvPolynomial.C a₁ * binaryQuadraticForm 1 b c +
          MvPolynomial.C b₁ * binaryQuadraticForm 0 e f ∧
      binaryLinearForm t u ^ 2 =
        MvPolynomial.C a₂ * binaryQuadraticForm 1 b c +
          MvPolynomial.C b₂ * binaryQuadraticForm 0 e f := by
  by_cases he : e = 0
  · have hf : f ≠ 0 := hQ.resolve_left (not_not.mpr he)
    refine ⟨1, b / 2, 0, 1, 1, (b ^ 2 / 4 - c) / f, 0, 1 / f,
      by norm_num, by simpa using inv_ne_zero hf, ?_, ?_⟩
    · have hc : c + (b ^ 2 / 4 - c) / f * f = (b / 2) ^ 2 := by field_simp; ring
      have hb : 2 * (b / 2) = b := by ring
      have hmapped := congrArg (MvPolynomial.C : ℂ → OrbitSourceForm) hc
      simp only [map_add, map_mul, map_pow] at hmapped
      have hbmapped := congrArg (MvPolynomial.C : ℂ → OrbitSourceForm) hb
      simp only [map_mul, map_ofNat] at hbmapped
      simp only [binaryLinearForm, binaryQuadraticForm, he, map_zero, map_one,
        zero_mul, one_mul, add_zero, zero_add]
      linear_combination
        -(orbitPolynomialLambda ℂ) ^ 2 * hmapped +
          orbitPolynomialS ℂ * orbitPolynomialLambda ℂ * hbmapped
    · have hh : MvPolynomial.C (1 / f) * MvPolynomial.C f =
          (1 : OrbitSourceForm) := by
        rw [← map_mul, one_div, inv_mul_cancel₀ hf, map_one]
      simp only [binaryLinearForm, binaryQuadraticForm, he, map_zero, map_one,
        zero_mul, one_mul, add_zero, zero_add]
      rw [← mul_assoc, hh, one_mul]
  · have hR : f ^ 2 - b * f * e + c * e ^ 2 ≠ 0 := by
      intro hz
      apply hno (-f) e (Or.inr he)
      constructor
      · linear_combination hz
      · ring
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self (f ^ 2 - b * f * e + c * e ^ 2)
    have hdsq : d ^ 2 = f ^ 2 - b * f * e + c * e ^ 2 := by
      simpa only [pow_two] using hd.symm
    have hdne : d ≠ 0 := by intro hz; apply hR; rw [← hdsq, hz]; simp
    let s := (f + d) / e
    let u := (f - d) / e
    let q := (2 * s - b) / e
    let q' := (2 * u - b) / e
    have hsu : u - s = -2 * d / e := by dsimp [u, s]; ring
    have hqq : q' - q = -4 * d / e ^ 2 := by dsimp [q', q, u, s]; field_simp; ring
    have hsource : u - s ≠ 0 := by
      rw [hsu]
      exact div_ne_zero (mul_ne_zero (by norm_num) hdne) he
    have htarget : q' - q ≠ 0 := by
      rw [hqq]
      exact div_ne_zero (mul_ne_zero (by norm_num) hdne) (pow_ne_zero 2 he)
    have hb (w : ℂ) : b + (2 * w - b) / e * e = 2 * w := by field_simp; ring
    have hc₁ : c + q * f = s ^ 2 := by
      dsimp [q, s]
      field_simp
      linear_combination -hdsq
    have hc₂ : c + q' * f = u ^ 2 := by
      dsimp [q', u]
      field_simp
      linear_combination -hdsq
    have hsquare (w z : ℂ) (hz : b + z * e = 2 * w) (hc : c + z * f = w ^ 2) :
        binaryLinearForm 1 w ^ 2 = binaryQuadraticForm 1 b c +
          MvPolynomial.C z * binaryQuadraticForm 0 e f := by
      have hzm := congrArg (MvPolynomial.C : ℂ → OrbitSourceForm) hz
      have hcm := congrArg (MvPolynomial.C : ℂ → OrbitSourceForm) hc
      simp only [map_add, map_mul, map_pow, map_ofNat] at hzm hcm
      simp only [binaryLinearForm, binaryQuadraticForm, map_zero, map_one,
        zero_mul, one_mul, zero_add]
      linear_combination
        -orbitPolynomialS ℂ * orbitPolynomialLambda ℂ * hzm -
          orbitPolynomialLambda ℂ ^ 2 * hcm
    refine ⟨1, s, 1, u, 1, q, 1, q', by simpa using hsource,
      by simpa using htarget, ?_, ?_⟩
    · simpa only [map_one, one_mul] using hsquare s q (hb s) hc₁
    · simpa only [map_one, one_mul] using hsquare u q' (hb u) hc₂

/-- Normalization of a nonzero first leading coefficient retains explicit
invertible target coefficients for the two square members. -/
theorem exists_independent_squares_of_first_quadratic_coefficient_ne_zero
    (a b c d e f : ℂ) (ha : a ≠ 0)
    (hpair : ¬ ∃ z : ℂ, binaryQuadraticForm d e f =
      MvPolynomial.C z * binaryQuadraticForm a b c)
    (hno : ∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) →
      ¬ (a * x ^ 2 + b * x * y + c * y ^ 2 = 0 ∧
        d * x ^ 2 + e * x * y + f * y ^ 2 = 0)) :
    ∃ r s t u a₁ b₁ a₂ b₂ : ℂ,
      r * u - s * t ≠ 0 ∧ a₁ * b₂ - b₁ * a₂ ≠ 0 ∧
      binaryLinearForm r s ^ 2 =
        MvPolynomial.C a₁ * binaryQuadraticForm a b c +
          MvPolynomial.C b₁ * binaryQuadraticForm d e f ∧
      binaryLinearForm t u ^ 2 =
        MvPolynomial.C a₂ * binaryQuadraticForm a b c +
          MvPolynomial.C b₂ * binaryQuadraticForm d e f := by
  let E := e - d * (b / a)
  let F := f - d * (c / a)
  have haunit : (MvPolynomial.C a : OrbitSourceForm) * MvPolynomial.C (a⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have hfirst : binaryQuadraticForm 1 (b / a) (c / a) =
      MvPolynomial.C (a⁻¹) * binaryQuadraticForm a b c := by
    simp only [binaryQuadraticForm, div_eq_mul_inv, map_mul, map_one]
    linear_combination -(orbitPolynomialS ℂ) ^ 2 * haunit
  have hsecond : binaryQuadraticForm 0 E F = binaryQuadraticForm d e f -
      MvPolynomial.C (d / a) * binaryQuadraticForm a b c := by
    simp only [binaryQuadraticForm, E, F, div_eq_mul_inv, map_mul, map_sub,
      map_zero, zero_mul, zero_add]
    linear_combination (MvPolynomial.C d * orbitPolynomialS ℂ ^ 2) * haunit
  have hEF : E ≠ 0 ∨ F ≠ 0 := by
    by_contra hz
    push Not at hz
    apply hpair
    refine ⟨d / a, ?_⟩
    have hzero : binaryQuadraticForm 0 E F = 0 := by
      simp [hz.1, hz.2, binaryQuadraticForm]
    rw [hsecond] at hzero
    exact sub_eq_zero.mp hzero
  have hno' : ∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) →
      ¬ (x ^ 2 + (b / a) * x * y + (c / a) * y ^ 2 = 0 ∧ E * x * y + F * y ^ 2 = 0) := by
    intro x y hxy hz
    apply hno x y hxy
    constructor
    · have h := hz.1
      field_simp at h
      linear_combination h
    · have h := hz.2
      dsimp only [E, F] at h
      field_simp at h
      have hP := hz.1
      field_simp at hP
      have heq : a * (d * x ^ 2 + e * x * y + f * y ^ 2) = 0 := by
        linear_combination d * hP + h
      exact (mul_eq_zero.mp heq).resolve_left ha
  obtain ⟨r, s, t, u, A, B, C, D, hsource, htarget, h₁, h₂⟩ :=
    exists_independent_squares_in_monic_quadratic_pencil (b / a) (c / a) E F hEF hno'
  have hrewrite (A B : ℂ) :
      MvPolynomial.C A * binaryQuadraticForm 1 (b / a) (c / a) +
        MvPolynomial.C B * binaryQuadraticForm 0 E F =
      MvPolynomial.C ((A - B * d) / a) * binaryQuadraticForm a b c +
        MvPolynomial.C B * binaryQuadraticForm d e f := by
    rw [hfirst, hsecond]
    simp only [div_eq_mul_inv, map_mul, map_sub]
    ring
  refine ⟨r, s, t, u, (A - B * d) / a, B, (C - D * d) / a, D,
    hsource, ?_, h₁.trans (hrewrite A B), h₂.trans (hrewrite C D)⟩
  have hdet : (A - B * d) / a * D - B * ((C - D * d) / a) =
      (A * D - B * C) / a := by ring
  rw [hdet]
  exact div_ne_zero htarget ha

/-- Every basepoint-free two-dimensional pencil of binary quadratics
contains two squares with independent linear roots. -/
theorem exists_independent_squares_of_basepointFree_quadratic_pencil
    (P Q : OrbitSourceForm) (hP : P.IsHomogeneous 2) (hQ : Q.IsHomogeneous 2)
    (hPne : P ≠ 0) (hpair : ¬ ∃ z : ℂ, Q = MvPolynomial.C z * P)
    (hno : ∀ z : Fin 2 → ℂ, z ≠ 0 →
      ¬ (MvPolynomial.eval z P = 0 ∧ MvPolynomial.eval z Q = 0)) :
    ∃ r s t u a₁ b₁ a₂ b₂ : ℂ,
      r * u - s * t ≠ 0 ∧ a₁ * b₂ - b₁ * a₂ ≠ 0 ∧
      binaryLinearForm r s ^ 2 = MvPolynomial.C a₁ * P + MvPolynomial.C b₁ * Q ∧
      binaryLinearForm t u ^ 2 = MvPolynomial.C a₂ * P + MvPolynomial.C b₂ * Q := by
  let a := binaryQuadraticCoefficients P 0
  let b := binaryQuadraticCoefficients P 1
  let c := binaryQuadraticCoefficients P 2
  let d := binaryQuadraticCoefficients Q 0
  let e := binaryQuadraticCoefficients Q 1
  let f := binaryQuadraticCoefficients Q 2
  have hPeq : P = binaryQuadraticForm a b c := eq_binaryQuadraticForm_of_isHomogeneous hP
  have hQeq : Q = binaryQuadraticForm d e f := eq_binaryQuadraticForm_of_isHomogeneous hQ
  have hno' : ∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) →
      ¬ (a * x ^ 2 + b * x * y + c * y ^ 2 = 0 ∧
        d * x ^ 2 + e * x * y + f * y ^ 2 = 0) := by
    intro x y hxy hz
    apply hno ![x, y] _
    · simpa [hPeq, hQeq, binaryQuadraticForm, orbitPolynomialS, orbitPolynomialLambda] using hz
    · intro hzero
      have hx := congrFun hzero 0
      have hy := congrFun hzero 1
      exact hxy.elim (fun h => h hx) (fun h => h hy)
  by_cases ha : a ≠ 0
  · obtain ⟨r, s, t, u, A, B, C, D, hs, ht, h₁, h₂⟩ :=
      exists_independent_squares_of_first_quadratic_coefficient_ne_zero a b c d e f ha
        (by simpa only [← hPeq, ← hQeq] using hpair) hno'
    exact ⟨r, s, t, u, A, B, C, D, hs, ht,
      by simpa only [← hPeq, ← hQeq] using h₁,
      by simpa only [← hPeq, ← hQeq] using h₂⟩
  · have ha0 : a = 0 := not_not.mp ha
    have hd : d ≠ 0 := by
      intro hz
      apply hno' 1 0 (Or.inl one_ne_zero)
      simp [ha0, hz]
    have hpair' : ¬ ∃ z : ℂ, P = MvPolynomial.C z * Q := by
      rintro ⟨z, hz⟩
      have hzne : z ≠ 0 := by
        intro hzero
        apply hPne
        simp only [hzero, map_zero, zero_mul] at hz
        exact hz
      apply hpair
      refine ⟨z⁻¹, ?_⟩
      rw [hz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hzne, map_one, one_mul]
    obtain ⟨r, s, t, u, A, B, C, D, hs, ht, h₁, h₂⟩ :=
      exists_independent_squares_of_first_quadratic_coefficient_ne_zero d e f a b c hd
        (by simpa only [← hPeq, ← hQeq] using hpair')
        (fun x y hxy hz => hno' x y hxy hz.symm)
    refine ⟨r, s, t, u, B, A, D, C, hs, ?_, ?_, ?_⟩
    · intro hz
      apply ht
      linear_combination -hz
    · simpa only [← hPeq, ← hQeq, add_comm] using h₁
    · simpa only [← hPeq, ← hQeq, add_comm] using h₂

end OnLeConjecture.DTwo
