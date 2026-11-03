/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicMixedCollision
public import OnLeConjecture.Polynomial.TwoRootFactorization

/-!
# A polynomial obstruction to identical vanishing on a cyclic branch

Weighted scaling eliminates the first coordinate after taking a power.
At a simple root of the plane polynomial, root multiplicities rule out
the resulting polynomial identity.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

private theorem eval_bivariate_aeval (L : MvPolynomial (Fin 2) ℂ)
    (A B : _root_.Polynomial ℂ) (y : ℂ) :
    (aeval ![A, B] L).eval y = eval ![A.eval y, B.eval y] L := by
  change (_root_.Polynomial.aeval y) (aeval _ L) = aeval _ L
  rw [comp_aeval_apply]
  apply congrArg (fun f : Fin 2 → ℂ ↦ aeval f L)
  ext index
  fin_cases index <;> simp

/-- Weighted scaling expresses the invariant difference in polynomial
functions of `xᵖ` and `yᵏ`, after multiplication by a power of `x`. -/
theorem cyclicMixed_scaled_difference
    (p d : ℕ) (hp : 0 < p) (L : MvPolynomial (Fin 2) ℂ)
    (hL : L.IsWeightedHomogeneous ![1, p] d) (x t : ℂ) :
    eval ![x ^ p, (x ^ p) ^ (p - 1)] L -
        t * eval ![-(x ^ p), (x ^ p) ^ (p - 1) * t] L =
      x ^ ((p - 1) * d) * (eval ![x, 1] L - t * eval ![-x, t] L) := by
  have hpower : x ^ (p - 1) * x = x ^ p := by
    rw [← pow_succ, Nat.sub_one_add_one hp.ne']
  have hcoordinates (z t : ℂ) :
      (fun index : Fin 2 ↦ (x ^ (p - 1)) ^ (![1, p] index) * (![z, t] index)) =
        ![x ^ (p - 1) * z, (x ^ p) ^ (p - 1) * t] := by
    ext index
    fin_cases index
    · simp
    · change (x ^ (p - 1)) ^ p * t = (x ^ p) ^ (p - 1) * t
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (p - 1) p]
  have hfirst := OnLeConjecture.DThree.eval_weighted_smul_of_isWeightedHomogeneous
    hL (x ^ (p - 1)) ![x, 1]
  have hsecond := OnLeConjecture.DThree.eval_weighted_smul_of_isWeightedHomogeneous
    hL (x ^ (p - 1)) ![-x, t]
  rw [hcoordinates, hpower, mul_one] at hfirst
  rw [hcoordinates, mul_neg, hpower] at hsecond
  rw [hfirst, hsecond, ← pow_mul]
  ring

/-- A power identity has incompatible multiplicities when one factor has
a simple zero and the other factor is nonzero there. -/
theorem polynomial_power_obstruction
    (p d : ℕ) (hp : 0 < p) (hnot : ¬ p ∣ d)
    (B G T : _root_.Polynomial ℂ) (a ζ : ℂ) (ha : a ≠ 0)
    (hGzero : G ≠ 0) (hG : G.rootMultiplicity ζ = 1) (hT : T.eval ζ ≠ 0) :
    B ^ p ≠ _root_.Polynomial.C a * G ^ ((p - 1) * d) * T ^ p := by
  intro heq
  have hTzero : T ≠ 0 := by intro h; exact hT (by simp [h])
  have hright : _root_.Polynomial.C a * G ^ ((p - 1) * d) * T ^ p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (_root_.Polynomial.C_ne_zero.mpr ha)
      (pow_ne_zero _ hGzero)) (pow_ne_zero _ hTzero)
  have hB : B ≠ 0 := by
    intro h
    exact hright (by simpa [h, zero_pow hp.ne'] using heq.symm)
  have hmultiplicity := congrArg (fun P : _root_.Polynomial ℂ ↦ P.rootMultiplicity ζ) heq
  rw [OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul B hB,
    _root_.Polynomial.rootMultiplicity_mul hright,
    _root_.Polynomial.rootMultiplicity_mul
      (mul_ne_zero (_root_.Polynomial.C_ne_zero.mpr ha) (pow_ne_zero _ hGzero)),
    _root_.Polynomial.rootMultiplicity_C,
    OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul G hGzero,
    OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul T hTzero,
    _root_.Polynomial.rootMultiplicity_eq_zero hT, hG, mul_one, mul_zero,
    zero_add, add_zero] at hmultiplicity
  apply hnot
  have hleft : p ∣ p * d := dvd_mul_right p d
  have hrightD : p ∣ (p - 1) * d := ⟨B.rootMultiplicity ζ, hmultiplicity.symm⟩
  have hdifference := Nat.dvd_sub hleft hrightD
  have heqd : p * d - (p - 1) * d = d := by
    have h := Nat.sub_one_add_one hp.ne'
    have hsum : p * d = (p - 1) * d + d := by nlinarith
    rw [hsum, Nat.add_sub_cancel_left]
  rwa [heqd] at hdifference

@[expose] noncomputable def cyclicMixedPlanePolynomial (k : ℕ) (c : ℂ) :
    _root_.Polynomial ℂ :=
  _root_.Polynomial.C (c / 2) * (_root_.Polynomial.X ^ k - 1)

theorem cyclicMixedPlanePolynomial_eval (k : ℕ) (c y : ℂ) :
    (cyclicMixedPlanePolynomial k c).eval y = c / 2 * (y ^ k - 1) := by
  simp [cyclicMixedPlanePolynomial]

/-- A nonzero root of unity is a simple zero of the plane polynomial. -/
theorem cyclicMixedPlanePolynomial_rootMultiplicity
    (k : ℕ) (hk : 0 < k) (c ζ : ℂ) (hc : c ≠ 0)
    (hζzero : ζ ≠ 0) (hζ : ζ ^ k = 1) :
    (cyclicMixedPlanePolynomial k c).rootMultiplicity ζ = 1 := by
  let G := cyclicMixedPlanePolynomial k c
  have hderivative : G.derivative.eval ζ ≠ 0 := by
    have heval : G.derivative.eval ζ = c / 2 * ((k : ℂ) * ζ ^ (k - 1)) := by
      simp [G, cyclicMixedPlanePolynomial, _root_.Polynomial.derivative_X_pow]
    rw [heval]
    exact mul_ne_zero (div_ne_zero hc (by norm_num))
      (mul_ne_zero (Nat.cast_ne_zero.mpr hk.ne') (pow_ne_zero _ hζzero))
  have hG : G ≠ 0 := by intro h; exact hderivative (by simp [h])
  have hroot : G.IsRoot ζ := by simp [G, _root_.Polynomial.IsRoot.def,
    cyclicMixedPlanePolynomial_eval, hζ]
  have hpos := (_root_.Polynomial.rootMultiplicity_pos hG).mpr hroot
  have hle : ¬ 1 < G.rootMultiplicity ζ := by
    intro h
    exact hderivative ((_root_.Polynomial.one_lt_rootMultiplicity_iff_isRoot hG).mp h).2
  change G.rootMultiplicity ζ = 1
  omega

/-- The polynomial numerator furnished by weighted scaling. -/
@[expose] noncomputable def cyclicMixedScaledPolynomial
    (k p : ℕ) (c : ℂ) (L : MvPolynomial (Fin 2) ℂ) : _root_.Polynomial ℂ :=
  let G := cyclicMixedPlanePolynomial k c
  aeval ![G, G ^ (p - 1)] L -
    _root_.Polynomial.X ^ k * aeval ![-G, G ^ (p - 1) * _root_.Polynomial.X ^ k] L

theorem cyclicMixedScaledPolynomial_eval
    (k p d : ℕ) (hp : 0 < p) (c x y : ℂ)
    (L : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hcurve : x ^ p = c / 2 * (y ^ k - 1)) :
    (cyclicMixedScaledPolynomial k p c L).eval y =
      x ^ ((p - 1) * d) * (eval ![x, 1] L - y ^ k * eval ![-x, y ^ k] L) := by
  simp only [cyclicMixedScaledPolynomial, _root_.Polynomial.eval_sub,
    _root_.Polynomial.eval_mul, eval_bivariate_aeval,
    _root_.Polynomial.eval_pow, _root_.Polynomial.eval_X,
    _root_.Polynomial.eval_neg, cyclicMixedPlanePolynomial_eval, ← hcurve]
  exact cyclicMixed_scaled_difference p d hp L hL x (y ^ k)

/-- The mixed third difference is never identically zero on an analytic
opposite-sign branch. The original second exponent is unchanged. -/
theorem cyclicMixedZero_opposite_not_eventually_zero
    (k p j d : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : p * j = k * d) (c γ Y : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (L : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (x : ℂ → ℂ) (hcurve : ∀ u, x u ^ p = c / 2 * ((Y + u) ^ k - 1)) :
    ¬ ∀ᶠ u in nhds 0,
      eval ![x u, 1] L - (Y + u) ^ k * eval ![-x u, (Y + u) ^ k] L +
        γ * (1 - (Y + u) ^ (k + j)) = 0 := by
  obtain ⟨ζ, _, hζzero, _, hζ, hζj, _, _, _⟩ :=
    exists_cyclicMixed_characters k p 0 j d hk hp hj (by simpa using hdegree)
  have hnot : ¬ p ∣ d := by
    rintro ⟨q, hq⟩
    apply hj
    refine ⟨q, ?_⟩
    rw [hq] at hdegree
    nlinarith [hp.pos]
  let B := cyclicMixedScaledPolynomial k p c L
  let G := cyclicMixedPlanePolynomial k c
  let T : _root_.Polynomial ℂ := 1 - _root_.Polynomial.X ^ (k + j)
  have hGmult : G.rootMultiplicity ζ = 1 :=
    cyclicMixedPlanePolynomial_rootMultiplicity k hk c ζ hc hζzero hζ
  have hGzero : G ≠ 0 := by intro h; simp [h] at hGmult
  have hT : T.eval ζ ≠ 0 := by
    simpa [T, pow_add, hζ] using sub_ne_zero.mpr hζj.symm
  have hnorm : B ^ p - _root_.Polynomial.C ((-γ) ^ p) * G ^ ((p - 1) * d) * T ^ p ≠ 0 :=
    sub_ne_zero.mpr (polynomial_power_obstruction p d hp.pos hnot B G T
      ((-γ) ^ p) ζ (pow_ne_zero _ (neg_ne_zero.mpr hγ)) hGzero hGmult hT)
  intro hzero
  apply not_eventually_polynomial_eval_add_eq_zero _ hnorm Y
  filter_upwards [hzero] with u hu
  have hB := cyclicMixedScaledPolynomial_eval k p d hp.pos c (x u) (Y + u) L hL (hcurve u)
  have hscalar : B.eval (Y + u) =
      x u ^ ((p - 1) * d) * (-γ) * (1 - (Y + u) ^ (k + j)) := by
    change (cyclicMixedScaledPolynomial k p c L).eval (Y + u) = _
    rw [hB]
    linear_combination x u ^ ((p - 1) * d) * hu
  simp only [_root_.Polynomial.eval_sub, _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_pow, _root_.Polynomial.eval_C, hscalar]
  have hpower : (x u ^ ((p - 1) * d)) ^ p = G.eval (Y + u) ^ ((p - 1) * d) := by
    rw [← pow_mul, Nat.mul_comm ((p - 1) * d) p, pow_mul, hcurve]
    simp only [G, cyclicMixedPlanePolynomial_eval]
  rw [mul_pow, mul_pow, hpower]
  simp [T, mul_comm, mul_left_comm]

end OnLeConjecture.DTwo
