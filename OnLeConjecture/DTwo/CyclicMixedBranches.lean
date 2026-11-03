/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPureMonomialCollision

/-!
# The two restrictions of a mixed cyclic residual

The invariant polynomial and the noninvariant monomial have different
characters under a root of unity of order `p`. Consequently neither
restriction to the two branches of the quadratic crossing vanishes
identically when the first exponent of the monomial is positive.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

/-- The degree identity separates the invariant and noninvariant characters.
No coprimality hypothesis on `k` and `p` is required. -/
theorem exists_cyclicMixed_characters
    (k p i j d : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : k * i + p * j = k * d) :
    ∃ ζ ρ : ℂ, ζ ≠ 0 ∧ ζ ≠ 1 ∧ ζ ^ k = 1 ∧ ζ ^ j ≠ 1 ∧
      ζ ^ j ≠ -1 ∧ ρ ^ p = 1 ∧ ρ ^ i ≠ ρ ^ d := by
  have hij : i ≤ d := by nlinarith [Nat.zero_le (p * j)]
  have hproduct : p * j = k * (d - i) := by
    have hsub := Nat.sub_add_cancel hij
    nlinarith
  have hnot : ¬ p ∣ d - i := by
    rintro ⟨r, hr⟩
    apply hj
    refine ⟨r, ?_⟩
    rw [hr] at hproduct
    nlinarith [hp.pos]
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (k : ℂ))
  let ρ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  have hρ : IsPrimitiveRoot ρ p := Complex.isPrimitiveRoot_exp p hp.pos.ne'
  have hζj : ζ ^ j ≠ 1 := fun h ↦ hj ((hζ.pow_eq_one_iff_dvd j).mp h)
  have hζjp : (ζ ^ j) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm j p, hproduct, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ, ρ, hζ.ne_zero hk.ne', ?_, hζ.pow_eq_one, hζj, ?_, hρ.pow_eq_one, ?_⟩
  · intro h
    exact hζj (by simp [h])
  · intro h
    rw [h, hp.neg_one_pow] at hζjp
    norm_num at hζjp
  · intro h
    have hpow : ρ ^ (d - i) = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero i (hρ.ne_zero hp.pos.ne'))
      rw [mul_one, ← pow_add, Nat.add_sub_of_le hij]
      exact h.symm
    exact hnot ((hρ.pow_eq_one_iff_dvd (d - i)).mp hpow)

/-- An explicit analytic branch of the opposite-sign plane equation. -/
@[expose] noncomputable def cyclicMixedOppositeY (k p : ℕ) (c ζ x : ℂ) : ℂ :=
  ζ * (1 + 2 * x ^ p / c) ^ ((k : ℂ)⁻¹)

theorem cyclicMixedOppositeY_analyticAt (k p : ℕ) (hp : 0 < p) (c ζ : ℂ) :
    AnalyticAt ℂ (cyclicMixedOppositeY k p c ζ) 0 := by
  apply analyticAt_const.mul
  apply (analyticAt_const.add ((analyticAt_const.mul (analyticAt_id.pow p)).div_const)).cpow
    analyticAt_const
  simp [zero_pow hp.ne', Complex.one_mem_slitPlane]

@[simp] theorem cyclicMixedOppositeY_zero (k p : ℕ) (hp : 0 < p) (c ζ : ℂ) :
    cyclicMixedOppositeY k p c ζ 0 = ζ := by
  simp [cyclicMixedOppositeY, zero_pow hp.ne']

theorem cyclicMixedOppositeY_pow (k p : ℕ) (hk : 0 < k) (c ζ : ℂ)
    (hζ : ζ ^ k = 1) (x : ℂ) :
    cyclicMixedOppositeY k p c ζ x ^ k = 1 + 2 * x ^ p / c := by
  rw [cyclicMixedOppositeY, mul_pow, hζ, one_mul, Complex.cpow_nat_inv_pow _ hk.ne']

theorem cyclicMixedOppositeY_rotation (k p : ℕ) (c ζ ρ : ℂ) (hρ : ρ ^ p = 1)
    (x : ℂ) : cyclicMixedOppositeY k p c ζ (ρ * x) = cyclicMixedOppositeY k p c ζ x := by
  simp [cyclicMixedOppositeY, mul_pow, hρ]

/-- Distinct characters cannot cancel a monomial times a function nonzero
at the origin on a neighborhood. -/
theorem not_eventually_zero_of_distinct_rotation_characters
    (K V : ℂ → ℂ) (i d : ℕ) (ρ γ : ℂ) (hγ : γ ≠ 0)
    (hcharacters : ρ ^ i ≠ ρ ^ d)
    (hK : ∀ x, K (ρ * x) = ρ ^ d * K x)
    (hV : ∀ x, V (ρ * x) = V x)
    (hVcontinuous : ContinuousAt V 0) (hVzero : V 0 ≠ 0) :
    ¬ ∀ᶠ x in nhds 0, K x + γ * x ^ i * V x = 0 := by
  intro hzero
  have hrotate : Tendsto (fun x : ℂ ↦ ρ * x) (nhds 0) (nhds 0) := by
    have hcontinuous : Continuous (fun x : ℂ ↦ ρ * x) := continuous_const.mul continuous_id
    simpa using hcontinuous.tendsto 0
  have hcoordinate : ∀ᶠ x : ℂ in nhds 0, x = 0 := by
    filter_upwards [hzero, hrotate.eventually hzero,
      hVcontinuous.eventually_ne hVzero] with x hx hrot hxV
    rw [hK, hV, mul_pow] at hrot
    have hproduct : γ * (ρ ^ i - ρ ^ d) * x ^ i * V x = 0 := by
      linear_combination hrot - ρ ^ d * hx
    have hxpower : x ^ i = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hxV)).resolve_left
        (mul_ne_zero hγ (sub_ne_zero.mpr hcharacters))
    exact eq_zero_of_pow_eq_zero hxpower
  exact not_eventually_polynomial_eval_add_eq_zero
    (_root_.Polynomial.X : _root_.Polynomial ℂ) _root_.Polynomial.X_ne_zero 0
    (by simpa using hcoordinate)

/-- At a `p`th root of unity the invariant polynomial has its degree character. -/
theorem cyclicMixed_invariant_rotation
    (p d : ℕ) (L : MvPolynomial (Fin 2) ℂ)
    (hL : L.IsWeightedHomogeneous ![1, p] d) (ρ : ℂ) (hρ : ρ ^ p = 1)
    (x t : ℂ) : eval ![ρ * x, t] L = ρ ^ d * eval ![x, t] L := by
  have hcoordinates : (fun index : Fin 2 ↦ ρ ^ (![1, p] index) * (![x, t] index)) =
      ![ρ * x, t] := by
    ext index
    fin_cases index <;> simp [hρ]
  simpa only [hcoordinates] using
    OnLeConjecture.DThree.eval_weighted_smul_of_isWeightedHomogeneous hL ρ ![x, t]

/-- The opposite-sign restriction of a mixed residual cannot vanish
identically. The unit is constructed by an analytic root, not assumed. -/
theorem cyclicMixed_opposite_not_eventually_zero
    (k p i j d : ℕ) (hp : 0 < p)
    (c ζ ρ γ : ℂ) (hγ : γ ≠ 0) (hζ : ζ ^ k = 1)
    (hcoefficient : 1 - (-1 : ℂ) ^ i * ζ ^ j ≠ 0)
    (hρ : ρ ^ p = 1) (hcharacters : ρ ^ i ≠ ρ ^ d)
    (L : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d) :
    ¬ ∀ᶠ x in nhds 0,
      eval ![x, 1] L -
          cyclicMixedOppositeY k p c ζ x ^ k *
            eval ![-x, cyclicMixedOppositeY k p c ζ x ^ k] L +
        γ * x ^ i *
          (1 - (-1 : ℂ) ^ i * cyclicMixedOppositeY k p c ζ x ^ (k + j)) = 0 := by
  let Y := cyclicMixedOppositeY k p c ζ
  let K : ℂ → ℂ := fun x ↦
    eval ![x, 1] L - Y x ^ k * eval ![-x, Y x ^ k] L
  let V : ℂ → ℂ := fun x ↦ 1 - (-1 : ℂ) ^ i * Y x ^ (k + j)
  apply not_eventually_zero_of_distinct_rotation_characters K V i d ρ γ hγ hcharacters
  · intro x
    dsimp [K, Y]
    rw [cyclicMixedOppositeY_rotation k p c ζ ρ hρ]
    rw [cyclicMixed_invariant_rotation p d L hL ρ hρ]
    rw [show -(ρ * x) = ρ * (-x) by ring,
      cyclicMixed_invariant_rotation p d L hL ρ hρ]
    ring
  · intro x
    dsimp [V, Y]
    rw [cyclicMixedOppositeY_rotation k p c ζ ρ hρ]
  · exact (analyticAt_const.sub (analyticAt_const.mul
      ((cyclicMixedOppositeY_analyticAt k p hp c ζ).pow (k + j)))).continuousAt
  · dsimp [V, Y]
    simpa only [cyclicMixedOppositeY_zero k p hp c ζ, pow_add, hζ, one_mul]
      using hcoefficient

set_option maxRecDepth 2048 in
/-- Both restrictions of the initial third difference are nonzero germs
at the selected cyclic crossing. The second branch is analytic. -/
theorem exists_cyclicMixed_crossing_branches
    (k p i j d : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : k * i + p * j = k * d)
    (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (L : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 0 ^ i * X 1 ^ j)) :
    ∃ ζ : ℂ, ∃ Y : ℂ → ℂ, ζ ≠ 0 ∧ ζ ≠ 1 ∧ ζ ^ k = 1 ∧
      AnalyticAt ℂ Y 0 ∧ Y 0 = ζ ∧
      (∀ x, x ^ p + c - ((-x) ^ p + c * Y x ^ k) = 0) ∧
      (¬ ∀ᶠ x in nhds 0, eval ![x, 1] R - eval ![x, ζ] R = 0) ∧
      (¬ ∀ᶠ x in nhds 0, eval ![x, 1] R - eval ![-x, Y x] R = 0) := by
  obtain ⟨ζ, ρ, hζzero, hζone, hζ, hζj, hζneg, hρ, hcharacters⟩ :=
    exists_cyclicMixed_characters k p i j d hk hp hj hdegree
  have hcoefficient : 1 - (-1 : ℂ) ^ i * ζ ^ j ≠ 0 := by
    rcases Nat.even_or_odd i with hi | hi
    · rw [hi.neg_one_pow, one_mul]
      exact sub_ne_zero.mpr hζj.symm
    · rw [hi.neg_one_pow]
      intro h
      apply hζneg
      linear_combination h
  have heval (x y : ℂ) : eval ![x, y] R =
      y ^ k * (eval ![x, y ^ k] L + γ * x ^ i * y ^ j) := by
    rw [hR]
    simp [cyclicInvariantLift_eval]
  refine ⟨ζ, cyclicMixedOppositeY k p c ζ, hζzero, hζone, hζ,
    cyclicMixedOppositeY_analyticAt k p hp.pos c ζ,
    cyclicMixedOppositeY_zero k p hp.pos c ζ, ?_, ?_, ?_⟩
  · intro x
    rw [hp.neg_pow, cyclicMixedOppositeY_pow k p hk c ζ hζ]
    field_simp [hc]
    ring
  · intro hzero
    have hcoordinate : ∀ᶠ x : ℂ in nhds 0, x = 0 := by
      filter_upwards [hzero] with x hx
      simp only [heval, one_pow, hζ, one_mul, mul_one] at hx
      have hproduct : γ * (1 - ζ ^ j) * x ^ i = 0 := by linear_combination hx
      exact eq_zero_of_pow_eq_zero
        ((mul_eq_zero.mp hproduct).resolve_left (mul_ne_zero hγ (sub_ne_zero.mpr hζj.symm)))
    exact not_eventually_polynomial_eval_add_eq_zero
      (_root_.Polynomial.X : _root_.Polynomial ℂ) _root_.Polynomial.X_ne_zero 0
      (by simpa using hcoordinate)
  · intro hzero
    apply cyclicMixed_opposite_not_eventually_zero k p i j d hp.pos
      c ζ ρ γ hγ hζ hcoefficient hρ hcharacters L hL
    filter_upwards [hzero] with x hx
    simp only [heval, one_pow, one_mul, mul_one] at hx
    rw [neg_pow] at hx
    rw [pow_add]
    linear_combination hx

end OnLeConjecture.DTwo
