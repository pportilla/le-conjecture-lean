/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HDerivativeIdentity
public import OnLeConjecture.DThree.HGlobalOrders
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The derivative rational function in the `H` case

This file substitutes the fixed rational parametrization of the `H` conic in
weighted homogeneous bivariate polynomials.  A common denominator records the
three possible poles on the parameter line.  The resulting denominator bound
is then applied to the Cramer rational function from Lemma `dthree-Horders`.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-! ## Weighted forms and conic pullback -/

/-- The weights of `x` and `w` are respectively one and two. -/
@[expose]
def hFormWeight : Fin 2 → ℕ
  | 0 => 1
  | 1 => 2

/-- Evaluation of a bivariate polynomial at two elements of a `K` algebra. -/
@[expose]
noncomputable def hFormEval {A : Type*} [CommRing A] [Algebra K A]
    (x w : A) (F : MvPolynomial (Fin 2) K) : A :=
  MvPolynomial.eval₂ (algebraMap K A) (fun i => if i = 0 then x else w) F

/-- Pullback to the first point `(1,w)` of the conic fibre pair. -/
@[expose]
noncomputable def hFirstConicPullback
    (F : MvPolynomial (Fin 2) K) : RatFunc K :=
  hFormEval 1 (hConicParamW (K := K)) F

/-- Pullback to the second point `(X,W)` of the conic fibre pair. -/
@[expose]
noncomputable def hSecondConicPullback
    (F : MvPolynomial (Fin 2) K) : RatFunc K :=
  hFormEval (hConicParamX (K := K))
    (hConicParamCapitalW (K := K)) F

/-- The difference denoted by `[F]` in Lemma `dthree-Horders`. -/
@[expose]
noncomputable def hConicDifference
    (F : MvPolynomial (Fin 2) K) : RatFunc K :=
  hFirstConicPullback F - hSecondConicPullback F

/-- The source variable `x` in the weighted polynomial ring. -/
@[expose]
noncomputable def hFormX : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0

/-- The source variable `w` in the weighted polynomial ring. -/
@[expose]
noncomputable def hFormW : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1

/-- The degree three coordinate of the `H` pair. -/
@[expose]
noncomputable def hPForm : MvPolynomial (Fin 2) K :=
  hFormX ^ 3 + MvPolynomial.C 3 * (hFormX * hFormW)

/-- The degree four coordinate of the `H` pair. -/
@[expose]
noncomputable def hQForm : MvPolynomial (Fin 2) K :=
  hFormX ^ 4 + MvPolynomial.C 4 * (hFormX ^ 2 * hFormW) +
    MvPolynomial.C 2 * hFormW ^ 2

/-- The Jacobian determinant in the two weighted variables. -/
@[expose]
noncomputable def hFormJacobian
    (F G : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.pderiv 0 F * MvPolynomial.pderiv 1 G -
    MvPolynomial.pderiv 1 F * MvPolynomial.pderiv 0 G

omit [CharZero K] in
/-- The Jacobian of two weighted homogeneous forms has the expected weighted
degree. -/
theorem hFormJacobian_isWeightedHomogeneous
    (F G : MvPolynomial (Fin 2) K) (m n : ℕ)
    (hF : F.IsWeightedHomogeneous hFormWeight m)
    (hG : G.IsWeightedHomogeneous hFormWeight n)
    (hFm0 : 1 ≤ m) (hFm1 : 2 ≤ m)
    (hGn0 : 1 ≤ n) (hGn1 : 2 ≤ n) :
    (hFormJacobian F G).IsWeightedHomogeneous hFormWeight
      ((m - 1) + (n - 2)) := by
  have hdF0 := hF.pderiv (i := (0 : Fin 2)) (n' := m - 1) (by
    simpa [hFormWeight] using Nat.sub_add_cancel hFm0)
  have hdF1 := hF.pderiv (i := (1 : Fin 2)) (n' := m - 2) (by
    simpa [hFormWeight] using Nat.sub_add_cancel hFm1)
  have hdG0 := hG.pderiv (i := (0 : Fin 2)) (n' := n - 1) (by
    simpa [hFormWeight] using Nat.sub_add_cancel hGn0)
  have hdG1 := hG.pderiv (i := (1 : Fin 2)) (n' := n - 2) (by
    simpa [hFormWeight] using Nat.sub_add_cancel hGn1)
  have hfirst := hdF0.mul hdG1
  have hsecond := hdF1.mul hdG0
  have hdegrees :
      (m - 2) + (n - 1) = (m - 1) + (n - 2) := by
    omega
  rw [hdegrees] at hsecond
  simpa [hFormJacobian] using hfirst.sub hsecond

omit [CharZero K] in
/-- Multiplication by a monomial reflects weighted homogeneity after its
weight is subtracted from the total degree. -/
theorem isWeightedHomogeneous_of_monomial_mul
    (w : Fin 2 → ℕ) (s : Fin 2 →₀ ℕ)
    (F : MvPolynomial (Fin 2) K) (n M : ℕ)
    (hproduct :
      (MvPolynomial.monomial s 1 * F).IsWeightedHomogeneous w M)
    (hdegree : Finsupp.weight w s + n = M) :
    F.IsWeightedHomogeneous w n := by
  intro d hd
  have hcoeff : MvPolynomial.coeff (s + d)
      (MvPolynomial.monomial s 1 * F) ≠ 0 := by
    simpa using hd
  have hweight := hproduct hcoeff
  have hadd : Finsupp.weight w s + Finsupp.weight w d = M := by
    simpa only [map_add] using hweight
  exact Nat.add_left_cancel (hadd.trans hdegree.symm)

omit [CharZero K] in
/-- The first coordinate of the `H` pair is weighted homogeneous of degree
three. -/
theorem hPForm_isWeightedHomogeneous :
    (hPForm (K := K)).IsWeightedHomogeneous hFormWeight 3 := by
  have hx : (hFormX (K := K)).IsWeightedHomogeneous hFormWeight 1 := by
    exact MvPolynomial.isWeightedHomogeneous_X K hFormWeight 0
  have hw : (hFormW (K := K)).IsWeightedHomogeneous hFormWeight 2 := by
    exact MvPolynomial.isWeightedHomogeneous_X K hFormWeight 1
  have hfirst := hx.pow 3
  have hsecond := (hx.mul hw).C_mul (3 : K)
  simpa [hPForm, mul_assoc] using hfirst.add hsecond

omit [CharZero K] in
/-- The second coordinate of the `H` pair is weighted homogeneous of degree
four. -/
theorem hQForm_isWeightedHomogeneous :
    (hQForm (K := K)).IsWeightedHomogeneous hFormWeight 4 := by
  have hx : (hFormX (K := K)).IsWeightedHomogeneous hFormWeight 1 := by
    exact MvPolynomial.isWeightedHomogeneous_X K hFormWeight 0
  have hw : (hFormW (K := K)).IsWeightedHomogeneous hFormWeight 2 := by
    exact MvPolynomial.isWeightedHomogeneous_X K hFormWeight 1
  have hfirst := hx.pow 4
  have hsecond := ((hx.pow 2).mul hw).C_mul (4 : K)
  have hthird := (hw.pow 2).C_mul (2 : K)
  simpa [hQForm, mul_assoc] using
    (hfirst.add hsecond).add hthird

/-! ## A common denominator for the three possible poles -/

/-- The polynomial denominator with exponent `a` at `m = -1` and exponent
`b` at each root of the parametrization denominator. -/
@[expose]
noncomputable def hPoleProfileDenominator (a b : ℕ) : K[X] :=
  (3 * (X + 1)) ^ a * (hConicParamDenominator (K := K)) ^ b

/-- A rational function has pole profile `(a,b)` if it admits the displayed
common denominator and a numerator whose degree does not exceed the degree of
that denominator. -/
@[expose]
def HasHPoleProfile (a b : ℕ) (f : RatFunc K) : Prop :=
  ∃ p : K[X],
    p.natDegree ≤ a + 2 * b ∧
      f = algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) (hPoleProfileDenominator a b)

theorem h_pole_profile_denominator_ne_zero (a b : ℕ) :
    hPoleProfileDenominator (K := K) a b ≠ 0 := by
  exact mul_ne_zero
    (pow_ne_zero a (mul_ne_zero (by norm_num) h_conic_param_linear_ne_zero))
    (pow_ne_zero b h_conic_param_denominator_ne_zero)

theorem h_pole_profile_denominator_natDegree (a b : ℕ) :
    (hPoleProfileDenominator (K := K) a b).natDegree = a + 2 * b := by
  simp only [hPoleProfileDenominator]
  rw [Polynomial.natDegree_mul
    (pow_ne_zero a
      (mul_ne_zero (by norm_num) h_conic_param_linear_ne_zero))
    (pow_ne_zero b h_conic_param_denominator_ne_zero),
    Polynomial.natDegree_pow, Polynomial.natDegree_pow]
  have hlinear : ((X + 1 : K[X])).natDegree = 1 := by
    rw [show (1 : K[X]) = Polynomial.C (1 : K) by rfl,
      Polynomial.natDegree_X_add_C]
  have hl : ((3 : K[X]) * (X + 1)).natDegree = 1 := by
    rw [Polynomial.natDegree_mul (by norm_num)
      h_conic_param_linear_ne_zero, hlinear]
    norm_num
  have hd : (hConicParamDenominator (K := K)).natDegree = 2 := by
    rw [hConicParamDenominator,
      show (2 : K[X]) = Polynomial.C (2 : K) by rfl]
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_pow,
      Polynomial.natDegree_X]
  rw [hl, hd]
  omega

omit [CharZero K] in
/-- Every scalar has the zero pole profile. -/
theorem hasHPoleProfile_algebraMap (c : K) :
    HasHPoleProfile 0 0 (algebraMap K (RatFunc K) c) := by
  refine ⟨Polynomial.C c, by simp, ?_⟩
  simp [hPoleProfileDenominator]

omit [CharZero K] in
/-- The zero rational function has every pole profile. -/
theorem hasHPoleProfile_zero (a b : ℕ) :
    HasHPoleProfile a b (0 : RatFunc K) := by
  refine ⟨0, by simp, ?_⟩
  simp

omit [CharZero K] in
/-- Pole profile denominators multiply by adding their two exponents. -/
theorem h_pole_profile_denominator_add
    (a b c d : ℕ) :
    hPoleProfileDenominator (K := K) (a + c) (b + d) =
      hPoleProfileDenominator a b * hPoleProfileDenominator c d := by
  simp only [hPoleProfileDenominator, pow_add]
  ring

/-- Pole profiles are closed under multiplication. -/
theorem HasHPoleProfile.mul
    {a b c d : ℕ} {f g : RatFunc K}
    (hf : HasHPoleProfile a b f)
    (hg : HasHPoleProfile c d g) :
    HasHPoleProfile (a + c) (b + d) (f * g) := by
  rcases hf with ⟨p, hpdeg, hp⟩
  rcases hg with ⟨q, hqdeg, hq⟩
  refine ⟨p * q, ?_, ?_⟩
  · exact (Polynomial.natDegree_mul_le.trans <| by omega)
  · rw [hp, hq, h_pole_profile_denominator_add, map_mul, map_mul]
    ring

/-- Pole profiles are closed under addition when the common denominator is
unchanged. -/
theorem HasHPoleProfile.add
    {a b : ℕ} {f g : RatFunc K}
    (hf : HasHPoleProfile a b f)
    (hg : HasHPoleProfile a b g) :
    HasHPoleProfile a b (f + g) := by
  rcases hf with ⟨p, hpdeg, hp⟩
  rcases hg with ⟨q, hqdeg, hq⟩
  refine ⟨p + q, Polynomial.natDegree_add_le _ _ |>.trans (by omega), ?_⟩
  rw [hp, hq, map_add]
  field_simp [RatFunc.algebraMap_ne_zero
    (h_pole_profile_denominator_ne_zero (K := K) a b)]

omit [CharZero K] in
/-- Pole profiles are closed under negation. -/
theorem HasHPoleProfile.neg
    {a b : ℕ} {f : RatFunc K}
    (hf : HasHPoleProfile a b f) :
    HasHPoleProfile a b (-f) := by
  rcases hf with ⟨p, hpdeg, hp⟩
  refine ⟨-p, by simpa using hpdeg, ?_⟩
  rw [hp, map_neg, neg_div]

/-- Pole profiles are closed under subtraction. -/
theorem HasHPoleProfile.sub
    {a b : ℕ} {f g : RatFunc K}
    (hf : HasHPoleProfile a b f)
    (hg : HasHPoleProfile a b g) :
    HasHPoleProfile a b (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- Multiplication by a scalar does not change a pole profile. -/
theorem HasHPoleProfile.const_mul
    {a b : ℕ} (c : K) {f : RatFunc K}
    (hf : HasHPoleProfile a b f) :
    HasHPoleProfile a b (algebraMap K (RatFunc K) c * f) := by
  simpa [zero_add] using (hasHPoleProfile_algebraMap c).mul hf

/-- The constant one can be written with any profile denominator. -/
theorem hasHPoleProfile_one (a b : ℕ) :
    HasHPoleProfile a b (1 : RatFunc K) := by
  refine ⟨hPoleProfileDenominator a b,
    (h_pole_profile_denominator_natDegree a b).le, ?_⟩
  rw [div_self (RatFunc.algebraMap_ne_zero
    (h_pole_profile_denominator_ne_zero a b))]

/-- Increasing either profile exponent preserves the pole profile. -/
theorem HasHPoleProfile.mono
    {a b A B : ℕ} {f : RatFunc K}
    (hf : HasHPoleProfile a b f) (ha : a ≤ A) (hb : b ≤ B) :
    HasHPoleProfile A B f := by
  have hmul := hf.mul
    (hasHPoleProfile_one (K := K) (A - a) (B - b))
  rw [mul_one, Nat.add_sub_of_le ha, Nat.add_sub_of_le hb] at hmul
  exact hmul

/-- Taking a power multiplies both pole profile exponents. -/
theorem HasHPoleProfile.pow
    {a b : ℕ} {f : RatFunc K}
    (hf : HasHPoleProfile a b f) (n : ℕ) :
    HasHPoleProfile (n * a) (n * b) (f ^ n) := by
  induction n with
  | zero => simpa using hasHPoleProfile_one (K := K) 0 0
  | succ n ih =>
      simpa [pow_succ, Nat.succ_mul] using ih.mul hf

omit [CharZero K] in
/-- Evaluation of a monomial in the two variables `x,w`. -/
theorem hFormEval_monomial {A : Type*} [CommRing A] [Algebra K A]
    (x w : A) (d : Fin 2 →₀ ℕ) (c : K) :
    hFormEval x w (MvPolynomial.monomial d c) =
      algebraMap K A c * x ^ d 0 * w ^ d 1 := by
  rw [MvPolynomial.monomial_fin_two]
  simp [hFormEval]

/-- The weight of a two variable monomial is `d(0) + 2d(1)`. -/
theorem h_form_weight_apply (d : Fin 2 →₀ ℕ) :
    Finsupp.weight hFormWeight d = d 0 + 2 * d 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two,
    hFormWeight]
  omega

omit [CharZero K] in
@[simp]
theorem hConicDifference_zero :
    hConicDifference (K := K) 0 = 0 := by
  simp [hConicDifference, hFirstConicPullback, hSecondConicPullback,
    hFormEval]

omit [CharZero K] in
/-- Conic difference is additive in the polynomial. -/
theorem hConicDifference_add
    (F G : MvPolynomial (Fin 2) K) :
    hConicDifference (F + G) = hConicDifference F + hConicDifference G := by
  simp only [hConicDifference, hFirstConicPullback, hSecondConicPullback,
    hFormEval, MvPolynomial.eval₂_add]
  ring

omit [CharZero K] in
private theorem h_natDegree_add_le_of_le
    {p q : K[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  Polynomial.natDegree_add_le p q |>.trans (max_le hp hq)

omit [CharZero K] in
private theorem h_natDegree_X_pow_le (n : ℕ) :
    (X ^ n : K[X]).natDegree ≤ n := by
  simp

omit [CharZero K] in
private theorem h_natDegree_const_mul_X_pow_le
    (c : K[X]) (hc : c.natDegree = 0) (n : ℕ) :
    (c * X ^ n).natDegree ≤ n := by
  exact Polynomial.natDegree_mul_le.trans (by simp [hc])

omit [CharZero K] in
private theorem h_natDegree_const_le
    (c : K[X]) (hc : c.natDegree = 0) (n : ℕ) :
    c.natDegree ≤ n := by
  simp [hc]

omit [CharZero K] in
/-- The conic coordinate `X` has profile `(0,1)`. -/
theorem hasHPoleProfile_hConicParamX :
    HasHPoleProfile 0 1 (hConicParamX (K := K)) := by
  refine ⟨hConicParamXNumerator, ?_, ?_⟩
  · change (hConicParamXNumerator (K := K)).natDegree ≤ 2
    simp only [hConicParamXNumerator]
    rw [Polynomial.natDegree_neg]
    apply h_natDegree_add_le_of_le
    · apply h_natDegree_add_le_of_le
      · exact h_natDegree_X_pow_le 2
      · exact (by
          simpa only [pow_one] using
            (h_natDegree_const_mul_X_pow_le (4 : K[X]) (by simp) 1).trans
              (show 1 ≤ 2 by norm_num))
    · exact h_natDegree_const_le (6 : K[X]) (by simp) 2
  · simp [hConicParamX, hPoleProfileDenominator]

omit [CharZero K] in
/-- The conic function `w` has profile `(1,2)`. -/
theorem hasHPoleProfile_hConicParamW :
    HasHPoleProfile 1 2 (hConicParamW (K := K)) := by
  refine ⟨-hConicParamOneFactor * hConicParamWFactor, ?_, ?_⟩
  · change (-hConicParamOneFactor (K := K) *
      hConicParamWFactor).natDegree ≤ 5
    have hq :
        (hConicParamOneFactor (K := K)).natDegree ≤ 2 := by
      simp only [hConicParamOneFactor]
      apply h_natDegree_add_le_of_le
      · apply h_natDegree_add_le_of_le
        · exact h_natDegree_X_pow_le 2
        · exact (by
            simpa only [pow_one] using
              (h_natDegree_const_mul_X_pow_le (2 : K[X]) (by simp) 1).trans
                (show 1 ≤ 2 by norm_num))
      · exact h_natDegree_const_le (4 : K[X]) (by simp) 2
    have hr :
        (hConicParamWFactor (K := K)).natDegree ≤ 3 := by
      simp only [hConicParamWFactor]
      apply h_natDegree_add_le_of_le
      · apply h_natDegree_add_le_of_le
        · exact h_natDegree_X_pow_le 3
        · exact (by
            simpa only [pow_one] using
              (h_natDegree_const_mul_X_pow_le (6 : K[X]) (by simp) 1).trans
                (show 1 ≤ 3 by norm_num))
      · exact h_natDegree_const_le (16 : K[X]) (by simp) 3
    calc
      (-hConicParamOneFactor (K := K) * hConicParamWFactor).natDegree ≤
          (-hConicParamOneFactor (K := K)).natDegree +
            hConicParamWFactor.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 2 + 3 := Nat.add_le_add (by simpa using hq) hr
      _ = 5 := rfl
  · simp [hConicParamW, hPoleProfileDenominator,
      hConicParamFunctionDenominator]

omit [CharZero K] in
/-- The conic function `W` has profile `(1,2)`. -/
theorem hasHPoleProfile_hConicParamCapitalW :
    HasHPoleProfile 1 2 (hConicParamCapitalW (K := K)) := by
  refine ⟨-hConicParamOneFactor * hConicParamCapitalWFactor, ?_, ?_⟩
  · change (-hConicParamOneFactor (K := K) *
      hConicParamCapitalWFactor).natDegree ≤ 5
    have hq :
        (hConicParamOneFactor (K := K)).natDegree ≤ 2 := by
      simp only [hConicParamOneFactor]
      apply h_natDegree_add_le_of_le
      · apply h_natDegree_add_le_of_le
        · exact h_natDegree_X_pow_le 2
        · exact (by
            simpa only [pow_one] using
              (h_natDegree_const_mul_X_pow_le (2 : K[X]) (by simp) 1).trans
                (show 1 ≤ 2 by norm_num))
      · exact h_natDegree_const_le (4 : K[X]) (by simp) 2
    have hr :
        (hConicParamCapitalWFactor (K := K)).natDegree ≤ 3 := by
      simp only [hConicParamCapitalWFactor]
      apply h_natDegree_add_le_of_le
      · apply h_natDegree_add_le_of_le
        · apply h_natDegree_add_le_of_le
          · exact h_natDegree_X_pow_le 3
          · exact (h_natDegree_const_mul_X_pow_le (6 : K[X]) (by simp) 2).trans
              (show 2 ≤ 3 by norm_num)
        · exact (by
            simpa only [pow_one] using
              (h_natDegree_const_mul_X_pow_le (18 : K[X]) (by simp) 1).trans
                (show 1 ≤ 3 by norm_num))
      · exact h_natDegree_const_le (4 : K[X]) (by simp) 3
    calc
      (-hConicParamOneFactor (K := K) *
          hConicParamCapitalWFactor).natDegree ≤
        (-hConicParamOneFactor (K := K)).natDegree +
          hConicParamCapitalWFactor.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 2 + 3 := Nat.add_le_add (by simpa using hq) hr
      _ = 5 := rfl
  · simp [hConicParamCapitalW, hPoleProfileDenominator,
      hConicParamFunctionDenominator]

/-! ## Pole profiles of weighted homogeneous pullbacks -/

/-- The first pullback of a weighted monomial has the pole profile predicted
by its weighted degree. -/
theorem hasHPoleProfile_hFirstConicPullback_monomial
    (N : ℕ) (d : Fin 2 →₀ ℕ) (c : K)
    (hd : Finsupp.weight hFormWeight d = N) :
    HasHPoleProfile (N / 2) N
      (hFirstConicPullback (K := K) (MvPolynomial.monomial d c)) := by
  have hweight : d 0 + 2 * d 1 = N := by
    rw [h_form_weight_apply] at hd
    exact hd
  have hwPow := hasHPoleProfile_hConicParamW (K := K) |>.pow (d 1)
  have hwMono := hwPow.mono (A := N / 2) (B := N)
    (by omega) (by omega)
  have hscalar := (hasHPoleProfile_algebraMap (K := K) c).mul hwMono
  simpa [hFirstConicPullback, hFormEval_monomial] using hscalar

/-- The second pullback of a weighted monomial has the pole profile predicted
by its weighted degree. -/
theorem hasHPoleProfile_hSecondConicPullback_monomial
    (N : ℕ) (d : Fin 2 →₀ ℕ) (c : K)
    (hd : Finsupp.weight hFormWeight d = N) :
    HasHPoleProfile (N / 2) N
      (hSecondConicPullback (K := K) (MvPolynomial.monomial d c)) := by
  have hweight : d 0 + 2 * d 1 = N := by
    rw [h_form_weight_apply] at hd
    exact hd
  have hxPow := hasHPoleProfile_hConicParamX (K := K) |>.pow (d 0)
  have hWPow := hasHPoleProfile_hConicParamCapitalW (K := K) |>.pow (d 1)
  have hproduct := hxPow.mul hWPow
  have hsecondExponent : d 0 + d 1 * 2 = N := by omega
  have hproduct' : HasHPoleProfile (d 1) N
      (hConicParamX (K := K) ^ d 0 *
        hConicParamCapitalW (K := K) ^ d 1) := by
    simpa [hsecondExponent] using hproduct
  have hmono := hproduct'.mono (A := N / 2) (B := N)
    (by omega) le_rfl
  have hscalar := (hasHPoleProfile_algebraMap (K := K) c).mul hmono
  rw [hSecondConicPullback, hFormEval_monomial]
  simpa only [zero_add, mul_assoc] using hscalar

/-- The conic difference of a weighted monomial has no poles outside the
three marked parameter values and has the uniform profile used in the
derivative estimate. -/
theorem hasHPoleProfile_hConicDifference_monomial
    (N : ℕ) (d : Fin 2 →₀ ℕ) (c : K)
    (hd : Finsupp.weight hFormWeight d = N) :
    HasHPoleProfile (N / 2) N
      (hConicDifference (K := K) (MvPolynomial.monomial d c)) := by
  exact (hasHPoleProfile_hFirstConicPullback_monomial N d c hd).sub
    (hasHPoleProfile_hSecondConicPullback_monomial N d c hd)

/-- Substitution in the rational conic parametrization gives every weighted
homogeneous form of degree `N` the common pole profile `(floor(N/2),N)`. -/
theorem hasHPoleProfile_hConicDifference
    (N : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F.IsWeightedHomogeneous hFormWeight N) :
    HasHPoleProfile (N / 2) N (hConicDifference F) := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using hasHPoleProfile_zero (K := K) (N / 2) N
  | add p q hp hq ihp ihq =>
      rw [hConicDifference_add]
      exact ihp.add ihq
  | monomial d c hd =>
      exact hasHPoleProfile_hConicDifference_monomial N d c hd

/-- A pole profile gives a direct bound for the projective pole divisor. -/
theorem HasHPoleProfile.projectivePoleDegree_le
    [IsAlgClosed K] {a b : ℕ} {f : RatFunc K}
    (hf : HasHPoleProfile a b f) :
    hProjectivePoleDivisorDegree f ≤ a + 2 * b := by
  rcases hf with ⟨p, hpdeg, hp⟩
  let q := hPoleProfileDenominator (K := K) a b
  have hq : q ≠ 0 := h_pole_profile_denominator_ne_zero a b
  have hnumDvd : f.num ∣ p := by
    rw [hp]
    exact RatFunc.num_div_dvd p hq
  have hdenDvd : f.denom ∣ q := by
    rw [hp]
    exact RatFunc.denom_div_dvd p q
  rw [h_projective_pole_divisor_degree_eq_max]
  apply max_le
  · by_cases hp0 : p = 0
    · have hf0 : f = 0 := by
        rw [hp, hp0]
        simp
      simp [hf0]
    · exact (Polynomial.natDegree_le_of_dvd hnumDvd hp0).trans hpdeg
  · exact (Polynomial.natDegree_le_of_dvd hdenDvd hq).trans_eq
      (h_pole_profile_denominator_natDegree a b)

/-! ## Jacobian quotients and the Cramer rational function -/

omit [CharZero K] in
/-- Evaluation of the `x` derivative of the first `H` coordinate. -/
theorem hFormEval_pderiv_hPForm_zero
    {A : Type*} [Field A] [Algebra K A] (x w : A) :
    hFormEval x w (MvPolynomial.pderiv 0 (hPForm (K := K))) =
      hPPartialX x w := by
  rw [hPForm, map_add, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_mul]
  simp [hFormEval, hFormX, hFormW, hPPartialX, map_ofNat]

omit [CharZero K] in
/-- Evaluation of the `w` derivative of the first `H` coordinate. -/
theorem hFormEval_pderiv_hPForm_one
    {A : Type*} [Field A] [Algebra K A] (x w : A) :
    hFormEval x w (MvPolynomial.pderiv 1 (hPForm (K := K))) =
      hPPartialW x := by
  rw [hPForm, map_add, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_mul]
  simp [hFormEval, hFormX, hFormW, hPPartialW, map_ofNat]

omit [CharZero K] in
/-- Evaluation of the `x` derivative of the second `H` coordinate. -/
theorem hFormEval_pderiv_hQForm_zero
    {A : Type*} [Field A] [Algebra K A] (x w : A) :
    hFormEval x w (MvPolynomial.pderiv 0 (hQForm (K := K))) =
      hQPartialX x w := by
  have htwo : MvPolynomial.pderiv (R := K) (0 : Fin 2)
      (2 : MvPolynomial (Fin 2) K) = 0 :=
    (MvPolynomial.pderiv (R := K) (0 : Fin 2)).map_natCast 2
  rw [hQForm, map_add, map_add, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_mul]
  simp [hFormEval, hFormX, hFormW, hQPartialX, map_ofNat, htwo]
  ring

omit [CharZero K] in
/-- Evaluation of the `w` derivative of the second `H` coordinate. -/
theorem hFormEval_pderiv_hQForm_one
    {A : Type*} [Field A] [Algebra K A] (x w : A) :
    hFormEval x w (MvPolynomial.pderiv 1 (hQForm (K := K))) =
      hQPartialW x w := by
  have htwo : MvPolynomial.pderiv (R := K) (1 : Fin 2)
      (2 : MvPolynomial (Fin 2) K) = 0 :=
    (MvPolynomial.pderiv (R := K) (1 : Fin 2)).map_natCast 2
  rw [hQForm, map_add, map_add, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_mul]
  simp [hFormEval, hFormX, hFormW, hQPartialW, map_ofNat, htwo]
  ring

omit [CharZero K] in
/-- Evaluation carries the polynomial Jacobian to the determinant of the four
evaluated partial derivatives. -/
theorem hFormEval_hFormJacobian
    {A : Type*} [Field A] [Algebra K A]
    (F G : MvPolynomial (Fin 2) K) (x w : A) :
    hFormEval x w (hFormJacobian F G) =
      hFormEval x w (MvPolynomial.pderiv 0 F) *
          hFormEval x w (MvPolynomial.pderiv 1 G) -
        hFormEval x w (MvPolynomial.pderiv 1 F) *
          hFormEval x w (MvPolynomial.pderiv 0 G) := by
  simp [hFormJacobian, hFormEval]

omit [CharZero K] in
/-- Evaluation of `w² Lambda` is `w²` times the evaluated quotient. -/
theorem hFormEval_hFormW_sq_mul
    {A : Type*} [Field A] [Algebra K A]
    (Lambda : MvPolynomial (Fin 2) K) (x w : A) :
    hFormEval x w (hFormW ^ 2 * Lambda) =
      w ^ 2 * hFormEval x w Lambda := by
  simp [hFormEval, hFormW]

omit [CharZero K] in
/-- Evaluation of the first Jacobian quotient agrees with the pointwise
quotient `hLambdaP`. -/
theorem hFormEval_jacobian_quotient_P
    {A : Type*} [Field A] [Algebra K A]
    (R LambdaP : MvPolynomial (Fin 2) K) (x w : A)
    (hdivP :
      hFormJacobian hPForm R =
        hFormW ^ 2 * LambdaP)
    (hw : w ≠ 0) :
    hFormEval x w LambdaP =
      OnLeConjecture.DThree.hLambdaP x w
        (hFormEval x w (MvPolynomial.pderiv 0 R))
        (hFormEval x w (MvPolynomial.pderiv 1 R)) := by
  have heval := congrArg (fun F : MvPolynomial (Fin 2) K =>
    hFormEval x w F) hdivP
  rw [hFormEval_hFormJacobian, hFormEval_hFormW_sq_mul,
    hFormEval_pderiv_hPForm_zero,
    hFormEval_pderiv_hPForm_one] at heval
  simp only [OnLeConjecture.DThree.hLambdaP]
  rw [eq_div_iff (pow_ne_zero 2 hw)]
  simpa [mul_comm] using heval.symm

omit [CharZero K] in
/-- Evaluation of the second Jacobian quotient agrees with the pointwise
quotient `hLambdaQ`. -/
theorem hFormEval_jacobian_quotient_Q
    {A : Type*} [Field A] [Algebra K A]
    (R LambdaQ : MvPolynomial (Fin 2) K) (x w : A)
    (hdivQ :
      hFormJacobian hQForm R =
        hFormW ^ 2 * LambdaQ)
    (hw : w ≠ 0) :
    hFormEval x w LambdaQ =
      OnLeConjecture.DThree.hLambdaQ x w
        (hFormEval x w (MvPolynomial.pderiv 0 R))
        (hFormEval x w (MvPolynomial.pderiv 1 R)) := by
  have heval := congrArg (fun F : MvPolynomial (Fin 2) K =>
    hFormEval x w F) hdivQ
  rw [hFormEval_hFormJacobian, hFormEval_hFormW_sq_mul,
    hFormEval_pderiv_hQForm_zero,
    hFormEval_pderiv_hQForm_one] at heval
  simp only [OnLeConjecture.DThree.hLambdaQ]
  rw [eq_div_iff (pow_ne_zero 2 hw)]
  simpa [mul_comm] using heval.symm

omit [CharZero K] in
/-- Divisibility of the two Jacobians by `w²` gives quotient forms of
weighted degrees `N-4` and `N-3`. -/
theorem h_jacobian_quotients_isWeightedHomogeneous
    (N : ℕ) (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hN : 4 ≤ N)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R =
        hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R =
        hFormW ^ 2 * LambdaQ) :
    LambdaP.IsWeightedHomogeneous hFormWeight (N - 4) ∧
      LambdaQ.IsWeightedHomogeneous hFormWeight (N - 3) := by
  have hjP0 := hFormJacobian_isWeightedHomogeneous
    hPForm R 3 N hPForm_isWeightedHomogeneous hR
    (by norm_num) (by norm_num)
    (by omega) (by omega)
  have hdegP :
      (3 - 1) + (N - 2) = N := by omega
  rw [hdegP] at hjP0
  have hjP : MvPolynomial.IsWeightedHomogeneous hFormWeight
      (hFormJacobian hPForm R) N := hjP0
  have hjQ0 := hFormJacobian_isWeightedHomogeneous
    hQForm R 4 N hQForm_isWeightedHomogeneous hR
    (by norm_num) (by norm_num)
    (by omega) (by omega)
  have hdegQ :
      (4 - 1) + (N - 2) = N + 1 := by omega
  rw [hdegQ] at hjQ0
  have hjQ : MvPolynomial.IsWeightedHomogeneous hFormWeight
      (hFormJacobian hQForm R) (N + 1) := hjQ0
  let s : Fin 2 →₀ ℕ := Finsupp.single 1 2
  have hwPow : (hFormW (K := K)) ^ 2 = MvPolynomial.monomial s 1 := by
    simp [hFormW, s, MvPolynomial.X_pow_eq_monomial]
  have hsWeight : Finsupp.weight hFormWeight s = 4 := by
    rw [h_form_weight_apply]
    simp [s]
  have hpProduct : MvPolynomial.IsWeightedHomogeneous hFormWeight
      (MvPolynomial.monomial s 1 * LambdaP) N := by
    rw [← hwPow, ← hLambdaP]
    exact hjP
  have hqProduct : MvPolynomial.IsWeightedHomogeneous hFormWeight
      (MvPolynomial.monomial s 1 * LambdaQ) (N + 1) := by
    rw [← hwPow, ← hLambdaQ]
    exact hjQ
  constructor
  · apply isWeightedHomogeneous_of_monomial_mul
      hFormWeight s LambdaP (N - 4) N hpProduct
    rw [hsWeight]
    omega
  · apply isWeightedHomogeneous_of_monomial_mul
      hFormWeight s LambdaQ (N - 3) (N + 1) hqProduct
    rw [hsWeight]
    omega

/-- The rational function representing `d[R]/dw` in the Cramer formula. -/
@[expose]
noncomputable def hDerivativeRatFunc
    (LambdaP LambdaQ : MvPolynomial (Fin 2) K) : RatFunc K :=
  (-3 * hConicDifference LambdaQ +
      4 * (1 + hConicParamW) * hConicDifference LambdaP) / 12

/-- The Cramer rational function has exactly the common denominator bound
used in Lemma `dthree-Horders`. -/
theorem hasHPoleProfile_hDerivativeRatFunc
    (N : ℕ) (LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hN : 4 ≤ N)
    (hLambdaP :
      LambdaP.IsWeightedHomogeneous hFormWeight (N - 4))
    (hLambdaQ :
      LambdaQ.IsWeightedHomogeneous hFormWeight (N - 3)) :
    HasHPoleProfile ((N - 2) / 2) (N - 2)
      (hDerivativeRatFunc LambdaP LambdaQ) := by
  have hdiffP := hasHPoleProfile_hConicDifference (N - 4) LambdaP hLambdaP
  have hdiffQ := hasHPoleProfile_hConicDifference (N - 3) LambdaQ hLambdaQ
  have honePlusW : HasHPoleProfile 1 2
      (1 + hConicParamW (K := K)) :=
    (hasHPoleProfile_one (K := K) 1 2).add
      hasHPoleProfile_hConicParamW
  have hsecond0 := honePlusW.mul hdiffP
  have hsecond : HasHPoleProfile ((N - 2) / 2) (N - 2)
      ((1 + hConicParamW (K := K)) * hConicDifference LambdaP) := by
    apply hsecond0.mono
    · omega
    · omega
  have hfirst : HasHPoleProfile ((N - 2) / 2) (N - 2)
      (hConicDifference LambdaQ) := by
    apply hdiffQ.mono
    · omega
    · omega
  have hsum := (hfirst.const_mul (-3 : K)).add
    ((hsecond.const_mul (4 : K)))
  have hscaled := hsum.const_mul ((12 : K)⁻¹)
  convert hscaled using 1
  simp only [hDerivativeRatFunc, div_eq_mul_inv, map_inv₀, map_ofNat,
    map_neg]
  ring

/-- The Jacobian divisibility hypotheses imply the pole divisor bound for
the derivative rational function. -/
theorem hDerivativeRatFunc_projectivePoleDegree_le
    [IsAlgClosed K]
    (N : ℕ) (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hN : 4 ≤ N)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R =
        hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R =
        hFormW ^ 2 * LambdaQ) :
    hProjectivePoleDivisorDegree (hDerivativeRatFunc LambdaP LambdaQ) ≤
      hDerivativePoleDegreeBound N := by
  obtain ⟨hPdegree, hQdegree⟩ :=
    h_jacobian_quotients_isWeightedHomogeneous N R LambdaP LambdaQ
      hN hR hLambdaP hLambdaQ
  have hprofile := hasHPoleProfile_hDerivativeRatFunc N LambdaP LambdaQ
    hN hPdegree hQdegree
  have hbound := hprofile.projectivePoleDegree_le
  calc
    hProjectivePoleDivisorDegree (hDerivativeRatFunc LambdaP LambdaQ) ≤
        (N - 2) / 2 + 2 * (N - 2) := hbound
    _ = (N - 2) / 2 + (N - 2) + (N - 2) := by omega
    _ ≤ hDerivativePoleDegreeBound N :=
      h_derivative_pole_degree_le N ((N - 2) / 2) (N - 2) (N - 2)
        le_rfl le_rfl le_rfl

/-- The two Jacobian divisibility hypotheses produce polynomial quotients and
a Cramer rational function with the required pole divisor bound. -/
theorem exists_hDerivativeRatFunc_of_jacobian_dvd
    [IsAlgClosed K]
    (N : ℕ) (R : MvPolynomial (Fin 2) K)
    (hN : 4 ≤ N)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hPdvd : hFormW ^ 2 ∣
      hFormJacobian hPForm R)
    (hQdvd : hFormW ^ 2 ∣
      hFormJacobian hQForm R) :
    ∃ LambdaP LambdaQ : MvPolynomial (Fin 2) K,
      hFormJacobian hPForm R =
          hFormW ^ 2 * LambdaP ∧
        hFormJacobian hQForm R =
          hFormW ^ 2 * LambdaQ ∧
        hProjectivePoleDivisorDegree
            (hDerivativeRatFunc LambdaP LambdaQ) ≤
          hDerivativePoleDegreeBound N := by
  rcases hPdvd with ⟨LambdaP, hLambdaP⟩
  rcases hQdvd with ⟨LambdaQ, hLambdaQ⟩
  refine ⟨LambdaP, LambdaQ, hLambdaP, hLambdaQ, ?_⟩
  exact hDerivativeRatFunc_projectivePoleDegree_le N R LambdaP LambdaQ
    hN hR hLambdaP hLambdaQ

omit [CharZero K] in
/-- A finite local order certifies that a rational function is nonzero. -/
theorem h_ratFunc_ne_zero_of_finite_order
    {f : RatFunc K} {a : K} {z : ℤ}
    (horder : hFiniteOrderAt a f = WithZero.exp z) :
    f ≠ 0 := by
  intro hf
  rw [hf, map_zero] at horder
  exact WithZero.exp_ne_zero horder.symm

/-- Exact local derivative orders at the two branches, together with the
Jacobian divisibility hypotheses, imply the strict branch order estimate in
Lemma `dthree-Horders`. -/
theorem h_branch_order_sum_lt_five_halves_of_jacobian_quotients
    [IsAlgClosed K]
    (N kOne kTwo : ℕ) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R =
        hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R =
        hFormW ^ 2 * LambdaQ)
    {a b : K} (hab : a ≠ b)
    (ha : hFiniteOrderAt a (hDerivativeRatFunc LambdaP LambdaQ) =
      WithZero.exp ((kOne - 1 : ℕ) : ℤ))
    (hb : hFiniteOrderAt b (hDerivativeRatFunc LambdaP LambdaQ) =
      WithZero.exp ((kTwo - 1 : ℕ) : ℤ)) :
    (kOne + kTwo : ℚ) < 5 * (N : ℚ) / 2 := by
  have hderivative : hDerivativeRatFunc LambdaP LambdaQ ≠ 0 :=
    h_ratFunc_ne_zero_of_finite_order ha
  apply h_branch_order_sum_lt_five_halves_of_ratFunc N kOne kTwo hN
    hkOne hkTwo hderivative hab ha hb
  exact hDerivativeRatFunc_projectivePoleDegree_le N R LambdaP LambdaQ
    (by omega) hR hLambdaP hLambdaQ

end OnLeConjecture.DThree
