/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.Numerical
public import OnLeConjecture.DThree.TwoForms
public import OnLeConjecture.Polynomial.RatFuncConstants
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The polynomial calculation in the order three Newton argument

This file isolates the polynomial part of Lemma `dthree-newton`.  All input
from the analytic and intersection theoretic arguments is stated explicitly.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The polynomial obtained by taking the Jacobian of weighted initial forms
whose first factor is a depressed cubic. -/
@[expose]
noncomputable def newtonOmega
    (ell alpha : ℕ) (A B : K) (U : K[X]) : K[X] :=
  C (ell : K) * (cubic A B).derivative * U -
    C (3 * (alpha : K)) * cubic A B * U.derivative

omit [CharZero K] in
/-- The explicit expansion of the polynomial in the Newton calculation. -/
theorem newtonOmega_expansion
    (ell alpha : ℕ) (A B : K) (U : K[X]) :
    newtonOmega ell alpha A B U =
      C (3 * (ell : K)) * X ^ 2 * U + C ((ell : K) * A) * U -
        C (3 * (alpha : K)) * X ^ 3 * U.derivative -
        C (3 * (alpha : K) * A) * X * U.derivative -
        C (3 * (alpha : K) * B) * U.derivative := by
  have hp : (cubic A B).derivative = 3 * X ^ 2 + C A := by
    simp [cubic]
    simp only [C_ofNat]
    ring
  rw [newtonOmega, hp, cubic]
  simp only [map_mul, C_ofNat]
  ring

/-- The depressed cubic has degree three. -/
@[simp]
theorem cubic_natDegree (A B : K) : (cubic A B).natDegree = 3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simp only [cubic]
    calc
      (X ^ 3 + C A * X + C B).natDegree ≤
          max (X ^ 3 + C A * X).natDegree (C B).natDegree :=
        natDegree_add_le _ _
      _ ≤ 3 := by
        apply max_le
        · apply (natDegree_add_le _ _).trans
          apply max_le
          · simp
          · exact (natDegree_C_mul_le A X).trans (by simp)
        · simp
  · simp [cubic, coeff_X_pow]

omit [CharZero K] in
/-- The derivative of the depressed cubic. -/
theorem cubic_derivative (A B : K) :
    (cubic A B).derivative = 3 * X ^ 2 + C A := by
  simp [cubic]
  simp only [C_ofNat]
  ring

/-- A depressed cubic with a nonzero lower coefficient has a simple root over
an algebraically closed field of characteristic zero. -/
theorem exists_simple_root_cubic
    [IsAlgClosed K] (A B : K) (hnonzero : A ≠ 0 ∨ B ≠ 0) :
    ∃ r : K, (cubic A B).IsRoot r ∧
      (cubic A B).rootMultiplicity r = 1 := by
  have hp : cubic A B ≠ 0 := by
    intro hpzero
    have hdegree := cubic_natDegree A B
    rw [hpzero, natDegree_zero] at hdegree
    omega
  have hpDegree : (cubic A B).degree = 3 := by
    rw [degree_eq_natDegree hp, cubic_natDegree]
    norm_num
  obtain ⟨r, hr⟩ :=
    IsAlgClosed.exists_root (cubic A B) (by
      rw [hpDegree]
      norm_num)
  by_cases hrDerivative : (cubic A B).derivative.IsRoot r
  · have hrEquation : r ^ 3 + A * r + B = 0 := by
      simpa only [cubic, IsRoot, eval_add, eval_pow, eval_X, eval_mul,
        eval_C] using hr
    have hderivativeEquation : 3 * r ^ 2 + A = 0 := by
      rw [cubic_derivative] at hrDerivative
      simpa only [IsRoot, eval_add, eval_mul, eval_ofNat, eval_pow,
        eval_X, eval_C] using hrDerivative
    have hA : A = -3 * r ^ 2 := by
      linear_combination hderivativeEquation
    have hB : B = 2 * r ^ 3 := by
      rw [hA] at hrEquation
      linear_combination hrEquation
    have hrNonzero : r ≠ 0 := by
      intro hrZero
      subst r
      rcases hnonzero with hANonzero | hBNonzero
      · apply hANonzero
        simpa using hA
      · apply hBNonzero
        simpa using hB
    let q : K := -2 * r
    have hq : (cubic A B).IsRoot q := by
      simp only [cubic, IsRoot, eval_add, eval_pow, eval_X, eval_mul,
        eval_C, q]
      rw [hA, hB]
      ring
    have hqNotDerivative : ¬ (cubic A B).derivative.IsRoot q := by
      rw [cubic_derivative]
      simp only [IsRoot, eval_add, eval_mul, eval_ofNat, eval_pow,
        eval_X, eval_C, q]
      intro hzero
      have hsquare : r ^ 2 = 0 := by
        rw [hA] at hzero
        have hmultiple : (9 : K) * r ^ 2 = 0 := by
          linear_combination hzero
        exact (mul_eq_zero.mp hmultiple).resolve_left (by norm_num)
      exact hrNonzero (eq_zero_of_pow_eq_zero hsquare)
    refine ⟨q, hq, ?_⟩
    have hpositive : 0 < (cubic A B).rootMultiplicity q :=
      (rootMultiplicity_pos hp).mpr hq
    have hnotLarge : ¬ 1 < (cubic A B).rootMultiplicity q := by
      rw [one_lt_rootMultiplicity_iff_isRoot hp]
      exact fun h ↦ hqNotDerivative h.2
    omega
  · refine ⟨r, hr, ?_⟩
    have hpositive : 0 < (cubic A B).rootMultiplicity r :=
      (rootMultiplicity_pos hp).mpr hr
    have hnotLarge : ¬ 1 < (cubic A B).rootMultiplicity r := by
      rw [one_lt_rootMultiplicity_iff_isRoot hp]
      exact fun h ↦ hrDerivative h.2
    omega

omit [CharZero K] in
/-- The Newton polynomial is additive under subtraction in its last
argument. -/
lemma newtonOmega_sub
    (ell alpha : ℕ) (A B : K) (U V : K[X]) :
    newtonOmega ell alpha A B (U - V) =
      newtonOmega ell alpha A B U - newtonOmega ell alpha A B V := by
  simp only [newtonOmega, derivative_sub]
  ring

/-- A scalar multiple of the corresponding power of the cubic has zero
Newton polynomial. -/
theorem newtonOmega_cubic_power
    (alpha s : ℕ) (A B c : K) :
    newtonOmega (3 * alpha * s) alpha A B
        (C c * cubic A B ^ s) = 0 := by
  cases s with
  | zero => simp [newtonOmega]
  | succ s =>
      simp only [newtonOmega, derivative_mul, derivative_C, zero_mul,
        zero_add, derivative_pow]
      push_cast
      simp only [map_mul, C_ofNat]
      ring

/-- Subtracting a scalar multiple of the cubic preserves the Newton
polynomial when `ell = 3 * alpha`. -/
theorem newtonOmega_sub_cubic
    (alpha : ℕ) (A B c : K) (U : K[X]) :
    newtonOmega (3 * alpha) alpha A B (U - C c * cubic A B) =
      newtonOmega (3 * alpha) alpha A B U := by
  have hzero :
      newtonOmega (3 * alpha) alpha A B (C c * cubic A B) = 0 := by
    simpa using newtonOmega_cubic_power alpha 1 A B c
  rw [newtonOmega_sub, hzero, sub_zero]

omit [CharZero K] in
/-- Vanishing of the Newton polynomial makes the numerator of the derivative
of `U ^ (3 * alpha) / p ^ ell` vanish. -/
theorem power_ratio_derivative_numerator_eq_zero
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (hell : 0 < ell)
    (halpha : 0 < alpha)
    (homega : newtonOmega ell alpha A B U = 0) :
    (U ^ (3 * alpha)).derivative * cubic A B ^ ell -
        U ^ (3 * alpha) * (cubic A B ^ ell).derivative = 0 := by
  have hn : 3 * alpha ≠ 0 := by omega
  have hellNe : ell ≠ 0 := Nat.ne_of_gt hell
  have homega' :
      C (ell : K) * (cubic A B).derivative * U -
          C ((3 * alpha : ℕ) : K) * cubic A B * U.derivative = 0 := by
    simpa only [newtonOmega, Nat.cast_mul, Nat.cast_ofNat] using homega
  rw [derivative_pow, derivative_pow,
    ← pow_sub_one_mul hn U,
    ← pow_sub_one_mul hellNe (cubic A B)]
  linear_combination
    -(U ^ (3 * alpha - 1) * cubic A B ^ (ell - 1)) * homega'

/-- If the Newton polynomial vanishes, a positive power of `U` is a scalar
multiple of the corresponding power of the cubic. -/
theorem exists_power_identity_of_newtonOmega_eq_zero
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (hell : 0 < ell)
    (halpha : 0 < alpha)
    (hU : U ≠ 0)
    (homega : newtonOmega ell alpha A B U = 0) :
    ∃ c : K, c ≠ 0 ∧
      U ^ (3 * alpha) = C c * cubic A B ^ ell := by
  let f : RatFunc K :=
    algebraMap K[X] (RatFunc K) (U ^ (3 * alpha)) /
      algebraMap K[X] (RatFunc K) (cubic A B ^ ell)
  have hp : cubic A B ≠ 0 := by
    intro hpzero
    have := cubic_natDegree A B
    rw [hpzero, natDegree_zero] at this
    omega
  have hdenominator : cubic A B ^ ell ≠ 0 := pow_ne_zero ell hp
  have hdenominatorMap :
      algebraMap K[X] (RatFunc K) (cubic A B ^ ell) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hdenominator
  have hnumerator :=
    power_ratio_derivative_numerator_eq_zero
      ell alpha A B U hell halpha homega
  have hnumeratorMap :
      algebraMap K[X] (RatFunc K) (U ^ (3 * alpha)).derivative *
            algebraMap K[X] (RatFunc K) (cubic A B ^ ell) -
          algebraMap K[X] (RatFunc K) (U ^ (3 * alpha)) *
            algebraMap K[X] (RatFunc K) (cubic A B ^ ell).derivative = 0 := by
    simpa only [map_sub, map_mul, map_zero] using
      congrArg (algebraMap K[X] (RatFunc K)) hnumerator
  have hderivative : ratFuncDerivative f = 0 := by
    change ratFuncDerivative
      (algebraMap K[X] (RatFunc K) (U ^ (3 * alpha)) /
        algebraMap K[X] (RatFunc K) (cubic A B ^ ell)) = 0
    rw [ratFuncDerivative_div]
    rw [hnumeratorMap, zero_div]
  obtain ⟨c, hc⟩ :=
    (OnLeConjecture.Polynomial.ratFuncDerivative_eq_zero_iff_constant f).mp
      hderivative
  change
    algebraMap K[X] (RatFunc K) (U ^ (3 * alpha)) /
        algebraMap K[X] (RatFunc K) (cubic A B ^ ell) =
      RatFunc.C c at hc
  have hmap :
      algebraMap K[X] (RatFunc K) (U ^ (3 * alpha)) =
        algebraMap K[X] (RatFunc K) (C c * cubic A B ^ ell) := by
    rw [map_mul, RatFunc.algebraMap_C]
    exact (div_eq_iff hdenominatorMap).mp hc
  have hpolynomial :
      U ^ (3 * alpha) = C c * cubic A B ^ ell :=
    RatFunc.algebraMap_injective K hmap
  refine ⟨c, ?_, hpolynomial⟩
  intro hcZero
  apply hU
  have hpower : U ^ (3 * alpha) = 0 := by
    simpa [hcZero] using hpolynomial
  exact eq_zero_of_pow_eq_zero hpower

omit [CharZero K] in
/-- Root multiplicity is multiplied by a positive integral power. -/
theorem rootMultiplicity_pow_eq_mul
    (r : K) (U : K[X]) (n : ℕ) (hU : U ≠ 0) :
    (U ^ n).rootMultiplicity r = n * U.rootMultiplicity r := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,
        rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hU) hU), ih]
      simp [Nat.succ_mul]

/-- If the cubic has a simple root, vanishing of the Newton polynomial makes
`U` a scalar multiple of a positive integral power of the cubic. -/
theorem exists_eq_cubic_power_of_newtonOmega_eq_zero
    (ell alpha : ℕ) (A B : K) (U : K[X]) (r : K)
    (hell : 0 < ell)
    (halpha : 0 < alpha)
    (hU : U ≠ 0)
    (hsimple : (cubic A B).rootMultiplicity r = 1)
    (homega : newtonOmega ell alpha A B U = 0) :
    ∃ s : ℕ, ∃ c : K, 0 < s ∧ c ≠ 0 ∧
      ell = 3 * alpha * s ∧ U = C c * cubic A B ^ s := by
  obtain ⟨d, hd, hpower⟩ :=
    exists_power_identity_of_newtonOmega_eq_zero
      ell alpha A B U hell halpha hU homega
  have hp : cubic A B ≠ 0 := by
    intro hpzero
    have hdegree := cubic_natDegree A B
    rw [hpzero, natDegree_zero] at hdegree
    omega
  have hn : 3 * alpha ≠ 0 := by omega
  have hright : C d * cubic A B ^ ell ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hd) (pow_ne_zero ell hp)
  have hmultiplicity := congrArg (rootMultiplicity r) hpower
  rw [rootMultiplicity_pow_eq_mul r U (3 * alpha) hU,
    rootMultiplicity_mul hright, rootMultiplicity_C,
    rootMultiplicity_pow_eq_mul r (cubic A B) ell hp,
    hsimple, mul_one, zero_add] at hmultiplicity
  let s : ℕ := U.rootMultiplicity r
  have hs : 0 < s := by
    by_contra hsNot
    have hsZero : s = 0 := Nat.eq_zero_of_not_pos hsNot
    have hrootZero : U.rootMultiplicity r = 0 := by
      simpa only [s] using hsZero
    rw [hrootZero, mul_zero] at hmultiplicity
    omega
  have hellPower : ell = 3 * alpha * s := by
    exact hmultiplicity.symm
  have hpower' :
      U ^ (3 * alpha) = C d * (cubic A B ^ s) ^ (3 * alpha) := by
    calc
      U ^ (3 * alpha) = C d * cubic A B ^ ell := hpower
      _ = C d * (cubic A B ^ s) ^ (3 * alpha) := by
        rw [hellPower, Nat.mul_comm (3 * alpha) s, pow_mul]
  have hconstantUnit : IsUnit (C d : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hd)
  have hassociatedPowers :
      Associated (U ^ (3 * alpha)) ((cubic A B ^ s) ^ (3 * alpha)) :=
    (Associated.of_eq hpower').trans
      (associated_unit_mul_left _ _ hconstantUnit)
  have hassociated : Associated U (cubic A B ^ s) :=
    (Associated.pow_iff hn).mp hassociatedPowers
  rcases hassociated.symm with ⟨u, hu⟩
  obtain ⟨c, hcUnit, hconstant⟩ :=
    _root_.Polynomial.isUnit_iff.mp (Units.isUnit u)
  have hc : c ≠ 0 := isUnit_iff_ne_zero.mp hcUnit
  refine ⟨s, c, hs, hc, hellPower, ?_⟩
  calc
    U = cubic A B ^ s * (u : K[X]) := hu.symm
    _ = cubic A B ^ s * C c := by rw [hconstant]
    _ = C c * cubic A B ^ s := mul_comm _ _

/-- A simple root and exclusion of scalar cubic powers imply that the Newton
polynomial is nonzero. -/
theorem newtonOmega_ne_zero_of_not_cubic_power
    (ell alpha : ℕ) (A B : K) (U : K[X]) (r : K)
    (hell : 0 < ell)
    (halpha : 0 < alpha)
    (hU : U ≠ 0)
    (hsimple : (cubic A B).rootMultiplicity r = 1)
    (hnotPower :
      ∀ (s : ℕ) (c : K), 0 < s → c ≠ 0 →
        U ≠ C c * cubic A B ^ s) :
    newtonOmega ell alpha A B U ≠ 0 := by
  intro homega
  obtain ⟨s, c, hs, hc, _, hUeq⟩ :=
    exists_eq_cubic_power_of_newtonOmega_eq_zero
      ell alpha A B U r hell halpha hU hsimple homega
  exact hnotPower s c hs hc hUeq

/-- Over an algebraically closed field, nonvanishing of a lower cubic
coefficient supplies the simple root needed for the power exclusion. -/
theorem newtonOmega_ne_zero_of_nonzero_lower_coefficient
    [IsAlgClosed K]
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (hell : 0 < ell)
    (halpha : 0 < alpha)
    (hU : U ≠ 0)
    (hlower : A ≠ 0 ∨ B ≠ 0)
    (hnotPower :
      ∀ (s : ℕ) (c : K), 0 < s → c ≠ 0 →
        U ≠ C c * cubic A B ^ s) :
    newtonOmega ell alpha A B U ≠ 0 := by
  obtain ⟨r, _, hsimple⟩ := exists_simple_root_cubic A B hlower
  exact newtonOmega_ne_zero_of_not_cubic_power
    ell alpha A B U r hell halpha hU hsimple hnotPower

/-- Subtracting the leading multiple of the cubic from a polynomial of
degree three leaves a polynomial of degree at most two. -/
theorem natDegree_sub_le_two_of_natDegree_eq_three
    (A B : K) (U : K[X]) (hdegree : U.natDegree = 3) :
    (U - C U.leadingCoeff * cubic A B).natDegree ≤ 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_sub, coeff_C_mul]
  by_cases hnThree : n = 3
  · subst n
    have hleading : U.coeff 3 = U.leadingCoeff := by
      simpa [hdegree] using U.coeff_natDegree
    simp [cubic, coeff_X_pow, hleading]
  · have hnLarge : 3 < n := by omega
    have hUcoeff : U.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    have hpcoeff : (cubic A B).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa using hnLarge)
    rw [hUcoeff, hpcoeff, mul_zero, sub_zero]

omit [CharZero K] in
/-- The coefficient two degrees above a nonconstant polynomial is the
coefficient used in the Newton argument. -/
theorem newtonOmega_coeff_natDegree_add_two
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (hdegree : 1 ≤ U.natDegree) :
    (newtonOmega ell alpha A B U).coeff (U.natDegree + 2) =
      3 * ((ell : K) - (alpha : K) * (U.natDegree : K)) *
        U.leadingCoeff := by
  have hcoeffTwo : U.coeff (U.natDegree + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeffThree : U.coeff (U.natDegree + 3) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [newtonOmega_expansion]
  simp only [coeff_sub, coeff_add, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', coeff_derivative]
  simp [hdegree, hcoeffTwo, hcoeffThree, coeff_derivative]
  ring

omit [CharZero K] in
/-- The same coefficient formula when the last polynomial has degree zero. -/
theorem newtonOmega_coeff_two_of_natDegree_eq_zero
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (hdegree : U.natDegree = 0) :
    (newtonOmega ell alpha A B U).coeff 2 =
      3 * (ell : K) * U.leadingCoeff := by
  have hcoeffTwo : U.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeffThree : U.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hleading : U.coeff 0 = U.leadingCoeff := by
    simpa [hdegree] using U.coeff_natDegree
  rw [newtonOmega_expansion]
  simp only [coeff_sub, coeff_add, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', coeff_derivative]
  simp [hcoeffTwo, hcoeffThree, hleading, coeff_derivative]

/-- The coefficient formula holds for every polynomial. -/
theorem newtonOmega_coeff_natDegree_add_two_all
    (ell alpha : ℕ) (A B : K) (U : K[X]) :
    (newtonOmega ell alpha A B U).coeff (U.natDegree + 2) =
      3 * ((ell : K) - (alpha : K) * (U.natDegree : K)) *
        U.leadingCoeff := by
  by_cases hdegree : 1 ≤ U.natDegree
  · exact newtonOmega_coeff_natDegree_add_two ell alpha A B U hdegree
  · have hzero : U.natDegree = 0 := by omega
    rw [hzero]
    simpa using newtonOmega_coeff_two_of_natDegree_eq_zero ell alpha A B U hzero

/-- For positive `alpha`, a nonzero polynomial of degree at most two gives a
Newton polynomial of degree at least two. -/
theorem two_le_newtonOmega_natDegree_of_natDegree_le_two
    (alpha : ℕ) (A B : K) (U : K[X])
    (halpha : 0 < alpha)
    (hU : U ≠ 0)
    (hdegree : U.natDegree ≤ 2) :
    2 ≤ (newtonOmega (3 * alpha) alpha A B U).natDegree := by
  have halphaCast : (alpha : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt halpha)
  have hgap : (3 : K) - (U.natDegree : K) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by omega : 3 ≠ U.natDegree)
  have hfactor :
      ((3 * alpha : ℕ) : K) - (alpha : K) * (U.natDegree : K) =
        (alpha : K) * ((3 : K) - (U.natDegree : K)) := by
    push_cast
    ring
  have hcoefficient :
      (newtonOmega (3 * alpha) alpha A B U).coeff (U.natDegree + 2) ≠ 0 := by
    rw [newtonOmega_coeff_natDegree_add_two_all, hfactor]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero halphaCast hgap))
      (leadingCoeff_ne_zero.mpr hU)
  have hindex :
      U.natDegree + 2 ≤
        (newtonOmega (3 * alpha) alpha A B U).natDegree :=
    le_natDegree_of_ne_zero hcoefficient
  omega

/-- If the Newton polynomial has degree at most one, its top coefficient
forces the weight of `U` to equal its degree times `alpha`. -/
theorem ell_eq_alpha_mul_natDegree_of_newtonOmega_natDegree_le_one
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (hdegree : 3 ≤ U.natDegree)
    (homegaDegree : (newtonOmega ell alpha A B U).natDegree ≤ 1) :
    ell = alpha * U.natDegree := by
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hdegree
    omega
  have hindex :
      (newtonOmega ell alpha A B U).natDegree < U.natDegree + 2 := by
    omega
  have hcoefficient :
      (newtonOmega ell alpha A B U).coeff (U.natDegree + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt hindex
  rw [newtonOmega_coeff_natDegree_add_two ell alpha A B U (by omega)] at hcoefficient
  have hscalar :
      (ell : K) - (alpha : K) * (U.natDegree : K) = 0 := by
    rcases mul_eq_zero.mp hcoefficient with hproduct | hleading
    · rcases mul_eq_zero.mp hproduct with hthree | hscalar
      · norm_num at hthree
      · exact hscalar
    · exact (leadingCoeff_ne_zero.mpr hU hleading).elim
  have hcast :
      (ell : K) = (alpha : K) * (U.natDegree : K) :=
    sub_eq_zero.mp hscalar
  exact_mod_cast hcast

/-- The top coefficient calculation and the cubic subtraction force degree
at least four.  The last hypothesis is precisely the exclusion needed after
the subtraction. -/
theorem newton_polynomial_degree_constraints
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (halpha : 0 < alpha)
    (hdegree : 3 ≤ U.natDegree)
    (homegaDegree : (newtonOmega ell alpha A B U).natDegree ≤ 1)
    (hnotCubic : ∀ c : K, U ≠ C c * cubic A B) :
    ell = alpha * U.natDegree ∧ 4 ≤ U.natDegree := by
  have hell :=
    ell_eq_alpha_mul_natDegree_of_newtonOmega_natDegree_le_one
      ell alpha A B U hdegree homegaDegree
  refine ⟨hell, ?_⟩
  by_contra hfour
  have hdegreeThree : U.natDegree = 3 := by omega
  have hellThree : ell = 3 * alpha := by
    rw [hdegreeThree] at hell
    simpa [mul_comm] using hell
  let V : K[X] := U - C U.leadingCoeff * cubic A B
  have hVDegree : V.natDegree ≤ 2 := by
    exact natDegree_sub_le_two_of_natDegree_eq_three A B U hdegreeThree
  have hV : V ≠ 0 := by
    intro hzero
    apply hnotCubic U.leadingCoeff
    exact sub_eq_zero.mp hzero
  have hLower :
      2 ≤ (newtonOmega (3 * alpha) alpha A B V).natDegree :=
    two_le_newtonOmega_natDegree_of_natDegree_le_two
      alpha A B V halpha hV hVDegree
  have hSame :
      newtonOmega (3 * alpha) alpha A B V =
        newtonOmega (3 * alpha) alpha A B U := by
    exact newtonOmega_sub_cubic alpha A B U.leadingCoeff U
  rw [hSame, ← hellThree] at hLower
  omega

/-- The polynomial constraints and the Newton inequalities give all numerical
equalities in Lemma `dthree-newton`. -/
theorem newton_polynomial_and_estimates_force_equalities
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (A₃ j b S m M : ℤ)
    (halpha : 0 < alpha)
    (hUDegree : 3 ≤ U.natDegree)
    (homegaDegree : (newtonOmega ell alpha A B U).natDegree ≤ 1)
    (hnotCubic : ∀ c : K, U ≠ C c * cubic A B)
    (hA₃ : A₃ ≤ (alpha : ℤ))
    (hjzero : 0 ≤ j)
    (hjone : j ≤ 1)
    (hdegree :
      ((U.natDegree : ℤ) - 4 + 2 * j) * (alpha : ℤ) ≤ A₃)
    (hb : 1 ≤ b)
    (hbthree : b ≤ 3)
    (hS :
      S = 3 * (alpha : ℤ) * ((U.natDegree : ℤ) - 2) - b + 3)
    (hSm : S ≤ m)
    (hm :
      m ≤ (alpha : ℤ) * ((U.natDegree : ℤ) + 2 - j))
    (hM : M = 3 * (U.natDegree : ℤ) * (alpha : ℤ)) :
    ell = 4 * alpha ∧ j = 0 ∧ U.natDegree = 4 ∧ b = 3 ∧
      S = 6 * (alpha : ℤ) ∧ m = 6 * (alpha : ℤ) ∧
      M = 12 * (alpha : ℤ) := by
  obtain ⟨hell, hk⟩ :=
    newton_polynomial_degree_constraints ell alpha A B U halpha
      hUDegree homegaDegree hnotCubic
  have halphaInt : 1 ≤ (alpha : ℤ) := by exact_mod_cast halpha
  have hkInt : 4 ≤ (U.natDegree : ℤ) := by exact_mod_cast hk
  obtain ⟨hj, hkCast, hbEq, hSEq, hmEq, hMEq⟩ :=
    newton_estimates_force_equalities
      (alpha : ℤ) A₃ (U.natDegree : ℤ) j b S m M
      halphaInt hA₃ hkInt hjzero hjone hdegree hb hbthree hS hSm hm hM
  have hkEq : U.natDegree = 4 := by exact_mod_cast hkCast
  have hellEq : ell = 4 * alpha := by
    rw [hell, hkEq]
    omega
  exact ⟨hellEq, hj, hkEq, hbEq, hSEq, hmEq, hMEq⟩

/-- With a simple root and the full power exclusion, the actual degree of the
Newton polynomial satisfies the numerical estimates and is forced to be zero.
The Newton polynomial itself remains nonzero. -/
theorem newton_power_exclusion_and_estimates_force_equalities
    (ell alpha : ℕ) (A B : K) (U : K[X]) (r : K)
    (A₃ b S m M : ℤ)
    (halpha : 0 < alpha)
    (hUDegree : 3 ≤ U.natDegree)
    (homegaDegree : (newtonOmega ell alpha A B U).natDegree ≤ 1)
    (hsimple : (cubic A B).rootMultiplicity r = 1)
    (hnotPower :
      ∀ (s : ℕ) (c : K), 0 < s → c ≠ 0 →
        U ≠ C c * cubic A B ^ s)
    (hA₃ : A₃ ≤ (alpha : ℤ))
    (hdegree :
      ((U.natDegree : ℤ) - 4 +
          2 * ((newtonOmega ell alpha A B U).natDegree : ℤ)) *
        (alpha : ℤ) ≤ A₃)
    (hb : 1 ≤ b)
    (hbthree : b ≤ 3)
    (hS :
      S = 3 * (alpha : ℤ) * ((U.natDegree : ℤ) - 2) - b + 3)
    (hSm : S ≤ m)
    (hm :
      m ≤ (alpha : ℤ) *
        ((U.natDegree : ℤ) + 2 -
          ((newtonOmega ell alpha A B U).natDegree : ℤ)))
    (hM : M = 3 * (U.natDegree : ℤ) * (alpha : ℤ)) :
    ell = 4 * alpha ∧
      newtonOmega ell alpha A B U ≠ 0 ∧
      (newtonOmega ell alpha A B U).natDegree = 0 ∧
      U.natDegree = 4 ∧ b = 3 ∧ S = 6 * (alpha : ℤ) ∧
      m = 6 * (alpha : ℤ) ∧ M = 12 * (alpha : ℤ) := by
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hUDegree
    omega
  have hellEq :=
    ell_eq_alpha_mul_natDegree_of_newtonOmega_natDegree_le_one
      ell alpha A B U hUDegree homegaDegree
  have hell : 0 < ell := by
    rw [hellEq]
    exact Nat.mul_pos halpha (by omega)
  have homega : newtonOmega ell alpha A B U ≠ 0 :=
    newtonOmega_ne_zero_of_not_cubic_power
      ell alpha A B U r hell halpha hU hsimple hnotPower
  have hnotCubic : ∀ c : K, U ≠ C c * cubic A B := by
    intro c
    by_cases hc : c = 0
    · simpa [hc] using hU
    · simpa using hnotPower 1 c (by omega) hc
  have hjzero :
      0 ≤ ((newtonOmega ell alpha A B U).natDegree : ℤ) := by omega
  have hjone :
      ((newtonOmega ell alpha A B U).natDegree : ℤ) ≤ 1 := by
    exact_mod_cast homegaDegree
  obtain ⟨hellFour, hj, hk, hbEq, hSEq, hmEq, hMEq⟩ :=
    newton_polynomial_and_estimates_force_equalities
      ell alpha A B U A₃
      ((newtonOmega ell alpha A B U).natDegree : ℤ) b S m M
      halpha hUDegree homegaDegree hnotCubic hA₃ hjzero hjone
      hdegree hb hbthree hS hSm hm hM
  have hjNat : (newtonOmega ell alpha A B U).natDegree = 0 := by
    exact_mod_cast hj
  exact ⟨hellFour, homega, hjNat, hk, hbEq, hSEq, hmEq, hMEq⟩

/-- Over an algebraically closed field, the nonzero lower coefficient of the
depressed cubic supplies the simple root in the preceding theorem. -/
theorem newton_lower_coefficient_and_estimates_force_equalities
    [IsAlgClosed K]
    (ell alpha : ℕ) (A B : K) (U : K[X])
    (A₃ b S m M : ℤ)
    (halpha : 0 < alpha)
    (hUDegree : 3 ≤ U.natDegree)
    (homegaDegree : (newtonOmega ell alpha A B U).natDegree ≤ 1)
    (hlower : A ≠ 0 ∨ B ≠ 0)
    (hnotPower :
      ∀ (s : ℕ) (c : K), 0 < s → c ≠ 0 →
        U ≠ C c * cubic A B ^ s)
    (hA₃ : A₃ ≤ (alpha : ℤ))
    (hdegree :
      ((U.natDegree : ℤ) - 4 +
          2 * ((newtonOmega ell alpha A B U).natDegree : ℤ)) *
        (alpha : ℤ) ≤ A₃)
    (hb : 1 ≤ b)
    (hbthree : b ≤ 3)
    (hS :
      S = 3 * (alpha : ℤ) * ((U.natDegree : ℤ) - 2) - b + 3)
    (hSm : S ≤ m)
    (hm :
      m ≤ (alpha : ℤ) *
        ((U.natDegree : ℤ) + 2 -
          ((newtonOmega ell alpha A B U).natDegree : ℤ)))
    (hM : M = 3 * (U.natDegree : ℤ) * (alpha : ℤ)) :
    ell = 4 * alpha ∧
      newtonOmega ell alpha A B U ≠ 0 ∧
      (newtonOmega ell alpha A B U).natDegree = 0 ∧
      U.natDegree = 4 ∧ b = 3 ∧ S = 6 * (alpha : ℤ) ∧
      m = 6 * (alpha : ℤ) ∧ M = 12 * (alpha : ℤ) := by
  obtain ⟨r, _, hsimple⟩ := exists_simple_root_cubic A B hlower
  exact newton_power_exclusion_and_estimates_force_equalities
    ell alpha A B U r A₃ b S m M halpha hUDegree homegaDegree
    hsimple hnotPower hA₃ hdegree hb hbthree hS hSm hm hM

end OnLeConjecture.DThree
