/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HGlobalOrders
public import Mathlib.Algebra.Polynomial.Derivation

/-!
# Differentiation of rational functions

This file constructs the derivation of `K(m)` over `K` that sends the
rational parameter `m` to one. It also records the decrease of a positive
finite order under differentiation.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial WithZero

variable {K : Type*} [Field K]

/-- The formal derivative of a rational function in the parameter `m`. -/
@[expose]
noncomputable def ratFuncDerivative (f : RatFunc K) : RatFunc K :=
  f.liftOn'
    (fun p q ↦
      (algebraMap K[X] (RatFunc K) p.derivative *
          algebraMap K[X] (RatFunc K) q -
        algebraMap K[X] (RatFunc K) p *
          algebraMap K[X] (RatFunc K) q.derivative) /
        algebraMap K[X] (RatFunc K) q ^ 2)
    (by
      intro p q c hq hc
      have hqc : algebraMap K[X] (RatFunc K) q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hq
      have hcc : algebraMap K[X] (RatFunc K) c ≠ 0 :=
        RatFunc.algebraMap_ne_zero hc
      simp only [derivative_mul, map_mul, map_add]
      field_simp [hqc, hcc]
      ring)

/-- The derivative of an explicit polynomial fraction is the quotient rule. -/
theorem ratFuncDerivative_div
    (p q : K[X]) :
    ratFuncDerivative
        (algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q) =
      (algebraMap K[X] (RatFunc K) p.derivative *
          algebraMap K[X] (RatFunc K) q -
        algebraMap K[X] (RatFunc K) p *
          algebraMap K[X] (RatFunc K) q.derivative) /
        algebraMap K[X] (RatFunc K) q ^ 2 := by
  rw [ratFuncDerivative, RatFunc.liftOn'_div]
  · intro r
    simp

theorem ratFuncDerivative_add (f g : RatFunc K) :
    ratFuncDerivative (f + g) =
      ratFuncDerivative f + ratFuncDerivative g := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
      induction g using RatFunc.induction_on with
      | f r s hs =>
          have hqMap : algebraMap K[X] (RatFunc K) q ≠ 0 :=
            RatFunc.algebraMap_ne_zero hq
          have hsMap : algebraMap K[X] (RatFunc K) s ≠ 0 :=
            RatFunc.algebraMap_ne_zero hs
          have hadd :
              algebraMap K[X] (RatFunc K) p /
                    algebraMap K[X] (RatFunc K) q +
                  algebraMap K[X] (RatFunc K) r /
                    algebraMap K[X] (RatFunc K) s =
                algebraMap K[X] (RatFunc K) (p * s + q * r) /
                  algebraMap K[X] (RatFunc K) (q * s) := by
            simp only [map_add, map_mul]
            field_simp [hqMap, hsMap]
          rw [hadd, ratFuncDerivative_div,
            ratFuncDerivative_div, ratFuncDerivative_div]
          simp only [derivative_mul, map_add, map_mul]
          field_simp [hqMap, hsMap]
          ring_nf

theorem ratFuncDerivative_smul (c : K) (f : RatFunc K) :
    ratFuncDerivative (c • f) = c • ratFuncDerivative f := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
      have hqMap : algebraMap K[X] (RatFunc K) q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hq
      have hfraction :
          c • (algebraMap K[X] (RatFunc K) p /
            algebraMap K[X] (RatFunc K) q) =
          algebraMap K[X] (RatFunc K) (C c * p) /
            algebraMap K[X] (RatFunc K) q := by
        simpa [Polynomial.smul_eq_C_mul] using
          (RatFunc.div_smul c p q).symm
      have hcMap :
          algebraMap K[X] (RatFunc K) (C c) =
            algebraMap K (RatFunc K) c := by
        rw [RatFunc.algebraMap_apply (K := K) (R := K) c]
        change algebraMap K[X] (RatFunc K) (C c) =
          algebraMap K[X] (RatFunc K) (C c) /
            algebraMap K[X] (RatFunc K) 1
        rw [map_one, div_one]
      rw [hfraction, ratFuncDerivative_div,
        ratFuncDerivative_div]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add,
        map_mul, Algebra.smul_def]
      rw [hcMap]
      ring

theorem ratFuncDerivative_mul (f g : RatFunc K) :
    ratFuncDerivative (f * g) =
      f * ratFuncDerivative g + g * ratFuncDerivative f := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
      induction g using RatFunc.induction_on with
      | f r s hs =>
          have hqMap : algebraMap K[X] (RatFunc K) q ≠ 0 :=
            RatFunc.algebraMap_ne_zero hq
          have hsMap : algebraMap K[X] (RatFunc K) s ≠ 0 :=
            RatFunc.algebraMap_ne_zero hs
          have hmul :
              (algebraMap K[X] (RatFunc K) p /
                    algebraMap K[X] (RatFunc K) q) *
                  (algebraMap K[X] (RatFunc K) r /
                    algebraMap K[X] (RatFunc K) s) =
                algebraMap K[X] (RatFunc K) (p * r) /
                  algebraMap K[X] (RatFunc K) (q * s) := by
            simp only [map_mul]
            ring
          rw [hmul, ratFuncDerivative_div,
            ratFuncDerivative_div, ratFuncDerivative_div]
          simp only [derivative_mul, map_add, map_mul]
          field_simp [hqMap, hsMap]
          ring

/-- The formal derivative in `m`, bundled as a `K` derivation. -/
@[expose]
noncomputable def ratFuncDerivativeDerivation :
    Derivation K (RatFunc K) (RatFunc K) :=
  Derivation.mk'
    { toFun := ratFuncDerivative
      map_add' := ratFuncDerivative_add
      map_smul' := ratFuncDerivative_smul }
    ratFuncDerivative_mul

@[simp]
theorem ratFuncDerivativeDerivation_apply (f : RatFunc K) :
    ratFuncDerivativeDerivation f = ratFuncDerivative f := rfl

/-- Differentiation of a polynomial inside the rational function field. -/
@[simp]
theorem ratFuncDerivative_algebraMap (p : K[X]) :
    ratFuncDerivative (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  have hformula := ratFuncDerivative_div (K := K) p 1
  simpa using hformula

/-- Constants have derivative zero. -/
@[simp]
theorem ratFuncDerivative_C (c : K) :
    ratFuncDerivative (RatFunc.C c) = 0 := by
  rw [← RatFunc.algebraMap_C, ratFuncDerivative_algebraMap,
    derivative_C, map_zero]

/-- The multiplicative unit has derivative zero. -/
@[simp]
theorem ratFuncDerivative_one :
    ratFuncDerivative (1 : RatFunc K) = 0 := by
  change ratFuncDerivativeDerivation (1 : RatFunc K) = 0
  exact Derivation.map_one_eq_zero ratFuncDerivativeDerivation

/-- The zero rational function has derivative zero. -/
@[simp]
theorem ratFuncDerivative_zero :
    ratFuncDerivative (0 : RatFunc K) = 0 := by
  change ratFuncDerivativeDerivation (0 : RatFunc K) = 0
  exact Derivation.map_zero ratFuncDerivativeDerivation

/-- Differentiation commutes with subtraction. -/
theorem ratFuncDerivative_sub (f g : RatFunc K) :
    ratFuncDerivative (f - g) =
      ratFuncDerivative f - ratFuncDerivative g := by
  change ratFuncDerivativeDerivation (f - g) =
    ratFuncDerivativeDerivation f - ratFuncDerivativeDerivation g
  exact ratFuncDerivativeDerivation.map_sub f g

/-- The rational parameter has derivative one. -/
@[simp]
theorem ratFuncDerivative_X :
    ratFuncDerivative (RatFunc.X : RatFunc K) = 1 := by
  rw [← RatFunc.algebraMap_X, ratFuncDerivative_algebraMap,
    derivative_X, map_one]

/-- A positive finite order decreases by one under differentiation in the
parameter `m`. -/
theorem h_finite_order_ratFuncDerivative_of_pos
    [CharZero K] (a : K) (f : RatFunc K) (k : ℕ) (hk : 0 < k)
    (horder : hFiniteOrderAt a f = WithZero.exp (k : ℤ)) :
    hFiniteOrderAt a (ratFuncDerivative f) =
      WithZero.exp ((k - 1 : ℕ) : ℤ) := by
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, map_zero] at horder
    exact WithZero.exp_ne_zero horder.symm
  obtain ⟨hnumMultiplicity, hdenMultiplicity⟩ :=
    h_divisor_coefficients_of_finite_order hf a k horder
  rw [h_finite_zero_divisor_apply] at hnumMultiplicity
  rw [h_finite_pole_divisor_apply] at hdenMultiplicity
  let p : K[X] := f.num
  let q : K[X] := f.denom
  let u : K[X] :=
    p /ₘ (X - C a) ^ p.rootMultiplicity a
  have hp : p ≠ 0 := by
    exact RatFunc.num_ne_zero hf
  have hq : q ≠ 0 := by
    exact f.denom_ne_zero
  have hqNotRoot : ¬ q.IsRoot a := by
    intro hroot
    have hpositive := (Polynomial.rootMultiplicity_pos hq).2 hroot
    change q.rootMultiplicity a = 0 at hdenMultiplicity
    omega
  have hqEval : q.eval a ≠ 0 := by
    simpa [Polynomial.IsRoot] using hqNotRoot
  have hfactor :
      (X - C a) ^ k * u = p := by
    have hcanonical :=
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p a
    change p.rootMultiplicity a = k at hnumMultiplicity
    simpa [u, hnumMultiplicity] using hcanonical
  have huEval : u.eval a ≠ 0 := by
    have hcanonical :=
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
    exact hcanonical
  have hkPower :
      (X - C a : K[X]) ^ k =
        (X - C a) ^ (k - 1) * (X - C a) := by
    calc
      (X - C a : K[X]) ^ k =
          (X - C a) ^ ((k - 1) + 1) :=
        congrArg (fun n : ℕ ↦ (X - C a : K[X]) ^ n)
          (Nat.sub_add_cancel hk).symm
      _ = (X - C a) ^ (k - 1) * (X - C a) :=
        pow_succ (X - C a) (k - 1)
  have hpDerivative :
      p.derivative =
        (X - C a) ^ (k - 1) *
          (C (k : K) * u + (X - C a) * u.derivative) := by
    rw [← hfactor, derivative_mul, derivative_X_sub_C_pow, hkPower]
    ring
  let v : K[X] :=
    (C (k : K) * u + (X - C a) * u.derivative) * q -
      (X - C a) * u * q.derivative
  have hnumerator :
      p.derivative * q - p * q.derivative =
        (X - C a) ^ (k - 1) * v := by
    rw [hpDerivative, ← hfactor, hkPower]
    simp only [v]
    ring
  have hvEvalIdentity :
      v.eval a = (k : K) * u.eval a * q.eval a := by
    simp [v]
  have hkCast : (k : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hvEval : v.eval a ≠ 0 := by
    rw [hvEvalIdentity]
    exact mul_ne_zero (mul_ne_zero hkCast huEval) hqEval
  have hformula :
      ratFuncDerivative f =
        algebraMap K[X] (RatFunc K)
              (p.derivative * q - p * q.derivative) /
          algebraMap K[X] (RatFunc K) (q ^ 2) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [ratFuncDerivative_div]
    simp only [p, q, map_sub, map_mul, map_pow]
  rw [hformula, hnumerator, map_div₀, map_mul, map_pow, map_pow,
    map_mul, map_pow, map_pow,
    h_finite_order_parameter,
    h_finite_order_polynomial_of_eval_ne_zero a v hvEval,
    h_finite_order_polynomial_of_eval_ne_zero a q hqEval]
  simp

end OnLeConjecture.DThree
