/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.RatFuncDerivative

/-!
# Constants in a rational function field

This file identifies the kernel of differentiation on a rational function
field in characteristic zero.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial
open OnLeConjecture.DThree

/-- A rational function over a field of characteristic zero has derivative
zero exactly when it is constant. -/
theorem ratFuncDerivative_eq_zero_iff_constant
    {K : Type*} [Field K] [CharZero K] (f : RatFunc K) :
    ratFuncDerivative f = 0 ↔ ∃ c : K, f = RatFunc.C c := by
  constructor
  · intro h
    let p : K[X] := f.num
    let q : K[X] := f.denom
    have hq0 : q ≠ 0 := f.denom_ne_zero
    have hqmap : algebraMap K[X] (RatFunc K) q ≠ 0 :=
      RatFunc.algebraMap_ne_zero hq0
    have hquotient :
        algebraMap K[X] (RatFunc K) p /
            algebraMap K[X] (RatFunc K) q = f :=
      RatFunc.num_div_denom f
    have hnumMap : algebraMap K[X] (RatFunc K)
        (p.derivative * q - p * q.derivative) = 0 := by
      have hformula := ratFuncDerivative_div p q
      rw [hquotient, h] at hformula
      have hnumerator :
          algebraMap K[X] (RatFunc K) p.derivative *
                algebraMap K[X] (RatFunc K) q -
              algebraMap K[X] (RatFunc K) p *
                algebraMap K[X] (RatFunc K) q.derivative = 0 :=
        (div_eq_zero_iff.mp hformula.symm).resolve_right
          (pow_ne_zero 2 hqmap)
      simpa only [map_sub, map_mul] using hnumerator
    have hnum : p.derivative * q - p * q.derivative = 0 :=
      RatFunc.algebraMap_injective K (by simpa using hnumMap)
    have heq : p.derivative * q = p * q.derivative :=
      sub_eq_zero.mp hnum
    have hcoprime : IsCoprime q p := by
      simpa only [p, q] using (RatFunc.isCoprime_num_denom f).symm
    have hqdvd : q ∣ q.derivative := by
      apply hcoprime.dvd_of_dvd_mul_left
      refine ⟨p.derivative, ?_⟩
      calc
        p * q.derivative = p.derivative * q := heq.symm
        _ = q * p.derivative := mul_comm _ _
    have hqderivative : q.derivative = 0 := by
      by_contra hqderivative
      have hqdegree : q.natDegree ≠ 0 :=
        _root_.Polynomial.derivative_ne_zero.mp hqderivative
      exact hqderivative
        (_root_.Polynomial.eq_zero_of_dvd_of_natDegree_lt hqdvd
          (_root_.Polynomial.natDegree_derivative_lt hqdegree))
    have hpeq : p.derivative * q = 0 := by
      simpa only [hqderivative, mul_zero] using heq
    have hpderivative : p.derivative = 0 :=
      (mul_eq_zero.mp hpeq).resolve_right hq0
    let pc : K := p.coeff 0
    let qc : K := q.coeff 0
    have hpconstant : p = C pc :=
      _root_.Polynomial.eq_C_of_derivative_eq_zero hpderivative
    have hqconstant : q = C qc :=
      _root_.Polynomial.eq_C_of_derivative_eq_zero hqderivative
    have hqc : qc ≠ 0 := by
      intro hqc
      apply hq0
      simpa only [hqc, C_0] using hqconstant
    refine ⟨pc / qc, ?_⟩
    calc
      f = algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q := hquotient.symm
      _ = algebraMap K[X] (RatFunc K) (C pc) /
          algebraMap K[X] (RatFunc K) (C qc) := by
        rw [hpconstant, hqconstant]
      _ = RatFunc.C pc / RatFunc.C qc := by
        rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C]
      _ = RatFunc.C (pc / qc) := by rw [map_div₀]
  · rintro ⟨c, rfl⟩
    exact ratFuncDerivative_C c

end OnLeConjecture.Polynomial
