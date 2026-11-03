/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HBaseDifferenceInterface
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# A six term spanning system for the homogeneous H pair

The polynomial ring `K[x,w]` is generated over `K[P,Q]` by

`1, x, x^2, w, xw, x^2w`.

The proof gives the exact reduction formulas for multiplication by `x` and
`w`. Only spanning is asserted here.
-/

public section

namespace OnLeConjecture.DThree

variable (K : Type*) [Field K] [CharZero K]

/-- The six source terms `1, x, x^2, w, xw, x^2w`. -/
@[expose]
noncomputable def hSixTerm (i : Fin 6) : MvPolynomial (Fin 2) K :=
  ![1, hFormX, hFormX ^ 2, hFormW,
    hFormX * hFormW, hFormX ^ 2 * hFormW] i

/-- A source polynomial written as a sum of the six terms with coefficients
in `K[P,Q]`. -/
@[expose]
noncomputable def hSixTermValue
    (c : Fin 6 → HBaseRing K) : MvPolynomial (Fin 2) K :=
  ∑ i : Fin 6, hBaseToWeightedForm K (c i) * hSixTerm K i

/-- Coefficients after multiplying a six term expression by `x`. -/
noncomputable def hSixTermMultiplyX
    (c : Fin 6 → HBaseRing K) : Fin 6 → HBaseRing K :=
  ![hBaseP K * c 2,
    c 0 + MvPolynomial.C (3 : K) * hBaseQ K * c 5,
    c 1 - MvPolynomial.C (3 : K) * hBaseP K * c 5,
    -MvPolynomial.C (2 : K) * hBaseP K * c 5,
    c 3 - MvPolynomial.C (3 : K) * c 2,
    c 4]

/-- Coefficients after multiplying a six term expression by `w`. -/
noncomputable def hSixTermMultiplyW
    (c : Fin 6 → HBaseRing K) : Fin 6 → HBaseRing K :=
  ![MvPolynomial.C ((2 : K)⁻¹) * hBaseQ K * c 3 +
      hBaseP K ^ 2 * c 5,
    -(MvPolynomial.C ((2 : K)⁻¹) * hBaseP K * c 3) -
      hBaseQ K * c 4,
    hBaseP K * c 4 - hBaseQ K * c 5,
    c 0 + hBaseP K * c 4,
    c 1 - MvPolynomial.C (2 : K) * hBaseP K * c 5,
    c 2 - MvPolynomial.C ((2 : K)⁻¹) * c 3]

omit [CharZero K] in
theorem hSixTermValue_multiplyX
    (c : Fin 6 → HBaseRing K) :
    hSixTermValue K (hSixTermMultiplyX K c) =
      hSixTermValue K c * hFormX := by
  have hC2 : MvPolynomial.C (2 : K) =
      (2 : MvPolynomial (Fin 2) K) := map_natCast _ 2
  have hC3 : MvPolynomial.C (3 : K) =
      (3 : MvPolynomial (Fin 2) K) := map_natCast _ 3
  have hC4 : MvPolynomial.C (4 : K) =
      (4 : MvPolynomial (Fin 2) K) := map_natCast _ 4
  simp only [hSixTermValue, hSixTermMultiplyX, Fin.isValue, neg_mul,
    hSixTerm, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_six,
    Matrix.cons_val_zero, map_mul, hBaseToWeightedForm_p, hPForm,
    mul_one, Matrix.cons_val_one, map_add, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, hBaseToWeightedForm_q, hQForm,
    Matrix.cons_val, map_sub, map_neg]
  rw [hC2, hC3, hC4]
  ring

theorem hSixTermValue_multiplyW
    (c : Fin 6 → HBaseRing K) :
    hSixTermValue K (hSixTermMultiplyW K c) =
      hSixTermValue K c * hFormW := by
  have hC2 : MvPolynomial.C (2 : K) =
      (2 : MvPolynomial (Fin 2) K) := map_natCast _ 2
  have hC3 : MvPolynomial.C (3 : K) =
      (3 : MvPolynomial (Fin 2) K) := map_natCast _ 3
  have hC4 : MvPolynomial.C (4 : K) =
      (4 : MvPolynomial (Fin 2) K) := map_natCast _ 4
  have hhalf : MvPolynomial.C ((2 : K)⁻¹) *
      (2 : MvPolynomial (Fin 2) K) = 1 := by
    rw [← hC2, ← map_mul]
    norm_num
  simp only [hSixTermValue, hSixTermMultiplyW, Fin.isValue, hSixTerm,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_six,
    Matrix.cons_val_zero, map_add, map_mul, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, hBaseToWeightedForm_q, hQForm,
    map_pow, hBaseToWeightedForm_p, hPForm, mul_one,
    Matrix.cons_val_one, map_sub, map_neg, Matrix.cons_val]
  rw [hC2, hC3, hC4]
  linear_combination hhalf *
    (hFormW ^ 2 * hBaseToWeightedForm K (c 3))

/-- Every source polynomial has a six term expression over `K[P,Q]`. -/
theorem exists_hSixTermValue
    (R : MvPolynomial (Fin 2) K) :
    ∃ c : Fin 6 → HBaseRing K, R = hSixTermValue K c := by
  induction R using MvPolynomial.induction_on with
  | C r =>
      let c : Fin 6 → HBaseRing K := ![MvPolynomial.C r, 0, 0, 0, 0, 0]
      refine ⟨c, ?_⟩
      simp [hSixTermValue, hSixTerm, c, Fin.sum_univ_six]
  | add p q hp hq =>
      obtain ⟨c, hc⟩ := hp
      obtain ⟨d, hd⟩ := hq
      refine ⟨fun i ↦ c i + d i, ?_⟩
      rw [hc, hd, hSixTermValue, hSixTermValue]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_add, add_mul]
  | mul_X p i hp =>
      obtain ⟨c, hc⟩ := hp
      fin_cases i
      · refine ⟨hSixTermMultiplyX K c, ?_⟩
        rw [hc, hSixTermValue_multiplyX]
        rfl
      · refine ⟨hSixTermMultiplyW K c, ?_⟩
        rw [hc, hSixTermValue_multiplyW]
        rfl

end OnLeConjecture.DThree
