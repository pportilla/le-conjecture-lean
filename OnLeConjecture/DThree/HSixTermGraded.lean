/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HSixTermSpanning

/-!
# Homogeneous six term expressions for the H pair

This module equips the abstract coordinates `P,Q` and the six source terms
with their weights. Projecting an arbitrary six term expression onto one
weighted degree produces an expression whose six coefficients are weighted
homogeneous in `P,Q`.
-/

public section

namespace OnLeConjecture.DThree

variable {K : Type*} [Field K] [CharZero K]

/-- The weights three and four of the abstract coordinates `P,Q`. -/
@[expose]
def hBaseWeight : HBaseCoordinate → ℕ
  | .p => 3
  | .q => 4

/-- The weights of `1,x,x²,w,xw,x²w`. -/
@[expose]
def hSixTermDegree : Fin 6 → ℕ := ![0, 1, 2, 2, 3, 4]

omit [CharZero K] in
/-- Substitution of the two base forms preserves weighted degree. -/
theorem hBaseToWeightedForm_isWeightedHomogeneous
    {S : HBaseRing K} {M : ℕ}
    (hS : S.IsWeightedHomogeneous hBaseWeight M) :
    (hBaseToWeightedForm K S).IsWeightedHomogeneous hFormWeight M := by
  induction hS using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      rw [map_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero K hFormWeight M
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact ihp.add ihq
  | monomial d c hd =>
      have hcoordinate (i : HBaseCoordinate) :
          (match i with
            | .p => hPForm
            | .q => hQForm : MvPolynomial (Fin 2) K).IsWeightedHomogeneous
              hFormWeight (hBaseWeight i) := by
        cases i
        · exact hPForm_isWeightedHomogeneous
        · exact hQForm_isWeightedHomogeneous
      have hprod := MvPolynomial.IsWeightedHomogeneous.prod d.support
        (fun i ↦ (match i with
          | .p => hPForm
          | .q => hQForm : MvPolynomial (Fin 2) K) ^ d i)
        (fun i ↦ d i • hBaseWeight i)
        (fun i _ ↦ (hcoordinate i).pow (d i))
      have hdegree :
          ∑ i ∈ d.support, d i • hBaseWeight i = M := by
        simpa [Finsupp.weight_apply, Finsupp.sum, mul_comm] using hd
      rw [hdegree] at hprod
      have himage :
          hBaseToWeightedForm K (MvPolynomial.monomial d c) =
            MvPolynomial.C c * ∏ i ∈ d.support,
              (match i with
                | .p => hPForm
                | .q => hQForm : MvPolynomial (Fin 2) K) ^ d i := by
        rw [MvPolynomial.monomial_eq, map_mul]
        congr 1
        · exact (hBaseToWeightedForm K).commutes c
        · classical
          simp only [Finsupp.prod, map_prod, map_pow]
          apply Finset.prod_congr rfl
          intro i hi
          cases i with
          | p =>
              rw [show MvPolynomial.X HBaseCoordinate.p = hBaseP K by rfl,
                hBaseToWeightedForm_p]
          | q =>
              rw [show MvPolynomial.X HBaseCoordinate.q = hBaseQ K by rfl,
                hBaseToWeightedForm_q]
      rw [himage]
      exact hprod.C_mul c

omit [CharZero K] in
/-- Each of the six source terms has its displayed weight. -/
theorem hSixTerm_isWeightedHomogeneous (i : Fin 6) :
    (hSixTerm K i).IsWeightedHomogeneous hFormWeight
      (hSixTermDegree i) := by
  have hx : (hFormX (K := K)).IsWeightedHomogeneous hFormWeight 1 :=
    MvPolynomial.isWeightedHomogeneous_X K hFormWeight 0
  have hw : (hFormW (K := K)).IsWeightedHomogeneous hFormWeight 2 :=
    MvPolynomial.isWeightedHomogeneous_X K hFormWeight 1
  fin_cases i
  · simpa [hSixTerm, hSixTermDegree] using
      MvPolynomial.isWeightedHomogeneous_one K hFormWeight
  · simpa [hSixTerm, hSixTermDegree] using hx
  · simpa [hSixTerm, hSixTermDegree] using hx.pow 2
  · simpa [hSixTerm, hSixTermDegree] using hw
  · simpa [hSixTerm, hSixTermDegree] using hx.mul hw
  · simpa [hSixTerm, hSixTermDegree] using (hx.pow 2).mul hw

omit [CharZero K] in
/-- Multiplying a homogeneous base coefficient by its source term adds the
two displayed weights. -/
theorem hSixTermSummand_isWeightedHomogeneous
    {S : HBaseRing K} {M : ℕ} (i : Fin 6)
    (hS : S.IsWeightedHomogeneous hBaseWeight M) :
    (hBaseToWeightedForm K S * hSixTerm K i).IsWeightedHomogeneous
      hFormWeight (M + hSixTermDegree i) :=
  (hBaseToWeightedForm_isWeightedHomogeneous hS).mul
    (hSixTerm_isWeightedHomogeneous i)

omit [CharZero K] in
theorem hWeightedHomogeneousComponent_summand_of_le
    (S : HBaseRing K) (i : Fin 6) (N : ℕ)
    (hle : hSixTermDegree i ≤ N) :
    MvPolynomial.weightedHomogeneousComponent hFormWeight N
        (hBaseToWeightedForm K S * hSixTerm K i) =
      hBaseToWeightedForm K
          (MvPolynomial.weightedHomogeneousComponent hBaseWeight
            (N - hSixTermDegree i) S) *
        hSixTerm K i := by
  induction S using MvPolynomial.induction_on' with
  | add p q ihp ihq =>
      rw [map_add, add_mul, map_add, ihp, ihq]
      simp only [map_add, add_mul]
  | monomial d c =>
      let M := Finsupp.weight hBaseWeight d
      have hmonomial :
          (MvPolynomial.monomial d c : HBaseRing K).IsWeightedHomogeneous
            hBaseWeight M :=
        MvPolynomial.isWeightedHomogeneous_monomial hBaseWeight d c rfl
      have hsummand := hSixTermSummand_isWeightedHomogeneous
        (K := K) i hmonomial
      by_cases hdegree : M + hSixTermDegree i = N
      · subst N
        rw [hsummand.weightedHomogeneousComponent_same,
          Nat.add_sub_cancel, hmonomial.weightedHomogeneousComponent_same]
      · rw [hsummand.weightedHomogeneousComponent_ne N (Ne.symm hdegree)]
        have hsub : N - hSixTermDegree i ≠ M := by omega
        rw [hmonomial.weightedHomogeneousComponent_ne _ hsub]
        simp

omit [CharZero K] in
theorem hWeightedHomogeneousComponent_summand_of_lt
    (S : HBaseRing K) (i : Fin 6) (N : ℕ)
    (hlt : N < hSixTermDegree i) :
    MvPolynomial.weightedHomogeneousComponent hFormWeight N
        (hBaseToWeightedForm K S * hSixTerm K i) = 0 := by
  induction S using MvPolynomial.induction_on' with
  | add p q ihp ihq =>
      rw [map_add, add_mul, map_add, ihp, ihq, add_zero]
  | monomial d c =>
      let M := Finsupp.weight hBaseWeight d
      have hmonomial :
          (MvPolynomial.monomial d c : HBaseRing K).IsWeightedHomogeneous
            hBaseWeight M :=
        MvPolynomial.isWeightedHomogeneous_monomial hBaseWeight d c rfl
      have hsummand := hSixTermSummand_isWeightedHomogeneous
        (K := K) i hmonomial
      apply hsummand.weightedHomogeneousComponent_ne
      omega

/-- The coefficient of the prescribed source term in the projection onto
weighted degree `N`. -/
noncomputable def hSixTermHomogeneousCoefficient
    (N : ℕ) (c : Fin 6 → HBaseRing K) (i : Fin 6) : HBaseRing K :=
  if hSixTermDegree i ≤ N then
    MvPolynomial.weightedHomogeneousComponent hBaseWeight
      (N - hSixTermDegree i) (c i)
  else 0

omit [CharZero K] in
theorem hSixTermHomogeneousCoefficient_isWeightedHomogeneous
    (N : ℕ) (c : Fin 6 → HBaseRing K) (i : Fin 6) :
    (hSixTermHomogeneousCoefficient N c i).IsWeightedHomogeneous
      hBaseWeight (N - hSixTermDegree i) := by
  by_cases hle : hSixTermDegree i ≤ N
  · rw [hSixTermHomogeneousCoefficient, if_pos hle]
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · rw [hSixTermHomogeneousCoefficient, if_neg hle]
    exact MvPolynomial.isWeightedHomogeneous_zero K _ _

omit [CharZero K] in
theorem hSixTermHomogeneousCoefficient_eq_zero_of_lt
    (N : ℕ) (c : Fin 6 → HBaseRing K) (i : Fin 6)
    (hlt : N < hSixTermDegree i) :
    hSixTermHomogeneousCoefficient N c i = 0 := by
  rw [hSixTermHomogeneousCoefficient, if_neg (Nat.not_le.mpr hlt)]

omit [CharZero K] in
theorem hWeightedHomogeneousComponent_hSixTermValue
    (N : ℕ) (c : Fin 6 → HBaseRing K) :
    MvPolynomial.weightedHomogeneousComponent hFormWeight N
        (hSixTermValue K c) =
      hSixTermValue K (hSixTermHomogeneousCoefficient N c) := by
  rw [hSixTermValue, hSixTermValue, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hle : hSixTermDegree i ≤ N
  · rw [hSixTermHomogeneousCoefficient, if_pos hle]
    exact hWeightedHomogeneousComponent_summand_of_le
      (K := K) (c i) i N hle
  · rw [hSixTermHomogeneousCoefficient, if_neg hle, map_zero, zero_mul]
    exact hWeightedHomogeneousComponent_summand_of_lt
      (K := K) (c i) i N (Nat.lt_of_not_ge hle)

/-- Every homogeneous source form has a six term expression whose base
coefficients have the complementary weighted degrees. -/
theorem exists_homogeneous_hSixTermValue
    (R : MvPolynomial (Fin 2) K) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N) :
    ∃ c : Fin 6 → HBaseRing K,
      R = hSixTermValue K c ∧
      (∀ i, (c i).IsWeightedHomogeneous hBaseWeight
        (N - hSixTermDegree i)) ∧
      ∀ i, N < hSixTermDegree i → c i = 0 := by
  obtain ⟨c, hc⟩ := exists_hSixTermValue K R
  refine ⟨hSixTermHomogeneousCoefficient N c, ?_, ?_, ?_⟩
  · rw [← hWeightedHomogeneousComponent_hSixTermValue]
    rw [← hc, hR.weightedHomogeneousComponent_same]
  · exact hSixTermHomogeneousCoefficient_isWeightedHomogeneous N c
  · exact hSixTermHomogeneousCoefficient_eq_zero_of_lt N c

end OnLeConjecture.DThree
