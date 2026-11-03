/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitProjective
public import OnLeConjecture.DTwo.OrbitSixTermSpanning

/-!
# Homogeneous six term expressions for the quadratic orbit pair

The abstract coordinates `Phi,Psi` have degrees two and three. Projecting a
six term expression onto one degree yields coefficients of the complementary
weighted degrees in the base ring.
-/

public section

namespace OnLeConjecture.DTwo

variable {K : Type*} [Field K] [CharZero K]

/-- The degrees two and three of the abstract orbit coordinates. -/
@[expose]
def orbitBaseWeight : OrbitBaseCoordinate → ℕ
  | .phi => 2
  | .psi => 3

/-- The degrees of `1,s,s²,lambda,s lambda,s² lambda`. -/
@[expose]
def orbitSixTermDegree : Fin 6 → ℕ := ![0, 1, 2, 1, 2, 3]

omit [CharZero K] in
theorem orbitPolynomialPhi_isHomogeneous :
    (orbitPolynomialPhi K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 2 := by
  have hs : (orbitPolynomialS K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 1 :=
    MvPolynomial.isHomogeneous_X K 0
  have hlambda : (orbitPolynomialLambda K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 1 :=
    MvPolynomial.isHomogeneous_X K 1
  simpa [orbitPolynomialPhi] using (hs.pow 2).sub (hlambda.pow 2)

omit [CharZero K] in
theorem orbitPolynomialPsi_isHomogeneous :
    (orbitPolynomialPsi K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 3 := by
  have hs : (orbitPolynomialS K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 1 :=
    MvPolynomial.isHomogeneous_X K 0
  have hlambda : (orbitPolynomialLambda K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 1 :=
    MvPolynomial.isHomogeneous_X K 1
  simpa [orbitPolynomialPsi, mul_assoc] using
    (hs.pow 3).C_mul (2 : K) |>.sub
      ((hs.mul (hlambda.pow 2)).C_mul (3 : K))

omit [CharZero K] in
/-- Substitution of the orbit forms preserves the weighted degree. -/
theorem orbitBaseToSource_isHomogeneous
    {S : OrbitBaseRing K} {M : ℕ}
    (hS : S.IsWeightedHomogeneous orbitBaseWeight M) :
    (orbitBaseToSource K S).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) M := by
  induction hS using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      rw [map_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero K (1 : Fin 2 → ℕ) M
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact ihp.add ihq
  | monomial d c hd =>
      have hcoordinate (i : OrbitBaseCoordinate) :
          (match i with
            | .phi => orbitPolynomialPhi K
            | .psi => orbitPolynomialPsi K).IsWeightedHomogeneous
              (1 : Fin 2 → ℕ)
              (orbitBaseWeight i) := by
        cases i
        · exact orbitPolynomialPhi_isHomogeneous
        · exact orbitPolynomialPsi_isHomogeneous
      have hprod := MvPolynomial.IsWeightedHomogeneous.prod d.support
        (fun i ↦ (match i with
          | .phi => orbitPolynomialPhi K
          | .psi => orbitPolynomialPsi K) ^ d i)
        (fun i ↦ d i • orbitBaseWeight i)
        (fun i _ ↦ (hcoordinate i).pow (d i))
      have hdegree :
          ∑ i ∈ d.support, d i • orbitBaseWeight i = M := by
        simpa [Finsupp.weight_apply, Finsupp.sum, mul_comm] using hd
      rw [hdegree] at hprod
      have himage :
          orbitBaseToSource K (MvPolynomial.monomial d c) =
            MvPolynomial.C c * ∏ i ∈ d.support,
              (match i with
                | .phi => orbitPolynomialPhi K
                | .psi => orbitPolynomialPsi K) ^ d i := by
        rw [MvPolynomial.monomial_eq, map_mul]
        congr 1
        · exact (orbitBaseToSource K).commutes c
        · classical
          simp only [Finsupp.prod, map_prod, map_pow]
          apply Finset.prod_congr rfl
          intro i hi
          cases i with
          | phi =>
              rw [show MvPolynomial.X OrbitBaseCoordinate.phi =
                    orbitBasePhi K by rfl,
                orbitBaseToSource_phi]
          | psi =>
              rw [show MvPolynomial.X OrbitBaseCoordinate.psi =
                    orbitBasePsi K by rfl,
                orbitBaseToSource_psi]
      rw [himage]
      exact hprod.C_mul c

omit [CharZero K] in
/-- Each of the six source terms has its displayed degree. -/
theorem orbitSixTerm_isHomogeneous (i : Fin 6) :
    (orbitSixTerm K i).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) (orbitSixTermDegree i) := by
  have hs : (orbitPolynomialS K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 1 :=
    MvPolynomial.isHomogeneous_X K 0
  have hlambda : (orbitPolynomialLambda K).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) 1 :=
    MvPolynomial.isHomogeneous_X K 1
  fin_cases i
  · simpa [orbitSixTerm, orbitSixTermDegree] using
      MvPolynomial.isWeightedHomogeneous_one K (1 : Fin 2 → ℕ)
  · simpa [orbitSixTerm, orbitSixTermDegree] using hs
  · simpa [orbitSixTerm, orbitSixTermDegree] using hs.pow 2
  · simpa [orbitSixTerm, orbitSixTermDegree] using hlambda
  · simpa [orbitSixTerm, orbitSixTermDegree] using hs.mul hlambda
  · simpa [orbitSixTerm, orbitSixTermDegree] using
      (hs.pow 2).mul hlambda

omit [CharZero K] in
theorem orbitSixTermSummand_isHomogeneous
    {S : OrbitBaseRing K} {M : ℕ} (i : Fin 6)
    (hS : S.IsWeightedHomogeneous orbitBaseWeight M) :
    (orbitBaseToSource K S * orbitSixTerm K i).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ)
      (M + orbitSixTermDegree i) :=
  (orbitBaseToSource_isHomogeneous hS).mul
    (orbitSixTerm_isHomogeneous i)

omit [CharZero K] in
theorem orbitHomogeneousComponent_summand_of_le
    (S : OrbitBaseRing K) (i : Fin 6) (N : ℕ)
    (hle : orbitSixTermDegree i ≤ N) :
    MvPolynomial.weightedHomogeneousComponent (1 : Fin 2 → ℕ) N
        (orbitBaseToSource K S * orbitSixTerm K i) =
      orbitBaseToSource K
          (MvPolynomial.weightedHomogeneousComponent orbitBaseWeight
            (N - orbitSixTermDegree i) S) *
        orbitSixTerm K i := by
  induction S using MvPolynomial.induction_on' with
  | add p q ihp ihq =>
      rw [map_add, add_mul, map_add, ihp, ihq]
      simp only [map_add, add_mul]
  | monomial d c =>
      let M := Finsupp.weight orbitBaseWeight d
      have hmonomial :
          (MvPolynomial.monomial d c : OrbitBaseRing K).IsWeightedHomogeneous
            orbitBaseWeight M :=
        MvPolynomial.isWeightedHomogeneous_monomial orbitBaseWeight d c rfl
      have hsummand := orbitSixTermSummand_isHomogeneous
        (K := K) i hmonomial
      by_cases hdegree : M + orbitSixTermDegree i = N
      · subst N
        rw [hsummand.weightedHomogeneousComponent_same,
          Nat.add_sub_cancel, hmonomial.weightedHomogeneousComponent_same]
      · rw [hsummand.weightedHomogeneousComponent_ne N
          (Ne.symm hdegree)]
        have hsub : N - orbitSixTermDegree i ≠ M := by omega
        rw [hmonomial.weightedHomogeneousComponent_ne _ hsub]
        simp

omit [CharZero K] in
theorem orbitHomogeneousComponent_summand_of_lt
    (S : OrbitBaseRing K) (i : Fin 6) (N : ℕ)
    (hlt : N < orbitSixTermDegree i) :
    MvPolynomial.weightedHomogeneousComponent (1 : Fin 2 → ℕ) N
        (orbitBaseToSource K S * orbitSixTerm K i) = 0 := by
  induction S using MvPolynomial.induction_on' with
  | add p q ihp ihq =>
      rw [map_add, add_mul, map_add, ihp, ihq, add_zero]
  | monomial d c =>
      let M := Finsupp.weight orbitBaseWeight d
      have hmonomial :
          (MvPolynomial.monomial d c : OrbitBaseRing K).IsWeightedHomogeneous
            orbitBaseWeight M :=
        MvPolynomial.isWeightedHomogeneous_monomial orbitBaseWeight d c rfl
      have hsummand := orbitSixTermSummand_isHomogeneous
        (K := K) i hmonomial
      apply hsummand.weightedHomogeneousComponent_ne
      omega

/-- The coefficient of one source term in the projection onto degree `N`. -/
noncomputable def orbitSixTermHomogeneousCoefficient
    (N : ℕ) (c : Fin 6 → OrbitBaseRing K) (i : Fin 6) :
    OrbitBaseRing K :=
  if orbitSixTermDegree i ≤ N then
    MvPolynomial.weightedHomogeneousComponent orbitBaseWeight
      (N - orbitSixTermDegree i) (c i)
  else 0

omit [CharZero K] in
theorem orbitSixTermHomogeneousCoefficient_isWeightedHomogeneous
    (N : ℕ) (c : Fin 6 → OrbitBaseRing K) (i : Fin 6) :
    (orbitSixTermHomogeneousCoefficient N c i).IsWeightedHomogeneous
      orbitBaseWeight (N - orbitSixTermDegree i) := by
  by_cases hle : orbitSixTermDegree i ≤ N
  · rw [orbitSixTermHomogeneousCoefficient, if_pos hle]
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · rw [orbitSixTermHomogeneousCoefficient, if_neg hle]
    exact MvPolynomial.isWeightedHomogeneous_zero K _ _

omit [CharZero K] in
theorem orbitSixTermHomogeneousCoefficient_eq_zero_of_lt
    (N : ℕ) (c : Fin 6 → OrbitBaseRing K) (i : Fin 6)
    (hlt : N < orbitSixTermDegree i) :
    orbitSixTermHomogeneousCoefficient N c i = 0 := by
  rw [orbitSixTermHomogeneousCoefficient, if_neg (Nat.not_le.mpr hlt)]

omit [CharZero K] in
theorem orbitHomogeneousComponent_orbitSixTermValue
    (N : ℕ) (c : Fin 6 → OrbitBaseRing K) :
    MvPolynomial.weightedHomogeneousComponent (1 : Fin 2 → ℕ) N
        (orbitSixTermValue K c) =
      orbitSixTermValue K (orbitSixTermHomogeneousCoefficient N c) := by
  rw [orbitSixTermValue, orbitSixTermValue, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hle : orbitSixTermDegree i ≤ N
  · rw [orbitSixTermHomogeneousCoefficient, if_pos hle]
    exact orbitHomogeneousComponent_summand_of_le
      (K := K) (c i) i N hle
  · rw [orbitSixTermHomogeneousCoefficient, if_neg hle,
      map_zero, zero_mul]
    exact orbitHomogeneousComponent_summand_of_lt
      (K := K) (c i) i N (Nat.lt_of_not_ge hle)

omit [CharZero K] in
/-- Every homogeneous source form has a six term expression whose base
coefficients have the complementary weighted degrees. -/
theorem exists_homogeneous_orbitSixTermValue
    (R : OrbitPolynomial K) (N : ℕ)
    (hR : R.IsWeightedHomogeneous (1 : Fin 2 → ℕ) N) :
    ∃ c : Fin 6 → OrbitBaseRing K,
      R = orbitSixTermValue K c ∧
      (∀ i, (c i).IsWeightedHomogeneous orbitBaseWeight
        (N - orbitSixTermDegree i)) ∧
      ∀ i, N < orbitSixTermDegree i → c i = 0 := by
  obtain ⟨c, hc⟩ := exists_orbitSixTermValue K R
  refine ⟨orbitSixTermHomogeneousCoefficient N c, ?_, ?_, ?_⟩
  · rw [← orbitHomogeneousComponent_orbitSixTermValue]
    rw [← hc, hR.weightedHomogeneousComponent_same]
  · exact orbitSixTermHomogeneousCoefficient_isWeightedHomogeneous N c
  · exact orbitSixTermHomogeneousCoefficient_eq_zero_of_lt N c

end OnLeConjecture.DTwo
