/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# A six term spanning system for the quadratic orbit pair

The polynomial ring `K[s,lambda]` is generated over `K[Phi,Psi]` by

`1, s, s^2, lambda, s lambda, s^2 lambda`.

The proof records the reduction formulas for multiplication by the two source
coordinates. Only spanning is asserted in this module.
-/

public section

namespace OnLeConjecture.DTwo

variable (K : Type*) [Field K] [CharZero K]

/-- The two abstract coordinates of the orbit base. -/
inductive OrbitBaseCoordinate where
  | phi
  | psi
  deriving DecidableEq

/-- The abstract coordinate ring `K[Phi,Psi]`. -/
abbrev OrbitBaseRing := MvPolynomial OrbitBaseCoordinate K

/-- The source polynomial ring `K[s,lambda]`. -/
abbrev OrbitPolynomial := MvPolynomial (Fin 2) K

/-- The abstract quadratic coordinate. -/
@[expose]
noncomputable def orbitBasePhi : OrbitBaseRing K :=
  MvPolynomial.X OrbitBaseCoordinate.phi

/-- The abstract cubic coordinate. -/
@[expose]
noncomputable def orbitBasePsi : OrbitBaseRing K :=
  MvPolynomial.X OrbitBaseCoordinate.psi

/-- The first source coordinate. -/
@[expose]
noncomputable def orbitPolynomialS : OrbitPolynomial K :=
  MvPolynomial.X 0

/-- The second source coordinate. -/
@[expose]
noncomputable def orbitPolynomialLambda : OrbitPolynomial K :=
  MvPolynomial.X 1

/-- The quadratic orbit form in the source polynomial ring. -/
@[expose]
noncomputable def orbitPolynomialPhi : OrbitPolynomial K :=
  orbitPolynomialS K ^ 2 - orbitPolynomialLambda K ^ 2

/-- The cubic orbit form in the source polynomial ring. -/
@[expose]
noncomputable def orbitPolynomialPsi : OrbitPolynomial K :=
  MvPolynomial.C (2 : K) * orbitPolynomialS K ^ 3 -
    MvPolynomial.C (3 : K) * orbitPolynomialS K *
      orbitPolynomialLambda K ^ 2

/-- Substitution of the orbit pair into a polynomial in `K[Phi,Psi]`. -/
@[expose]
noncomputable def orbitBaseToSource :
    OrbitBaseRing K →ₐ[K] OrbitPolynomial K :=
  MvPolynomial.aeval fun
    | OrbitBaseCoordinate.phi => orbitPolynomialPhi K
    | OrbitBaseCoordinate.psi => orbitPolynomialPsi K

omit [CharZero K] in
@[simp]
theorem orbitBaseToSource_phi :
    orbitBaseToSource K (orbitBasePhi K) = orbitPolynomialPhi K := by
  rw [orbitBaseToSource, orbitBasePhi, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem orbitBaseToSource_psi :
    orbitBaseToSource K (orbitBasePsi K) = orbitPolynomialPsi K := by
  rw [orbitBaseToSource, orbitBasePsi, MvPolynomial.aeval_X]

omit [CharZero K] in
/-- The source relations used by the six term reduction. -/
theorem orbitPolynomialLambda_sq :
    orbitPolynomialLambda K ^ 2 =
      orbitPolynomialS K ^ 2 -
        orbitBaseToSource K (orbitBasePhi K) := by
  rw [orbitBaseToSource_phi, orbitPolynomialPhi]
  ring

omit [CharZero K] in
/-- The cubic source relation used by the six term reduction. -/
theorem orbitPolynomialS_cube :
    orbitPolynomialS K ^ 3 =
      MvPolynomial.C (3 : K) *
          orbitBaseToSource K (orbitBasePhi K) * orbitPolynomialS K -
        orbitBaseToSource K (orbitBasePsi K) := by
  have hC2 : MvPolynomial.C (2 : K) =
      (2 : OrbitPolynomial K) := map_natCast _ 2
  have hC3 : MvPolynomial.C (3 : K) =
      (3 : OrbitPolynomial K) := map_natCast _ 3
  rw [orbitBaseToSource_phi, orbitBaseToSource_psi,
    orbitPolynomialPhi, orbitPolynomialPsi]
  rw [hC2, hC3]
  ring

/-- The six source terms `1,s,s^2,lambda,s lambda,s^2 lambda`. -/
@[expose]
noncomputable def orbitSixTerm (i : Fin 6) : OrbitPolynomial K :=
  ![1, orbitPolynomialS K, orbitPolynomialS K ^ 2,
    orbitPolynomialLambda K,
    orbitPolynomialS K * orbitPolynomialLambda K,
    orbitPolynomialS K ^ 2 * orbitPolynomialLambda K] i

/-- A source polynomial written with the six terms and coefficients in the
orbit base ring. -/
@[expose]
noncomputable def orbitSixTermValue
    (c : Fin 6 → OrbitBaseRing K) : OrbitPolynomial K :=
  ∑ i : Fin 6, orbitBaseToSource K (c i) * orbitSixTerm K i

/-- Coefficients after multiplying a six term expression by `s`. -/
noncomputable def orbitSixTermMultiplyS
    (c : Fin 6 → OrbitBaseRing K) : Fin 6 → OrbitBaseRing K :=
  ![-orbitBasePsi K * c 2,
    c 0 + MvPolynomial.C (3 : K) * orbitBasePhi K * c 2,
    c 1,
    -orbitBasePsi K * c 5,
    c 3 + MvPolynomial.C (3 : K) * orbitBasePhi K * c 5,
    c 4]

/-- Coefficients after multiplying a six term expression by `lambda`. -/
noncomputable def orbitSixTermMultiplyLambda
    (c : Fin 6 → OrbitBaseRing K) : Fin 6 → OrbitBaseRing K :=
  ![-orbitBasePhi K * c 3 - orbitBasePsi K * c 4,
    MvPolynomial.C (2 : K) * orbitBasePhi K * c 4 -
      orbitBasePsi K * c 5,
    c 3 + MvPolynomial.C (2 : K) * orbitBasePhi K * c 5,
    c 0,
    c 1,
    c 2]

omit [CharZero K] in
theorem orbitSixTermValue_multiplyS
    (c : Fin 6 → OrbitBaseRing K) :
    orbitSixTermValue K (orbitSixTermMultiplyS K c) =
      orbitSixTermValue K c * orbitPolynomialS K := by
  have hC2 : MvPolynomial.C (2 : K) =
      (2 : OrbitPolynomial K) := map_natCast _ 2
  have hC3 : MvPolynomial.C (3 : K) =
      (3 : OrbitPolynomial K) := map_natCast _ 3
  simp only [orbitSixTermValue, orbitSixTermMultiplyS, Fin.isValue,
    orbitSixTerm, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_six,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_neg, map_mul, map_add, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, orbitBaseToSource_phi,
    orbitBaseToSource_psi, mul_one]
  simp only [orbitPolynomialPhi, orbitPolynomialPsi]
  rw [hC2, hC3]
  ring

omit [CharZero K] in
theorem orbitSixTermValue_multiplyLambda
    (c : Fin 6 → OrbitBaseRing K) :
    orbitSixTermValue K (orbitSixTermMultiplyLambda K c) =
      orbitSixTermValue K c * orbitPolynomialLambda K := by
  have hC2 : MvPolynomial.C (2 : K) =
      (2 : OrbitPolynomial K) := map_natCast _ 2
  have hC3 : MvPolynomial.C (3 : K) =
      (3 : OrbitPolynomial K) := map_natCast _ 3
  simp only [orbitSixTermValue, orbitSixTermMultiplyLambda, Fin.isValue,
    orbitSixTerm, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_six,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_neg, map_sub, map_mul, map_add, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, orbitBaseToSource_phi,
    orbitBaseToSource_psi, mul_one]
  simp only [orbitPolynomialPhi, orbitPolynomialPsi]
  rw [hC2, hC3]
  ring

omit [CharZero K] in
/-- Every polynomial in `K[s,lambda]` has a six term expression over
`K[Phi,Psi]`. -/
theorem exists_orbitSixTermValue
    (R : OrbitPolynomial K) :
    ∃ c : Fin 6 → OrbitBaseRing K, R = orbitSixTermValue K c := by
  induction R using MvPolynomial.induction_on with
  | C r =>
      let c : Fin 6 → OrbitBaseRing K :=
        ![MvPolynomial.C r, 0, 0, 0, 0, 0]
      refine ⟨c, ?_⟩
      simp [orbitSixTermValue, orbitSixTerm, c, Fin.sum_univ_six]
  | add p q hp hq =>
      obtain ⟨c, hc⟩ := hp
      obtain ⟨d, hd⟩ := hq
      refine ⟨fun i ↦ c i + d i, ?_⟩
      rw [hc, hd, orbitSixTermValue, orbitSixTermValue]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_add, add_mul]
  | mul_X p i hp =>
      obtain ⟨c, hc⟩ := hp
      fin_cases i
      · refine ⟨orbitSixTermMultiplyS K c, ?_⟩
        rw [hc, orbitSixTermValue_multiplyS]
        rfl
      · refine ⟨orbitSixTermMultiplyLambda K c, ?_⟩
        rw [hc, orbitSixTermValue_multiplyLambda]
        rfl

end OnLeConjecture.DTwo
