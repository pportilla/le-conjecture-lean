/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EThetaBridge
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Tactic.FinCases

/-!
# Vanishing of the residual difference polynomial

This file proves that the three nonconstant coefficients in the canonical
quartic basis vanish when their residual difference polynomial vanishes.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable (K : Type*) [Field K] [CharZero K]

/-- The identification of the two base coordinates with `Fin 2` in which
`q` is the first coordinate. -/
def eBaseCoordinateEquivFin : EBaseCoordinate ≃ Fin 2 where
  toFun
    | EBaseCoordinate.p => 1
    | EBaseCoordinate.q => 0
  invFun i := if i = 0 then EBaseCoordinate.q else EBaseCoordinate.p
  left_inv i := by
    cases i
    all_goals simp
  right_inv i := by
    fin_cases i
    all_goals simp

/-- A polynomial in `P,Q`, regarded as a polynomial in `Q` whose
coefficients are polynomials in `P`. -/
noncomputable def eBaseAsQPolynomial :
    EBaseRing K ≃ₐ[K] Polynomial (Polynomial K) :=
  (MvPolynomial.renameEquiv K eBaseCoordinateEquivFin).trans
    ((MvPolynomial.finSuccEquiv K 1).trans
      (Polynomial.mapAlgEquiv
        (MvPolynomial.uniqueAlgEquiv K (Fin 1))))

omit [CharZero K] in
@[simp]
theorem eBaseAsQPolynomial_p :
    eBaseAsQPolynomial K (eBaseP K) = C X := by
  rw [eBaseAsQPolynomial]
  simp only [AlgEquiv.trans_apply, eBaseP,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change Polynomial.map
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1)) = C X
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  congr 1
  simp [MvPolynomial.uniqueAlgEquiv]

omit [CharZero K] in
@[simp]
theorem eBaseAsQPolynomial_q :
    eBaseAsQPolynomial K (eBaseQ K) = X := by
  rw [eBaseAsQPolynomial]
  simp only [AlgEquiv.trans_apply, eBaseQ,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change Polynomial.map
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0)) = X
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

/-- Constant coefficient as an algebra homomorphism over the ground field. -/
noncomputable def ePolynomialConstantCoeff :
    Polynomial (Polynomial K) →ₐ[K] Polynomial K where
  toFun := Polynomial.constantCoeff
  map_one' := by simp
  map_mul' a b := by simp
  map_zero' := by simp
  map_add' a b := by simp
  commutes' a := by simp

/-- Constant coefficient in `Q`, expressed as a polynomial in `P`. -/
noncomputable def eBaseQConstant : EBaseRing K →ₐ[K] Polynomial K where
  toFun := (ePolynomialConstantCoeff K).comp
    (eBaseAsQPolynomial K).toAlgHom
  map_one' := by simp
  map_mul' a b := by simp
  map_zero' := by simp
  map_add' a b := by simp
  commutes' a := by simp

omit [CharZero K] in
@[simp]
theorem eBaseQConstant_p :
    eBaseQConstant K (eBaseP K) = X := by
  rw [eBaseQConstant]
  change (eBaseAsQPolynomial K (eBaseP K)).coeff 0 = X
  rw [eBaseAsQPolynomial_p]
  simp

omit [CharZero K] in
@[simp]
theorem eBaseQConstant_q :
    eBaseQConstant K (eBaseQ K) = 0 := by
  rw [eBaseQConstant]
  change (eBaseAsQPolynomial K (eBaseQ K)).coeff 0 = 0
  rw [eBaseAsQPolynomial_q]
  simp

/-- Substitution `P = X^3/4` in a polynomial in `P`. -/
noncomputable def ePAtFirstZero : Polynomial K →ₐ[K] Polynomial K :=
  Polynomial.aeval (C ((4 : K)⁻¹) * X ^ 3)

omit [CharZero K] in
@[simp]
theorem ePAtFirstZero_X :
    ePAtFirstZero K X = C ((4 : K)⁻¹) * X ^ 3 := by
  simp [ePAtFirstZero]

/-- Setting the first residual source coordinate equal to zero. -/
noncomputable def ePairFirstZeroEval :
    EPairRing K →ₐ[K] Polynomial K :=
  Polynomial.mapAlgHom (Polynomial.aeval (0 : K))

omit [CharZero K] in
@[simp]
theorem ePairFirstZeroEval_first :
    ePairFirstZeroEval K (ePairFirst K) = 0 := by
  simp [ePairFirstZeroEval, ePairFirst]

omit [CharZero K] in
@[simp]
theorem ePairFirstZeroEval_second :
    ePairFirstZeroEval K (ePairSecond K) = X := by
  simp [ePairFirstZeroEval, ePairSecond]

/-- The base specialization induced by setting the first residual source
coordinate equal to zero. -/
noncomputable def eBaseFirstZeroEval :
    EBaseRing K →ₐ[K] Polynomial K :=
  (ePAtFirstZero K).comp (eBaseQConstant K)

omit [CharZero K] in
@[simp]
theorem eBaseFirstZeroEval_p :
    eBaseFirstZeroEval K (eBaseP K) = C ((4 : K)⁻¹) * X ^ 3 := by
  simp [eBaseFirstZeroEval]

omit [CharZero K] in
@[simp]
theorem eBaseFirstZeroEval_q :
    eBaseFirstZeroEval K (eBaseQ K) = 0 := by
  simp [eBaseFirstZeroEval]

theorem ePairFirstZeroEval_comp_residualBaseToPair :
    (ePairFirstZeroEval K).comp (eResidualBaseToPair K) =
      eBaseFirstZeroEval K := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
      change ePairFirstZeroEval K
          (eResidualBaseToPair K (eBaseP K)) =
        eBaseFirstZeroEval K (eBaseP K)
      rw [eResidualBaseToPair_p, eBaseFirstZeroEval_p]
      simp only [eResidualPairP, map_mul, map_add, map_pow,
        ePairFirstZeroEval_first, ePairFirstZeroEval_second,
        algebraMap_apply, algebraMap_eq, OfNat.ofNat]
      simp [ePairFirstZeroEval]
      ring
  | q =>
      change ePairFirstZeroEval K
          (eResidualBaseToPair K (eBaseQ K)) =
        eBaseFirstZeroEval K (eBaseQ K)
      rw [eResidualBaseToPair_q, eBaseFirstZeroEval_q]
      simp [eResidualPairQ]

theorem ePairFirstZeroEval_residualBaseToPair (c : EBaseRing K) :
    ePairFirstZeroEval K (eResidualBaseToPair K c) =
      eBaseFirstZeroEval K c := by
  exact AlgHom.congr_fun
    (ePairFirstZeroEval_comp_residualBaseToPair K) c

theorem ePairFirstZeroEval_thetaPolynomial
    (c : Fin 4 → EBaseRing K) :
    ePairFirstZeroEval K (eThetaPolynomial K c) =
      eBaseFirstZeroEval K (c 1) +
        eBaseFirstZeroEval K (c 2) * X +
        eBaseFirstZeroEval K (c 3) * X ^ 2 := by
  have hfactor := congrArg (ePairFirstZeroEval K)
    (e_residual_basis_difference_factorization K c)
  simp only [map_sub, map_mul, eResidualBasisValue,
    ePairFirstZeroEval_residualBaseToPair,
    ePairFirstZeroEval_first, ePairFirstZeroEval_second,
    map_add, map_pow, OfNat.ofNat] at hfactor
  norm_num at hfactor
  rw [show (3 : Fin 4) = Fin.last 3 by decide]
  apply mul_left_cancel₀ (show (X : Polynomial K) ≠ 0 from X_ne_zero)
  linear_combination hfactor

/-- The polynomial used to specialize `P` has degree three. -/
theorem ePAtFirstZero_value_natDegree :
    (C ((4 : K)⁻¹) * X ^ 3 : Polynomial K).natDegree = 3 := by
  apply Polynomial.natDegree_C_mul_X_pow
  exact inv_ne_zero (by norm_num)

/-- Specialization at a zero first residual coordinate multiplies the
degree in `P` by three. -/
theorem eBaseFirstZeroEval_natDegree (c : EBaseRing K) :
    (eBaseFirstZeroEval K c).natDegree =
      (eBaseQConstant K c).natDegree * 3 := by
  change ((eBaseQConstant K c).comp
      (C ((4 : K)⁻¹) * X ^ 3)).natDegree = _
  rw [Polynomial.natDegree_comp, ePAtFirstZero_value_natDegree]

/-- Three polynomials whose degrees belong respectively to the residue
classes zero, one, and two modulo three cannot cancel. -/
theorem eBaseFirstZeroEval_sum_eq_zero
    (a b c : EBaseRing K)
    (hzero :
      eBaseFirstZeroEval K a + eBaseFirstZeroEval K b * X +
        eBaseFirstZeroEval K c * X ^ 2 = 0) :
    eBaseFirstZeroEval K a = 0 ∧
      eBaseFirstZeroEval K b = 0 ∧
      eBaseFirstZeroEval K c = 0 := by
  classical
  let f : Fin 3 → Polynomial K := ![
    eBaseFirstZeroEval K a,
    eBaseFirstZeroEval K b * X,
    eBaseFirstZeroEval K c * X ^ 2]
  have hsum : ∑ i : Fin 3, f i = 0 := by
    rw [Fin.sum_univ_three]
    exact hzero
  have hresidue (i : Fin 3) (hi : f i ≠ 0) :
      (f i).natDegree % 3 = i := by
    fin_cases i
    · change (eBaseFirstZeroEval K a).natDegree % 3 = 0
      rw [eBaseFirstZeroEval_natDegree]
      omega
    · change
        (eBaseFirstZeroEval K b * X).natDegree % 3 = 1
      change eBaseFirstZeroEval K b * X ≠ 0 at hi
      have hb : eBaseFirstZeroEval K b ≠ 0 := by
        intro hb
        exact hi (by rw [hb, zero_mul])
      rw [Polynomial.natDegree_mul hb X_ne_zero,
        Polynomial.natDegree_X, eBaseFirstZeroEval_natDegree]
      omega
    · change
        (eBaseFirstZeroEval K c * X ^ 2).natDegree % 3 = 2
      change eBaseFirstZeroEval K c * X ^ 2 ≠ 0 at hi
      have hc : eBaseFirstZeroEval K c ≠ 0 := by
        intro hc
        exact hi (by rw [hc, zero_mul])
      rw [Polynomial.natDegree_mul hc (pow_ne_zero 2 X_ne_zero),
        Polynomial.natDegree_X_pow, eBaseFirstZeroEval_natDegree]
      omega
  have hpairwiseNatDegree :
      Set.Pairwise {i | i ∈ Finset.univ ∧ f i ≠ 0}
        (Function.onFun Ne (Polynomial.natDegree ∘ f)) := by
    intro i hi j hj hij
    change i ∈ Finset.univ ∧ f i ≠ 0 at hi
    change j ∈ Finset.univ ∧ f j ≠ 0 at hj
    intro hdegree
    have hiResidue := hresidue i hi.2
    have hjResidue := hresidue j hj.2
    simp only [Function.comp_apply] at hdegree
    rw [hdegree] at hiResidue
    have hval : i.val = j.val := by omega
    exact hij (Fin.ext hval)
  have hpairwiseDegree :
      Set.Pairwise {i | i ∈ Finset.univ ∧ f i ≠ 0}
        (Function.onFun Ne (Polynomial.degree ∘ f)) := by
    intro i hi j hj hij
    change i ∈ Finset.univ ∧ f i ≠ 0 at hi
    change j ∈ Finset.univ ∧ f j ≠ 0 at hj
    change Polynomial.degree (f i) ≠ Polynomial.degree (f j)
    rw [Polynomial.degree_eq_natDegree hi.2,
      Polynomial.degree_eq_natDegree hj.2]
    exact_mod_cast hpairwiseNatDegree hi hj hij
  have hdegree := Polynomial.degree_sum_eq_of_disjoint
    f Finset.univ hpairwiseDegree
  rw [hsum, Polynomial.degree_zero] at hdegree
  have hfzero (i : Fin 3) : f i = 0 := by
    by_contra hi
    have hle : Polynomial.degree (f i) ≤
        Finset.univ.sup fun j : Fin 3 => Polynomial.degree (f j) :=
      Finset.le_sup (f := fun j : Fin 3 => Polynomial.degree (f j))
        (Finset.mem_univ i)
    rw [← hdegree] at hle
    have hbot : Polynomial.degree (f i) = ⊥ := le_bot_iff.mp hle
    exact hi (Polynomial.degree_eq_bot.mp hbot)
  have ha := hfzero 0
  have hb := hfzero 1
  have hc := hfzero 2
  simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at ha hb hc
  exact ⟨ha,
    (mul_eq_zero.mp hb).resolve_right X_ne_zero,
    (mul_eq_zero.mp hc).resolve_right (pow_ne_zero 2 X_ne_zero)⟩

/-- Substitution `P = X^3/4` is injective. -/
theorem ePAtFirstZero_injective :
    Function.Injective (ePAtFirstZero K) := by
  intro p q hpq
  apply sub_eq_zero.mp
  have hzero : ePAtFirstZero K (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  change (p - q).comp (C ((4 : K)⁻¹) * X ^ 3) = 0 at hzero
  rw [Polynomial.comp_eq_zero_iff] at hzero
  rcases hzero with hzero | hconstant
  · exact hzero
  · have hdegree := congrArg Polynomial.natDegree hconstant.2
    rw [ePAtFirstZero_value_natDegree] at hdegree
    simp at hdegree

/-- A base polynomial that vanishes after setting the first residual
coordinate to zero is divisible by `Q`. -/
theorem eBaseQ_dvd_of_firstZeroEval_eq_zero
    (c : EBaseRing K) (hzero : eBaseFirstZeroEval K c = 0) :
    eBaseQ K ∣ c := by
  have hconstant : eBaseQConstant K c = 0 := by
    apply ePAtFirstZero_injective K
    simpa [eBaseFirstZeroEval] using hzero
  change (eBaseAsQPolynomial K c).coeff 0 = 0 at hconstant
  obtain ⟨d, hd⟩ := Polynomial.X_dvd_iff.mpr hconstant
  refine ⟨(eBaseAsQPolynomial K).symm d, ?_⟩
  apply (eBaseAsQPolynomial K).injective
  rw [map_mul, eBaseAsQPolynomial_q,
    (eBaseAsQPolynomial K).apply_symm_apply]
  exact hd

/-- The residual value of `Q` is nonzero. -/
theorem eResidualBaseToPair_q_ne_zero :
    eResidualBaseToPair K (eBaseQ K) ≠ 0 := by
  rw [eResidualBaseToPair_q]
  intro hzero
  have heval := congrArg (ePairPointEval K 1 1) hzero
  rw [map_zero, ePairPointEval_residualPairQ] at heval
  norm_num at heval

omit [CharZero K] in
/-- The residual factor depends only on the coefficients of the powers
`x`, `x^2`, and `x^3`. -/
theorem eThetaPolynomial_congr
    {c d : Fin 4 → EBaseRing K}
    (h1 : c 1 = d 1) (h2 : c 2 = d 2) (h3 : c 3 = d 3) :
    eThetaPolynomial K c = eThetaPolynomial K d := by
  have hdiagonal : ePairFirst K - ePairSecond K ≠ 0 := by
    change (C X : EPairRing K) - X ≠ 0
    rw [show (C X : EPairRing K) - X = -(X - C X) by ring]
    exact neg_ne_zero.mpr (Polynomial.X_sub_C_ne_zero X)
  apply mul_left_cancel₀ hdiagonal
  calc
    (ePairFirst K - ePairSecond K) * eThetaPolynomial K c =
        eResidualBasisValue K c (ePairFirst K) -
          eResidualBasisValue K c (ePairSecond K) :=
      (e_residual_basis_difference_factorization K c).symm
    _ = eResidualBasisValue K d (ePairFirst K) -
          eResidualBasisValue K d (ePairSecond K) := by
      simp only [eResidualBasisValue]
      rw [h1, h2, h3]
      ring
    _ = (ePairFirst K - ePairSecond K) * eThetaPolynomial K d :=
      e_residual_basis_difference_factorization K d

omit [CharZero K] in
/-- Multiplying all canonical coefficients by `Q` multiplies the residual
factor by the residual value of `Q`. -/
theorem eThetaPolynomial_baseQ_mul (d : Fin 4 → EBaseRing K) :
    eThetaPolynomial K (fun i => eBaseQ K * d i) =
      eResidualBaseToPair K (eBaseQ K) * eThetaPolynomial K d := by
  have hdiagonal : ePairFirst K - ePairSecond K ≠ 0 := by
    change (C X : EPairRing K) - X ≠ 0
    rw [show (C X : EPairRing K) - X = -(X - C X) by ring]
    exact neg_ne_zero.mpr (Polynomial.X_sub_C_ne_zero X)
  apply mul_left_cancel₀ hdiagonal
  calc
    (ePairFirst K - ePairSecond K) *
        eThetaPolynomial K (fun i => eBaseQ K * d i) =
        eResidualBasisValue K (fun i => eBaseQ K * d i)
            (ePairFirst K) -
          eResidualBasisValue K (fun i => eBaseQ K * d i)
            (ePairSecond K) :=
      (e_residual_basis_difference_factorization K _).symm
    _ = eResidualBaseToPair K (eBaseQ K) *
        (eResidualBasisValue K d (ePairFirst K) -
          eResidualBasisValue K d (ePairSecond K)) := by
      simp only [eResidualBasisValue, map_mul]
      ring
    _ = eResidualBaseToPair K (eBaseQ K) *
        ((ePairFirst K - ePairSecond K) * eThetaPolynomial K d) := by
      rw [e_residual_basis_difference_factorization]
    _ = (ePairFirst K - ePairSecond K) *
        (eResidualBaseToPair K (eBaseQ K) *
          eThetaPolynomial K d) := by ring

/-- Degree with respect to the base coordinate `Q`. -/
noncomputable def eBaseQDegree (c : EBaseRing K) : ℕ :=
  (eBaseAsQPolynomial K c).natDegree

omit [CharZero K] in
theorem eBaseQDegree_baseQ_mul
    (d : EBaseRing K) (hd : d ≠ 0) :
    eBaseQDegree K (eBaseQ K * d) = eBaseQDegree K d + 1 := by
  have hmap : eBaseAsQPolynomial K d ≠ 0 := by
    intro hzero
    apply hd
    apply (eBaseAsQPolynomial K).injective
    simpa using hzero
  simp only [eBaseQDegree, map_mul, eBaseAsQPolynomial_q]
  rw [Polynomial.natDegree_mul X_ne_zero hmap,
    Polynomial.natDegree_X]
  omega

/-- Vanishing of the residual difference polynomial forces the three
nonconstant canonical basis coefficients to vanish. -/
theorem eThetaPolynomial_eq_zero_coefficients
    (c : Fin 4 → EBaseRing K) :
    eThetaPolynomial K c = 0 →
      c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 := by
  classical
  induction hn :
      eBaseQDegree K (c 1) + eBaseQDegree K (c 2) +
        eBaseQDegree K (c 3) using Nat.strong_induction_on generalizing c with
  | h n ih =>
      intro htheta
      by_cases hall : c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0
      · exact hall
      have hspecial :
          eBaseFirstZeroEval K (c 1) +
              eBaseFirstZeroEval K (c 2) * X +
              eBaseFirstZeroEval K (c 3) * X ^ 2 = 0 := by
        have heval := congrArg (ePairFirstZeroEval K) htheta
        rw [map_zero, ePairFirstZeroEval_thetaPolynomial] at heval
        exact heval
      obtain ⟨hc1zero, hc2zero, hc3zero⟩ :=
        eBaseFirstZeroEval_sum_eq_zero
          K (c 1) (c 2) (c 3) hspecial
      obtain ⟨d1, hd1⟩ :=
        eBaseQ_dvd_of_firstZeroEval_eq_zero K (c 1) hc1zero
      obtain ⟨d2, hd2⟩ :=
        eBaseQ_dvd_of_firstZeroEval_eq_zero K (c 2) hc2zero
      obtain ⟨d3, hd3⟩ :=
        eBaseQ_dvd_of_firstZeroEval_eq_zero K (c 3) hc3zero
      let d : Fin 4 → EBaseRing K := ![0, d1, d2, d3]
      have hc1 : c 1 = eBaseQ K * d 1 := by
        simpa [d] using hd1
      have hc2 : c 2 = eBaseQ K * d 2 := by
        simpa [d] using hd2
      have hc3 : c 3 = eBaseQ K * d 3 := by
        simpa [d] using hd3
      have hfactor :
          eThetaPolynomial K c =
            eResidualBaseToPair K (eBaseQ K) *
              eThetaPolynomial K d := by
        calc
          eThetaPolynomial K c =
              eThetaPolynomial K (fun i => eBaseQ K * d i) :=
            eThetaPolynomial_congr K hc1 hc2 hc3
          _ = eResidualBaseToPair K (eBaseQ K) *
              eThetaPolynomial K d := eThetaPolynomial_baseQ_mul K d
      have hdtheta : eThetaPolynomial K d = 0 := by
        have hproduct :
            eResidualBaseToPair K (eBaseQ K) *
                eThetaPolynomial K d = 0 := by
          rw [← hfactor, htheta]
        exact (mul_eq_zero.mp hproduct).resolve_left
          (eResidualBaseToPair_q_ne_zero K)
      have hdegree1 :
          eBaseQDegree K d1 ≤ eBaseQDegree K (c 1) := by
        by_cases hd : d1 = 0
        · simp [hd, eBaseQDegree]
        · rw [hd1, eBaseQDegree_baseQ_mul K d1 hd]
          omega
      have hdegree2 :
          eBaseQDegree K d2 ≤ eBaseQDegree K (c 2) := by
        by_cases hd : d2 = 0
        · simp [hd, eBaseQDegree]
        · rw [hd2, eBaseQDegree_baseQ_mul K d2 hd]
          omega
      have hdegree3 :
          eBaseQDegree K d3 ≤ eBaseQDegree K (c 3) := by
        by_cases hd : d3 = 0
        · simp [hd, eBaseQDegree]
        · rw [hd3, eBaseQDegree_baseQ_mul K d3 hd]
          omega
      have hdegree1lt (hc : c 1 ≠ 0) :
          eBaseQDegree K d1 < eBaseQDegree K (c 1) := by
        have hd : d1 ≠ 0 := by
          intro hd
          apply hc
          rw [hd1, hd, mul_zero]
        rw [hd1, eBaseQDegree_baseQ_mul K d1 hd]
        omega
      have hdegree2lt (hc : c 2 ≠ 0) :
          eBaseQDegree K d2 < eBaseQDegree K (c 2) := by
        have hd : d2 ≠ 0 := by
          intro hd
          apply hc
          rw [hd2, hd, mul_zero]
        rw [hd2, eBaseQDegree_baseQ_mul K d2 hd]
        omega
      have hdegree3lt (hc : c 3 ≠ 0) :
          eBaseQDegree K d3 < eBaseQDegree K (c 3) := by
        have hd : d3 ≠ 0 := by
          intro hd
          apply hc
          rw [hd3, hd, mul_zero]
        rw [hd3, eBaseQDegree_baseQ_mul K d3 hd]
        omega
      have hsome : c 1 ≠ 0 ∨ c 2 ≠ 0 ∨ c 3 ≠ 0 := by
        by_cases hc1 : c 1 = 0
        · right
          by_cases hc2 : c 2 = 0
          · right
            intro hc3
            exact hall ⟨hc1, hc2, hc3⟩
          · left
            exact hc2
        · left
          exact hc1
      have hmeasure :
          eBaseQDegree K (d 1) + eBaseQDegree K (d 2) +
              eBaseQDegree K (d 3) < n := by
        have hmeasure' :
            eBaseQDegree K d1 + eBaseQDegree K d2 +
                eBaseQDegree K d3 < n := by
          rw [← hn]
          rcases hsome with hsome | hsome | hsome
          · have := hdegree1lt hsome
            omega
          · have := hdegree2lt hsome
            omega
          · have := hdegree3lt hsome
            omega
        simpa [d] using hmeasure'
      have hdzeros := ih _ hmeasure d rfl hdtheta
      have hd1zero : d1 = 0 := by
        simpa [d] using hdzeros.1
      have hd2zero : d2 = 0 := by
        simpa [d] using hdzeros.2.1
      have hd3zero : d3 = 0 := by
        simpa [d] using hdzeros.2.2
      exact ⟨by rw [hd1, hd1zero, mul_zero],
        by rw [hd2, hd2zero, mul_zero],
        by rw [hd3, hd3zero, mul_zero]⟩

/-- A canonical basis decomposition with zero residual factor belongs to
the image of the base coordinate ring. -/
theorem eSource_mem_range_baseToSource_of_theta_eq_zero
    (R : ESourceRing K) (c : Fin 4 → EBaseRing K)
    (hdecomposition :
      R = ∑ i : Fin 4,
        eBaseToSource K (c i) * eSourceX K ^ (i : ℕ))
    (htheta : eThetaPolynomial K c = 0) :
    R ∈ Set.range (eBaseToSource K) := by
  obtain ⟨hc1, hc2, hc3⟩ :=
    eThetaPolynomial_eq_zero_coefficients K c htheta
  refine ⟨c 0, ?_⟩
  rw [hdecomposition, Fin.sum_univ_four, hc1, hc2, hc3]
  norm_num

end OnLeConjecture.DThree
