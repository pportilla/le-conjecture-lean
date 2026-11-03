/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HSixTermGraded
public import OnLeConjecture.DThree.HProjectiveDifferenceFiniteBoundary

/-!
# Invariant descent for the homogeneous H pair

For a weighted homogeneous form, vanishing of the residual conic difference
implies membership in `K[P,Q]`. The proof uses the six term expression over
the base ring. The two points at infinity of the residual conic force the
five nonconstant coefficients to be divisible by `P`. Removing this common
factor lowers the weighted degree by three, which gives a finite induction.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

@[expose]
noncomputable def hInfinityBoundaryX (z : K) : K :=
  hConicParamXNumerator.eval z

@[expose]
noncomputable def hInfinityBoundaryW (z : K) : K :=
  (-hConicParamOneFactor * hConicParamWFactor).eval z /
    (3 * (Polynomial.X + 1) : K[X]).eval z

@[expose]
noncomputable def hInfinityBoundaryCapitalW (z : K) : K :=
  (-hConicParamOneFactor * hConicParamCapitalWFactor).eval z /
    (3 * (Polynomial.X + 1) : K[X]).eval z

omit [CharZero K] in
theorem h_invariant_x_formula {z : K} (hz : z ^ 2 + 2 = 0) :
    hInfinityBoundaryX z = -4 * (z + 1) := by
  simp only [hInfinityBoundaryX, hConicParamXNumerator,
    Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  linear_combination -hz

theorem h_invariant_w_formula {z : K} (hz : z ^ 2 + 2 = 0) :
    hInfinityBoundaryW z =
      z / 6 * hInfinityBoundaryX z ^ 2 := by
  have hplus : z + 1 ≠ 0 :=
    h_conic_param_infinity_root_add_one_ne_zero hz
  rw [h_invariant_x_formula hz]
  simp only [hInfinityBoundaryW, hConicParamOneFactor,
    hConicParamWFactor, Polynomial.eval_neg,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  field_simp [hplus]
  linear_combination (-6 * z ^ 3 - 60 * z ^ 2 - 192 * z - 192) * hz

theorem h_invariant_W_formula {z : K} (hz : z ^ 2 + 2 = 0) :
    hInfinityBoundaryCapitalW z =
      -(hInfinityBoundaryX z ^ 2) / 3 := by
  have hplus : z + 1 ≠ 0 :=
    h_conic_param_infinity_root_add_one_ne_zero hz
  rw [h_invariant_x_formula hz]
  simp only [hInfinityBoundaryCapitalW, hConicParamOneFactor,
    hConicParamCapitalWFactor, Polynomial.eval_neg,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  field_simp [hplus]
  linear_combination (-z ^ 3 - 8 * z ^ 2 - 16 * z) * hz

theorem h_invariant_boundary_eq
    (F : MvPolynomial (Fin 2) K) (N : ℕ)
    (hF : F.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference F = 0)
    {z : K} (hz : z ^ 2 + 2 = 0) :
    hFormEval 0 (hInfinityBoundaryW z) F =
      hFormEval (hInfinityBoundaryX z)
        (hInfinityBoundaryCapitalW z) F := by
  let linear : K[X] := 3 * (Polynomial.X + 1)
  let firstNumerator : K[X] :=
    -hConicParamOneFactor * hConicParamWFactor
  let secondNumerator : K[X] :=
    -hConicParamOneFactor * hConicParamCapitalWFactor
  have hlinear : linear.eval z ≠ 0 := by
    simp only [linear, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact mul_ne_zero (by norm_num)
      (h_conic_param_infinity_root_add_one_ne_zero hz)
  have hidentity := h_scaled_infinity_conic_difference F N hF
  rw [hdifference, mul_zero] at hidentity
  have hzero := congrArg (RatFunc.eval (RingHom.id K) z) hidentity
  simp only [RatFunc.eval_zero] at hzero
  have hfirstRegular :
      HRatFuncRegularAt z
        (algebraMap K[X] (RatFunc K) firstNumerator /
          algebraMap K[X] (RatFunc K) linear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd firstNumerator linear) hlinear
  have hsecondRegular :
      HRatFuncRegularAt z
        (algebraMap K[X] (RatFunc K) secondNumerator /
          algebraMap K[X] (RatFunc K) linear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd secondNumerator linear) hlinear
  have hdenRegular := hRatFuncRegularAt_algebraMap
    (K := K) z hConicParamDenominator
  have hxRegular := hRatFuncRegularAt_algebraMap
    (K := K) z hConicParamXNumerator
  have hfirstFormRegular := hRatFuncRegularAt_hFormEval z
    (algebraMap K[X] (RatFunc K) hConicParamDenominator)
    (algebraMap K[X] (RatFunc K) firstNumerator /
      algebraMap K[X] (RatFunc K) linear) F
    hdenRegular hfirstRegular
  have hsecondFormRegular := hRatFuncRegularAt_hFormEval z
    (algebraMap K[X] (RatFunc K) hConicParamXNumerator)
    (algebraMap K[X] (RatFunc K) secondNumerator /
      algebraMap K[X] (RatFunc K) linear) F
    hxRegular hsecondRegular
  rw [h_ratFunc_eval_sub z _ _ hfirstFormRegular hsecondFormRegular,
    h_ratFunc_eval_hFormEval z _ _ F hdenRegular hfirstRegular,
    h_ratFunc_eval_hFormEval z _ _ F hxRegular hsecondRegular,
    h_ratFunc_eval_algebraMap_div z firstNumerator linear hlinear,
    h_ratFunc_eval_algebraMap_div z secondNumerator linear hlinear,
    h_ratFunc_eval_algebraMap_id] at hzero
  have heq := sub_eq_zero.mp hzero.symm
  simpa [linear, firstNumerator, secondNumerator,
    hInfinityBoundaryX, hInfinityBoundaryW,
    hInfinityBoundaryCapitalW, hConicParamDenominator, hz] using heq

@[expose]
def hBaseCoordinateEquivFin : HBaseCoordinate ≃ Fin 2 where
  toFun
    | HBaseCoordinate.p => 0
    | HBaseCoordinate.q => 1
  invFun i := if i = 0 then HBaseCoordinate.p else HBaseCoordinate.q
  left_inv i := by
    cases i
    all_goals simp
  right_inv i := by
    fin_cases i
    all_goals simp

@[expose]
noncomputable def hBaseAsPPolynomial (K : Type*) [Field K] :
    HBaseRing K ≃ₐ[K] Polynomial (Polynomial K) :=
  (MvPolynomial.renameEquiv K hBaseCoordinateEquivFin).trans
    ((MvPolynomial.finSuccEquiv K 1).trans
      (Polynomial.mapAlgEquiv
        (MvPolynomial.uniqueAlgEquiv K (Fin 1))))

@[simp]
theorem h_invariant_baseAsP_p (K : Type*) [Field K] :
    hBaseAsPPolynomial K (hBaseP K) = Polynomial.X := by
  rw [hBaseAsPPolynomial]
  simp only [AlgEquiv.trans_apply, hBaseP,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change Polynomial.map
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0)) = Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp]
theorem h_invariant_baseAsP_q (K : Type*) [Field K] :
    hBaseAsPPolynomial K (hBaseQ K) = Polynomial.C Polynomial.X := by
  rw [hBaseAsPPolynomial]
  simp only [AlgEquiv.trans_apply, hBaseQ,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change Polynomial.map
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1)) =
        Polynomial.C Polynomial.X
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  congr 1
  simp [MvPolynomial.uniqueAlgEquiv]

@[expose]
noncomputable def hPolynomialConstantCoeff (K : Type*) [Field K] :
    Polynomial (Polynomial K) →ₐ[K] Polynomial K where
  toFun := Polynomial.constantCoeff
  map_one' := by simp
  map_mul' a b := by simp
  map_zero' := by simp
  map_add' a b := by simp
  commutes' a := by simp

@[expose]
noncomputable def hBasePConstant (K : Type*) [Field K] :
    HBaseRing K →ₐ[K] Polynomial K :=
  (hPolynomialConstantCoeff K).comp (hBaseAsPPolynomial K).toAlgHom

@[simp]
theorem h_invariant_basePConstant_p (K : Type*) [Field K] :
    hBasePConstant K (hBaseP K) = 0 := by
  change (hBaseAsPPolynomial K (hBaseP K)).coeff 0 = 0
  rw [h_invariant_baseAsP_p]
  simp

@[simp]
theorem h_invariant_basePConstant_q (K : Type*) [Field K] :
    hBasePConstant K (hBaseQ K) = Polynomial.X := by
  change (hBaseAsPPolynomial K (hBaseQ K)).coeff 0 = Polynomial.X
  rw [h_invariant_baseAsP_q]
  simp

@[expose]
noncomputable def hQAtInfinity (z : K) : Polynomial K →ₐ[K] Polynomial K :=
  Polynomial.aeval
    (Polynomial.C (hQ 0 (hInfinityBoundaryW z)) * Polynomial.X ^ 4)

@[expose]
noncomputable def hBaseInfinityEval (z : K) :
    HBaseRing K →ₐ[K] Polynomial K :=
  (hQAtInfinity z).comp (hBasePConstant K)

omit [CharZero K] in
@[simp]
theorem h_invariant_baseInfinityEval_p (z : K) :
    hBaseInfinityEval z (hBaseP K) = 0 := by
  simp [hBaseInfinityEval]

omit [CharZero K] in
@[simp]
theorem h_invariant_baseInfinityEval_q (z : K) :
    hBaseInfinityEval z (hBaseQ K) =
      Polynomial.C (hQ 0 (hInfinityBoundaryW z)) * Polynomial.X ^ 4 := by
  simp [hBaseInfinityEval, hQAtInfinity]

theorem h_invariant_boundary_w_ne_zero {z : K} (hz : z ^ 2 + 2 = 0) :
    hInfinityBoundaryW z ≠ 0 := by
  rw [h_invariant_w_formula hz]
  exact mul_ne_zero
    (div_ne_zero (h_conic_param_infinity_root_ne_zero hz) (by norm_num))
    (pow_ne_zero 2 (by
      rw [h_invariant_x_formula hz]
      exact mul_ne_zero (by norm_num)
        (h_conic_param_infinity_root_add_one_ne_zero hz)))

theorem h_invariant_boundary_q_ne_zero {z : K} (hz : z ^ 2 + 2 = 0) :
    hQ 0 (hInfinityBoundaryW z) ≠ 0 := by
  have hne : (2 : K) * hInfinityBoundaryW z ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (h_invariant_boundary_w_ne_zero hz))
  simpa [hQ] using hne

theorem h_invariant_Qvalue_degree {z : K} (hz : z ^ 2 + 2 = 0) :
    (Polynomial.C (hQ 0 (hInfinityBoundaryW z)) * Polynomial.X ^ 4).natDegree = 4 := by
  apply Polynomial.natDegree_C_mul_X_pow
  exact h_invariant_boundary_q_ne_zero hz

theorem h_invariant_QAtInfinity_injective {z : K} (hz : z ^ 2 + 2 = 0) :
    Function.Injective (hQAtInfinity z) := by
  intro p q hpq
  apply sub_eq_zero.mp
  have hzero : hQAtInfinity z (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  change (p - q).comp
      (Polynomial.C (hQ 0 (hInfinityBoundaryW z)) * Polynomial.X ^ 4) = 0 at hzero
  rw [Polynomial.comp_eq_zero_iff] at hzero
  rcases hzero with hzero | hconstant
  · exact hzero
  · have hdegree := congrArg Polynomial.natDegree hconstant.2
    rw [h_invariant_Qvalue_degree hz] at hdegree
    simp at hdegree

theorem h_invariant_baseP_dvd_of_infinityEval_eq_zero
    {z : K} (hz : z ^ 2 + 2 = 0)
    (c : HBaseRing K) (hzero : hBaseInfinityEval z c = 0) :
    hBaseP K ∣ c := by
  have hconstant : hBasePConstant K c = 0 := by
    apply h_invariant_QAtInfinity_injective hz
    simpa [hBaseInfinityEval] using hzero
  change (hBaseAsPPolynomial K c).coeff 0 = 0 at hconstant
  obtain ⟨d, hd⟩ := Polynomial.X_dvd_iff.mpr hconstant
  refine ⟨(hBaseAsPPolynomial K).symm d, ?_⟩
  apply (hBaseAsPPolynomial K).injective
  rw [map_mul, h_invariant_baseAsP_p,
    (hBaseAsPPolynomial K).apply_symm_apply]
  exact hd

omit [CharZero K] in
theorem h_invariant_C_hFormEval (x w : K)
    (F : MvPolynomial (Fin 2) K) :
    Polynomial.C (hFormEval x w F) =
      hFormEval (Polynomial.C x) (Polynomial.C w) F := by
  let left : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
    (Polynomial.CAlgHom : K →ₐ[K] Polynomial K).comp
      (MvPolynomial.aeval fun i ↦ if i = 0 then x else w)
  let right : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval fun i ↦
      if i = 0 then Polynomial.C x else Polynomial.C w
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [left, right]
  change left F = right F
  exact AlgHom.congr_fun heq F

theorem h_invariant_boundary_polynomial_eq
    (F : MvPolynomial (Fin 2) K) (N : ℕ)
    (hF : F.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference F = 0)
    {z : K} (hz : z ^ 2 + 2 = 0) :
    hFormEval 0
        (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2) F =
      hFormEval
        (Polynomial.C (hInfinityBoundaryX z) * Polynomial.X)
        (Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2) F := by
  have hboundary := congrArg Polynomial.C
    (h_invariant_boundary_eq F N hF hdifference hz)
  rw [h_invariant_C_hFormEval, h_invariant_C_hFormEval] at hboundary
  have hfirst := hFormEval_weighted_smul F N hF
    Polynomial.X (Polynomial.C 0)
      (Polynomial.C (hInfinityBoundaryW z))
  have hsecond := hFormEval_weighted_smul F N hF
    Polynomial.X (Polynomial.C (hInfinityBoundaryX z))
      (Polynomial.C (hInfinityBoundaryCapitalW z))
  have hfirst' :
      hFormEval 0
          (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2) F =
        Polynomial.X ^ N *
          hFormEval (Polynomial.C 0)
            (Polynomial.C (hInfinityBoundaryW z)) F := by
    rw [show (0 : Polynomial K) = Polynomial.X * Polynomial.C 0 by simp,
      show Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2 =
        Polynomial.X ^ 2 * Polynomial.C (hInfinityBoundaryW z) by ring]
    exact hfirst
  have hsecond' :
      hFormEval
          (Polynomial.C (hInfinityBoundaryX z) * Polynomial.X)
          (Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2) F =
        Polynomial.X ^ N *
          hFormEval (Polynomial.C (hInfinityBoundaryX z))
            (Polynomial.C (hInfinityBoundaryCapitalW z)) F := by
    rw [show Polynomial.C (hInfinityBoundaryX z) * Polynomial.X =
          Polynomial.X * Polynomial.C (hInfinityBoundaryX z) by ring,
      show Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2 =
        Polynomial.X ^ 2 *
          Polynomial.C (hInfinityBoundaryCapitalW z) by ring]
    exact hsecond
  calc
    hFormEval 0
        (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2) F =
        Polynomial.X ^ N *
          hFormEval (Polynomial.C 0)
            (Polynomial.C (hInfinityBoundaryW z)) F := by
      exact hfirst'
    _ = Polynomial.X ^ N *
          hFormEval (Polynomial.C (hInfinityBoundaryX z))
            (Polynomial.C (hInfinityBoundaryCapitalW z)) F := by
      rw [hboundary]
    _ = hFormEval
        (Polynomial.C (hInfinityBoundaryX z) * Polynomial.X)
        (Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2) F := by
      exact hsecond'.symm

omit [CharZero K] in
theorem h_invariant_baseInfinityEval_eq_hBaseEval (z : K) :
    hBaseInfinityEval z =
      hBaseEval K 0
        (Polynomial.C (hQ 0 (hInfinityBoundaryW z)) * Polynomial.X ^ 4) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
      rw [show MvPolynomial.X HBaseCoordinate.p = hBaseP K by rfl]
      rw [h_invariant_baseInfinityEval_p]
      simp only [hBaseEval, hBaseP, MvPolynomial.aeval_X]
  | q =>
      rw [show MvPolynomial.X HBaseCoordinate.q = hBaseQ K by rfl]
      rw [h_invariant_baseInfinityEval_q]
      simp only [hBaseEval, hBaseQ, MvPolynomial.aeval_X]

@[expose]
noncomputable def hPAlgebra
    (K : Type*) [Field K]
    {A : Type*} [CommRing A] [Algebra K A]
    (x w : A) : A :=
  x ^ 3 + algebraMap K A 3 * (x * w)

@[expose]
noncomputable def hQAlgebra
    (K : Type*) [Field K]
    {A : Type*} [CommRing A] [Algebra K A]
    (x w : A) : A :=
  x ^ 4 + algebraMap K A 4 * (x ^ 2 * w) +
    algebraMap K A 2 * w ^ 2

omit [CharZero K] in
theorem h_invariant_hFormEval_hBaseToWeightedForm
    {A : Type*} [CommRing A] [Algebra K A]
    (x w : A) (S : HBaseRing K) :
    hFormEval x w (hBaseToWeightedForm K S) =
      hBaseEval K (hPAlgebra K x w) (hQAlgebra K x w) S := by
  let left : HBaseRing K →ₐ[K] A :=
    (MvPolynomial.aeval fun i : Fin 2 ↦ if i = 0 then x else w).comp
      (hBaseToWeightedForm K)
  have heq : left = hBaseEval K (hPAlgebra K x w) (hQAlgebra K x w) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | p =>
        simp only [left, AlgHom.comp_apply, hBaseToWeightedForm,
          MvPolynomial.aeval_X, hBaseEval]
        change hFormEval x w hPForm = hPAlgebra K x w
        simp [hFormEval, hPForm, hFormX, hFormW,
          hPAlgebra, map_ofNat]
    | q =>
        simp only [left, AlgHom.comp_apply, hBaseToWeightedForm,
          MvPolynomial.aeval_X, hBaseEval]
        change hFormEval x w hQForm = hQAlgebra K x w
        simp [hFormEval, hQForm, hFormX, hFormW,
          hQAlgebra, map_ofNat]
  exact AlgHom.congr_fun heq S

omit [CharZero K] in
theorem h_invariant_hFormEval_base_first_boundary
    (z : K) (c : HBaseRing K) :
    hFormEval 0
        (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2)
        (hBaseToWeightedForm K c) =
      hBaseInfinityEval z c := by
  rw [h_invariant_hFormEval_hBaseToWeightedForm]
  rw [h_invariant_baseInfinityEval_eq_hBaseEval]
  congr 2
  · simp [hPAlgebra]
  · rw [show hQ 0 (hInfinityBoundaryW z) =
        2 * hInfinityBoundaryW z ^ 2 by simp [hQ]]
    simp only [hQAlgebra, algebraMap_eq]
    simp only [map_mul, map_pow, map_ofNat]
    ring

theorem h_invariant_h_boundary_fibre {z : K} (hz : z ^ 2 + 2 = 0) :
    hP 0 (hInfinityBoundaryW z) =
        hP (hInfinityBoundaryX z) (hInfinityBoundaryCapitalW z) ∧
      hQ 0 (hInfinityBoundaryW z) =
        hQ (hInfinityBoundaryX z) (hInfinityBoundaryCapitalW z) := by
  rw [h_invariant_w_formula hz, h_invariant_W_formula hz]
  constructor
  · simp only [hP]
    field_simp
    ring
  · simp only [hQ]
    field_simp
    linear_combination 18 * hInfinityBoundaryX z ^ 4 * hz

theorem h_invariant_hFormEval_base_second_boundary
    {z : K} (hz : z ^ 2 + 2 = 0) (c : HBaseRing K) :
    hFormEval
        (Polynomial.C (hInfinityBoundaryX z) * Polynomial.X)
        (Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2)
        (hBaseToWeightedForm K c) =
      hBaseInfinityEval z c := by
  rw [h_invariant_hFormEval_hBaseToWeightedForm]
  rw [h_invariant_baseInfinityEval_eq_hBaseEval]
  obtain ⟨hPboundary, hQboundary⟩ := h_invariant_h_boundary_fibre hz
  congr 2
  · calc
      hPAlgebra K
          (Polynomial.C (hInfinityBoundaryX z) * Polynomial.X)
          (Polynomial.C (hInfinityBoundaryCapitalW z) *
            Polynomial.X ^ 2) =
          Polynomial.X ^ 3 * Polynomial.C
            (hP (hInfinityBoundaryX z)
              (hInfinityBoundaryCapitalW z)) := by
        simp only [hPAlgebra, hP, algebraMap_eq]
        simp only [map_add, map_mul, map_pow, map_ofNat]
        ring
      _ = Polynomial.X ^ 3 * Polynomial.C
          (hP 0 (hInfinityBoundaryW z)) := by rw [← hPboundary]
      _ = 0 := by simp [hP]
  · calc
      hQAlgebra K
          (Polynomial.C (hInfinityBoundaryX z) * Polynomial.X)
          (Polynomial.C (hInfinityBoundaryCapitalW z) *
            Polynomial.X ^ 2) =
          Polynomial.X ^ 4 * Polynomial.C
            (hQ (hInfinityBoundaryX z)
              (hInfinityBoundaryCapitalW z)) := by
        simp only [hQAlgebra, hQ, algebraMap_eq]
        simp only [map_add, map_mul, map_pow, map_ofNat]
        ring
      _ = Polynomial.X ^ 4 * Polynomial.C
          (hQ 0 (hInfinityBoundaryW z)) := by rw [← hQboundary]
      _ = Polynomial.C (hQ 0 (hInfinityBoundaryW z)) *
          Polynomial.X ^ 4 := by ring

omit [CharZero K] in
theorem h_invariant_hFormEval_hSixTerm_first_boundary
    (z : K) (c : Fin 6 → HBaseRing K) :
    hFormEval 0
        (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2)
        (hSixTermValue K c) =
      hBaseInfinityEval z (c 0) +
        hBaseInfinityEval z (c 3) *
          Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2 := by
  have hadd (F G : MvPolynomial (Fin 2) K) :
      hFormEval 0
          (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2)
          (F + G) =
        hFormEval 0
            (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2) F +
          hFormEval 0
            (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2) G := by
    simp [hFormEval]
  have hmul (F G : MvPolynomial (Fin 2) K) :
      hFormEval 0
          (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2)
          (F * G) =
        hFormEval 0
            (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2) F *
          hFormEval 0
            (Polynomial.C (hInfinityBoundaryW z) * Polynomial.X ^ 2) G := by
    simp [hFormEval]
  simp only [hSixTermValue, Fin.sum_univ_six, hadd, hmul]
  rw [h_invariant_hFormEval_base_first_boundary,
    h_invariant_hFormEval_base_first_boundary,
    h_invariant_hFormEval_base_first_boundary,
    h_invariant_hFormEval_base_first_boundary,
    h_invariant_hFormEval_base_first_boundary,
    h_invariant_hFormEval_base_first_boundary]
  simp [hSixTerm, hFormEval, hFormX, hFormW]
  ring

theorem h_invariant_hFormEval_hSixTerm_second_boundary
    {z : K} (hz : z ^ 2 + 2 = 0)
    (c : Fin 6 → HBaseRing K) :
    hFormEval
        (Polynomial.C (hInfinityBoundaryX z) * Polynomial.X)
        (Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2)
        (hSixTermValue K c) =
      hBaseInfinityEval z (c 0) +
        hBaseInfinityEval z (c 1) *
          Polynomial.C (hInfinityBoundaryX z) * Polynomial.X +
        hBaseInfinityEval z (c 2) *
          Polynomial.C (hInfinityBoundaryX z ^ 2) * Polynomial.X ^ 2 +
        hBaseInfinityEval z (c 3) *
          Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2 +
        hBaseInfinityEval z (c 4) *
          Polynomial.C
            (hInfinityBoundaryX z * hInfinityBoundaryCapitalW z) *
            Polynomial.X ^ 3 +
        hBaseInfinityEval z (c 5) *
          Polynomial.C
            (hInfinityBoundaryX z ^ 2 * hInfinityBoundaryCapitalW z) *
            Polynomial.X ^ 4 := by
  let x : Polynomial K :=
    Polynomial.C (hInfinityBoundaryX z) * Polynomial.X
  let w : Polynomial K :=
    Polynomial.C (hInfinityBoundaryCapitalW z) * Polynomial.X ^ 2
  have hadd (F G : MvPolynomial (Fin 2) K) :
      hFormEval x w (F + G) = hFormEval x w F + hFormEval x w G := by
    simp [hFormEval]
  have hmul (F G : MvPolynomial (Fin 2) K) :
      hFormEval x w (F * G) = hFormEval x w F * hFormEval x w G := by
    simp [hFormEval]
  change hFormEval x w (hSixTermValue K c) = _
  simp only [hSixTermValue, Fin.sum_univ_six, hadd, hmul]
  rw [h_invariant_hFormEval_base_second_boundary hz,
    h_invariant_hFormEval_base_second_boundary hz,
    h_invariant_hFormEval_base_second_boundary hz,
    h_invariant_hFormEval_base_second_boundary hz,
    h_invariant_hFormEval_base_second_boundary hz,
    h_invariant_hFormEval_base_second_boundary hz]
  simp [hSixTerm, hFormEval, hFormX, hFormW, x, w]
  ring

theorem h_invariant_sixTerm_infinity_relation
    (R : MvPolynomial (Fin 2) K) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R = 0)
    (c : Fin 6 → HBaseRing K)
    (hdecomposition : R = hSixTermValue K c)
    {z : K} (hz : z ^ 2 + 2 = 0) :
    -(hBaseInfinityEval z (c 1) *
        Polynomial.C (hInfinityBoundaryX z) * Polynomial.X) -
      hBaseInfinityEval z (c 2) *
        Polynomial.C (hInfinityBoundaryX z ^ 2) * Polynomial.X ^ 2 +
      hBaseInfinityEval z (c 3) *
        Polynomial.C
          (hInfinityBoundaryW z - hInfinityBoundaryCapitalW z) *
          Polynomial.X ^ 2 -
      hBaseInfinityEval z (c 4) *
        Polynomial.C
          (hInfinityBoundaryX z * hInfinityBoundaryCapitalW z) *
          Polynomial.X ^ 3 -
      hBaseInfinityEval z (c 5) *
        Polynomial.C
          (hInfinityBoundaryX z ^ 2 * hInfinityBoundaryCapitalW z) *
          Polynomial.X ^ 4 = 0 := by
  have hpoly := h_invariant_boundary_polynomial_eq R N hR hdifference hz
  rw [hdecomposition] at hpoly
  rw [h_invariant_hFormEval_hSixTerm_first_boundary,
    h_invariant_hFormEval_hSixTerm_second_boundary hz] at hpoly
  simp only [map_sub] at ⊢
  linear_combination hpoly

theorem h_invariant_QAtInfinity_natDegree
    {z : K} (hz : z ^ 2 + 2 = 0) (p : Polynomial K) :
    (hQAtInfinity z p).natDegree = p.natDegree * 4 := by
  change (p.comp
    (Polynomial.C (hQ 0 (hInfinityBoundaryW z)) * Polynomial.X ^ 4)).natDegree = _
  rw [Polynomial.natDegree_comp, h_invariant_Qvalue_degree hz]

theorem h_invariant_QAtInfinity_residue_separation
    {z : K} (hz : z ^ 2 + 2 = 0)
    (p0 p1 p2 p3 : Polynomial K)
    (hzero :
      hQAtInfinity z p0 * Polynomial.X ^ 4 +
        hQAtInfinity z p1 * Polynomial.X +
        hQAtInfinity z p2 * Polynomial.X ^ 2 +
        hQAtInfinity z p3 * Polynomial.X ^ 3 = 0) :
    p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 := by
  classical
  let f : Fin 4 → Polynomial K := ![
    hQAtInfinity z p0 * Polynomial.X ^ 4,
    hQAtInfinity z p1 * Polynomial.X,
    hQAtInfinity z p2 * Polynomial.X ^ 2,
    hQAtInfinity z p3 * Polynomial.X ^ 3]
  have hsum : ∑ i : Fin 4, f i = 0 := by
    rw [Fin.sum_univ_four]
    exact hzero
  have hresidue (i : Fin 4) (hi : f i ≠ 0) :
      (f i).natDegree % 4 = i := by
    fin_cases i
    · change (hQAtInfinity z p0 * Polynomial.X ^ 4).natDegree % 4 = 0
      change hQAtInfinity z p0 * Polynomial.X ^ 4 ≠ 0 at hi
      have hp : hQAtInfinity z p0 ≠ 0 := by
        intro hp
        exact hi (by rw [hp, zero_mul])
      rw [Polynomial.natDegree_mul hp
        (pow_ne_zero 4 Polynomial.X_ne_zero),
        Polynomial.natDegree_X_pow, h_invariant_QAtInfinity_natDegree hz]
      omega
    · change (hQAtInfinity z p1 * Polynomial.X).natDegree % 4 = 1
      change hQAtInfinity z p1 * Polynomial.X ≠ 0 at hi
      have hp : hQAtInfinity z p1 ≠ 0 := by
        intro hp
        exact hi (by rw [hp, zero_mul])
      rw [Polynomial.natDegree_mul hp Polynomial.X_ne_zero,
        Polynomial.natDegree_X, h_invariant_QAtInfinity_natDegree hz]
      omega
    · change (hQAtInfinity z p2 * Polynomial.X ^ 2).natDegree % 4 = 2
      change hQAtInfinity z p2 * Polynomial.X ^ 2 ≠ 0 at hi
      have hp : hQAtInfinity z p2 ≠ 0 := by
        intro hp
        exact hi (by rw [hp, zero_mul])
      rw [Polynomial.natDegree_mul hp
        (pow_ne_zero 2 Polynomial.X_ne_zero),
        Polynomial.natDegree_X_pow, h_invariant_QAtInfinity_natDegree hz]
      omega
    · change (hQAtInfinity z p3 * Polynomial.X ^ 3).natDegree % 4 = 3
      change hQAtInfinity z p3 * Polynomial.X ^ 3 ≠ 0 at hi
      have hp : hQAtInfinity z p3 ≠ 0 := by
        intro hp
        exact hi (by rw [hp, zero_mul])
      rw [Polynomial.natDegree_mul hp
        (pow_ne_zero 3 Polynomial.X_ne_zero),
        Polynomial.natDegree_X_pow, h_invariant_QAtInfinity_natDegree hz]
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
  have hfzero (i : Fin 4) : f i = 0 := by
    by_contra hi
    have hle : Polynomial.degree (f i) ≤
        Finset.univ.sup fun j : Fin 4 ↦ Polynomial.degree (f j) :=
      Finset.le_sup (f := fun j : Fin 4 ↦ Polynomial.degree (f j))
        (Finset.mem_univ i)
    rw [← hdegree] at hle
    have hbot : Polynomial.degree (f i) = ⊥ := le_bot_iff.mp hle
    exact hi (Polynomial.degree_eq_bot.mp hbot)
  have h0 := hfzero 0
  have h1 := hfzero 1
  have h2 := hfzero 2
  have h3 := hfzero 3
  simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  have he0 : hQAtInfinity z p0 = 0 :=
    (mul_eq_zero.mp h0).resolve_right
      (pow_ne_zero 4 Polynomial.X_ne_zero)
  have he1 : hQAtInfinity z p1 = 0 :=
    (mul_eq_zero.mp h1).resolve_right Polynomial.X_ne_zero
  have he2 : hQAtInfinity z p2 = 0 :=
    (mul_eq_zero.mp h2).resolve_right
      (pow_ne_zero 2 Polynomial.X_ne_zero)
  have he3 : hQAtInfinity z p3 = 0 :=
    (mul_eq_zero.mp h3).resolve_right
      (pow_ne_zero 3 Polynomial.X_ne_zero)
  exact ⟨h_invariant_QAtInfinity_injective hz (by simpa using he0),
    h_invariant_QAtInfinity_injective hz (by simpa using he1),
    h_invariant_QAtInfinity_injective hz (by simpa using he2),
    h_invariant_QAtInfinity_injective hz (by simpa using he3)⟩

theorem h_invariant_boundary_x_ne_zero {z : K} (hz : z ^ 2 + 2 = 0) :
    hInfinityBoundaryX z ≠ 0 := by
  rw [h_invariant_x_formula hz]
  exact mul_ne_zero (by norm_num)
    (h_conic_param_infinity_root_add_one_ne_zero hz)

theorem h_invariant_boundary_capitalW_ne_zero {z : K} (hz : z ^ 2 + 2 = 0) :
    hInfinityBoundaryCapitalW z ≠ 0 := by
  rw [h_invariant_W_formula hz]
  exact div_ne_zero (neg_ne_zero.mpr
    (pow_ne_zero 2 (h_invariant_boundary_x_ne_zero hz))) (by norm_num)

omit [CharZero K] in
theorem h_invariant_baseInfinityEval_eq_QAtInfinity (z : K) (c : HBaseRing K) :
    hBaseInfinityEval z c = hQAtInfinity z (hBasePConstant K c) := rfl

theorem h_invariant_sixTerm_infinity_coefficients
    (R : MvPolynomial (Fin 2) K) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R = 0)
    (c : Fin 6 → HBaseRing K)
    (hdecomposition : R = hSixTermValue K c)
    {z : K} (hz : z ^ 2 + 2 = 0) :
    hBasePConstant K (c 1) = 0 ∧
      -hBasePConstant K (c 2) +
          Polynomial.C ((z + 2) / 6) * hBasePConstant K (c 3) = 0 ∧
      hBasePConstant K (c 4) = 0 ∧
      hBasePConstant K (c 5) = 0 := by
  let A : Fin 6 → Polynomial K := fun i => hBasePConstant K (c i)
  let p0 : Polynomial K :=
    -(A 5 * Polynomial.C
      (hInfinityBoundaryX z ^ 2 * hInfinityBoundaryCapitalW z))
  let p1 : Polynomial K :=
    -(A 1 * Polynomial.C (hInfinityBoundaryX z))
  let p2 : Polynomial K :=
    -(A 2 * Polynomial.C (hInfinityBoundaryX z ^ 2)) +
      A 3 * Polynomial.C
        (hInfinityBoundaryW z - hInfinityBoundaryCapitalW z)
  let p3 : Polynomial K :=
    -(A 4 * Polynomial.C
      (hInfinityBoundaryX z * hInfinityBoundaryCapitalW z))
  have hQAtInfinity_C (a : K) :
      hQAtInfinity z (Polynomial.C a) = Polynomial.C a := by
    simp [hQAtInfinity]
  have hrelation := h_invariant_sixTerm_infinity_relation
    R N hR hdifference c hdecomposition hz
  have hzero :
      hQAtInfinity z p0 * Polynomial.X ^ 4 +
        hQAtInfinity z p1 * Polynomial.X +
        hQAtInfinity z p2 * Polynomial.X ^ 2 +
        hQAtInfinity z p3 * Polynomial.X ^ 3 = 0 := by
    simp only [p0, p1, p2, p3, A, map_neg, map_mul, map_add,
      map_sub, hQAtInfinity_C]
    simp only [h_invariant_baseInfinityEval_eq_QAtInfinity] at hrelation
    simp only [Polynomial.C_mul, Polynomial.C_sub] at hrelation ⊢
    linear_combination hrelation
  obtain ⟨hp0, hp1, hp2, hp3⟩ :=
    h_invariant_QAtInfinity_residue_separation hz p0 p1 p2 p3 hzero
  have hx : hInfinityBoundaryX z ≠ 0 := h_invariant_boundary_x_ne_zero hz
  have hW : hInfinityBoundaryCapitalW z ≠ 0 :=
    h_invariant_boundary_capitalW_ne_zero hz
  have hA1 : A 1 = 0 := by
    have hproduct : A 1 * Polynomial.C (hInfinityBoundaryX z) = 0 := by
      simpa [p1] using congrArg Neg.neg hp1
    exact (mul_eq_zero.mp hproduct).resolve_right
      (Polynomial.C_ne_zero.mpr hx)
  have hA4 : A 4 = 0 := by
    have hscalar : hInfinityBoundaryX z *
        hInfinityBoundaryCapitalW z ≠ 0 := mul_ne_zero hx hW
    have hproduct : A 4 * Polynomial.C
        (hInfinityBoundaryX z * hInfinityBoundaryCapitalW z) = 0 := by
      simpa [p3] using congrArg Neg.neg hp3
    exact (mul_eq_zero.mp hproduct).resolve_right
      (Polynomial.C_ne_zero.mpr hscalar)
  have hA5 : A 5 = 0 := by
    have hscalar : hInfinityBoundaryX z ^ 2 *
        hInfinityBoundaryCapitalW z ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hx) hW
    have hproduct : A 5 * Polynomial.C
        (hInfinityBoundaryX z ^ 2 * hInfinityBoundaryCapitalW z) = 0 := by
      simpa [p0] using congrArg Neg.neg hp0
    exact (mul_eq_zero.mp hproduct).resolve_right
      (Polynomial.C_ne_zero.mpr hscalar)
  have hdifferenceFormula :
      hInfinityBoundaryW z - hInfinityBoundaryCapitalW z =
        (z + 2) / 6 * hInfinityBoundaryX z ^ 2 := by
    rw [h_invariant_w_formula hz, h_invariant_W_formula hz]
    ring
  have hA23 : -A 2 + Polynomial.C ((z + 2) / 6) * A 3 = 0 := by
    have hfactor : p2 =
        (-A 2 + Polynomial.C ((z + 2) / 6) * A 3) *
          Polynomial.C (hInfinityBoundaryX z ^ 2) := by
      dsimp [p2]
      rw [hdifferenceFormula, map_mul]
      ring
    rw [hfactor] at hp2
    exact (mul_eq_zero.mp hp2).resolve_right
      (Polynomial.C_ne_zero.mpr (pow_ne_zero 2 hx))
  exact ⟨hA1, hA23, hA4, hA5⟩

theorem h_invariant_sixTerm_base_constants_eq_zero
    (R : MvPolynomial (Fin 2) K) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R = 0)
    (c : Fin 6 → HBaseRing K)
    (hdecomposition : R = hSixTermValue K c)
    {z u : K} (hz : z ^ 2 + 2 = 0) (hu : u ^ 2 + 2 = 0)
    (hzu : z ≠ u) :
    hBasePConstant K (c 1) = 0 ∧
      hBasePConstant K (c 2) = 0 ∧
      hBasePConstant K (c 3) = 0 ∧
      hBasePConstant K (c 4) = 0 ∧
      hBasePConstant K (c 5) = 0 := by
  obtain ⟨hc1, hrelationZ, hc4, hc5⟩ :=
    h_invariant_sixTerm_infinity_coefficients
      R N hR hdifference c hdecomposition hz
  obtain ⟨_hc1u, hrelationU, _hc4u, _hc5u⟩ :=
    h_invariant_sixTerm_infinity_coefficients
      R N hR hdifference c hdecomposition hu
  have hscalar : (z + 2) / 6 ≠ (u + 2) / 6 := by
    intro heq
    apply hzu
    field_simp at heq
    linear_combination heq
  have hCscalar : Polynomial.C ((z + 2) / 6) -
      Polynomial.C ((u + 2) / 6) ≠ 0 := by
    rw [← Polynomial.C_sub, Polynomial.C_ne_zero]
    exact sub_ne_zero.mpr hscalar
  have hc3 : hBasePConstant K (c 3) = 0 := by
    have hproduct :
        (Polynomial.C ((z + 2) / 6) -
            Polynomial.C ((u + 2) / 6)) *
          hBasePConstant K (c 3) = 0 := by
      linear_combination hrelationZ - hrelationU
    exact (mul_eq_zero.mp hproduct).resolve_left hCscalar
  have hc2 : hBasePConstant K (c 2) = 0 := by
    rw [hc3, mul_zero, add_zero] at hrelationZ
    exact neg_eq_zero.mp hrelationZ
  exact ⟨hc1, hc2, hc3, hc4, hc5⟩

omit [CharZero K] in
theorem h_invariant_baseP_dvd_of_PConstant_eq_zero
    (c : HBaseRing K) (hzero : hBasePConstant K c = 0) :
    hBaseP K ∣ c := by
  change (hBaseAsPPolynomial K c).coeff 0 = 0 at hzero
  obtain ⟨d, hd⟩ := Polynomial.X_dvd_iff.mpr hzero
  refine ⟨(hBaseAsPPolynomial K).symm d, ?_⟩
  apply (hBaseAsPPolynomial K).injective
  rw [map_mul, h_invariant_baseAsP_p,
    (hBaseAsPPolynomial K).apply_symm_apply]
  exact hd

theorem h_invariant_sixTerm_nonconstant_coefficients_baseP_dvd
    (R : MvPolynomial (Fin 2) K) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R = 0)
    (c : Fin 6 → HBaseRing K)
    (hdecomposition : R = hSixTermValue K c)
    {z u : K} (hz : z ^ 2 + 2 = 0) (hu : u ^ 2 + 2 = 0)
    (hzu : z ≠ u) :
    ∀ i : Fin 6, i ≠ 0 → hBaseP K ∣ c i := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ :=
    h_invariant_sixTerm_base_constants_eq_zero
      R N hR hdifference c hdecomposition hz hu hzu
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact h_invariant_baseP_dvd_of_PConstant_eq_zero (c 1) hc1
  · exact h_invariant_baseP_dvd_of_PConstant_eq_zero (c 2) hc2
  · exact h_invariant_baseP_dvd_of_PConstant_eq_zero (c 3) hc3
  · exact h_invariant_baseP_dvd_of_PConstant_eq_zero (c 4) hc4
  · exact h_invariant_baseP_dvd_of_PConstant_eq_zero (c 5) hc5

omit [CharZero K] in
theorem h_invariant_hBase_isWeightedHomogeneous_of_p_mul
    (S : HBaseRing K) (M : ℕ)
    (hproduct : (hBaseP K * S).IsWeightedHomogeneous hBaseWeight M) :
    S.IsWeightedHomogeneous hBaseWeight (M - 3) := by
  intro d hd
  have hcoefficient : MvPolynomial.coeff
      (Finsupp.single HBaseCoordinate.p 1 + d) (hBaseP K * S) ≠ 0 := by
    simpa [hBaseP] using
      (MvPolynomial.coeff_X_mul d HBaseCoordinate.p S).symm ▸ hd
  have hweight := hproduct hcoefficient
  have hsingle :
      Finsupp.weight hBaseWeight
        (Finsupp.single HBaseCoordinate.p 1) = 3 := by
    simp [Finsupp.weight_apply, hBaseWeight]
  rw [map_add, hsingle] at hweight
  omega

omit [CharZero K] in
theorem h_invariant_hBase_degree_three_le_of_p_mul_ne_zero
    (S : HBaseRing K) (M : ℕ)
    (hproduct : (hBaseP K * S).IsWeightedHomogeneous hBaseWeight M)
    (hS : S ≠ 0) :
    3 ≤ M := by
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hS
  have hcoefficient : MvPolynomial.coeff
      (Finsupp.single HBaseCoordinate.p 1 + d) (hBaseP K * S) ≠ 0 := by
    simpa [hBaseP] using
      (MvPolynomial.coeff_X_mul d HBaseCoordinate.p S).symm ▸ hd
  have hweight := hproduct hcoefficient
  have hsingle :
      Finsupp.weight hBaseWeight
        (Finsupp.single HBaseCoordinate.p 1) = 3 := by
    simp [Finsupp.weight_apply, hBaseWeight]
  rw [map_add, hsingle] at hweight
  omega

omit [CharZero K] in
theorem h_invariant_hSixTermValue_baseP_mul
    (d : Fin 6 → HBaseRing K) :
    hSixTermValue K (fun i => hBaseP K * d i) =
      hPForm * hSixTermValue K d := by
  simp only [hSixTermValue, map_mul, hBaseToWeightedForm_p]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [CharZero K] in
theorem h_invariant_hFormEval_mul
    {A : Type*} [CommRing A] [Algebra K A]
    (x w : A) (F G : MvPolynomial (Fin 2) K) :
    hFormEval x w (F * G) = hFormEval x w F * hFormEval x w G := by
  simp [hFormEval]

omit [CharZero K] in
theorem h_invariant_hConicDifference_add
    (F G : MvPolynomial (Fin 2) K) :
    hConicDifference (F + G) = hConicDifference F + hConicDifference G := by
  simp only [hConicDifference, hFirstConicPullback,
    hSecondConicPullback, hFormEval, MvPolynomial.eval₂_add]
  ring

theorem h_invariant_hConicDifference_hPForm_mul
    (F : MvPolynomial (Fin 2) K) :
    hConicDifference (hPForm * F) =
      hFirstConicPullback hPForm * hConicDifference F := by
  obtain ⟨hPfiber, _hQfiber⟩ :=
    h_conic_param_fibre_equations (K := K)
  have hfirstP : hFirstConicPullback (hPForm (K := K)) =
      hP 1 hConicParamW := by
    exact hFormEval_hPForm 1 hConicParamW
  have hsecondP : hSecondConicPullback (hPForm (K := K)) =
      hP hConicParamX hConicParamCapitalW := by
    exact hFormEval_hPForm hConicParamX hConicParamCapitalW
  rw [hConicDifference, hFirstConicPullback, hSecondConicPullback,
    h_invariant_hFormEval_mul, h_invariant_hFormEval_mul,
    ← hFirstConicPullback, ← hSecondConicPullback]
  rw [hfirstP, hsecondP, hPfiber]
  rw [hConicDifference, hFirstConicPullback, hSecondConicPullback]
  ring

theorem h_invariant_hFirstConicPullback_hPForm_ne_zero
    {a : K} (ha : a ^ 2 + 2 * a + 4 = 0) :
    hFirstConicPullback (hPForm (K := K)) ≠ 0 := by
  intro hzero
  have hden : hConicParamDenominator (K := K).eval a ≠ 0 := by
    simpa [hConicParamDenominator] using
      h_conic_param_denominator_at_one_root_ne_zero ha
  obtain ⟨_hxRegular, hwRegular, _hWRegular⟩ :=
    h_conic_param_regular_at a
      (h_conic_param_one_root_add_one_ne_zero ha) hden
  have honeRegular : HRatFuncRegularAt a (1 : RatFunc K) := by
    simpa using hRatFuncRegularAt_algebraMap (K := K) a 1
  have heval := congrArg (RatFunc.eval (RingHom.id K) a) hzero
  rw [hFirstConicPullback,
    h_ratFunc_eval_hFormEval a 1 hConicParamW hPForm
      honeRegular hwRegular,
    RatFunc.eval_zero] at heval
  have hvalues := h_conic_param_values_at_one ha
  rw [hvalues.2.1] at heval
  norm_num [hFormEval, hPForm, hFormX, hFormW] at heval

theorem h_invariant_homogeneous_conicDifference_eq_zero_mem_base
    {a z u : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hz : z ^ 2 + 2 = 0) (hu : u ^ 2 + 2 = 0) (hzu : z ≠ u)
    (R : MvPolynomial (Fin 2) K) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R = 0) :
    R ∈ Set.range (hBaseToWeightedForm K) := by
  classical
  induction N using Nat.strong_induction_on generalizing R with
  | h N ih =>
      obtain ⟨c, hdecomposition, hcHomogeneous, hcZero⟩ :=
        exists_homogeneous_hSixTermValue R N hR
      by_cases hall : ∀ i : Fin 6, i ≠ 0 → c i = 0
      · have hc1 : c 1 = 0 := hall 1 (by decide)
        have hc2 : c 2 = 0 := hall 2 (by decide)
        have hc3 : c 3 = 0 := hall 3 (by decide)
        have hc4 : c 4 = 0 := hall 4 (by decide)
        have hc5 : c 5 = 0 := hall 5 (by decide)
        refine ⟨c 0, ?_⟩
        rw [hdecomposition, hSixTermValue, Fin.sum_univ_six,
          hc1, hc2, hc3, hc4, hc5]
        simp [hSixTerm]
      · push Not at hall
        obtain ⟨i, hi, hci⟩ := hall
        have hiDegree : 0 < hSixTermDegree i := by
          fin_cases i <;> simp_all [hSixTermDegree]
        have hiLe : hSixTermDegree i ≤ N := by
          by_contra hnot
          exact hci (hcZero i (Nat.lt_of_not_ge hnot))
        have hNpositive : 0 < N := lt_of_lt_of_le hiDegree hiLe
        have hmeasure : N - 3 < N := by omega
        have hdiv := h_invariant_sixTerm_nonconstant_coefficients_baseP_dvd
          R N hR hdifference c hdecomposition hz hu hzu
        obtain ⟨d1, hd1⟩ := hdiv 1 (by decide)
        obtain ⟨d2, hd2⟩ := hdiv 2 (by decide)
        obtain ⟨d3, hd3⟩ := hdiv 3 (by decide)
        obtain ⟨d4, hd4⟩ := hdiv 4 (by decide)
        obtain ⟨d5, hd5⟩ := hdiv 5 (by decide)
        let d : Fin 6 → HBaseRing K := ![0, d1, d2, d3, d4, d5]
        have hc1 : c 1 = hBaseP K * d 1 := by simpa [d] using hd1
        have hc2 : c 2 = hBaseP K * d 2 := by simpa [d] using hd2
        have hc3 : c 3 = hBaseP K * d 3 := by simpa [d] using hd3
        have hc4 : c 4 = hBaseP K * d 4 := by simpa [d] using hd4
        have hc5 : c 5 = hBaseP K * d 5 := by simpa [d] using hd5
        have hrepresentation :
            R = hBaseToWeightedForm K (c 0) +
              hPForm * hSixTermValue K d := by
          rw [hdecomposition, hSixTermValue, Fin.sum_univ_six,
            hSixTermValue, Fin.sum_univ_six]
          rw [hc1, hc2, hc3, hc4, hc5]
          simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.cons_val_three,
            Matrix.cons_val_four,
            map_zero, map_mul, hBaseToWeightedForm_p, zero_mul]
          simp [hSixTerm]
          ring
        have hcoefficientEquation (j : Fin 6) (hj : j ≠ 0) :
            c j = hBaseP K * d j := by
          fin_cases j
          · exact (hj rfl).elim
          · exact hc1
          · exact hc2
          · exact hc3
          · exact hc4
          · exact hc5
        have hdHomogeneous (j : Fin 6) :
            (d j).IsWeightedHomogeneous hBaseWeight
              ((N - hSixTermDegree j) - 3) := by
          by_cases hj : j = 0
          · subst j
            simp only [d, Matrix.cons_val_zero]
            exact MvPolynomial.isWeightedHomogeneous_zero K _ _
          · apply h_invariant_hBase_isWeightedHomogeneous_of_p_mul
            rw [← hcoefficientEquation j hj]
            exact hcHomogeneous j
        have hbasePne : hBaseP K ≠ 0 := by
          exact MvPolynomial.X_ne_zero HBaseCoordinate.p
        have hsummand (j : Fin 6) :
            (hBaseToWeightedForm K (d j) * hSixTerm K j).IsWeightedHomogeneous
              hFormWeight (N - 3) := by
          by_cases hdj : d j = 0
          · rw [hdj, map_zero, zero_mul]
            exact MvPolynomial.isWeightedHomogeneous_zero K _ _
          · have hcjne : c j ≠ 0 := by
              by_cases hj : j = 0
              · subst j
                simp [d] at hdj
              · rw [hcoefficientEquation j hj]
                exact mul_ne_zero hbasePne hdj
            have hjLe : hSixTermDegree j ≤ N := by
              by_contra hnot
              exact hcjne (hcZero j (Nat.lt_of_not_ge hnot))
            have hdegreeLower : 3 ≤ N - hSixTermDegree j := by
              apply h_invariant_hBase_degree_three_le_of_p_mul_ne_zero
                (d j) (N - hSixTermDegree j)
              · rw [← hcoefficientEquation j (by
                    intro hj
                    subst j
                    simp [d] at hdj)]
                exact hcHomogeneous j
              · exact hdj
            have hterm := hSixTermSummand_isWeightedHomogeneous
              (K := K) j (hdHomogeneous j)
            convert hterm using 1
            omega
        have hquotientHomogeneous :
            (hSixTermValue K d).IsWeightedHomogeneous
              hFormWeight (N - 3) := by
          rw [hSixTermValue]
          exact MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ _
            (fun j _ => hsummand j)
        have hfactor : hConicDifference R =
            hFirstConicPullback hPForm *
              hConicDifference (hSixTermValue K d) := by
          rw [hrepresentation, h_invariant_hConicDifference_add,
            hConicDifference_hBaseToWeightedForm,
            h_invariant_hConicDifference_hPForm_mul, zero_add]
        have hquotientDifference :
            hConicDifference (hSixTermValue K d) = 0 := by
          have hproduct : hFirstConicPullback (hPForm (K := K)) *
              hConicDifference (hSixTermValue K d) = 0 := by
            rw [← hfactor, hdifference]
          exact (mul_eq_zero.mp hproduct).resolve_left
            (h_invariant_hFirstConicPullback_hPForm_ne_zero ha)
        obtain ⟨S, hS⟩ := ih (N - 3) hmeasure
          (hSixTermValue K d) hquotientHomogeneous hquotientDifference
        refine ⟨c 0 + hBaseP K * S, ?_⟩
        rw [map_add, map_mul, hBaseToWeightedForm_p, hS]
        exact hrepresentation.symm

/-- The first point at infinity of the complex residual conic. -/
@[expose]
noncomputable def hConicInfinityRootPlus : ℂ :=
  Complex.I * Real.sqrt 2

/-- The second point at infinity of the complex residual conic. -/
@[expose]
noncomputable def hConicInfinityRootMinus : ℂ :=
  -Complex.I * Real.sqrt 2

private theorem h_complex_sqrt_two_square :
    ((Complex.I * (Real.sqrt 2 : ℂ)) ^ 2) = -2 := by
  have hsqrt : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [mul_pow, Complex.I_sq, hsqrt]
  norm_num

/-- The two specified complex parameters are the roots at infinity. -/
theorem h_conic_infinity_roots_equations :
    hConicInfinityRootPlus ^ 2 + 2 = 0 ∧
      hConicInfinityRootMinus ^ 2 + 2 = 0 := by
  constructor
  · simp only [hConicInfinityRootPlus]
    linear_combination h_complex_sqrt_two_square
  · simp only [hConicInfinityRootMinus]
    linear_combination h_complex_sqrt_two_square

/-- The two complex parameters at infinity are distinct. -/
theorem h_conic_infinity_roots_ne :
    hConicInfinityRootPlus ≠ hConicInfinityRootMinus := by
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have himaginary : Complex.I * (Real.sqrt 2 : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hsqrt
  intro hequal
  apply himaginary
  simp only [hConicInfinityRootPlus, hConicInfinityRootMinus] at hequal
  linear_combination (1 / 2) * hequal

/-- For a complex homogeneous form, vanishing of the residual conic
difference is equivalent to membership in the image of `ℂ[P,Q]` in the
direction needed for invariant descent. -/
theorem hConicDifference_eq_zero_mem_base_of_isWeightedHomogeneous
    (R : MvPolynomial (Fin 2) ℂ) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R = 0) :
    R ∈ Set.range (hBaseToWeightedForm ℂ) := by
  exact h_invariant_homogeneous_conicDifference_eq_zero_mem_base
    h_conic_one_roots_equations.1
    h_conic_infinity_roots_equations.1
    h_conic_infinity_roots_equations.2
    h_conic_infinity_roots_ne R N hR hdifference

/-- Weighted homogeneity supplies the base detection assertion used by the
projective collision theorem. -/
theorem hConicDifferenceDetectsBase_of_isWeightedHomogeneous
    (R : MvPolynomial (Fin 2) ℂ) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N) :
    HConicDifferenceDetectsBase ℂ R := by
  intro hdifference
  exact hConicDifference_eq_zero_mem_base_of_isWeightedHomogeneous
    R N hR hdifference

/-- A complex homogeneous form outside `ℂ[P,Q]` has nonzero residual
conic difference. -/
theorem hConicDifference_ne_zero_of_not_mem_base
    (R : MvPolynomial (Fin 2) ℂ) (N : ℕ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hnotbase : R ∉ Set.range (hBaseToWeightedForm ℂ)) :
    hConicDifference R ≠ 0 := by
  intro hdifference
  exact hnotbase
    (hConicDifference_eq_zero_mem_base_of_isWeightedHomogeneous
      R N hR hdifference)

/-- Base ring exclusion and the two literal Jacobian divisibilities produce
an off diagonal projective fibre pair for the homogeneous `H` map. -/
theorem exists_complex_h_homogeneous_fibre_difference_zero_of_not_mem_base
    (N : ℕ) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hnotbase : R ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R)) :
    ∃ x t X T : ℂ,
      (x ≠ 0 ∨ t ≠ 0 ∨ X ≠ 0 ∨ T ≠ 0) ∧
      (x ≠ X ∨ t ≠ T) ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R := by
  exact exists_complex_h_homogeneous_fibre_difference_zero_of_detectsBase
    N hN R hR
      (hConicDifferenceDetectsBase_of_isWeightedHomogeneous R N hR)
      hnotbase hPdiv hQdiv

end OnLeConjecture.DThree
