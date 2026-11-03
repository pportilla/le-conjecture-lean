/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitSixTermGraded
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Tactic.ComputeDegree

/-!
# The equalizer for the quadratic orbit pair

This module studies the two pullbacks from the source polynomial ring to the
normalization of the residual fibre relation. The target statement is that a
homogeneous form with equal pullbacks belongs to `C[Phi,Psi]`.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- Pullback through the first source point on the residual curve. -/
@[expose]
noncomputable def orbitFirstConicPullback (delta : ℂ) :
    OrbitPolynomial ℂ →ₐ[ℂ] OrbitParameterForm :=
  MvPolynomial.aeval ![orbitConicS, orbitConicLambda delta]

/-- Pullback through the second source point on the residual curve. -/
@[expose]
noncomputable def orbitSecondConicPullback (delta : ℂ) :
    OrbitPolynomial ℂ →ₐ[ℂ] OrbitParameterForm :=
  MvPolynomial.aeval ![orbitConicT, orbitConicZeta delta]

theorem orbitFirstConicPullback_phi
    {delta : ℂ} (hdelta : delta ^ 2 = 3) :
    orbitFirstConicPullback delta (orbitPolynomialPhi ℂ) =
      orbitSecondConicPullback delta (orbitPolynomialPhi ℂ) := by
  have hC2 : (MvPolynomial.C (2 : ℂ) : OrbitParameterForm) = 2 :=
    map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 2
  have hC3 : (MvPolynomial.C (3 : ℂ) : OrbitParameterForm) = 3 :=
    map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 3
  have hdeltaForm :
      (MvPolynomial.C delta : OrbitParameterForm) ^ 2 = 3 := by
    rw [← map_pow, hdelta, hC3]
  rw [orbitFirstConicPullback, orbitSecondConicPullback,
    orbitPolynomialPhi]
  simp only [map_sub, map_pow, orbitPolynomialS,
    orbitPolynomialLambda, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    orbitConicS, orbitConicLambda, orbitConicT, orbitConicZeta,
    orbitConicRho, orbitConicAlpha, orbitConicBeta,
    orbitParameterU, orbitParameterV]
  rw [hC2]
  ring_nf
  rw [hdeltaForm]
  ring

theorem orbitFirstConicPullback_psi
    {delta : ℂ} (hdelta : delta ^ 2 = 3) :
    orbitFirstConicPullback delta (orbitPolynomialPsi ℂ) =
      orbitSecondConicPullback delta (orbitPolynomialPsi ℂ) := by
  have hC2 : (MvPolynomial.C (2 : ℂ) : OrbitParameterForm) = 2 :=
    map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 2
  have hC3 : (MvPolynomial.C (3 : ℂ) : OrbitParameterForm) = 3 :=
    map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 3
  have hdeltaForm :
      (MvPolynomial.C delta : OrbitParameterForm) ^ 2 = 3 := by
    rw [← map_pow, hdelta, hC3]
  rw [orbitFirstConicPullback, orbitSecondConicPullback,
    orbitPolynomialPsi]
  simp only [map_sub, map_mul, map_pow, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, orbitPolynomialS,
    orbitPolynomialLambda, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    orbitConicS, orbitConicLambda, orbitConicT, orbitConicZeta,
    orbitConicRho, orbitConicAlpha, orbitConicBeta,
    orbitParameterU, orbitParameterV]
  rw [hC2, hC3]
  ring_nf
  rw [hdeltaForm]
  ring

/-- The two conic pullbacks agree on every polynomial in the orbit base. -/
theorem orbitConicPullbacks_base_eq
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    (S : OrbitBaseRing ℂ) :
    orbitFirstConicPullback delta (orbitBaseToSource ℂ S) =
      orbitSecondConicPullback delta (orbitBaseToSource ℂ S) := by
  let first : OrbitBaseRing ℂ →ₐ[ℂ] OrbitParameterForm :=
    (orbitFirstConicPullback delta).comp (orbitBaseToSource ℂ)
  let second : OrbitBaseRing ℂ →ₐ[ℂ] OrbitParameterForm :=
    (orbitSecondConicPullback delta).comp (orbitBaseToSource ℂ)
  have heq : first = second := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | phi =>
        simp only [first, second, AlgHom.comp_apply,
          orbitBaseToSource, MvPolynomial.aeval_X]
        exact orbitFirstConicPullback_phi hdelta
    | psi =>
        simp only [first, second, AlgHom.comp_apply,
          orbitBaseToSource, MvPolynomial.aeval_X]
        exact orbitFirstConicPullback_psi hdelta
  exact AlgHom.congr_fun heq S

theorem orbitConicDifference_eq_pullbacks
    (delta : ℂ) (R : OrbitPolynomial ℂ) :
    orbitConicDifference delta R =
      orbitFirstConicPullback delta R -
        orbitSecondConicPullback delta R := by
  rfl

theorem orbitConicDifference_base
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    (S : OrbitBaseRing ℂ) :
    orbitConicDifference delta (orbitBaseToSource ℂ S) = 0 := by
  rw [orbitConicDifference_eq_pullbacks,
    orbitConicPullbacks_base_eq hdelta, sub_self]

/-- Restriction of the first source coordinate to the parameter chart
`v=1`. -/
@[expose]
noncomputable def orbitFirstLineS : Polynomial ℂ :=
  -(Polynomial.X ^ 4 + 6 * Polynomial.X ^ 2 + 1)

/-- Restriction of the second source coordinate to the parameter chart
`v=1`. -/
@[expose]
noncomputable def orbitFirstLineLambda (delta : ℂ) : Polynomial ℂ :=
  Polynomial.C (2 * delta) * Polynomial.X * (Polynomial.X ^ 2 + 1)

/-- Restriction of a parameter form to the chart `v=1`. -/
@[expose]
noncomputable def orbitParameterLinePullback :
    OrbitParameterForm →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval ![Polynomial.X, 1]

theorem orbitParameterLinePullback_conicS :
    orbitParameterLinePullback orbitConicS = orbitFirstLineS := by
  rw [orbitParameterLinePullback, orbitConicS, orbitConicAlpha,
    orbitConicBeta, orbitParameterU, orbitParameterV]
  simp only [map_neg, map_add, map_pow, MvPolynomial.algHom_C,
    map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue]
  norm_num
  rw [orbitFirstLineS]
  simp only [Polynomial.C_ofNat]
  ring_nf

theorem orbitParameterLinePullback_conicLambda (delta : ℂ) :
    orbitParameterLinePullback (orbitConicLambda delta) =
      orbitFirstLineLambda delta := by
  rw [orbitParameterLinePullback, orbitConicLambda, orbitConicRho,
    orbitConicBeta, orbitParameterU, orbitParameterV]
  simp only [map_mul, map_add, map_pow, MvPolynomial.algHom_C,
    MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue]
  norm_num
  rw [orbitFirstLineLambda]
  simp only [Polynomial.C_ofNat, Polynomial.C_mul]
  ring_nf

/-- Pullback to the first source point followed by the chart `v=1`. -/
@[expose]
noncomputable def orbitFirstLinePullback (delta : ℂ) :
    OrbitPolynomial ℂ →ₐ[ℂ] Polynomial ℂ :=
  orbitParameterLinePullback.comp (orbitFirstConicPullback delta)

theorem orbitFirstLinePullback_eq_aeval (delta : ℂ) :
    orbitFirstLinePullback delta =
      MvPolynomial.aeval
        ![orbitFirstLineS, orbitFirstLineLambda delta] := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [orbitFirstLinePullback, orbitFirstConicPullback,
      orbitParameterLinePullback_conicS]
  · simp [orbitFirstLinePullback, orbitFirstConicPullback,
      orbitParameterLinePullback_conicLambda]

theorem orbitFirstLineS_natDegree : orbitFirstLineS.natDegree = 4 := by
  rw [orbitFirstLineS]
  compute_degree
  simp [Polynomial.coeff_one]

theorem orbitFirstLineS_ne_zero : orbitFirstLineS ≠ 0 := by
  have hdegree := orbitFirstLineS_natDegree
  intro hzero
  rw [hzero] at hdegree
  norm_num at hdegree

theorem orbitFirstLineLambda_natDegree
    {delta : ℂ} (hdelta : delta ≠ 0) :
    (orbitFirstLineLambda delta).natDegree = 3 := by
  rw [orbitFirstLineLambda]
  compute_degree
  · exact mul_ne_zero (by norm_num) hdelta
  · omega

theorem orbitFirstLineLambda_ne_zero
    {delta : ℂ} (hdelta : delta ≠ 0) :
    orbitFirstLineLambda delta ≠ 0 := by
  have hdegree := orbitFirstLineLambda_natDegree hdelta
  intro hzero
  rw [hzero] at hdegree
  norm_num at hdegree

/-- The ratio of the two source coordinates on the parameter line. -/
@[expose]
noncomputable def orbitFirstLineRatio (delta : ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) orbitFirstLineS /
    algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (orbitFirstLineLambda delta)

theorem orbitFirstLineRatio_ne_C
    {delta : ℂ} (hdelta : delta ≠ 0) :
    ¬ ∃ c : ℂ, orbitFirstLineRatio delta = RatFunc.C c := by
  rintro ⟨c, hc⟩
  have hLambda : orbitFirstLineLambda delta ≠ 0 :=
    orbitFirstLineLambda_ne_zero hdelta
  have hLambdaMap :
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (orbitFirstLineLambda delta) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hLambda
  have hcross :
      algebraMap (Polynomial ℂ) (RatFunc ℂ) orbitFirstLineS =
        RatFunc.C c *
          algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (orbitFirstLineLambda delta) := by
    exact (div_eq_iff hLambdaMap).mp hc
  have hconstant : RatFunc.C c =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) := by
    simp
  rw [hconstant, ← map_mul] at hcross
  have hpolynomial :
      orbitFirstLineS = Polynomial.C c * orbitFirstLineLambda delta :=
    IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) hcross
  have hleftDegree := orbitFirstLineS_natDegree
  have hLambdaDegree := orbitFirstLineLambda_natDegree hdelta
  have hrightDegree :
      (Polynomial.C c * orbitFirstLineLambda delta).natDegree ≤ 3 := by
    calc
      (Polynomial.C c * orbitFirstLineLambda delta).natDegree ≤
      (Polynomial.C c).natDegree +
            (orbitFirstLineLambda delta).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 3 := by
        rw [hLambdaDegree]
        simp
  rw [hpolynomial] at hleftDegree
  omega

theorem orbitFirstLineRatio_transcendental
    {delta : ℂ} (hdelta : delta ≠ 0) :
    Transcendental ℂ (orbitFirstLineRatio delta) :=
  RatFunc.transcendental_of_ne_C _ (orbitFirstLineRatio_ne_C hdelta)

/-- The first conic pullback is injective on each homogeneous component. -/
theorem eq_zero_of_orbitFirstConicPullback_eq_zero_of_isHomogeneous
    {delta : ℂ} (hdelta : delta ≠ 0)
    {R : OrbitPolynomial ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hzero : orbitFirstConicPullback delta R = 0) :
    R = 0 := by
  let p : Polynomial ℂ := orbitParameterDehomogenize R
  have hpDegree : p.natDegree ≤ N :=
    orbitParameterDehomogenize_natDegree_le hR
  have hhomogenize : p.homogenize N = R :=
    orbitParameter_homogenize_dehomogenize hR
  have hline : orbitFirstLinePullback delta R = 0 := by
    rw [orbitFirstLinePullback, AlgHom.comp_apply, hzero, map_zero]
  rw [orbitFirstLinePullback_eq_aeval] at hline
  let polynomialInclusion : ℂ[X] →+* RatFunc ℂ :=
    algebraMap (Polynomial ℂ) (RatFunc ℂ)
  let scalarInclusion : ℂ →+* RatFunc ℂ :=
    algebraMap ℂ (RatFunc ℂ)
  let sourceValues : Fin 2 → RatFunc ℂ :=
    ![polynomialInclusion orbitFirstLineS,
      polynomialInclusion (orbitFirstLineLambda delta)]
  have hlineEval₂ :
      MvPolynomial.eval₂ (algebraMap ℂ ℂ[X])
        ![orbitFirstLineS, orbitFirstLineLambda delta] R = 0 := by
    simpa [MvPolynomial.aeval_def] using hline
  have hscalar :
      polynomialInclusion.comp (algebraMap ℂ ℂ[X]) =
        scalarInclusion := by
    ext c
    simp [polynomialInclusion, scalarInclusion]
  have heval₂ :
      MvPolynomial.eval₂ scalarInclusion sourceValues R = 0 := by
    calc
      MvPolynomial.eval₂ scalarInclusion sourceValues R =
          polynomialInclusion
            (MvPolynomial.eval₂ (algebraMap ℂ ℂ[X])
              ![orbitFirstLineS, orbitFirstLineLambda delta] R) := by
        rw [← hscalar, MvPolynomial.hom_eval₂]
        congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
      _ = 0 := by rw [hlineEval₂, map_zero]
  have heval :
      MvPolynomial.eval sourceValues
        (MvPolynomial.map scalarInclusion R) = 0 := by
    rw [← MvPolynomial.eval₂_eq_eval_map]
    exact heval₂
  have hmapHomogenize :
      MvPolynomial.map scalarInclusion R =
        (p.map scalarInclusion).homogenize N := by
    rw [← hhomogenize, Polynomial.homogenize_map]
  rw [hmapHomogenize] at heval
  have hpMapDegree : (p.map scalarInclusion).natDegree ≤ N :=
    (Polynomial.natDegree_map_le.trans hpDegree)
  have hLambdaMap : sourceValues 1 ≠ 0 := by
    change polynomialInclusion (orbitFirstLineLambda delta) ≠ 0
    exact RatFunc.algebraMap_ne_zero (orbitFirstLineLambda_ne_zero hdelta)
  rw [Polynomial.eval_homogenize hpMapDegree sourceValues hLambdaMap] at heval
  have hpEval :
      (p.map scalarInclusion).eval (orbitFirstLineRatio delta) = 0 := by
    apply (mul_eq_zero.mp heval).resolve_right
    exact pow_ne_zero N hLambdaMap
  have hpAeval : Polynomial.aeval (orbitFirstLineRatio delta) p = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hpEval
  have hpzero : p = 0 :=
    (transcendental_iff.mp
      (orbitFirstLineRatio_transcendental hdelta)) p hpAeval
  rw [← hhomogenize, hpzero, Polynomial.homogenize_zero]

/-- Reflection of the second source coordinate. -/
@[expose]
noncomputable def orbitSourceLambdaReflection :
    OrbitPolynomial ℂ →ₐ[ℂ] OrbitPolynomial ℂ :=
  MvPolynomial.aeval
    ![orbitPolynomialS ℂ, -orbitPolynomialLambda ℂ]

/-- Negation of the first conic parameter. -/
@[expose]
noncomputable def orbitParameterNegFirst :
    OrbitParameterForm →ₐ[ℂ] OrbitParameterForm :=
  MvPolynomial.aeval ![-orbitParameterU, orbitParameterV]

/-- Multiplication of the first conic parameter by `i`. -/
@[expose]
noncomputable def orbitParameterQuarterFirst :
    OrbitParameterForm →ₐ[ℂ] OrbitParameterForm :=
  MvPolynomial.aeval
    ![MvPolynomial.C Complex.I * orbitParameterU, orbitParameterV]

/-- The third first coordinate in a fibre of the cubic orbit map. -/
@[expose]
noncomputable def orbitConicThird : OrbitParameterForm :=
  -(orbitConicS + orbitConicT)

theorem orbitSourceLambdaReflection_isHomogeneous
    {R : OrbitPolynomial ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    (orbitSourceLambdaReflection R).IsHomogeneous N := by
  have hsubstitution : ∀ i : Fin 2,
      MvPolynomial.IsHomogeneous
        (![orbitPolynomialS ℂ, -orbitPolynomialLambda ℂ] i) 1 := by
    intro i
    fin_cases i
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · simpa [orbitPolynomialLambda] using
        (MvPolynomial.isHomogeneous_X ℂ 1).neg
  simpa [orbitSourceLambdaReflection, Nat.one_mul] using
    hR.aeval ![orbitPolynomialS ℂ, -orbitPolynomialLambda ℂ]
      hsubstitution

@[simp]
theorem orbitSourceLambdaReflection_s :
    orbitSourceLambdaReflection (orbitPolynomialS ℂ) =
      orbitPolynomialS ℂ := by
  rw [orbitSourceLambdaReflection, orbitPolynomialS,
    MvPolynomial.aeval_X]
  rfl

@[simp]
theorem orbitSourceLambdaReflection_lambda :
    orbitSourceLambdaReflection (orbitPolynomialLambda ℂ) =
      -orbitPolynomialLambda ℂ := by
  rw [orbitSourceLambdaReflection, orbitPolynomialLambda,
    MvPolynomial.aeval_X]
  rfl

theorem orbitSourceLambdaReflection_phi :
    orbitSourceLambdaReflection (orbitPolynomialPhi ℂ) =
      orbitPolynomialPhi ℂ := by
  rw [orbitPolynomialPhi, map_sub, map_pow, map_pow,
    orbitSourceLambdaReflection_s, orbitSourceLambdaReflection_lambda]
  ring

theorem orbitSourceLambdaReflection_psi :
    orbitSourceLambdaReflection (orbitPolynomialPsi ℂ) =
      orbitPolynomialPsi ℂ := by
  have hC2 : orbitSourceLambdaReflection
      (MvPolynomial.C (2 : ℂ)) = MvPolynomial.C (2 : ℂ) :=
    orbitSourceLambdaReflection.commutes 2
  have hC3 : orbitSourceLambdaReflection
      (MvPolynomial.C (3 : ℂ)) = MvPolynomial.C (3 : ℂ) :=
    orbitSourceLambdaReflection.commutes 3
  rw [orbitPolynomialPsi, map_sub, map_mul, map_pow, map_mul,
    map_mul, map_pow, orbitSourceLambdaReflection_s,
    orbitSourceLambdaReflection_lambda, hC2, hC3]
  ring

theorem orbitSourceLambdaReflection_base (S : OrbitBaseRing ℂ) :
    orbitSourceLambdaReflection (orbitBaseToSource ℂ S) =
      orbitBaseToSource ℂ S := by
  let left : OrbitBaseRing ℂ →ₐ[ℂ] OrbitPolynomial ℂ :=
    orbitSourceLambdaReflection.comp (orbitBaseToSource ℂ)
  have heq : left = orbitBaseToSource ℂ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | phi =>
        simpa [left, orbitBaseToSource] using
          orbitSourceLambdaReflection_phi
    | psi =>
        simpa [left, orbitBaseToSource] using
          orbitSourceLambdaReflection_psi
  exact AlgHom.congr_fun heq S

/-- The part of a six term expression that is even in the second source
coordinate. -/
@[expose]
noncomputable def orbitSixTermEvenValue
    (c : Fin 6 → OrbitBaseRing ℂ) : OrbitPolynomial ℂ :=
  orbitBaseToSource ℂ (c 0) +
    orbitBaseToSource ℂ (c 1) * orbitPolynomialS ℂ +
    orbitBaseToSource ℂ (c 2) * orbitPolynomialS ℂ ^ 2

/-- The part of a six term expression that is odd in the second source
coordinate. -/
@[expose]
noncomputable def orbitSixTermOddValue
    (c : Fin 6 → OrbitBaseRing ℂ) : OrbitPolynomial ℂ :=
  orbitBaseToSource ℂ (c 3) * orbitPolynomialLambda ℂ +
    orbitBaseToSource ℂ (c 4) * orbitPolynomialS ℂ *
      orbitPolynomialLambda ℂ +
    orbitBaseToSource ℂ (c 5) * orbitPolynomialS ℂ ^ 2 *
      orbitPolynomialLambda ℂ

theorem orbitSixTermValue_eq_even_add_odd
    (c : Fin 6 → OrbitBaseRing ℂ) :
    orbitSixTermValue ℂ c =
      orbitSixTermEvenValue c + orbitSixTermOddValue c := by
  simp only [orbitSixTermValue, orbitSixTermEvenValue,
    orbitSixTermOddValue, orbitSixTerm, Fin.sum_univ_six,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, mul_one]
  ring

theorem orbitSourceLambdaReflection_even
    (c : Fin 6 → OrbitBaseRing ℂ) :
    orbitSourceLambdaReflection (orbitSixTermEvenValue c) =
      orbitSixTermEvenValue c := by
  rw [orbitSixTermEvenValue, map_add, map_add, map_mul, map_mul,
    map_pow, orbitSourceLambdaReflection_base,
    orbitSourceLambdaReflection_base, orbitSourceLambdaReflection_base,
    orbitSourceLambdaReflection_s]

theorem orbitSourceLambdaReflection_odd
    (c : Fin 6 → OrbitBaseRing ℂ) :
    orbitSourceLambdaReflection (orbitSixTermOddValue c) =
      -orbitSixTermOddValue c := by
  rw [orbitSixTermOddValue, map_add, map_add, map_mul, map_mul,
    map_mul, map_mul, map_mul, map_pow,
    orbitSourceLambdaReflection_base,
    orbitSourceLambdaReflection_base, orbitSourceLambdaReflection_base,
    orbitSourceLambdaReflection_s, orbitSourceLambdaReflection_lambda]
  ring

/-- A reflection invariant six term expression equals its even part. -/
theorem eq_orbitSixTermEvenValue_of_reflection_eq
    {R : OrbitPolynomial ℂ} (c : Fin 6 → OrbitBaseRing ℂ)
    (hc : R = orbitSixTermValue ℂ c)
    (hreflection : orbitSourceLambdaReflection R = R) :
    R = orbitSixTermEvenValue c := by
  have hvalue : orbitSourceLambdaReflection (orbitSixTermValue ℂ c) =
      orbitSixTermValue ℂ c := by
    rw [← hc, hreflection]
  rw [orbitSixTermValue_eq_even_add_odd, map_add,
    orbitSourceLambdaReflection_even, orbitSourceLambdaReflection_odd] at hvalue
  have hodd : orbitSixTermOddValue c = 0 := by
    have hneg : -orbitSixTermOddValue c = orbitSixTermOddValue c :=
      add_left_cancel hvalue
    have hadd : orbitSixTermOddValue c + orbitSixTermOddValue c = 0 := by
      calc
        orbitSixTermOddValue c + orbitSixTermOddValue c =
            -orbitSixTermOddValue c + orbitSixTermOddValue c :=
          congrArg (fun value ↦ value + orbitSixTermOddValue c) hneg.symm
        _ = 0 := neg_add_cancel (orbitSixTermOddValue c)
    exact add_self_eq_zero.mp hadd
  rw [hc, orbitSixTermValue_eq_even_add_odd, hodd, add_zero]

theorem orbitParameterNegFirst_conicS :
    orbitParameterNegFirst orbitConicS = orbitConicS := by
  rw [orbitParameterNegFirst, orbitConicS, orbitConicAlpha,
    orbitConicBeta, orbitParameterU, orbitParameterV]
  simp only [map_neg]
  norm_num

theorem orbitParameterNegFirst_conicLambda (delta : ℂ) :
    orbitParameterNegFirst (orbitConicLambda delta) =
      -orbitConicLambda delta := by
  rw [orbitParameterNegFirst, orbitConicLambda, orbitConicRho,
    orbitConicBeta, orbitParameterU, orbitParameterV]
  simp only [map_mul, map_add, map_pow,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  norm_num

theorem orbitParameterNegFirst_conicT :
    orbitParameterNegFirst orbitConicT = orbitConicT := by
  rw [orbitParameterNegFirst, orbitConicT, orbitConicAlpha,
    orbitConicBeta, orbitParameterU, orbitParameterV]
  simp only [map_add, map_sub, map_pow, map_mul,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  norm_num

theorem orbitParameterNegFirst_conicZeta (delta : ℂ) :
    orbitParameterNegFirst (orbitConicZeta delta) =
      orbitConicZeta delta := by
  rw [orbitParameterNegFirst, orbitConicZeta, orbitConicRho,
    orbitConicAlpha, orbitParameterU, orbitParameterV]
  simp only [map_mul, map_add, map_sub, map_pow,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  norm_num

theorem orbitParameterQuarterFirst_conicS :
    orbitParameterQuarterFirst orbitConicS = orbitConicThird := by
  have hI : (MvPolynomial.C Complex.I : OrbitParameterForm) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    simp
  have hC2 : (MvPolynomial.C (2 : ℂ) : OrbitParameterForm) = 2 :=
    map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 2
  rw [orbitParameterQuarterFirst, orbitConicThird, orbitConicS,
    orbitConicT, orbitConicAlpha, orbitConicBeta, orbitParameterU,
    orbitParameterV]
  simp only [map_neg, map_add, map_sub, map_pow, map_mul,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [hC2]
  simp only [mul_pow, hI]
  ring

theorem orbitParameterQuarterFirst_conicT :
    orbitParameterQuarterFirst orbitConicT = orbitConicT := by
  have hI : (MvPolynomial.C Complex.I : OrbitParameterForm) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    simp
  have hC2 : (MvPolynomial.C (2 : ℂ) : OrbitParameterForm) = 2 :=
    map_ofNat (MvPolynomial.C : ℂ →+* OrbitParameterForm) 2
  rw [orbitParameterQuarterFirst, orbitConicT, orbitConicAlpha,
    orbitConicBeta, orbitParameterU, orbitParameterV]
  simp only [map_add, map_sub, map_pow, map_mul,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [hC2]
  simp only [mul_pow, hI]
  ring

theorem orbitParameterQuarterFirst_conicZeta (delta : ℂ) :
    orbitParameterQuarterFirst (orbitConicZeta delta) =
      orbitConicZeta delta := by
  have hI : (MvPolynomial.C Complex.I : OrbitParameterForm) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    simp
  rw [orbitParameterQuarterFirst, orbitConicZeta, orbitConicRho,
    orbitConicAlpha, orbitParameterU, orbitParameterV]
  simp only [map_mul, map_add, map_sub, map_pow,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  simp only [mul_pow, hI]
  ring

theorem orbitParameterQuarterFirst_secondPullback (delta : ℂ)
    (R : OrbitPolynomial ℂ) :
    orbitParameterQuarterFirst (orbitSecondConicPullback delta R) =
      orbitSecondConicPullback delta R := by
  let left : OrbitPolynomial ℂ →ₐ[ℂ] OrbitParameterForm :=
    orbitParameterQuarterFirst.comp (orbitSecondConicPullback delta)
  have heq : left = orbitSecondConicPullback delta := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simpa [left, orbitSecondConicPullback] using
        orbitParameterQuarterFirst_conicT
    · simpa [left, orbitSecondConicPullback] using
        orbitParameterQuarterFirst_conicZeta delta
  exact AlgHom.congr_fun heq R

theorem orbitParameterQuarterFirst_firstBase
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    (S : OrbitBaseRing ℂ) :
    orbitParameterQuarterFirst
        (orbitFirstConicPullback delta (orbitBaseToSource ℂ S)) =
      orbitFirstConicPullback delta (orbitBaseToSource ℂ S) := by
  have hpullbacks := orbitConicPullbacks_base_eq hdelta S
  calc
    orbitParameterQuarterFirst
        (orbitFirstConicPullback delta (orbitBaseToSource ℂ S)) =
        orbitParameterQuarterFirst
          (orbitSecondConicPullback delta (orbitBaseToSource ℂ S)) :=
      congrArg orbitParameterQuarterFirst hpullbacks
    _ = orbitSecondConicPullback delta (orbitBaseToSource ℂ S) :=
      orbitParameterQuarterFirst_secondPullback delta _
    _ = orbitFirstConicPullback delta (orbitBaseToSource ℂ S) :=
      hpullbacks.symm

theorem orbitConicS_sub_T_ne_zero : orbitConicS - orbitConicT ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(1 : ℂ), 0]) hzero
  norm_num [orbitConicS, orbitConicT, orbitConicAlpha,
    orbitConicBeta, orbitParameterU, orbitParameterV] at heval

theorem orbitConicThird_sub_T_ne_zero :
    orbitConicThird - orbitConicT ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(1 : ℂ), 0]) hzero
  norm_num [orbitConicThird, orbitConicS, orbitConicT,
    orbitConicAlpha, orbitConicBeta, orbitParameterU,
    orbitParameterV] at heval

theorem orbitConicS_sub_third_ne_zero :
    orbitConicS - orbitConicThird ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(1 : ℂ), 1]) hzero
  norm_num [orbitConicThird, orbitConicS, orbitConicT,
    orbitConicAlpha, orbitConicBeta, orbitParameterU,
    orbitParameterV] at heval

private theorem orbitParameterNegFirst_firstPullbackAux (delta : ℂ)
    (R : OrbitPolynomial ℂ) :
    orbitParameterNegFirst (orbitFirstConicPullback delta R) =
      orbitFirstConicPullback delta (orbitSourceLambdaReflection R) := by
  let left : OrbitPolynomial ℂ →ₐ[ℂ] OrbitParameterForm :=
    orbitParameterNegFirst.comp (orbitFirstConicPullback delta)
  let right : OrbitPolynomial ℂ →ₐ[ℂ] OrbitParameterForm :=
    (orbitFirstConicPullback delta).comp orbitSourceLambdaReflection
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · dsimp only [left, right, AlgHom.comp_apply]
      simpa [orbitFirstConicPullback, orbitSourceLambdaReflection,
        orbitPolynomialS] using
        orbitParameterNegFirst_conicS
    · dsimp only [left, right, AlgHom.comp_apply]
      simpa [orbitFirstConicPullback, orbitSourceLambdaReflection,
        orbitPolynomialLambda] using
        orbitParameterNegFirst_conicLambda delta
  exact AlgHom.congr_fun heq R

private theorem orbitParameterNegFirst_secondPullbackAux (delta : ℂ)
    (R : OrbitPolynomial ℂ) :
    orbitParameterNegFirst (orbitSecondConicPullback delta R) =
      orbitSecondConicPullback delta R := by
  let left : OrbitPolynomial ℂ →ₐ[ℂ] OrbitParameterForm :=
    orbitParameterNegFirst.comp (orbitSecondConicPullback delta)
  have heq : left = orbitSecondConicPullback delta := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simpa [left, orbitSecondConicPullback] using
        orbitParameterNegFirst_conicT
    · simpa [left, orbitSecondConicPullback] using
        orbitParameterNegFirst_conicZeta delta
  exact AlgHom.congr_fun heq R

private theorem orbitSourceLambdaReflectionEqAux
    {delta : ℂ} (hdelta : delta ≠ 0)
    {R : OrbitPolynomial ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hzero : orbitConicDifference delta R = 0) :
    orbitSourceLambdaReflection R = R := by
  have hpullback : orbitFirstConicPullback delta R =
      orbitSecondConicPullback delta R := by
    rw [orbitConicDifference_eq_pullbacks] at hzero
    exact sub_eq_zero.mp hzero
  have htransformed := congrArg orbitParameterNegFirst hpullback
  rw [orbitParameterNegFirst_firstPullbackAux,
    orbitParameterNegFirst_secondPullbackAux] at htransformed
  have hkernel : orbitFirstConicPullback delta
      (orbitSourceLambdaReflection R - R) = 0 := by
    rw [map_sub, htransformed, ← hpullback, sub_self]
  have hhomogeneous :
      (orbitSourceLambdaReflection R - R).IsHomogeneous N :=
    (orbitSourceLambdaReflection_isHomogeneous hR).sub hR
  have := eq_zero_of_orbitFirstConicPullback_eq_zero_of_isHomogeneous
    hdelta hhomogeneous hkernel
  exact sub_eq_zero.mp this

/-- A homogeneous source form whose two pullbacks agree on the residual
conic belongs to the orbit base ring. -/
theorem orbitConicDifference_eq_zero_mem_base_of_isHomogeneous
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitPolynomial ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hzero : orbitConicDifference delta R = 0) :
    R ∈ Set.range (orbitBaseToSource ℂ) := by
  have hdeltaNe : delta ≠ 0 := by
    intro hzeroDelta
    rw [hzeroDelta] at hdelta
    norm_num at hdelta
  obtain ⟨c, hc, hcHomogeneous, _⟩ :=
    exists_homogeneous_orbitSixTermValue R N hR
  have hreflection :=
    orbitSourceLambdaReflectionEqAux hdeltaNe hR hzero
  have heven : R = orbitSixTermEvenValue c :=
    eq_orbitSixTermEvenValue_of_reflection_eq c hc hreflection
  let b : Fin 6 → OrbitParameterForm := fun i ↦
    orbitFirstConicPullback delta (orbitBaseToSource ℂ (c i))
  have hpullback : orbitFirstConicPullback delta R =
      orbitSecondConicPullback delta R := by
    rw [orbitConicDifference_eq_pullbacks] at hzero
    exact sub_eq_zero.mp hzero
  have hfirst : orbitFirstConicPullback delta R =
      b 0 + b 1 * orbitConicS + b 2 * orbitConicS ^ 2 := by
    rw [heven, orbitSixTermEvenValue, map_add, map_add, map_mul,
      map_mul, map_pow]
    simp only [b, orbitFirstConicPullback, orbitPolynomialS,
      MvPolynomial.aeval_X, Matrix.cons_val_zero, Fin.isValue]
  have hsecond : orbitSecondConicPullback delta R =
      b 0 + b 1 * orbitConicT + b 2 * orbitConicT ^ 2 := by
    rw [heven, orbitSixTermEvenValue, map_add, map_add, map_mul,
      map_mul, map_pow]
    rw [← orbitConicPullbacks_base_eq hdelta (c 0),
      ← orbitConicPullbacks_base_eq hdelta (c 1),
      ← orbitConicPullbacks_base_eq hdelta (c 2)]
    simp only [b, orbitSecondConicPullback, orbitPolynomialS,
      MvPolynomial.aeval_X, Matrix.cons_val_zero, Fin.isValue]
  have hequalityST :
      b 0 + b 1 * orbitConicS + b 2 * orbitConicS ^ 2 =
        b 0 + b 1 * orbitConicT + b 2 * orbitConicT ^ 2 :=
    hfirst.symm.trans (hpullback.trans hsecond)
  have hrelationST :
      b 1 + b 2 * (orbitConicS + orbitConicT) = 0 := by
    have hfactor :
        (orbitConicS - orbitConicT) *
          (b 1 + b 2 * (orbitConicS + orbitConicT)) = 0 := by
      linear_combination hequalityST
    exact (mul_eq_zero.mp hfactor).resolve_left orbitConicS_sub_T_ne_zero
  have hpullbackQuarter := congrArg orbitParameterQuarterFirst hpullback
  rw [orbitParameterQuarterFirst_secondPullback] at hpullbackQuarter
  have hquarterFirst :
      orbitParameterQuarterFirst (orbitFirstConicPullback delta R) =
        b 0 + b 1 * orbitConicThird + b 2 * orbitConicThird ^ 2 := by
    rw [hfirst, map_add, map_add, map_mul, map_mul, map_pow]
    dsimp only [b]
    rw [orbitParameterQuarterFirst_firstBase hdelta,
      orbitParameterQuarterFirst_firstBase hdelta,
      orbitParameterQuarterFirst_firstBase hdelta,
      orbitParameterQuarterFirst_conicS]
  have hequalityWT :
      b 0 + b 1 * orbitConicThird + b 2 * orbitConicThird ^ 2 =
        b 0 + b 1 * orbitConicT + b 2 * orbitConicT ^ 2 :=
    hquarterFirst.symm.trans (hpullbackQuarter.trans hsecond)
  have hrelationWT :
      b 1 + b 2 * (orbitConicThird + orbitConicT) = 0 := by
    have hfactor :
        (orbitConicThird - orbitConicT) *
          (b 1 + b 2 * (orbitConicThird + orbitConicT)) = 0 := by
      linear_combination hequalityWT
    exact (mul_eq_zero.mp hfactor).resolve_left
      orbitConicThird_sub_T_ne_zero
  have hcoefficientTwoFactor :
      b 2 * (orbitConicS - orbitConicThird) = 0 := by
    linear_combination hrelationST - hrelationWT
  have hb2 : b 2 = 0 :=
    (mul_eq_zero.mp hcoefficientTwoFactor).resolve_right
      orbitConicS_sub_third_ne_zero
  have hb1 : b 1 = 0 := by
    rw [hb2, zero_mul, add_zero] at hrelationST
    exact hrelationST
  have hsourceOneHomogeneous :
      (orbitBaseToSource ℂ (c 1)).IsHomogeneous
        (N - orbitSixTermDegree 1) := by
    change MvPolynomial.IsWeightedHomogeneous (1 : Fin 2 → ℕ)
      (orbitBaseToSource ℂ (c 1)) (N - orbitSixTermDegree 1)
    exact orbitBaseToSource_isHomogeneous (hcHomogeneous 1)
  have hsourceTwoHomogeneous :
      (orbitBaseToSource ℂ (c 2)).IsHomogeneous
        (N - orbitSixTermDegree 2) := by
    change MvPolynomial.IsWeightedHomogeneous (1 : Fin 2 → ℕ)
      (orbitBaseToSource ℂ (c 2)) (N - orbitSixTermDegree 2)
    exact orbitBaseToSource_isHomogeneous (hcHomogeneous 2)
  have hsourceOne : orbitBaseToSource ℂ (c 1) = 0 :=
    eq_zero_of_orbitFirstConicPullback_eq_zero_of_isHomogeneous
      hdeltaNe hsourceOneHomogeneous (by simpa [b] using hb1)
  have hsourceTwo : orbitBaseToSource ℂ (c 2) = 0 :=
    eq_zero_of_orbitFirstConicPullback_eq_zero_of_isHomogeneous
      hdeltaNe hsourceTwoHomogeneous (by simpa [b] using hb2)
  refine ⟨c 0, ?_⟩
  rw [heven, orbitSixTermEvenValue, hsourceOne, hsourceTwo]
  simp

theorem orbitParameterNegFirst_firstPullback (delta : ℂ)
    (R : OrbitPolynomial ℂ) :
    orbitParameterNegFirst (orbitFirstConicPullback delta R) =
      orbitFirstConicPullback delta (orbitSourceLambdaReflection R) :=
  orbitParameterNegFirst_firstPullbackAux delta R

theorem orbitParameterNegFirst_secondPullback (delta : ℂ)
    (R : OrbitPolynomial ℂ) :
    orbitParameterNegFirst (orbitSecondConicPullback delta R) =
      orbitSecondConicPullback delta R :=
  orbitParameterNegFirst_secondPullbackAux delta R

/-- Equality on the residual conic forces invariance under reflection of
the second source coordinate. -/
theorem orbitSourceLambdaReflection_eq_of_conicDifference_eq_zero
    {delta : ℂ} (hdelta : delta ≠ 0)
    {R : OrbitPolynomial ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hzero : orbitConicDifference delta R = 0) :
    orbitSourceLambdaReflection R = R :=
  orbitSourceLambdaReflectionEqAux hdelta hR hzero

end OnLeConjecture.DTwo
