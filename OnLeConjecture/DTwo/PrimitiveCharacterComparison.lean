/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.ResidualPreparedAnalyticInterface

/-!
# The primitive character comparison in order two

This file extracts the algebraic conclusions of the primitive component
comparison. Weighted homogeneity determines the coefficient formula of the
prepared polynomial. The component identity then determines the primitive
character.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open scoped Polynomial.Bivariate
open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- The exponent vector of the term `x^(N - 2h) T^h`. -/
@[expose]
noncomputable def preparedExponent (N h : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (N - 2 * h) + Finsupp.single 1 h

/-- The coefficients of a polynomial in the prepared weighted basis. -/
@[expose]
noncomputable def preparedCoefficient
    (N : ℕ) (P : MvPolynomial (Fin 2) ℂ) (h : ℕ) : ℂ :=
  MvPolynomial.coeff (preparedExponent N h) P

private theorem preparedExponent_injective_right
    {N h l : ℕ} (heq : preparedExponent N h = preparedExponent N l) :
    h = l := by
  have := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) heq
  simpa [preparedExponent] using this

private theorem preparedOddBivariatePolynomial_eq_sum_monomial
    (N : ℕ) (alpha : ℕ → ℂ) :
    preparedOddBivariatePolynomial N alpha =
      ∑ h ∈ Finset.range (N / 2 + 1),
        MvPolynomial.monomial (preparedExponent N h) (alpha h) := by
  classical
  apply Finset.sum_congr rfl
  intro h hh
  rw [MvPolynomial.C_mul_X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]
  rfl

private theorem coeff_preparedOddBivariatePolynomial_preparedExponent
    (N : ℕ) (alpha : ℕ → ℂ) {h : ℕ} (hh : h ≤ N / 2) :
    MvPolynomial.coeff (preparedExponent N h)
        (preparedOddBivariatePolynomial N alpha) = alpha h := by
  classical
  rw [preparedOddBivariatePolynomial_eq_sum_monomial]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single h]
  · simp
  · intro l hl hne
    simp only [ite_eq_right_iff]
    intro heq
    exact (hne (preparedExponent_injective_right heq)).elim
  · simp [hh]

/-- Every polynomial of weights `(1,2)` and degree `N` has the prepared
coefficient formula. -/
theorem eq_preparedOddBivariatePolynomial_of_isWeightedHomogeneous
    {N : ℕ} {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsWeightedHomogeneous ![1, 2] N) :
    P = preparedOddBivariatePolynomial N (preparedCoefficient N P) := by
  classical
  ext d
  by_cases hweight : Finsupp.weight ![1, 2] d = N
  · have hv : d 1 ≤ N / 2 := by
      have : d 0 + 2 * d 1 = N := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using
          hweight
      omega
    have hd : d = preparedExponent N (d 1) := by
      ext i
      fin_cases i
      · have : d 0 + 2 * d 1 = N := by
          simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using
            hweight
        simp [preparedExponent]
        omega
      · simp [preparedExponent]
    rw [hd]
    rw [coeff_preparedOddBivariatePolynomial_preparedExponent N
      (preparedCoefficient N P) hv]
    rfl
  · have hleft : MvPolynomial.coeff d P = 0 :=
      hP.coeff_eq_zero d hweight
    rw [hleft]
    symm
    apply MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero
      (preparedOddBivariatePolynomial_isWeightedHomogeneous N
        (preparedCoefficient N P)) d
    exact hweight

/-- A bivariate model of a prepared family determines its complete
coefficient formula. -/
theorem PreparedOddFamily.coefficientFormula_of_bivariateModel
    {N : ℕ} {Psi : PreparedOddFamily N} (model : Psi.BivariateModel) :
    ∀ T,
      Psi.polynomial T =
        ∑ h ∈ Finset.range (N / 2 + 1),
          C (preparedCoefficient N model.polynomial h * T ^ h) *
            X ^ (N - 2 * h) := by
  intro T
  let alpha := preparedCoefficient N model.polynomial
  have hpolynomial :
      model.polynomial = preparedOddBivariatePolynomial N alpha :=
    eq_preparedOddBivariatePolynomial_of_isWeightedHomogeneous
      model.weightedHomogeneous
  calc
    Psi.polynomial T = parameterSpecialization model.polynomial T :=
      model.specialization T
    _ = parameterSpecialization
        (preparedOddBivariatePolynomial N alpha) T := by rw [hpolynomial]
    _ = ∑ h ∈ Finset.range (N / 2 + 1),
        C (alpha h * T ^ h) * X ^ (N - 2 * h) :=
      parameterSpecialization_preparedOddBivariatePolynomial N alpha T

/-- The prepared polynomial in the component coordinates `x,T`. -/
@[expose]
noncomputable def preparedComponentPolynomial
    (N : ℕ) (alpha : ℕ → ℂ) : EqualizerBaseRing :=
  ∑ h ∈ Finset.range (N / 2 + 1),
    C (C (alpha h) * X ^ h) * X ^ (N - 2 * h)

/-- The parameter substitution into the polynomial ring of a ratio chart. -/
noncomputable def ratioParameter (chi : ℂ) : Polynomial ℂ :=
  C (1 - chi)⁻¹ * X

/-- The source coordinate in the chart `Sigma = q Delta`, with `Delta=1`. -/
noncomputable def differenceSourceCoordinate : Polynomial ℂ :=
  C (1 / 2) * (X - 1)

/-- The component coordinate in the chart `Sigma = q Delta`, with
`Delta=1`. -/
noncomputable def differenceComponentCoordinate : Polynomial ℂ :=
  C (1 / 2) * (X + 1)

/-- Evaluation of the component base ring in the second ratio chart. -/
noncomputable def differenceRatioBase (chi : ℂ) :
    EqualizerBaseRing →ₐ[ℂ] Polynomial ℂ :=
  Polynomial.aevalAeval (ratioParameter chi) differenceSourceCoordinate

private theorem differenceRatioBase_outer (chi : ℂ) :
    differenceRatioBase chi (X : EqualizerBaseRing) =
      differenceSourceCoordinate := by
  simp [differenceRatioBase]

private theorem differenceRatioBase_parameter (chi : ℂ) :
    differenceRatioBase chi (C X) = ratioParameter chi := by
  simp [differenceRatioBase]

private theorem differenceRatioBase_constant (chi z : ℂ) :
    differenceRatioBase chi (C (C z)) = C z := by
  simp [differenceRatioBase]

private theorem componentPolynomial_differenceRatio_eq_zero
    {chi : ℂ} (hchi : chi ≠ 1) :
    (componentPolynomial chi).eval₂ (differenceRatioBase chi)
      differenceComponentCoordinate = 0 := by
  have hdenominator : 1 - chi ≠ 0 := sub_ne_zero.mpr hchi.symm
  rw [componentPolynomial_eq, _root_.Polynomial.eval₂_sub,
    _root_.Polynomial.eval₂_pow, _root_.Polynomial.eval₂_X,
    _root_.Polynomial.eval₂_C, componentSquare_eq]
  simp only [map_sub, map_one, map_mul, RingHom.coe_coe, map_add, map_pow]
  rw [differenceRatioBase_outer, differenceRatioBase_constant,
    differenceRatioBase_parameter]
  have hscalar :
      (1 / 2 : ℂ) ^ 2 * 4 + chi * (1 - chi)⁻¹ - (1 - chi)⁻¹ = 0 := by
    field_simp [hdenominator]
    ring
  have hfour : (4 : Polynomial ℂ) = C (4 : ℂ) :=
    (C_eq_natCast 4).symm
  calc
    differenceComponentCoordinate ^ 2 -
          (differenceSourceCoordinate ^ 2 +
            (1 - C chi) * ratioParameter chi) =
        C (1 / 2) ^ 2 * X * 4 + X * C chi * C (1 - chi)⁻¹ -
          X * C (1 - chi)⁻¹ := by
            rw [differenceComponentCoordinate,
              differenceSourceCoordinate, ratioParameter]
            ring
    _ =
        C ((1 / 2 : ℂ) ^ 2 * 4 + chi * (1 - chi)⁻¹ -
          (1 - chi)⁻¹) * X := by
            simp only [map_sub, map_add, map_mul, map_pow]
            norm_num
            rw [hfour]
            ring
    _ = 0 := by rw [hscalar]; simp

/-- Evaluation of the quadratic component in the second ratio chart. -/
noncomputable def differenceRatioComponent
    (chi : ℂ) (hchi : chi ≠ 1) :
    EqualizerComponentRing chi →ₐ[ℂ] Polynomial ℂ :=
  AdjoinRoot.liftAlgHom (componentPolynomial chi) (differenceRatioBase chi)
    differenceComponentCoordinate
      (componentPolynomial_differenceRatio_eq_zero hchi)

private theorem differenceRatioComponent_algebraMap
    {chi : ℂ} (hchi : chi ≠ 1) (H : EqualizerBaseRing) :
    differenceRatioComponent chi hchi
        (algebraMap EqualizerBaseRing (EqualizerComponentRing chi) H) =
      differenceRatioBase chi H := by
  change differenceRatioComponent chi hchi
      (AdjoinRoot.of (componentPolynomial chi) H) = _
  rw [differenceRatioComponent, AdjoinRoot.liftAlgHom_of]

private theorem differenceRatioComponent_root
    {chi : ℂ} (hchi : chi ≠ 1) :
    differenceRatioComponent chi hchi
        (AdjoinRoot.root (componentPolynomial chi)) =
      differenceComponentCoordinate := by
  rw [differenceRatioComponent, AdjoinRoot.liftAlgHom_root]

private theorem differenceRatioComponent_sectorValue
    {chi : ℂ} (hchi : chi ≠ 1) (H : EqualizerBaseRing) :
    differenceRatioComponent chi hchi (componentSectorValue chi H) =
      Polynomial.aevalAeval
        (C chi * ratioParameter chi) differenceComponentCoordinate H := by
  rw [componentSectorValue_eq, differenceRatioComponent,
    AdjoinRoot.liftAlgHom_mk]
  induction H using _root_.Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp [hP, hQ]
  | monomial n a =>
      simp only [map_monomial, scaleEqualizerParameter_apply,
        _root_.Polynomial.eval₂_monomial, RingHom.coe_coe,
        _root_.Polynomial.aevalAevalEquiv_apply_apply,
        _root_.Polynomial.aeval_monomial, algebraMap_def, algebraMap_eq,
        _root_.Polynomial.coe_mapRingHom, _root_.Polynomial.eval_mul,
        _root_.Polynomial.eval_pow, _root_.Polynomial.eval_C,
        mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
      left
      rw [differenceRatioBase, _root_.Polynomial.aevalAeval_C]
      change (a.comp (C chi * X)).eval₂ C (ratioParameter chi) =
        (a.map C).eval (C chi * ratioParameter chi)
      rw [_root_.Polynomial.eval₂_eq_eval_map,
        _root_.Polynomial.map_comp, _root_.Polynomial.eval_comp]
      simp

/-- The nonzero component identity obtained from the primitive node
comparison. -/
def PreparedPrimitiveComponentIdentity
    (N : ℕ) (chi c : ℂ) (alpha : ℕ → ℂ) : Prop :=
  algebraMap EqualizerBaseRing (EqualizerComponentRing chi)
        (preparedComponentPolynomial N alpha) -
      componentSectorValue chi (preparedComponentPolynomial N alpha) =
    algebraMap ℂ (EqualizerComponentRing chi) c *
      (algebraMap EqualizerBaseRing (EqualizerComponentRing chi) X -
        AdjoinRoot.root (componentPolynomial chi)) ^ N

/-- The defining equation, available to constructors in other modules. -/
theorem preparedPrimitiveComponentIdentity_iff (N : ℕ) (chi c : ℂ) (alpha : ℕ → ℂ) :
    PreparedPrimitiveComponentIdentity N chi c alpha ↔
      algebraMap EqualizerBaseRing (EqualizerComponentRing chi)
          (preparedComponentPolynomial N alpha) -
        componentSectorValue chi (preparedComponentPolynomial N alpha) =
      algebraMap ℂ (EqualizerComponentRing chi) c *
        (algebraMap EqualizerBaseRing (EqualizerComponentRing chi) X -
          AdjoinRoot.root (componentPolynomial chi)) ^ N := Iff.rfl

private theorem differenceRatioBase_preparedComponentPolynomial
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) :
    differenceRatioBase chi (preparedComponentPolynomial N alpha) =
      ∑ h ∈ Finset.range (N / 2 + 1),
        C (alpha h) * ratioParameter chi ^ h *
          differenceSourceCoordinate ^ (N - 2 * h) := by
  classical
  simp [preparedComponentPolynomial, differenceRatioBase]

private theorem differenceSector_preparedComponentPolynomial
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) :
    Polynomial.aevalAeval (C chi * ratioParameter chi)
        differenceComponentCoordinate
        (preparedComponentPolynomial N alpha) =
      ∑ h ∈ Finset.range (N / 2 + 1),
        C (alpha h) * (C chi * ratioParameter chi) ^ h *
          differenceComponentCoordinate ^ (N - 2 * h) := by
  classical
  simp [preparedComponentPolynomial]

private theorem differenceRatioIdentity_of_componentIdentity
    {N : ℕ} {chi c : ℂ} {alpha : ℕ → ℂ}
    (hchi : chi ≠ 1)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c alpha) :
    differenceRatioBase chi (preparedComponentPolynomial N alpha) -
        Polynomial.aevalAeval (C chi * ratioParameter chi)
          differenceComponentCoordinate (preparedComponentPolynomial N alpha) =
      C c *
        (differenceSourceCoordinate - differenceComponentCoordinate) ^ N := by
  have hmapped := congrArg (differenceRatioComponent chi hchi) hidentity
  rw [map_sub, differenceRatioComponent_algebraMap,
    differenceRatioComponent_sectorValue, map_mul, map_pow, map_sub,
    differenceRatioComponent_algebraMap,
    differenceRatioComponent_root] at hmapped
  simpa [differenceRatioBase, differenceSourceCoordinate] using hmapped

private theorem derivative_eval_zero_constant_mul_linear_mul_pow
    (a r : ℂ) (Q : Polynomial ℂ) (m : ℕ) :
    (C a * (C r * X) * Q ^ m).derivative.eval 0 =
      a * r * Q.eval 0 ^ m := by
  simp [_root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_pow]

private theorem derivative_eval_zero_constant_mul_linear_pow_mul_pow
    (a r : ℂ) (Q : Polynomial ℂ) {h m : ℕ} (hh : 2 ≤ h) :
    (C a * (C r * X) ^ h * Q ^ m).derivative.eval 0 = 0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hh
  simp [_root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_pow]

/-- The contribution of one prepared monomial to the second ratio
comparison. -/
@[expose]
noncomputable def differenceRatioTerm
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) (h : ℕ) : Polynomial ℂ :=
  C (alpha h) * ratioParameter chi ^ h *
      differenceSourceCoordinate ^ (N - 2 * h) -
    C (alpha h) * (C chi * ratioParameter chi) ^ h *
      differenceComponentCoordinate ^ (N - 2 * h)

private theorem differenceRatioTerm_derivative_zero_of_two_le
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) {h : ℕ} (hh : 2 ≤ h) :
    (differenceRatioTerm N chi alpha h).derivative.eval 0 = 0 := by
  rw [differenceRatioTerm, _root_.Polynomial.derivative_sub,
    _root_.Polynomial.eval_sub]
  have hsource := derivative_eval_zero_constant_mul_linear_pow_mul_pow
    (alpha h) (1 - chi)⁻¹ differenceSourceCoordinate hh
      (m := N - 2 * h)
  have hsector := derivative_eval_zero_constant_mul_linear_pow_mul_pow
    (alpha h) (chi * (1 - chi)⁻¹) differenceComponentCoordinate hh
      (m := N - 2 * h)
  simpa [ratioParameter, map_mul, mul_assoc] using
    congrArg₂ (fun x y : ℂ ↦ x - y) hsource hsector

private theorem differenceRatioTerm_derivative_zero
    {N : ℕ} (hNodd : Odd N) (chi : ℂ) (alpha : ℕ → ℂ) :
    (differenceRatioTerm N chi alpha 0).derivative.eval 0 = 0 := by
  have heven : Even (N - 1) := by
    obtain ⟨m, hm⟩ := hNodd
    refine ⟨m, ?_⟩
    omega
  have hscalar :
      alpha 0 * ((N : ℂ) * (-2⁻¹ : ℂ) ^ (N - 1) * 2⁻¹) -
        alpha 0 * ((N : ℂ) * (2⁻¹ : ℂ) ^ (N - 1) * 2⁻¹) = 0 := by
    rw [heven.neg_pow]
    ring
  simpa [differenceRatioTerm, differenceSourceCoordinate,
    differenceComponentCoordinate, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_pow, inv_pow] using hscalar

private theorem differenceRatioTerm_derivative_one
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) :
    (differenceRatioTerm N chi alpha 1).derivative.eval 0 =
      alpha 1 * (1 - chi)⁻¹ * (-2⁻¹ : ℂ) ^ (N - 2) -
        alpha 1 * (chi * (1 - chi)⁻¹) * (2⁻¹ : ℂ) ^ (N - 2) := by
  rw [differenceRatioTerm, _root_.Polynomial.derivative_sub,
    _root_.Polynomial.eval_sub]
  have hsource := derivative_eval_zero_constant_mul_linear_mul_pow
    (alpha 1) (1 - chi)⁻¹ differenceSourceCoordinate (N - 2)
  have hsector := derivative_eval_zero_constant_mul_linear_mul_pow
    (alpha 1) (chi * (1 - chi)⁻¹) differenceComponentCoordinate (N - 2)
  have hsource' :
      (C (alpha 1) * ratioParameter chi *
          differenceSourceCoordinate ^ (N - 2)).derivative.eval 0 =
        alpha 1 * (1 - chi)⁻¹ * (-2⁻¹ : ℂ) ^ (N - 2) := by
    calc
      _ = alpha 1 * (1 - chi)⁻¹ *
          differenceSourceCoordinate.eval 0 ^ (N - 2) := by
        rw [ratioParameter]
        exact hsource
      _ = _ := by simp [differenceSourceCoordinate]
  have hsector' :
      (C (alpha 1) * (C chi * ratioParameter chi) *
          differenceComponentCoordinate ^ (N - 2)).derivative.eval 0 =
        alpha 1 * (chi * (1 - chi)⁻¹) * (2⁻¹ : ℂ) ^ (N - 2) := by
    calc
      _ = alpha 1 * (chi * (1 - chi)⁻¹) *
          differenceComponentCoordinate.eval 0 ^ (N - 2) := by
        have hlinear :
            C chi * (C (1 - chi)⁻¹ * X) =
              C (chi * (1 - chi)⁻¹) * X := by
          rw [← mul_assoc, ← map_mul]
        rw [ratioParameter, hlinear]
        exact hsector
      _ = _ := by simp [differenceComponentCoordinate]
  simp only [pow_one]
  exact
    congrArg₂ (fun x y : ℂ ↦ x - y) hsource' hsector'

private theorem derivative_sum_differenceRatioTerm_eq_one
    {N : ℕ} (hN : 3 ≤ N) (hNodd : Odd N)
    (chi : ℂ) (alpha : ℕ → ℂ) :
    (∑ h ∈ Finset.range (N / 2 + 1),
        differenceRatioTerm N chi alpha h).derivative.eval 0 =
      (differenceRatioTerm N chi alpha 1).derivative.eval 0 := by
  simp only [_root_.Polynomial.derivative_sum,
    _root_.Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single 1]
  · intro h hh hne
    by_cases hz : h = 0
    · subst h
      exact differenceRatioTerm_derivative_zero hNodd chi alpha
    · exact differenceRatioTerm_derivative_zero_of_two_le
        N chi alpha (by omega)
  · intro hone
    have : 1 < N / 2 + 1 := by omega
    exact (hone (Finset.mem_range.mpr this)).elim

/-- The primitive component comparison forces the nontrivial character to
be minus one. -/
theorem primitiveCharacter_eq_neg_one_of_preparedComponentIdentity
    {N : ℕ} {chi c : ℂ} {alpha : ℕ → ℂ}
    (hN : 3 ≤ N) (hNodd : Odd N) (hchi : chi ≠ 1)
    (halpha : alpha 1 ≠ 0)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c alpha) :
    chi = -1 := by
  classical
  have hratio :=
    differenceRatioIdentity_of_componentIdentity hchi hidentity
  rw [differenceRatioBase_preparedComponentPolynomial,
    differenceSector_preparedComponentPolynomial] at hratio
  have hsum :
      ∑ h ∈ Finset.range (N / 2 + 1),
          differenceRatioTerm N chi alpha h =
        C c *
          (differenceSourceCoordinate - differenceComponentCoordinate) ^ N := by
    simpa only [differenceRatioTerm, Finset.sum_sub_distrib] using hratio
  have hderivative := congrArg
    (fun P : Polynomial ℂ ↦ P.derivative.eval 0) hsum
  have hcoordinate :
      differenceSourceCoordinate - differenceComponentCoordinate = -1 := by
    have htwo : (2 : Polynomial ℂ) = C (2 : ℂ) :=
      (C_eq_natCast 2).symm
    have hhalf : C (1 / 2 : ℂ) * (2 : Polynomial ℂ) = 1 := by
      rw [htwo, ← map_mul]
      norm_num
    rw [differenceSourceCoordinate, differenceComponentCoordinate]
    calc
      C (1 / 2) * (X - 1) - C (1 / 2) * (X + 1) =
          -(C (1 / 2 : ℂ) * 2) := by ring
      _ = -1 := by rw [hhalf]
  have hconstantDerivative :
      ((-1 : Polynomial ℂ) ^ N).derivative = 0 := by
    rw [_root_.Polynomial.derivative_pow]
    simp
  have hright :
      (C c *
        (differenceSourceCoordinate - differenceComponentCoordinate) ^ N
          ).derivative.eval 0 = 0 := by
    rw [hcoordinate, _root_.Polynomial.derivative_mul,
      hconstantDerivative]
    simp
  have hsumZero :
      (∑ h ∈ Finset.range (N / 2 + 1),
          differenceRatioTerm N chi alpha h).derivative.eval 0 = 0 :=
    hderivative.trans hright
  have honeZero :
      (differenceRatioTerm N chi alpha 1).derivative.eval 0 = 0 := by
    rw [← derivative_sum_differenceRatioTerm_eq_one hN hNodd chi alpha]
    exact hsumZero
  rw [differenceRatioTerm_derivative_one] at honeZero
  have hoddSub : Odd (N - 2) :=
    Nat.Odd.sub_even (by omega) hNodd even_two
  rw [hoddSub.neg_pow] at honeZero
  have hdenominator : 1 - chi ≠ 0 := sub_ne_zero.mpr hchi.symm
  have hinverse : (1 - chi)⁻¹ ≠ 0 := inv_ne_zero hdenominator
  have hpower : (2⁻¹ : ℂ) ^ (N - 2) ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (by norm_num))
  have hproduct :
      alpha 1 * (1 - chi)⁻¹ * (2⁻¹ : ℂ) ^ (N - 2) *
        (1 + chi) = 0 := by
    calc
      _ = -(alpha 1 * (1 - chi)⁻¹ *
            (-(2⁻¹ : ℂ) ^ (N - 2)) -
          alpha 1 * (chi * (1 - chi)⁻¹) *
            (2⁻¹ : ℂ) ^ (N - 2)) := by ring
      _ = 0 := by rw [honeZero]; simp
  have hnonzero :
      alpha 1 * (1 - chi)⁻¹ * (2⁻¹ : ℂ) ^ (N - 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero halpha hinverse) hpower
  have honePlus : 1 + chi = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left hnonzero
  have hchiPlus : chi + 1 = 0 := by simpa [add_comm] using honePlus
  exact eq_neg_of_add_eq_zero_left hchiPlus

private theorem coeff_sub_two_prepared_formula
    {N : ℕ} (hN : 3 ≤ N) (alpha : ℕ → ℂ) (T : ℂ) :
    (∑ h ∈ Finset.range (N / 2 + 1),
        C (alpha h * T ^ h) * X ^ (N - 2 * h)).coeff (N - 2) =
      alpha 1 * T := by
  classical
  rw [_root_.Polynomial.finsetSum_coeff]
  simp only [_root_.Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro h hh hne
    have hle : h ≤ N / 2 := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
    have hexponent : N - 2 * h ≠ N - 2 := by omega
    rw [if_neg hexponent.symm]
  · intro hone
    have : 1 < N / 2 + 1 := by omega
    exact (hone (Finset.mem_range.mpr this)).elim

/-- The prepared coefficient of parameter degree one is the coefficient
fixed by the monic odd family. -/
theorem PreparedOddFamily.preparedCoefficient_one_of_bivariateModel
    {N : ℕ} {Psi : PreparedOddFamily N} (hN : 3 ≤ N)
    (model : Psi.BivariateModel) :
    preparedCoefficient N model.polynomial 1 = (N : ℂ) / 2 := by
  have hformula := Psi.coefficientFormula_of_bivariateModel model 1
  have hcoeff := congrArg
    (fun P : Polynomial ℂ ↦ P.coeff (N - 2)) hformula
  rw [Psi.coeff_sub_two,
    coeff_sub_two_prepared_formula hN] at hcoeff
  simpa using hcoeff.symm

/-- The coefficient of parameter degree one in a prepared bivariate model
is nonzero in degree at least three. -/
theorem PreparedOddFamily.preparedCoefficient_one_ne_zero
    {N : ℕ} {Psi : PreparedOddFamily N} (hN : 3 ≤ N)
    (model : Psi.BivariateModel) :
    preparedCoefficient N model.polynomial 1 ≠ 0 := by
  rw [Psi.preparedCoefficient_one_of_bivariateModel hN model]
  exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (by norm_num)

/-- The primitive comparison attached to a prepared bivariate model gives
both the coefficient formula and the character equation. -/
theorem PreparedOddFamily.coefficientFormula_and_primitiveCharacter
    {N : ℕ} {Psi : PreparedOddFamily N} (hN : 3 ≤ N)
    (model : Psi.BivariateModel) {chi c : ℂ} (hchi : chi ≠ 1)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c
      (preparedCoefficient N model.polynomial)) :
    (∀ T,
      Psi.polynomial T =
        ∑ h ∈ Finset.range (N / 2 + 1),
          C (preparedCoefficient N model.polynomial h * T ^ h) *
            X ^ (N - 2 * h)) ∧
      chi = -1 := by
  refine ⟨Psi.coefficientFormula_of_bivariateModel model, ?_⟩
  exact primitiveCharacter_eq_neg_one_of_preparedComponentIdentity
    hN (Psi.degree_odd 0) hchi
      (Psi.preparedCoefficient_one_ne_zero hN model) hidentity

/-- In the primitive sector notation, the component comparison gives the
character equation `zeta^j=-1`. -/
theorem PreparedOddFamily.primitivePower_eq_neg_one_of_componentIdentity
    {N : ℕ} {Psi : PreparedOddFamily N} (hN : 3 ≤ N)
    (model : Psi.BivariateModel) {zeta comparisonConstant : ℂ} {j : ℕ}
    (hcharacter : zeta ^ j ≠ 1)
    (hidentity : PreparedPrimitiveComponentIdentity N (zeta ^ j)
      comparisonConstant (preparedCoefficient N model.polynomial)) :
    zeta ^ j = -1 :=
  (Psi.coefficientFormula_and_primitiveCharacter
    hN model hcharacter hidentity).2

/-- The algebraic primitive comparison supplies the two algebraic fields of
the prepared analytic interface. The remaining hypotheses concern the
analytic representative and its correction terms. -/
theorem ResidualPreparedAnalyticData.ofBivariateModelAndPrimitiveComparison
    {a k j L N : ℕ} {zeta c T comparisonConstant : ℂ}
    {Psi : PreparedOddFamily N}
    {representative : ℂ × ℂ → Fin 3 → ℂ}
    (model : Psi.BivariateModel)
    (two_le_a : 2 ≤ a) (k_eq_two_mul_a : k = 2 * a)
    (L_eq_k_add_j : L = k + j) (primitive_root : IsPrimitiveRoot zeta k)
    (character_ne_one : zeta ^ j ≠ 1) (three_le_N : 3 ≤ N)
    (comparison_identity : PreparedPrimitiveComponentIdentity N (zeta ^ j)
      comparisonConstant (preparedCoefficient N model.polynomial))
    (c_ne_zero : c ≠ 0) (T_ne_zero : T ≠ 0)
    (representative_analytic : AnalyticAt ℂ representative 0)
    (representative_zero : representative 0 = 0)
    (correction_coefficient_divisibility : ∀ i,
      Germ.TwoWeightCoefficientDivisibility L 2
        (residualWeightedDegrees k L N i + 1)
        (pairRepresentativeComponentGerm representative
            representative_analytic i -
          Germ.coordinatePolynomialAlgHom 2
            (residualPreparedInitialPolynomials k L N c T
              (preparedCoefficient N model.polynomial) i))) :
    ResidualPreparedAnalyticData a k j L N zeta c T Psi
      (preparedCoefficient N model.polynomial) representative := by
  have hconclusions := Psi.coefficientFormula_and_primitiveCharacter
    three_le_N model character_ne_one comparison_identity
  exact {
    two_le_a := two_le_a
    k_eq_two_mul_a := k_eq_two_mul_a
    L_eq_k_add_j := L_eq_k_add_j
    primitive_root := primitive_root
    primitive_character := hconclusions.2
    three_le_N := three_le_N
    c_ne_zero := c_ne_zero
    T_ne_zero := T_ne_zero
    coefficient_formula := hconclusions.1
    representative_analytic := representative_analytic
    representative_zero := representative_zero
    correction_coefficient_divisibility :=
      correction_coefficient_divisibility
  }

end OnLeConjecture.DTwo
