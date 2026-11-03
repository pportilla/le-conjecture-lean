/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PrimitiveCharacterComparison
public import OnLeConjecture.DTwo.PreparedOddFamilyConstruction
import all OnLeConjecture.DTwo.PrimitiveCharacterComparison

/-!
# The first coefficient forced by the primitive component identity

We evaluate the quadratic component in the polynomial chart
`x = (1 - z) / 2`, `X = (1 + z) / 2`, `T = z / (1 - chi)`.
Differentiating the component identity at `z = 0` determines `alpha 1`
from `alpha 0`. In particular, a normalized leading coefficient forces
`alpha 1 = N / 2`. No assumption on that coefficient is used.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open scoped Polynomial.Bivariate

private noncomputable def sumRatioBase (chi : ℂ) :
    EqualizerBaseRing →ₐ[ℂ] Polynomial ℂ :=
  Polynomial.aevalAeval (ratioParameter chi) (-differenceSourceCoordinate)

private theorem componentPolynomial_sumRatio_eq_zero
    {chi : ℂ} (hchi : chi ≠ 1) :
    (componentPolynomial chi).eval₂ (sumRatioBase chi)
      differenceComponentCoordinate = 0 := by
  have h := componentPolynomial_differenceRatio_eq_zero hchi
  rw [componentPolynomial_eq, _root_.Polynomial.eval₂_sub,
    _root_.Polynomial.eval₂_pow, _root_.Polynomial.eval₂_X,
    _root_.Polynomial.eval₂_C, componentSquare_eq] at h ⊢
  simpa [sumRatioBase, differenceRatioBase] using h

private noncomputable def sumRatioComponent
    (chi : ℂ) (hchi : chi ≠ 1) :
    EqualizerComponentRing chi →ₐ[ℂ] Polynomial ℂ :=
  AdjoinRoot.liftAlgHom (componentPolynomial chi) (sumRatioBase chi)
    differenceComponentCoordinate (componentPolynomial_sumRatio_eq_zero hchi)

private theorem sumRatioComponent_algebraMap
    {chi : ℂ} (hchi : chi ≠ 1) (H : EqualizerBaseRing) :
    sumRatioComponent chi hchi
        (algebraMap EqualizerBaseRing (EqualizerComponentRing chi) H) =
      sumRatioBase chi H := by
  change sumRatioComponent chi hchi
      (AdjoinRoot.of (componentPolynomial chi) H) = _
  rw [sumRatioComponent, AdjoinRoot.liftAlgHom_of]

private theorem sumRatioComponent_root
    {chi : ℂ} (hchi : chi ≠ 1) :
    sumRatioComponent chi hchi
        (AdjoinRoot.root (componentPolynomial chi)) =
      differenceComponentCoordinate := by
  rw [sumRatioComponent, AdjoinRoot.liftAlgHom_root]

private theorem sumRatioComponent_sectorValue
    {chi : ℂ} (hchi : chi ≠ 1) (H : EqualizerBaseRing) :
    sumRatioComponent chi hchi (componentSectorValue chi H) =
      Polynomial.aevalAeval
        (C chi * ratioParameter chi) differenceComponentCoordinate H := by
  rw [componentSectorValue_eq, sumRatioComponent,
    AdjoinRoot.liftAlgHom_mk]
  induction H using _root_.Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
      simp only [map_monomial, scaleEqualizerParameter_apply,
        _root_.Polynomial.eval₂_monomial, RingHom.coe_coe,
        _root_.Polynomial.aevalAevalEquiv_apply_apply,
        _root_.Polynomial.aeval_monomial, algebraMap_def, algebraMap_eq,
        _root_.Polynomial.coe_mapRingHom, _root_.Polynomial.eval_mul,
        _root_.Polynomial.eval_pow, _root_.Polynomial.eval_C,
        mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
      left
      rw [sumRatioBase, _root_.Polynomial.aevalAeval_C]
      change (a.comp (C chi * X)).eval₂ C (ratioParameter chi) =
        (a.map C).eval (C chi * ratioParameter chi)
      rw [_root_.Polynomial.eval₂_eq_eval_map,
        _root_.Polynomial.map_comp, _root_.Polynomial.eval_comp]
      simp

private noncomputable def sumRatioTerm
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) (h : ℕ) : Polynomial ℂ :=
  C (alpha h) * ratioParameter chi ^ h *
      (-differenceSourceCoordinate) ^ (N - 2 * h) -
    C (alpha h) * (C chi * ratioParameter chi) ^ h *
      differenceComponentCoordinate ^ (N - 2 * h)

private theorem sumRatioIdentity_of_componentIdentity
    {N : ℕ} {chi c : ℂ} {alpha : ℕ → ℂ}
    (hchi : chi ≠ 1)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c alpha) :
    ∑ h ∈ Finset.range (N / 2 + 1), sumRatioTerm N chi alpha h =
      C c * (-X) ^ N := by
  have hmapped := congrArg (sumRatioComponent chi hchi) hidentity
  rw [map_sub, sumRatioComponent_algebraMap,
    sumRatioComponent_sectorValue, map_mul, map_pow, map_sub,
    sumRatioComponent_algebraMap, sumRatioComponent_root] at hmapped
  have hcoordinate :
      -differenceSourceCoordinate - differenceComponentCoordinate = -X := by
    rw [differenceSourceCoordinate, differenceComponentCoordinate]
    have hhalf : C (1 / 2 : ℂ) * (2 : Polynomial ℂ) = 1 := by
      rw [← C_ofNat, ← map_mul]
      norm_num
    calc
      -(C (1 / 2 : ℂ) * (X - 1)) - C (1 / 2 : ℂ) * (X + 1) =
          -(C (1 / 2 : ℂ) * 2) * X := by ring
      _ = -X := by rw [hhalf]; simp
  simpa [sumRatioBase, preparedComponentPolynomial, sumRatioTerm,
    Finset.sum_sub_distrib, hcoordinate] using hmapped

private theorem sumRatioTerm_derivative_zero
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) :
    (sumRatioTerm N chi alpha 0).derivative.eval 0 =
      -alpha 0 * (N : ℂ) * (2⁻¹ : ℂ) ^ (N - 1) := by
  simp [sumRatioTerm, differenceSourceCoordinate,
    differenceComponentCoordinate, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_pow]
  ring

private theorem sumRatioTerm_derivative_one
    (N : ℕ) {chi : ℂ} (hchi : chi ≠ 1) (alpha : ℕ → ℂ) :
    (sumRatioTerm N chi alpha 1).derivative.eval 0 =
      alpha 1 * (2⁻¹ : ℂ) ^ (N - 2) := by
  have hdenominator : 1 - chi ≠ 0 := sub_ne_zero.mpr hchi.symm
  have hscalar :
      alpha 1 * (1 - chi)⁻¹ * (2⁻¹ : ℂ) ^ (N - 2) -
        alpha 1 * (chi * (1 - chi)⁻¹) * (2⁻¹ : ℂ) ^ (N - 2) =
      alpha 1 * (2⁻¹ : ℂ) ^ (N - 2) := by
    field_simp [hdenominator]
  simpa [sumRatioTerm, ratioParameter, differenceSourceCoordinate,
    differenceComponentCoordinate, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_pow, mul_assoc] using hscalar

private theorem sumRatioTerm_derivative_zero_of_two_le
    (N : ℕ) (chi : ℂ) (alpha : ℕ → ℂ) {h : ℕ} (hh : 2 ≤ h) :
    (sumRatioTerm N chi alpha h).derivative.eval 0 = 0 := by
  rw [sumRatioTerm, _root_.Polynomial.derivative_sub,
    _root_.Polynomial.eval_sub]
  have hsource := derivative_eval_zero_constant_mul_linear_pow_mul_pow
    (alpha h) (1 - chi)⁻¹ (-differenceSourceCoordinate) hh (m := N - 2 * h)
  have hsector := derivative_eval_zero_constant_mul_linear_pow_mul_pow
    (alpha h) (chi * (1 - chi)⁻¹) differenceComponentCoordinate hh
      (m := N - 2 * h)
  simpa [ratioParameter, map_mul, mul_assoc] using
    congrArg₂ (fun x y : ℂ ↦ x - y) hsource hsector

/-- The component identity and normalized leading coefficient determine
the next coefficient. Parity and a nonzero comparison constant are not
needed for this coefficient comparison. -/
theorem preparedCoefficient_one_of_primitiveComponentIdentity
    {N : ℕ} {chi c : ℂ} {alpha : ℕ → ℂ}
    (hN : 3 ≤ N) (hchi : chi ≠ 1) (hzero : alpha 0 = 1)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c alpha) :
    alpha 1 = (N : ℂ) / 2 := by
  classical
  have hsum := sumRatioIdentity_of_componentIdentity hchi hidentity
  have hderivative := congrArg (fun P : Polynomial ℂ ↦ P.derivative.eval 0) hsum
  have hright : (C c * (-X : Polynomial ℂ) ^ N).derivative.eval 0 = 0 := by
    have hpos : 0 < N - 1 := by omega
    simp [_root_.Polynomial.derivative_mul, _root_.Polynomial.derivative_pow,
      zero_pow hpos.ne']
  rw [hright, _root_.Polynomial.derivative_sum,
    _root_.Polynomial.eval_finsetSum] at hderivative
  have hzeroMem : 0 ∈ Finset.range (N / 2 + 1) := by simp
  rw [← Finset.add_sum_erase _ _ hzeroMem] at hderivative
  have herase :
      ∑ h ∈ (Finset.range (N / 2 + 1)).erase 0,
          (sumRatioTerm N chi alpha h).derivative.eval 0 =
        (sumRatioTerm N chi alpha 1).derivative.eval 0 := by
    apply Finset.sum_eq_single 1
    · intro h hh hne
      have hhzero := (Finset.mem_erase.mp hh).1
      exact sumRatioTerm_derivative_zero_of_two_le N chi alpha (by omega)
    · intro hnotmem
      have hmem : 1 ∈ (Finset.range (N / 2 + 1)).erase 0 := by
        simp only [Finset.mem_erase, ne_eq, one_ne_zero, not_false_eq_true,
          Finset.mem_range, true_and]
        omega
      exact (hnotmem hmem).elim
  rw [herase, sumRatioTerm_derivative_zero,
    sumRatioTerm_derivative_one N hchi, hzero] at hderivative
  have hexponent : N - 1 = (N - 2) + 1 := by omega
  rw [hexponent, pow_succ] at hderivative
  have hpower : (2⁻¹ : ℂ) ^ (N - 2) ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (by norm_num))
  have hproduct :
      (alpha 1 - (N : ℂ) / 2) * (2⁻¹ : ℂ) ^ (N - 2) = 0 := by
    convert hderivative using 1
    ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hpower)

/-- The normalized component identity supplies the nonzero coefficient
required by the existing primitive character comparison. -/
theorem primitiveCharacter_eq_neg_one_of_normalizedComponentIdentity
    {N : ℕ} {chi c : ℂ} {alpha : ℕ → ℂ}
    (hN : 3 ≤ N) (hodd : Odd N) (hchi : chi ≠ 1)
    (hzero : alpha 0 = 1)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c alpha) :
    chi = -1 := by
  have hone := preparedCoefficient_one_of_primitiveComponentIdentity
    hN hchi hzero hidentity
  have hnonzero : alpha 1 ≠ 0 := by
    rw [hone]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (by norm_num)
  exact primitiveCharacter_eq_neg_one_of_preparedComponentIdentity
    hN hodd hchi hnonzero hidentity

/-- The normalized primitive component identity constructs the prepared
odd family without an assumption on the next coefficient. -/
@[expose]
noncomputable def PreparedOddFamily.ofPrimitiveComponentIdentity
    {N : ℕ} {chi c : ℂ} {alpha : ℕ → ℂ}
    (hN : 3 ≤ N) (hodd : Odd N) (hchi : chi ≠ 1)
    (hzero : alpha 0 = 1)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c alpha) :
    PreparedOddFamily N :=
  PreparedOddFamily.ofCoefficients alpha hN hodd hzero
    (preparedCoefficient_one_of_primitiveComponentIdentity hN hchi hzero hidentity)

/-- The same component identity supplies the bivariate model of the
constructed family. -/
@[expose]
noncomputable def PreparedOddFamily.BivariateModel.ofPrimitiveComponentIdentity
    {N : ℕ} {chi c : ℂ} {alpha : ℕ → ℂ}
    (hN : 3 ≤ N) (hodd : Odd N) (hchi : chi ≠ 1)
    (hzero : alpha 0 = 1)
    (hidentity : PreparedPrimitiveComponentIdentity N chi c alpha) :
    (PreparedOddFamily.ofPrimitiveComponentIdentity
      hN hodd hchi hzero hidentity).BivariateModel :=
  PreparedOddFamily.BivariateModel.ofExplicitCoefficients alpha hN hodd hzero
    (preparedCoefficient_one_of_primitiveComponentIdentity hN hchi hzero hidentity)

end OnLeConjecture.DTwo
