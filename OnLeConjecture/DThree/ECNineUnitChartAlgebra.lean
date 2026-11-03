/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineKummerField
public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# The unit chart algebra of C9

On the projective chart `x = 1`, the two C9 equations are monic cubic
equations in `t` and `T` over `ℂ[X]`. Their successive root algebra has an
explicit basis indexed by `Fin 3 × Fin 3`.

The coefficient inclusion `ℂ[X] → ℂ(X)` extends to the generic C9 Kummer
field. Comparing the two product bases proves that this specialization is
injective. It follows that the unit chart algebra is a domain and is reduced.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial Module

/-- The coordinate ring of the parameter line on the chart `x = 1`. -/
abbrev ECNineUnitBase := ℂ[X]

/-- The right side of the monic equation for `t³` on the chart `x = 1`. -/
@[expose]
def eCNineUnitFirstRadicand : ECNineUnitBase :=
  -(C (12 : ℂ)⁻¹ *
    ((C 1 - X) * (X ^ 2 + C 2 * X + C 3)))

/-- The right side of the monic equation for `T³` on the chart `x = 1`. -/
@[expose]
def eCNineUnitSecondRadicand : ECNineUnitBase :=
  C (12 : ℂ)⁻¹ *
    ((C 1 - X) * (C 3 * X ^ 2 + C 2 * X + C 1))

/-- The inclusion of the polynomial parameter ring into its rational function
field. -/
def eCNineUnitBaseSpecialization : ECNineUnitBase →+* ECNineKummerBase :=
  algebraMap ℂ[X] (RatFunc ℂ)

theorem eCNineUnitFirstRadicand_specialization :
    eCNineUnitBaseSpecialization eCNineUnitFirstRadicand =
      eCNineFirstKummerFunction := by
  have hrad : eCNineUnitFirstRadicand =
      C (12 : ℂ)⁻¹ * eCNineFirstKummerNumerator := by
    rw [eCNineUnitFirstRadicand, eCNineFirstKummerNumerator,
      eCNineFirstKummerQuadratic]
    ring
  rw [hrad, eCNineFirstKummerFunction, eCNineUnitBaseSpecialization,
    map_mul, RatFunc.algebraMap_C]
  rw [map_inv₀]
  simp only [RatFunc.algebraMap_C]
  ring

theorem eCNineUnitSecondRadicand_specialization :
    eCNineUnitBaseSpecialization eCNineUnitSecondRadicand =
      eCNineSecondKummerFunction := by
  have hrad : eCNineUnitSecondRadicand =
      C (12 : ℂ)⁻¹ * eCNineSecondKummerNumerator := by
    rw [eCNineUnitSecondRadicand, eCNineSecondKummerNumerator,
      eCNineSecondKummerQuadratic]
  rw [hrad, eCNineSecondKummerFunction, eCNineUnitBaseSpecialization,
    map_mul, RatFunc.algebraMap_C]
  rw [map_inv₀]
  simp only [RatFunc.algebraMap_C]
  ring

/-- The monic cubic equation for the first root. -/
@[expose]
def eCNineUnitFirstPolynomial : ECNineUnitBase[X] :=
  X ^ 3 - C eCNineUnitFirstRadicand

/-- The root algebra of the first unit chart cubic. -/
abbrev ECNineUnitFirstAlgebra :=
  AdjoinRoot eCNineUnitFirstPolynomial

/-- The monic cubic equation for the second root over the first root algebra. -/
@[expose]
def eCNineUnitSecondPolynomial : ECNineUnitFirstAlgebra[X] :=
  X ^ 3 - C (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra
    eCNineUnitSecondRadicand)

/-- The successive root algebra representing the C9 equations on `x = 1`. -/
abbrev ECNineUnitAlgebra :=
  AdjoinRoot eCNineUnitSecondPolynomial

theorem eCNineUnitFirstPolynomial_monic :
    eCNineUnitFirstPolynomial.Monic := by
  rw [eCNineUnitFirstPolynomial]
  exact monic_X_pow_sub_C _ (by norm_num)

theorem eCNineUnitFirstPolynomial_natDegree :
    eCNineUnitFirstPolynomial.natDegree = 3 := by
  rw [eCNineUnitFirstPolynomial, natDegree_X_pow_sub_C]

instance eCNineUnitFirstAlgebraNontrivial :
    Nontrivial ECNineUnitFirstAlgebra := by
  apply AdjoinRoot.nontrivial eCNineUnitFirstPolynomial
  rw [degree_eq_natDegree eCNineUnitFirstPolynomial_monic.ne_zero,
    eCNineUnitFirstPolynomial_natDegree]
  norm_num

theorem eCNineUnitSecondPolynomial_monic :
    eCNineUnitSecondPolynomial.Monic := by
  rw [eCNineUnitSecondPolynomial]
  exact monic_X_pow_sub_C _ (by norm_num)

theorem eCNineUnitSecondPolynomial_natDegree :
    eCNineUnitSecondPolynomial.natDegree = 3 := by
  rw [eCNineUnitSecondPolynomial, natDegree_X_pow_sub_C]

/-- The powers of the first root, indexed by `Fin 3`. -/
def eCNineUnitFirstBasis :
    Basis (Fin 3) ECNineUnitBase ECNineUnitFirstAlgebra :=
  (AdjoinRoot.powerBasis' eCNineUnitFirstPolynomial_monic).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim]
      exact eCNineUnitFirstPolynomial_natDegree))

/-- The powers of the second root, indexed by `Fin 3`. -/
def eCNineUnitSecondBasis :
    Basis (Fin 3) ECNineUnitFirstAlgebra ECNineUnitAlgebra :=
  (AdjoinRoot.powerBasis' eCNineUnitSecondPolynomial_monic).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim]
      exact eCNineUnitSecondPolynomial_natDegree))

/-- The product basis of the unit chart algebra over `ℂ[X]`. -/
def eCNineUnitBasis :
    Basis (Fin 3 × Fin 3) ECNineUnitBase ECNineUnitAlgebra :=
  eCNineUnitFirstBasis.smulTower eCNineUnitSecondBasis

theorem eCNineUnitFirstBasis_apply (i : Fin 3) :
    eCNineUnitFirstBasis i =
      AdjoinRoot.root eCNineUnitFirstPolynomial ^ (i : ℕ) := by
  rw [eCNineUnitFirstBasis, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

theorem eCNineUnitSecondBasis_apply (j : Fin 3) :
    eCNineUnitSecondBasis j =
      AdjoinRoot.root eCNineUnitSecondPolynomial ^ (j : ℕ) := by
  rw [eCNineUnitSecondBasis, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

theorem eCNineUnitBasis_apply (i j : Fin 3) :
    eCNineUnitBasis (i, j) =
      (AdjoinRoot.root eCNineUnitFirstPolynomial ^ (i : ℕ)) •
        (AdjoinRoot.root eCNineUnitSecondPolynomial ^ (j : ℕ)) := by
  rw [eCNineUnitBasis, Basis.smulTower_apply,
    eCNineUnitFirstBasis_apply, eCNineUnitSecondBasis_apply]

theorem eCNineUnitFirstPolynomial_specialization :
    eCNineUnitFirstPolynomial.map eCNineUnitBaseSpecialization =
      eCNineFirstKummerPolynomial := by
  rw [eCNineUnitFirstPolynomial, eCNineFirstKummerPolynomial]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, eCNineUnitFirstRadicand_specialization]

/-- The specialization of the first root algebra to the first Kummer field. -/
def eCNineUnitFirstSpecialization :
    ECNineUnitFirstAlgebra →+* ECNineFirstKummerAlgebra :=
  AdjoinRoot.map eCNineUnitBaseSpecialization
    eCNineUnitFirstPolynomial eCNineFirstKummerPolynomial (by
      rw [eCNineUnitFirstPolynomial_specialization])

@[simp]
theorem eCNineUnitFirstSpecialization_algebraMap
    (r : ECNineUnitBase) :
    eCNineUnitFirstSpecialization
        (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra r) =
      algebraMap ECNineKummerBase ECNineFirstKummerAlgebra
        (eCNineUnitBaseSpecialization r) := by
  simp [eCNineUnitFirstSpecialization, AdjoinRoot.algebraMap_eq]

@[simp]
theorem eCNineUnitFirstSpecialization_root :
    eCNineUnitFirstSpecialization
        (AdjoinRoot.root eCNineUnitFirstPolynomial) =
      AdjoinRoot.root eCNineFirstKummerPolynomial := by
  simp [eCNineUnitFirstSpecialization]

theorem eCNineUnitSecondPolynomial_specialization :
    eCNineUnitSecondPolynomial.map eCNineUnitFirstSpecialization =
      eCNineSecondKummerPolynomialOverFirst := by
  rw [eCNineUnitSecondPolynomial,
    eCNineSecondKummerPolynomialOverFirst]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, eCNineUnitFirstSpecialization_algebraMap,
    eCNineUnitSecondRadicand_specialization]

/-- The canonical specialization from the unit chart algebra to the generic
Kummer field. -/
def eCNineUnitSpecialization :
    ECNineUnitAlgebra →+* ECNineKummerAlgebra :=
  AdjoinRoot.map eCNineUnitFirstSpecialization
    eCNineUnitSecondPolynomial eCNineSecondKummerPolynomialOverFirst (by
      rw [eCNineUnitSecondPolynomial_specialization])

@[simp]
theorem eCNineUnitSpecialization_algebraMap_first
    (r : ECNineUnitFirstAlgebra) :
    eCNineUnitSpecialization
        (algebraMap ECNineUnitFirstAlgebra ECNineUnitAlgebra r) =
      algebraMap ECNineFirstKummerAlgebra ECNineKummerAlgebra
        (eCNineUnitFirstSpecialization r) := by
  simp [eCNineUnitSpecialization, AdjoinRoot.algebraMap_eq]

@[simp]
theorem eCNineUnitSpecialization_algebraMap
    (r : ECNineUnitBase) :
    eCNineUnitSpecialization
        (algebraMap ECNineUnitBase ECNineUnitAlgebra r) =
      algebraMap ECNineKummerBase ECNineKummerAlgebra
        (eCNineUnitBaseSpecialization r) := by
  rw [IsScalarTower.algebraMap_apply ECNineUnitBase
    ECNineUnitFirstAlgebra ECNineUnitAlgebra,
    eCNineUnitSpecialization_algebraMap_first,
    eCNineUnitFirstSpecialization_algebraMap]
  exact IsScalarTower.algebraMap_apply ECNineKummerBase
    ECNineFirstKummerAlgebra ECNineKummerAlgebra _

@[simp]
theorem eCNineUnitSpecialization_root :
    eCNineUnitSpecialization
        (AdjoinRoot.root eCNineUnitSecondPolynomial) =
      AdjoinRoot.root eCNineSecondKummerPolynomialOverFirst := by
  simp [eCNineUnitSpecialization]

/-- The power basis of the first generic Kummer extension. -/
def eCNineGenericFirstBasis :
    Basis (Fin 3) ECNineKummerBase ECNineFirstKummerAlgebra :=
  (AdjoinRoot.powerBasis' eCNineFirstKummerPolynomial_monic).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim]
      exact eCNineFirstKummerPolynomial_natDegree))

/-- The power basis of the second generic Kummer extension. -/
def eCNineGenericSecondBasis :
    Basis (Fin 3) ECNineFirstKummerAlgebra ECNineKummerAlgebra :=
  (AdjoinRoot.powerBasis'
    eCNineSecondKummerPolynomialOverFirst_monic).basis.reindex
      (finCongr (by
        rw [AdjoinRoot.powerBasis'_dim]
        exact eCNineSecondKummerPolynomialOverFirst_natDegree))

/-- The product basis of the generic Kummer field. -/
def eCNineGenericBasis :
    Basis (Fin 3 × Fin 3) ECNineKummerBase ECNineKummerAlgebra :=
  eCNineGenericFirstBasis.smulTower eCNineGenericSecondBasis

theorem eCNineGenericFirstBasis_apply (i : Fin 3) :
    eCNineGenericFirstBasis i =
      AdjoinRoot.root eCNineFirstKummerPolynomial ^ (i : ℕ) := by
  rw [eCNineGenericFirstBasis, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

theorem eCNineGenericSecondBasis_apply (j : Fin 3) :
    eCNineGenericSecondBasis j =
      AdjoinRoot.root eCNineSecondKummerPolynomialOverFirst ^ (j : ℕ) := by
  rw [eCNineGenericSecondBasis, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

theorem eCNineGenericBasis_apply (i j : Fin 3) :
    eCNineGenericBasis (i, j) =
      (AdjoinRoot.root eCNineFirstKummerPolynomial ^ (i : ℕ)) •
        (AdjoinRoot.root eCNineSecondKummerPolynomialOverFirst ^
          (j : ℕ)) := by
  rw [eCNineGenericBasis, Basis.smulTower_apply,
    eCNineGenericFirstBasis_apply, eCNineGenericSecondBasis_apply]

theorem eCNineUnitSpecialization_basis (i j : Fin 3) :
    eCNineUnitSpecialization (eCNineUnitBasis (i, j)) =
      eCNineGenericBasis (i, j) := by
  rw [eCNineUnitBasis_apply, eCNineGenericBasis_apply,
    Algebra.smul_def, Algebra.smul_def, map_mul]
  rw [eCNineUnitSpecialization_algebraMap_first,
    map_pow eCNineUnitFirstSpecialization,
    eCNineUnitFirstSpecialization_root,
    map_pow eCNineUnitSpecialization,
    eCNineUnitSpecialization_root]

theorem eCNineUnitSpecialization_basis' (ij : Fin 3 × Fin 3) :
    eCNineUnitSpecialization (eCNineUnitBasis ij) =
      eCNineGenericBasis ij := by
  rcases ij with ⟨i, j⟩
  exact eCNineUnitSpecialization_basis i j

theorem eCNineUnitSpecialization_smul
    (r : ECNineUnitBase) (z : ECNineUnitAlgebra) :
    eCNineUnitSpecialization (r • z) =
      eCNineUnitBaseSpecialization r •
        eCNineUnitSpecialization z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    eCNineUnitSpecialization_algebraMap]

/-- Specialization maps every source basis coordinate through the coefficient
inclusion. -/
theorem eCNineGenericBasis_repr_specialization
    (z : ECNineUnitAlgebra) (ij : Fin 3 × Fin 3) :
    eCNineGenericBasis.repr (eCNineUnitSpecialization z) ij =
      eCNineUnitBaseSpecialization (eCNineUnitBasis.repr z ij) := by
  classical
  conv_lhs => rw [← eCNineUnitBasis.sum_repr z]
  simp_rw [map_sum, eCNineUnitSpecialization_smul,
    eCNineUnitSpecialization_basis']
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ij]
  · simp
  · intro c _ hci
    rw [Finsupp.single_eq_of_ne (Ne.symm hci)]
  · simp

theorem eCNineUnitBaseSpecialization_injective :
    Function.Injective eCNineUnitBaseSpecialization := by
  rw [eCNineUnitBaseSpecialization]
  exact RatFunc.algebraMap_injective ℂ

/-- The canonical specialization of the unit chart algebra is injective. -/
theorem eCNineUnitSpecialization_injective :
    Function.Injective eCNineUnitSpecialization := by
  intro x y hxy
  apply eCNineUnitBasis.repr.injective
  apply Finsupp.ext
  intro ij
  apply eCNineUnitBaseSpecialization_injective
  rw [← eCNineGenericBasis_repr_specialization x ij,
    ← eCNineGenericBasis_repr_specialization y ij, hxy]

instance eCNineUnitAlgebraFree :
    Module.Free ECNineUnitBase ECNineUnitAlgebra :=
  Module.Free.of_basis eCNineUnitBasis

instance eCNineUnitAlgebraFinite :
    Module.Finite ECNineUnitBase ECNineUnitAlgebra :=
  Module.Finite.of_basis eCNineUnitBasis

/-- The unit chart algebra is finite free of rank nine over `ℂ[X]`. -/
theorem eCNineUnitAlgebra_finrank :
    Module.finrank ECNineUnitBase ECNineUnitAlgebra = 9 := by
  rw [Module.finrank_eq_card_basis eCNineUnitBasis]
  norm_num

/-- The unit chart algebra is flat over `ℂ[X]`. -/
theorem eCNineUnitAlgebra_flat :
    Module.Flat ECNineUnitBase ECNineUnitAlgebra :=
  inferInstance

/-- Every element of the unit chart algebra is integral over `ℂ[X]`. -/
theorem eCNineUnitAlgebra_isIntegral :
    Algebra.IsIntegral ECNineUnitBase ECNineUnitAlgebra :=
  inferInstance

/-- The unit chart algebra is Noetherian. -/
theorem eCNineUnitAlgebra_isNoetherianRing :
    IsNoetherianRing ECNineUnitAlgebra :=
  inferInstance

/-- The unit chart algebra embeds in a field and is therefore a domain. -/
instance eCNineUnitAlgebraIsDomain : IsDomain ECNineUnitAlgebra :=
  eCNineUnitSpecialization_injective.isDomain eCNineUnitSpecialization

/-- The unit chart algebra is reduced. -/
theorem eCNineUnitAlgebra_isReduced : IsReduced ECNineUnitAlgebra :=
  inferInstance

/-- The unit chart algebra has Krull dimension at most one. -/
theorem eCNineUnitAlgebra_dimensionLEOne :
    Ring.DimensionLEOne ECNineUnitAlgebra :=
  Ring.DimensionLEOne.of_isIntegral ECNineUnitBase ECNineUnitAlgebra

/-- The unit chart algebra is not a field. -/
theorem eCNineUnitAlgebra_not_isField : ¬ IsField ECNineUnitAlgebra := by
  intro hfield
  exact Polynomial.not_isField ℂ
    (isField_of_isIntegral_of_isField
      (FaithfulSMul.algebraMap_injective ECNineUnitBase
        ECNineUnitAlgebra) hfield)

/-- The unit chart algebra has Krull dimension one. -/
theorem eCNineUnitAlgebra_ringKrullDim :
    ringKrullDim ECNineUnitAlgebra = 1 := by
  let _ : Ring.DimensionLEOne ECNineUnitAlgebra :=
    eCNineUnitAlgebra_dimensionLEOne
  apply le_antisymm
  · exact Ring.krullDimLE_iff.mp
      (inferInstance : Ring.KrullDimLE 1 ECNineUnitAlgebra)
  · change 1 ≤ Order.krullDim (PrimeSpectrum ECNineUnitAlgebra)
    rw [Order.one_le_krullDim_iff]
    obtain ⟨p, hp, hpprime⟩ :=
      Ring.not_isField_iff_exists_prime.mp
        eCNineUnitAlgebra_not_isField
    exact ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨p, hpprime⟩, hp.bot_lt⟩

theorem eCNineUnitFirstRoot_cube :
    AdjoinRoot.root eCNineUnitFirstPolynomial ^ 3 =
      algebraMap ECNineUnitBase ECNineUnitFirstAlgebra
        eCNineUnitFirstRadicand := by
  have h := AdjoinRoot.eval₂_root eCNineUnitFirstPolynomial
  rw [eCNineUnitFirstPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, sub_eq_zero] at h
  exact h

theorem eCNineUnitSecondRoot_cube :
    AdjoinRoot.root eCNineUnitSecondPolynomial ^ 3 =
      algebraMap ECNineUnitFirstAlgebra ECNineUnitAlgebra
        (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra
          eCNineUnitSecondRadicand) := by
  have h := AdjoinRoot.eval₂_root eCNineUnitSecondPolynomial
  rw [eCNineUnitSecondPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, sub_eq_zero] at h
  exact h

/-- The coordinate `X` in the unit chart algebra. -/
@[expose]
def eCNineUnitCapitalX : ECNineUnitAlgebra :=
  algebraMap ECNineUnitBase ECNineUnitAlgebra X

/-- The first adjoined root `t` in the unit chart algebra. -/
@[expose]
def eCNineUnitT : ECNineUnitAlgebra :=
  algebraMap ECNineUnitFirstAlgebra ECNineUnitAlgebra
    (AdjoinRoot.root eCNineUnitFirstPolynomial)

/-- The second adjoined root `T` in the unit chart algebra. -/
@[expose]
def eCNineUnitCapitalT : ECNineUnitAlgebra :=
  AdjoinRoot.root eCNineUnitSecondPolynomial

theorem eCNineUnitT_cube :
    eCNineUnitT ^ 3 =
      algebraMap ECNineUnitBase ECNineUnitAlgebra
        eCNineUnitFirstRadicand := by
  rw [eCNineUnitT, ← map_pow, eCNineUnitFirstRoot_cube]
  exact IsScalarTower.algebraMap_apply ECNineUnitBase
    ECNineUnitFirstAlgebra ECNineUnitAlgebra eCNineUnitFirstRadicand

theorem eCNineUnitCapitalT_cube :
    eCNineUnitCapitalT ^ 3 =
      algebraMap ECNineUnitBase ECNineUnitAlgebra
        eCNineUnitSecondRadicand := by
  rw [eCNineUnitCapitalT, eCNineUnitSecondRoot_cube]
  exact IsScalarTower.algebraMap_apply ECNineUnitBase
    ECNineUnitFirstAlgebra ECNineUnitAlgebra eCNineUnitSecondRadicand

@[simp]
theorem eCNineUnit_algebraMap_C (c : ℂ) :
    algebraMap ECNineUnitBase ECNineUnitAlgebra (C c) =
      algebraMap ℂ ECNineUnitAlgebra c := by
  simpa [Polynomial.algebraMap_apply] using
    (IsScalarTower.algebraMap_apply ℂ ECNineUnitBase
      ECNineUnitAlgebra c).symm

/-- The first dehomogenized C9 equation holds in the unit chart algebra. -/
theorem eCNineUnit_first_equation :
    12 * eCNineUnitT ^ 3 +
      (1 - eCNineUnitCapitalX) *
        (eCNineUnitCapitalX ^ 2 +
          2 * eCNineUnitCapitalX + 3) = 0 := by
  let Q : ECNineUnitAlgebra :=
    (1 - eCNineUnitCapitalX) *
      (eCNineUnitCapitalX ^ 2 +
        2 * eCNineUnitCapitalX + 3)
  let c : ECNineUnitAlgebra :=
    algebraMap ECNineUnitBase ECNineUnitAlgebra (C (12 : ℂ)⁻¹)
  have hc : (12 : ECNineUnitAlgebra) * c = 1 := by
    calc
      (12 : ECNineUnitAlgebra) * c =
          algebraMap ℂ ECNineUnitAlgebra 12 *
            algebraMap ℂ ECNineUnitAlgebra (12 : ℂ)⁻¹ := by
        rfl
      _ = algebraMap ℂ ECNineUnitAlgebra
          ((12 : ℂ) * 12⁻¹) := by rw [map_mul]
      _ = 1 := by norm_num
  have hradicand :
      algebraMap ECNineUnitBase ECNineUnitAlgebra
        eCNineUnitFirstRadicand = -(c * Q) := by
    simp [eCNineUnitFirstRadicand, c, Q, eCNineUnitCapitalX,
      map_neg, map_mul, map_sub, map_add, map_pow,
      eCNineUnit_algebraMap_C, map_ofNat]
  rw [eCNineUnitT_cube, hradicand]
  change 12 * (-(c * Q)) + Q = 0
  calc
    12 * (-(c * Q)) + Q = -(12 * c) * Q + Q := by ring
    _ = 0 := by
      rw [hc]
      ring

/-- The second dehomogenized C9 equation holds in the unit chart algebra. -/
theorem eCNineUnit_second_equation :
    12 * eCNineUnitCapitalT ^ 3 -
      (1 - eCNineUnitCapitalX) *
        (3 * eCNineUnitCapitalX ^ 2 +
          2 * eCNineUnitCapitalX + 1) = 0 := by
  let Q : ECNineUnitAlgebra :=
    (1 - eCNineUnitCapitalX) *
      (3 * eCNineUnitCapitalX ^ 2 +
        2 * eCNineUnitCapitalX + 1)
  let c : ECNineUnitAlgebra :=
    algebraMap ECNineUnitBase ECNineUnitAlgebra (C (12 : ℂ)⁻¹)
  have hc : (12 : ECNineUnitAlgebra) * c = 1 := by
    calc
      (12 : ECNineUnitAlgebra) * c =
          algebraMap ℂ ECNineUnitAlgebra 12 *
            algebraMap ℂ ECNineUnitAlgebra (12 : ℂ)⁻¹ := by
        rfl
      _ = algebraMap ℂ ECNineUnitAlgebra
          ((12 : ℂ) * 12⁻¹) := by rw [map_mul]
      _ = 1 := by norm_num
  have hradicand :
      algebraMap ECNineUnitBase ECNineUnitAlgebra
        eCNineUnitSecondRadicand = c * Q := by
    simp [eCNineUnitSecondRadicand, c, Q, eCNineUnitCapitalX,
      map_mul, map_sub, map_add, map_pow,
      eCNineUnit_algebraMap_C, map_ofNat]
  rw [eCNineUnitCapitalT_cube, hradicand]
  change 12 * (c * Q) - Q = 0
  calc
    12 * (c * Q) - Q = (12 * c) * Q - Q := by ring
    _ = 0 := by
      rw [hc]
      ring

end OnLeConjecture.DThree
