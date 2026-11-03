/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineAffineNormSupport
public import OnLeConjecture.DThree.ECNineGlobalNormMatrix

/-!
# Reciprocity at the boundary of the C9 norm

The fibres over `z` and `z⁻¹` are isomorphic when `z` is nonzero. The
isomorphism exchanges the two cubic roots and scales them by `z⁻¹`.
For a homogeneous source form, it sends the difference section over `z⁻¹`
to the negative of the section over `z`, scaled by `z⁻ᴺ`. Invariance of
the algebra norm yields reciprocity of the determinant polynomial.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial Module

theorem eCNineUnitFirstRadicand_eval_inv
    {z : ℂ} (hz : z ≠ 0) :
    eCNineUnitFirstRadicand.eval z⁻¹ =
      (z⁻¹) ^ 3 * eCNineUnitSecondRadicand.eval z := by
  rw [eCNineUnitFirstRadicand, eCNineUnitSecondRadicand]
  simp only [eval_neg, eval_mul, eval_C, eval_sub, eval_X,
    eval_add, eval_pow]
  field_simp
  ring

theorem eCNineUnitSecondRadicand_eval_inv
    {z : ℂ} (hz : z ≠ 0) :
    eCNineUnitSecondRadicand.eval z⁻¹ =
      (z⁻¹) ^ 3 * eCNineUnitFirstRadicand.eval z := by
  rw [eCNineUnitFirstRadicand, eCNineUnitSecondRadicand]
  simp only [eval_neg, eval_mul, eval_C, eval_sub, eval_X,
    eval_add, eval_pow]
  field_simp
  ring

/-- The first root in a specialized fibre. -/
def eCNineFiberT (z : ℂ) : ECNineFiberAlgebra z :=
  algebraMap (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z)
    (AdjoinRoot.root (eCNineFiberFirstPolynomial z))

/-- The second root in a specialized fibre. -/
def eCNineFiberCapitalT (z : ℂ) : ECNineFiberAlgebra z :=
  AdjoinRoot.root (eCNineFiberSecondPolynomial z)

theorem eCNineFiberFirstRoot_cube (z : ℂ) :
    AdjoinRoot.root (eCNineFiberFirstPolynomial z) ^ 3 =
      algebraMap ℂ (ECNineFiberFirstAlgebra z)
        (eCNineUnitFirstRadicand.eval z) := by
  have h := AdjoinRoot.eval₂_root (eCNineFiberFirstPolynomial z)
  rw [eCNineFiberFirstPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, sub_eq_zero] at h
  exact h

theorem eCNineFiberSecondRoot_cube (z : ℂ) :
    AdjoinRoot.root (eCNineFiberSecondPolynomial z) ^ 3 =
      algebraMap (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z)
        (algebraMap ℂ (ECNineFiberFirstAlgebra z)
          (eCNineUnitSecondRadicand.eval z)) := by
  have h := AdjoinRoot.eval₂_root (eCNineFiberSecondPolynomial z)
  rw [eCNineFiberSecondPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, sub_eq_zero] at h
  exact h

theorem eCNineFiberT_cube (z : ℂ) :
    eCNineFiberT z ^ 3 =
      algebraMap ℂ (ECNineFiberAlgebra z)
        (eCNineUnitFirstRadicand.eval z) := by
  rw [eCNineFiberT, ← map_pow, eCNineFiberFirstRoot_cube]
  exact IsScalarTower.algebraMap_apply ℂ
    (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z) _

theorem eCNineFiberCapitalT_cube (z : ℂ) :
    eCNineFiberCapitalT z ^ 3 =
      algebraMap ℂ (ECNineFiberAlgebra z)
        (eCNineUnitSecondRadicand.eval z) := by
  rw [eCNineFiberCapitalT, eCNineFiberSecondRoot_cube]
  exact IsScalarTower.algebraMap_apply ℂ
    (ECNineFiberFirstAlgebra z) (ECNineFiberAlgebra z) _

/-- The first stage of the reciprocal fibre map. -/
def eCNineReciprocalFirstMap (z : ℂ) (hz : z ≠ 0) :
    ECNineFiberFirstAlgebra z⁻¹ →ₐ[ℂ] ECNineFiberAlgebra z :=
  AdjoinRoot.liftAlgHom (eCNineFiberFirstPolynomial z⁻¹)
    (Algebra.ofId ℂ (ECNineFiberAlgebra z))
    (algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
      eCNineFiberCapitalT z) (by
        have hp : eCNineFiberFirstPolynomial z⁻¹ =
            X ^ 3 - C (eCNineUnitFirstRadicand.eval z⁻¹) := by
          rfl
        rw [hp, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        change (algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
            eCNineFiberCapitalT z) ^ 3 -
          algebraMap ℂ (ECNineFiberAlgebra z)
            (eCNineUnitFirstRadicand.eval z⁻¹) = 0
        rw [mul_pow, eCNineFiberCapitalT_cube, ← map_pow, ← map_mul,
          eCNineUnitFirstRadicand_eval_inv hz, sub_self])

@[simp]
theorem eCNineReciprocalFirstMap_root (z : ℂ) (hz : z ≠ 0) :
    eCNineReciprocalFirstMap z hz
        (AdjoinRoot.root (eCNineFiberFirstPolynomial z⁻¹)) =
      algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
        eCNineFiberCapitalT z := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem eCNineReciprocalFirstMap_algebraMap
    (z : ℂ) (hz : z ≠ 0) (c : ℂ) :
    eCNineReciprocalFirstMap z hz
        (algebraMap ℂ (ECNineFiberFirstAlgebra z⁻¹) c) =
      algebraMap ℂ (ECNineFiberAlgebra z) c := by
  exact (eCNineReciprocalFirstMap z hz).commutes c

theorem eCNineReciprocalSecondPolynomial_eval_zero
    (z : ℂ) (hz : z ≠ 0) :
    (eCNineFiberSecondPolynomial z⁻¹).eval₂
        (eCNineReciprocalFirstMap z hz)
        (algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
          eCNineFiberT z) = 0 := by
  have hp : eCNineFiberSecondPolynomial z⁻¹ =
      X ^ 3 - C (algebraMap ℂ (ECNineFiberFirstAlgebra z⁻¹)
        (eCNineUnitSecondRadicand.eval z⁻¹)) := by
    rfl
  rw [hp, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
      eCNineFiberT z) ^ 3 -
    eCNineReciprocalFirstMap z hz
      (algebraMap ℂ (ECNineFiberFirstAlgebra z⁻¹)
        (eCNineUnitSecondRadicand.eval z⁻¹)) = 0
  rw [mul_pow, eCNineReciprocalFirstMap_algebraMap,
    eCNineFiberT_cube, ← map_pow, ← map_mul,
    eCNineUnitSecondRadicand_eval_inv hz, sub_self]

/-- The reciprocal map exchanges the two specialized cubic roots. -/
def eCNineReciprocalMap (z : ℂ) (hz : z ≠ 0) :
    ECNineFiberAlgebra z⁻¹ →ₐ[ℂ] ECNineFiberAlgebra z :=
  AdjoinRoot.liftAlgHom (eCNineFiberSecondPolynomial z⁻¹)
    (eCNineReciprocalFirstMap z hz)
    (algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ * eCNineFiberT z)
    (eCNineReciprocalSecondPolynomial_eval_zero z hz)

@[simp]
theorem eCNineReciprocalMap_root (z : ℂ) (hz : z ≠ 0) :
    eCNineReciprocalMap z hz
        (AdjoinRoot.root (eCNineFiberSecondPolynomial z⁻¹)) =
      algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
        eCNineFiberT z := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem eCNineReciprocalMap_algebraMap_first
    (z : ℂ) (hz : z ≠ 0) (q : ECNineFiberFirstAlgebra z⁻¹) :
    eCNineReciprocalMap z hz
        (algebraMap (ECNineFiberFirstAlgebra z⁻¹)
          (ECNineFiberAlgebra z⁻¹) q) =
      eCNineReciprocalFirstMap z hz q := by
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ q

@[simp]
theorem eCNineReciprocalMap_t (z : ℂ) (hz : z ≠ 0) :
    eCNineReciprocalMap z hz (eCNineFiberT z⁻¹) =
      algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
        eCNineFiberCapitalT z := by
  rw [eCNineFiberT, eCNineReciprocalMap_algebraMap_first,
    eCNineReciprocalFirstMap_root]

@[simp]
theorem eCNineReciprocalMap_capitalT (z : ℂ) (hz : z ≠ 0) :
    eCNineReciprocalMap z hz (eCNineFiberCapitalT z⁻¹) =
      algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
        eCNineFiberT z := by
  exact eCNineReciprocalMap_root z hz

theorem eCNineUnitFirstRadicand_eval_from_inv
    {z : ℂ} (hz : z ≠ 0) :
    z ^ 3 * eCNineUnitSecondRadicand.eval z⁻¹ =
      eCNineUnitFirstRadicand.eval z := by
  rw [eCNineUnitSecondRadicand_eval_inv hz]
  field_simp

theorem eCNineUnitSecondRadicand_eval_from_inv
    {z : ℂ} (hz : z ≠ 0) :
    z ^ 3 * eCNineUnitFirstRadicand.eval z⁻¹ =
      eCNineUnitSecondRadicand.eval z := by
  rw [eCNineUnitFirstRadicand_eval_inv hz]
  field_simp

/-- The first stage of the reciprocal map in the opposite direction. -/
def eCNineReciprocalReverseFirstMap (z : ℂ) (hz : z ≠ 0) :
    ECNineFiberFirstAlgebra z →ₐ[ℂ] ECNineFiberAlgebra z⁻¹ :=
  AdjoinRoot.liftAlgHom (eCNineFiberFirstPolynomial z)
    (Algebra.ofId ℂ (ECNineFiberAlgebra z⁻¹))
    (algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z *
      eCNineFiberCapitalT z⁻¹) (by
        have hp : eCNineFiberFirstPolynomial z =
            X ^ 3 - C (eCNineUnitFirstRadicand.eval z) := by
          rfl
        rw [hp, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        change (algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z *
            eCNineFiberCapitalT z⁻¹) ^ 3 -
          algebraMap ℂ (ECNineFiberAlgebra z⁻¹)
            (eCNineUnitFirstRadicand.eval z) = 0
        rw [mul_pow, eCNineFiberCapitalT_cube, ← map_pow, ← map_mul,
          eCNineUnitFirstRadicand_eval_from_inv hz, sub_self])

@[simp]
theorem eCNineReciprocalReverseFirstMap_root
    (z : ℂ) (hz : z ≠ 0) :
    eCNineReciprocalReverseFirstMap z hz
        (AdjoinRoot.root (eCNineFiberFirstPolynomial z)) =
      algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z *
        eCNineFiberCapitalT z⁻¹ := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem eCNineReciprocalReverseSecondPolynomial_eval_zero
    (z : ℂ) (hz : z ≠ 0) :
    (eCNineFiberSecondPolynomial z).eval₂
        (eCNineReciprocalReverseFirstMap z hz)
        (algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z *
          eCNineFiberT z⁻¹) = 0 := by
  have hp : eCNineFiberSecondPolynomial z =
      X ^ 3 - C (algebraMap ℂ (ECNineFiberFirstAlgebra z)
        (eCNineUnitSecondRadicand.eval z)) := by
    rfl
  rw [hp, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z *
      eCNineFiberT z⁻¹) ^ 3 -
    eCNineReciprocalReverseFirstMap z hz
      (algebraMap ℂ (ECNineFiberFirstAlgebra z)
        (eCNineUnitSecondRadicand.eval z)) = 0
  rw [mul_pow, (eCNineReciprocalReverseFirstMap z hz).commutes,
    eCNineFiberT_cube,
    ← map_pow, ← map_mul,
    eCNineUnitSecondRadicand_eval_from_inv hz, sub_self]

/-- The reciprocal map in the opposite direction. -/
def eCNineReciprocalReverseMap (z : ℂ) (hz : z ≠ 0) :
    ECNineFiberAlgebra z →ₐ[ℂ] ECNineFiberAlgebra z⁻¹ :=
  AdjoinRoot.liftAlgHom (eCNineFiberSecondPolynomial z)
    (eCNineReciprocalReverseFirstMap z hz)
    (algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z * eCNineFiberT z⁻¹)
    (eCNineReciprocalReverseSecondPolynomial_eval_zero z hz)

@[simp]
theorem eCNineReciprocalReverseMap_t (z : ℂ) (hz : z ≠ 0) :
    eCNineReciprocalReverseMap z hz (eCNineFiberT z) =
      algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z *
        eCNineFiberCapitalT z⁻¹ := by
  rw [eCNineFiberT]
  rw [eCNineReciprocalReverseMap]
  change (AdjoinRoot.liftAlgHom (eCNineFiberSecondPolynomial z)
      (eCNineReciprocalReverseFirstMap z hz)
      (algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z * eCNineFiberT z⁻¹)
      (eCNineReciprocalReverseSecondPolynomial_eval_zero z hz))
      (AdjoinRoot.of (eCNineFiberSecondPolynomial z)
        (AdjoinRoot.root (eCNineFiberFirstPolynomial z))) = _
  rw [AdjoinRoot.liftAlgHom_of,
    eCNineReciprocalReverseFirstMap_root]

@[simp]
theorem eCNineReciprocalReverseMap_capitalT
    (z : ℂ) (hz : z ≠ 0) :
    eCNineReciprocalReverseMap z hz (eCNineFiberCapitalT z) =
      algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z *
        eCNineFiberT z⁻¹ := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem eCNineReciprocalMap_comp_reverse
    (z : ℂ) (hz : z ≠ 0) :
    (eCNineReciprocalMap z hz).comp (eCNineReciprocalReverseMap z hz) =
      AlgHom.id ℂ (ECNineFiberAlgebra z) := by
  apply AdjoinRoot.algHom_ext'
  · apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro c
      change eCNineReciprocalMap z hz
          (eCNineReciprocalReverseMap z hz
            (algebraMap ℂ (ECNineFiberAlgebra z) c)) =
        algebraMap ℂ (ECNineFiberAlgebra z) c
      rw [(eCNineReciprocalReverseMap z hz).commutes,
        (eCNineReciprocalMap z hz).commutes]
    · simp only [AlgHom.comp_apply, AlgHom.id_apply]
      change eCNineReciprocalMap z hz
          (eCNineReciprocalReverseMap z hz (eCNineFiberT z)) =
        eCNineFiberT z
      rw [eCNineReciprocalReverseMap_t, map_mul,
        (eCNineReciprocalMap z hz).commutes,
        eCNineReciprocalMap_capitalT]
      rw [← mul_assoc, ← map_mul]
      simp [hz]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change eCNineReciprocalMap z hz
        (eCNineReciprocalReverseMap z hz (eCNineFiberCapitalT z)) =
      eCNineFiberCapitalT z
    rw [eCNineReciprocalReverseMap_capitalT, map_mul,
      (eCNineReciprocalMap z hz).commutes,
      eCNineReciprocalMap_t]
    rw [← mul_assoc, ← map_mul]
    simp [hz]

theorem eCNineReciprocalReverse_comp_map
    (z : ℂ) (hz : z ≠ 0) :
    (eCNineReciprocalReverseMap z hz).comp (eCNineReciprocalMap z hz) =
      AlgHom.id ℂ (ECNineFiberAlgebra z⁻¹) := by
  apply AdjoinRoot.algHom_ext'
  · apply AdjoinRoot.algHom_ext'
    · apply AlgHom.ext
      intro c
      change eCNineReciprocalReverseMap z hz
          (eCNineReciprocalMap z hz
            (algebraMap ℂ (ECNineFiberAlgebra z⁻¹) c)) =
        algebraMap ℂ (ECNineFiberAlgebra z⁻¹) c
      rw [(eCNineReciprocalMap z hz).commutes,
        (eCNineReciprocalReverseMap z hz).commutes]
    · simp only [AlgHom.comp_apply, AlgHom.id_apply]
      change eCNineReciprocalReverseMap z hz
          (eCNineReciprocalMap z hz (eCNineFiberT z⁻¹)) =
        eCNineFiberT z⁻¹
      rw [eCNineReciprocalMap_t, map_mul,
        (eCNineReciprocalReverseMap z hz).commutes,
        eCNineReciprocalReverseMap_capitalT]
      rw [← mul_assoc, ← map_mul]
      simp [hz]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change eCNineReciprocalReverseMap z hz
        (eCNineReciprocalMap z hz (eCNineFiberCapitalT z⁻¹)) =
      eCNineFiberCapitalT z⁻¹
    rw [eCNineReciprocalMap_capitalT, map_mul,
      (eCNineReciprocalReverseMap z hz).commutes,
      eCNineReciprocalReverseMap_t]
    rw [← mul_assoc, ← map_mul]
    simp [hz]

/-- The reciprocal equivalence between the two specialized fibres. -/
def eCNineReciprocalEquiv (z : ℂ) (hz : z ≠ 0) :
    ECNineFiberAlgebra z⁻¹ ≃ₐ[ℂ] ECNineFiberAlgebra z :=
  AlgEquiv.ofAlgHom (eCNineReciprocalMap z hz)
    (eCNineReciprocalReverseMap z hz)
    (eCNineReciprocalMap_comp_reverse z hz)
    (eCNineReciprocalReverse_comp_map z hz)

theorem eCNineReciprocalEquiv_apply (z : ℂ) (hz : z ≠ 0)
    (a : ECNineFiberAlgebra z⁻¹) :
    eCNineReciprocalEquiv z hz a = eCNineReciprocalMap z hz a := by
  rfl

@[simp]
theorem eCNineUnitFiberSpecialization_t (z : ℂ) :
    eCNineUnitFiberSpecialization z eCNineUnitT = eCNineFiberT z := by
  rw [eCNineUnitT, eCNineFiberT,
    eCNineUnitFiberSpecialization_algebraMap_first,
    eCNineUnitFirstFiberSpecialization_root]

@[simp]
theorem eCNineUnitFiberSpecialization_capitalT (z : ℂ) :
    eCNineUnitFiberSpecialization z eCNineUnitCapitalT =
      eCNineFiberCapitalT z := by
  exact eCNineUnitFiberSpecialization_root z

@[simp]
theorem eCNineUnitFiberSpecialization_capitalX (z : ℂ) :
    eCNineUnitFiberSpecialization z eCNineUnitCapitalX =
      algebraMap ℂ (ECNineFiberAlgebra z) z := by
  rw [eCNineUnitCapitalX, eCNineUnitFiberSpecialization_algebraMap]
  simp

theorem hom_sourceForm_eval₂
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (R : Form ℂ) (x : Fin 2 → A) :
    f (MvPolynomial.eval₂ (algebraMap ℂ A) x R) =
      MvPolynomial.eval₂ (algebraMap ℂ B) (fun i ↦ f (x i)) R := by
  change f.toRingHom (MvPolynomial.eval₂ (algebraMap ℂ A) x R) = _
  rw [MvPolynomial.hom_eval₂ R (algebraMap ℂ A) f.toRingHom x]
  congr 1
  apply RingHom.ext
  intro c
  exact f.commutes c

theorem eCNineUnitFiberSpecialization_sourceForm
    (z : ℂ) (R : Form ℂ) (x : Fin 2 → ECNineUnitAlgebra) :
    eCNineUnitFiberSpecialization z
        (MvPolynomial.eval₂ (algebraMap ℂ ECNineUnitAlgebra) x R) =
      MvPolynomial.eval₂ (algebraMap ℂ (ECNineFiberAlgebra z))
        (fun i ↦ eCNineUnitFiberSpecialization z (x i)) R := by
  rw [MvPolynomial.hom_eval₂ R (algebraMap ℂ ECNineUnitAlgebra)
    (eCNineUnitFiberSpecialization z) x]
  congr 1
  apply RingHom.ext
  intro c
  exact eCNineUnitFiberSpecialization_algebraMap_complex z c

theorem eCNineUnitFiberSpecialization_differenceElement
    (z : ℂ) (R : Form ℂ) :
    eCNineUnitFiberSpecialization z (eCNineUnitDifferenceElement R) =
      MvPolynomial.eval₂ (algebraMap ℂ (ECNineFiberAlgebra z))
          ![1, eCNineFiberT z] R -
        MvPolynomial.eval₂ (algebraMap ℂ (ECNineFiberAlgebra z))
          ![algebraMap ℂ (ECNineFiberAlgebra z) z,
            eCNineFiberCapitalT z] R := by
  rw [eCNineUnitDifferenceElement, map_sub,
    eCNineUnitFiberSpecialization_sourceForm,
    eCNineUnitFiberSpecialization_sourceForm]
  congr 2
  · funext i
    fin_cases i
    · simp
    · simp
  · funext i
    fin_cases i
    · simp
    · simp

/-- Scaling both arguments of a homogeneous form scales its value by the
corresponding power. -/
theorem eval₂_smul_of_isHomogeneous
    {A : Type*} [CommRing A] [Algebra ℂ A]
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (c : A) (x : Fin 2 → A) :
    MvPolynomial.eval₂ (algebraMap ℂ A) (fun i ↦ c * x i) R =
      c ^ N * MvPolynomial.eval₂ (algebraMap ℂ A) x R := by
  induction hR using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, ihp, ihq]
      ring
  | monomial d r hr =>
      rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial]
      simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      have hdegree : ∑ i ∈ d.support, d i = N := by
        simpa [Finsupp.weight_apply, Finsupp.sum] using hr
      rw [hdegree]
      ring

theorem eCNine_eval₂_scaled_first
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    {z : ℂ} (hz : z ≠ 0) :
    algebraMap ℂ (ECNineFiberAlgebra z) (z ^ N) *
        MvPolynomial.eval₂ (algebraMap ℂ (ECNineFiberAlgebra z))
          ![1, algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
            eCNineFiberCapitalT z] R =
      MvPolynomial.eval₂ (algebraMap ℂ (ECNineFiberAlgebra z))
        ![algebraMap ℂ (ECNineFiberAlgebra z) z,
          eCNineFiberCapitalT z] R := by
  have hscale := eval₂_smul_of_isHomogeneous hR
    (algebraMap ℂ (ECNineFiberAlgebra z) z)
    ![1, algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
      eCNineFiberCapitalT z]
  rw [← map_pow] at hscale
  rw [← hscale]
  congr 1
  funext i
  fin_cases i
  · simp
  · change algebraMap ℂ (ECNineFiberAlgebra z) z *
        (algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
          eCNineFiberCapitalT z) = eCNineFiberCapitalT z
    rw [← mul_assoc, ← map_mul]
    simp [hz]

theorem eCNine_eval₂_scaled_second
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    {z : ℂ} (hz : z ≠ 0) :
    algebraMap ℂ (ECNineFiberAlgebra z) (z ^ N) *
        MvPolynomial.eval₂ (algebraMap ℂ (ECNineFiberAlgebra z))
          ![algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹,
            algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
              eCNineFiberT z] R =
      MvPolynomial.eval₂ (algebraMap ℂ (ECNineFiberAlgebra z))
        ![1, eCNineFiberT z] R := by
  have hscale := eval₂_smul_of_isHomogeneous hR
    (algebraMap ℂ (ECNineFiberAlgebra z) z)
    ![algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹,
      algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ * eCNineFiberT z]
  rw [← map_pow] at hscale
  rw [← hscale]
  congr 1
  funext i
  fin_cases i
  · change algebraMap ℂ (ECNineFiberAlgebra z) z *
        algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ = 1
    rw [← map_mul]
    simp [hz]
  · change algebraMap ℂ (ECNineFiberAlgebra z) z *
        (algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
          eCNineFiberT z) = eCNineFiberT z
    rw [← mul_assoc, ← map_mul]
    simp [hz]

theorem eCNineReciprocalMap_differenceElement
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    {z : ℂ} (hz : z ≠ 0) :
    algebraMap ℂ (ECNineFiberAlgebra z) (z ^ N) *
        eCNineReciprocalMap z hz
          (eCNineUnitFiberSpecialization z⁻¹
            (eCNineUnitDifferenceElement R)) =
      -(eCNineUnitFiberSpecialization z
        (eCNineUnitDifferenceElement R)) := by
  rw [eCNineUnitFiberSpecialization_differenceElement,
    eCNineUnitFiberSpecialization_differenceElement, map_sub,
    hom_sourceForm_eval₂, hom_sourceForm_eval₂]
  have hfirst :
      (fun i ↦ eCNineReciprocalMap z hz
        (![1, eCNineFiberT z⁻¹] i)) =
        ![1, algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
          eCNineFiberCapitalT z] := by
    funext i
    fin_cases i
    · simp
    · exact eCNineReciprocalMap_t z hz
  have hsecond :
      (fun i ↦ eCNineReciprocalMap z hz
        (![algebraMap ℂ (ECNineFiberAlgebra z⁻¹) z⁻¹,
          eCNineFiberCapitalT z⁻¹] i)) =
        ![algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹,
          algebraMap ℂ (ECNineFiberAlgebra z) z⁻¹ *
            eCNineFiberT z] := by
    funext i
    fin_cases i
    · exact (eCNineReciprocalMap z hz).commutes z⁻¹
    · exact eCNineReciprocalMap_capitalT z hz
  rw [hfirst, hsecond, mul_sub,
    eCNine_eval₂_scaled_first hR hz,
    eCNine_eval₂_scaled_second hR hz]
  ring

theorem eCNineFiberAlgebra_finrank (z : ℂ) :
    Module.finrank ℂ (ECNineFiberAlgebra z) = 9 := by
  rw [Module.finrank_eq_card_basis (eCNineFiberBasis z)]
  norm_num

theorem eCNineFiber_norm_neg (z : ℂ) (a : ECNineFiberAlgebra z) :
    Algebra.norm ℂ (-a) = -Algebra.norm ℂ a := by
  rw [show -a = algebraMap ℂ (ECNineFiberAlgebra z) (-1) * a by simp,
    map_mul, Algebra.norm_algebraMap, eCNineFiberAlgebra_finrank]
  norm_num

/-- The norm polynomial is anti reciprocal in its two projective chart
coordinates. -/
theorem eCNineUnitDifferenceNorm_eval_reciprocity
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    {z : ℂ} (hz : z ≠ 0) :
    z ^ (9 * N) * (eCNineUnitDifferenceNorm R).eval z⁻¹ =
      -(eCNineUnitDifferenceNorm R).eval z := by
  let qInv := eCNineUnitFiberSpecialization z⁻¹
    (eCNineUnitDifferenceElement R)
  let q := eCNineUnitFiberSpecialization z
    (eCNineUnitDifferenceElement R)
  let e := eCNineReciprocalEquiv z hz
  have hsection : algebraMap ℂ (ECNineFiberAlgebra z) (z ^ N) * e qInv = -q := by
    simpa only [qInv, q, e, eCNineReciprocalEquiv_apply] using
      eCNineReciprocalMap_differenceElement hR hz
  have hnorm := congrArg (Algebra.norm ℂ) hsection
  rw [map_mul, Algebra.norm_algebraMap, eCNineFiberAlgebra_finrank,
    Algebra.norm_eq_of_algEquiv e qInv,
    eCNineFiber_norm_neg] at hnorm
  rw [eCNineUnitDifferenceNorm_eval R z⁻¹,
    eCNineUnitDifferenceNorm_eval R z]
  change z ^ (9 * N) * Algebra.norm ℂ qInv = -Algebra.norm ℂ q
  calc
    z ^ (9 * N) * Algebra.norm ℂ qInv =
        (z ^ N) ^ 9 * Algebra.norm ℂ qInv := by
      rw [← pow_mul]
      congr 2
      omega
    _ = -Algebra.norm ℂ q := hnorm

theorem eval_reflect_eq_pow_mul_eval_inv
    {p : ℂ[X]} {D : ℕ} (hp : p.natDegree ≤ D)
    {z : ℂ} (hz : z ≠ 0) :
    (p.reflect D).eval z = z ^ D * p.eval z⁻¹ := by
  apply Polynomial.induction_with_natDegree_le
    (fun q ↦ (q.reflect D).eval z = z ^ D * q.eval z⁻¹)
      (N := D)
  · simp
  · intro n r _hr hn
    have hpower : z ^ (D - n) = z ^ D * (z⁻¹) ^ n := by
      calc
        z ^ (D - n) = z ^ (D - n) * (z * z⁻¹) ^ n := by
          simp [hz]
        _ = z ^ (D - n) * (z ^ n * (z⁻¹) ^ n) := by
          rw [mul_pow]
        _ = z ^ D * (z⁻¹) ^ n := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
    rw [Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_le hn,
      Polynomial.eval_C_mul, Polynomial.eval_X_pow,
      Polynomial.eval_C_mul, Polynomial.eval_X_pow, hpower]
    ring
  · intro f g _hdegree _hg hf hg
    rw [Polynomial.reflect_add, Polynomial.eval_add,
      Polynomial.eval_add, hf, hg]
    ring
  · exact hp

/-- Reflection at the global degree changes the C9 norm by a sign. -/
theorem eCNineUnitDifferenceNorm_reflect_eq_neg
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    (eCNineUnitDifferenceNorm R).reflect (9 * N) =
      -eCNineUnitDifferenceNorm R := by
  let p := eCNineUnitDifferenceNorm R
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_singleton (0 : ℂ)).infinite_compl.mono
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  change ((eCNineUnitDifferenceNorm R).reflect (9 * N)).eval z =
    (-eCNineUnitDifferenceNorm R).eval z
  rw [eval_reflect_eq_pow_mul_eval_inv
      (eCNineUnitDifferenceNorm_natDegree_le hR) hz,
    Polynomial.eval_neg,
    eCNineUnitDifferenceNorm_eval_reciprocity hR hz]

/-- The two chart norm values at the boundary origin differ by a sign. -/
theorem eCNineBoundary_norm_eval_zero
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    (eCNineCapitalXChartDifferenceNorm R N).eval 0 =
      -(eCNineUnitDifferenceNorm R).eval 0 := by
  rw [eCNineCapitalXChartDifferenceNorm,
    eCNineUnitDifferenceNorm_reflect_eq_neg hR,
    Polynomial.eval_neg]

end OnLeConjecture.DThree
