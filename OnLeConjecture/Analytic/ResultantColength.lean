/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.SylvesterCokernel
public import OnLeConjecture.Analytic.DVRCokernel

/-!
# Resultant and colength over the analytic discrete valuation ring

The quotient by two polynomials over the one-variable analytic germ ring
is the cokernel of their actual Sylvester matrix when the first polynomial
is monic. A nonzero resultant therefore implies finite complex dimension,
and that dimension is the order of the resultant.
-/

public section

namespace OnLeConjecture.Analytic

open _root_.Polynomial Module

namespace Germ

/-- The endomorphism on coefficient vectors given by the Sylvester matrix
with the actual polynomial degrees. -/
@[expose] noncomputable def sylvesterCoordinateEndomorphism
    (P Q : Polynomial (Germ 1)) :
    (Fin (P.natDegree + Q.natDegree) → Germ 1) →ₗ[Germ 1]
      (Fin (P.natDegree + Q.natDegree) → Germ 1) :=
  Matrix.toLin' (P.sylvester Q P.natDegree Q.natDegree)

/-- The determinant here is the defined polynomial resultant, without an
additional determinant-identification hypothesis. -/
@[simp] theorem det_sylvesterCoordinateEndomorphism
    (P Q : Polynomial (Germ 1)) :
    LinearMap.det (sylvesterCoordinateEndomorphism P Q) = P.resultant Q := by
  rw [sylvesterCoordinateEndomorphism, LinearMap.det_toLin']
  rfl

/-- The Sylvester matrix cokernel is the polynomial quotient by `(P,Q)`.
The change of bases uses the matrix of `Polynomial.sylvesterMap`. -/
@[expose] noncomputable def sylvesterMatrixCokernelEquiv
    (P Q : Polynomial (Germ 1)) (hP : P.Monic) :
    ((Fin (P.natDegree + Q.natDegree) → Germ 1) ⧸
      LinearMap.range (sylvesterCoordinateEndomorphism P Q)) ≃ₗ[Germ 1]
        Polynomial (Germ 1) ⧸ Ideal.span ({P, Q} : Set (Polynomial (Germ 1))) := by
  let L := P.sylvesterMap Q (le_refl P.natDegree) (le_refl Q.natDegree)
  let b₁ := ((degreeLT.basis (Germ 1) P.natDegree).prod
    (degreeLT.basis (Germ 1) Q.natDegree)).reindex finSumFinEquiv
  let b₂ := degreeLT.basis (Germ 1) (P.natDegree + Q.natDegree)
  have hmatrix : LinearMap.toMatrix b₁ b₂ L =
      P.sylvester Q P.natDegree Q.natDegree :=
    P.toMatrix_sylvesterMap' Q (le_refl _) (le_refl _)
  have hcoordinate (x : (degreeLT (Germ 1) P.natDegree) ×
      (degreeLT (Germ 1) Q.natDegree)) :
      sylvesterCoordinateEndomorphism P Q (b₁.equivFun x) = b₂.equivFun (L x) := by
    simp only [sylvesterCoordinateEndomorphism, Matrix.toLin'_apply,
      Basis.equivFun_apply]
    rw [← hmatrix]
    exact LinearMap.toMatrix_mulVec_repr b₁ b₂ L x
  have hmap : (LinearMap.range L).map b₂.equivFun.toLinearMap =
      LinearMap.range (sylvesterCoordinateEndomorphism P Q) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨b₁.equivFun x, hcoordinate x⟩
    · rintro ⟨x, rfl⟩
      refine ⟨L (b₁.equivFun.symm x), ⟨b₁.equivFun.symm x, rfl⟩, ?_⟩
      change b₂.equivFun (L (b₁.equivFun.symm x)) = sylvesterCoordinateEndomorphism P Q x
      simpa only [LinearEquiv.apply_symm_apply] using
        (hcoordinate (b₁.equivFun.symm x)).symm
  let e := Submodule.Quotient.equiv (LinearMap.range L)
    (LinearMap.range (sylvesterCoordinateEndomorphism P Q)) b₂.equivFun hmap
  exact e.symm.trans
    (OnLeConjecture.Polynomial.sylvesterCokernelEquiv P Q hP rfl le_rfl)

/-- A square endomorphism over the analytic discrete valuation ring with
nonzero determinant has a finite dimensional complex cokernel. -/
theorem quotient_range_moduleFinite_of_det_ne_zero
    {ι : Type*} [Finite ι]
    (f : (ι → Germ 1) →ₗ[Germ 1] (ι → Germ 1))
    (hdet : LinearMap.det f ≠ 0) :
    Module.Finite ℂ ((ι → Germ 1) ⧸ LinearMap.range f) := by
  classical
  let _ := Fintype.ofFinite ι
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hker)
  let N : Submodule (Germ 1) (ι → Germ 1) := LinearMap.range f
  let b : Basis ι (Germ 1) (ι → Germ 1) := Pi.basisFun (Germ 1) ι
  have hrank : Module.finrank (Germ 1) N =
      Module.finrank (Germ 1) (ι → Germ 1) := LinearMap.finrank_range_of_inj hf
  let _ (i : ι) : Module.Finite ℂ
      (Germ 1 ⧸ Ideal.span {N.smithNormalFormCoeffs b hrank i}) :=
    Germ.quotient_span_moduleFinite (N.smithNormalFormCoeffs_ne_zero b hrank i)
  let e := (N.quotientEquivPiSpan b hrank).restrictScalars ℂ
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- A nonzero resultant makes the polynomial pair quotient finite
dimensional over the complex numbers. -/
theorem polynomial_pair_quotient_moduleFinite_of_resultant_ne_zero
    (P Q : Polynomial (Germ 1)) (hP : P.Monic)
    (hresultant : P.resultant Q ≠ 0) :
    Module.Finite ℂ
      (Polynomial (Germ 1) ⧸ Ideal.span ({P, Q} : Set (Polynomial (Germ 1)))) := by
  have hdet : LinearMap.det (sylvesterCoordinateEndomorphism P Q) ≠ 0 := by
    simpa only [det_sylvesterCoordinateEndomorphism] using hresultant
  let _ := quotient_range_moduleFinite_of_det_ne_zero
    (sylvesterCoordinateEndomorphism P Q) hdet
  let e := (sylvesterMatrixCokernelEquiv P Q hP).restrictScalars ℂ
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

/-- The complex colength of a polynomial pair with monic first polynomial
and nonzero resultant equals the vanishing order of that resultant. -/
theorem polynomial_pair_quotient_finrank_eq_vanishingOrder_resultant_toNat
    (P Q : Polynomial (Germ 1)) (hP : P.Monic)
    (hresultant : P.resultant Q ≠ 0) :
    Module.finrank ℂ
      (Polynomial (Germ 1) ⧸ Ideal.span ({P, Q} : Set (Polynomial (Germ 1)))) =
        (Germ.vanishingOrder (P.resultant Q)).toNat := by
  have hdet : LinearMap.det (sylvesterCoordinateEndomorphism P Q) ≠ 0 := by
    simpa only [det_sylvesterCoordinateEndomorphism] using hresultant
  calc
    Module.finrank ℂ
        (Polynomial (Germ 1) ⧸ Ideal.span ({P, Q} : Set (Polynomial (Germ 1)))) =
        Module.finrank ℂ ((Fin (P.natDegree + Q.natDegree) → Germ 1) ⧸
          LinearMap.range (sylvesterCoordinateEndomorphism P Q)) :=
      ((sylvesterMatrixCokernelEquiv P Q hP).restrictScalars ℂ).finrank_eq.symm
    _ = (Germ.vanishingOrder (LinearMap.det (sylvesterCoordinateEndomorphism P Q))).toNat :=
      Germ.finrank_quotient_range_eq_vanishingOrder_det_toNat
        (sylvesterCoordinateEndomorphism P Q) hdet
    _ = (Germ.vanishingOrder (P.resultant Q)).toNat := by
      rw [det_sylvesterCoordinateEndomorphism]

end Germ

end OnLeConjecture.Analytic
