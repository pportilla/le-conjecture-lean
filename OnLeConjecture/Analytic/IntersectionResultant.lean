/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeierstrassPairQuotient
public import OnLeConjecture.Analytic.ResultantColength
public import OnLeConjecture.Analytic.PlaneElimination

/-!
# The resultant formula for analytic local intersection multiplicity

The polynomial and analytic quotients are identified by Weierstrass
division. Their complex dimension is therefore the order of the actual
polynomial resultant. Finite analytic intersection also implies that the
resultant is nonzero.
-/

public section

namespace OnLeConjecture.Analytic

/-- A square linear map over a domain has nonzero determinant if one
nonzero scalar annihilates its cokernel. -/
theorem det_ne_zero_of_smul_mem_range
    {R M ι : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Finite ι] (b : Module.Basis ι R M) (f : M →ₗ[R] M)
    (c : R) (hc : c ≠ 0) (h : ∀ v : M, c • v ∈ LinearMap.range f) :
    LinearMap.det f ≠ 0 := by
  classical
  let _ := Fintype.ofFinite ι
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  choose u hu using fun i ↦ h (b i)
  let g : M →ₗ[R] M := b.constr R u
  have hcomp : f.comp g = c • LinearMap.id := by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply, g, Module.Basis.constr_basis,
      LinearMap.smul_apply, LinearMap.id_apply] using hu i
  have hdet := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, mul_one] at hdet
  intro hzero
  rw [hzero, zero_mul] at hdet
  exact pow_ne_zero _ hc hdet.symm

namespace Germ

/-- A nonzero constant polynomial in the pair ideal forces a nonzero
resultant when the first polynomial is monic. -/
theorem resultant_ne_zero_of_constant_mem_pair_span
    (P Q : Polynomial (Germ 1)) (hP : P.Monic)
    (c : Germ 1) (hc : c ≠ 0)
    (hmem : Polynomial.C c ∈ Ideal.span ({P, Q} : Set (Polynomial (Germ 1)))) :
    P.resultant Q ≠ 0 := by
  classical
  let I := Ideal.span ({P, Q} : Set (Polynomial (Germ 1)))
  have hkill (z : Polynomial (Germ 1) ⧸ I) : c • z = 0 := by
    obtain ⟨S, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right S I hmem)
    have hsmul := map_smul (Ideal.Quotient.mkₐ (Germ 1) I).toLinearMap c S
    rw [Polynomial.smul_eq_C_mul] at hsmul
    exact hsmul.symm.trans hzero
  let e := sylvesterMatrixCokernelEquiv P Q hP
  have hrange (v : Fin (P.natDegree + Q.natDegree) → Germ 1) :
      c • v ∈ LinearMap.range (sylvesterCoordinateEndomorphism P Q) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply e.injective
    rw [map_zero]
    rw [Submodule.Quotient.mk_smul]
    rw [map_smul]
    exact hkill _
  simpa only [det_sylvesterCoordinateEndomorphism] using
    det_ne_zero_of_smul_mem_range (Pi.basisFun (Germ 1) _)
      (sylvesterCoordinateEndomorphism P Q) c hc hrange

/-- Finite intersection of distinguished polynomial germs forces their
resultant to be nonzero. -/
theorem resultant_ne_zero_of_hasFiniteIntersection
    (d : ℕ) (P Q : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q)) :
    P.resultant Q ≠ 0 := by
  obtain ⟨N, hN⟩ :=
    (PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le _ _).mp hfinite
  apply resultant_ne_zero_of_constant_mem_pair_span P Q hPMonic
    (coordinate (0 : Fin 1) ^ N) (pow_ne_zero _ coordinate_zero_ne_zero)
  rw [← comap_pairIdeal_firstCoordinatePolynomialEvaluation
    d P Q hPMonic hPDegree hPCoeff]
  change firstCoordinatePolynomialEvaluation
      (Polynomial.C (coordinate (0 : Fin 1) ^ N)) ∈
        PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation P)
          (firstCoordinatePolynomialEvaluation Q)
  have heval : firstCoordinatePolynomialEvaluation
      (Polynomial.C (coordinate (0 : Fin 1) ^ N)) = coordinate (1 : Fin 2) ^ N := by
    rw [firstCoordinatePolynomialEvaluation, Polynomial.eval₂_C, map_pow,
      hyperplaneExtension_coordinate_plane]
  rw [heval]
  exact hN (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (1 : Fin 2)) N)

/-- A nonzero resultant gives finite analytic intersection for a
distinguished monic first polynomial. -/
theorem hasFiniteIntersection_of_resultant_ne_zero
    (d : ℕ) (P Q : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)
    (hresultant : P.resultant Q ≠ 0) :
    PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q) := by
  let _ := polynomial_pair_quotient_moduleFinite_of_resultant_ne_zero P Q hPMonic hresultant
  exact Module.Finite.equiv
    (distinguishedWeierstrassPairQuotientAlgEquiv d P Q hPMonic hPDegree hPCoeff).toLinearEquiv

/-- The local intersection number equals the vanishing order of the
resultant whenever the first polynomial is distinguished monic and the
resultant is nonzero. -/
theorem intersectionMultiplicity_eq_resultant_order_of_ne_zero
    (d : ℕ) (P Q : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)
    (hresultant : P.resultant Q ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q)) :
    PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q) hfinite =
        (vanishingOrder (P.resultant Q)).toNat := by
  change Module.finrank ℂ _ = _
  rw [← (distinguishedWeierstrassPairQuotientAlgEquiv d P Q
    hPMonic hPDegree hPCoeff).toLinearEquiv.finrank_eq]
  exact polynomial_pair_quotient_finrank_eq_vanishingOrder_resultant_toNat
    P Q hPMonic hresultant

/-- The resultant formula for finite analytic intersections. The
nonvanishing of the resultant is a conclusion, not an extra hypothesis. -/
theorem intersectionMultiplicity_eq_resultant_order
    (d : ℕ) (P Q : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q)) :
    PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q) hfinite =
        (vanishingOrder (P.resultant Q)).toNat :=
  intersectionMultiplicity_eq_resultant_order_of_ne_zero d P Q hPMonic hPDegree hPCoeff
    (resultant_ne_zero_of_hasFiniteIntersection d P Q hPMonic hPDegree hPCoeff hfinite) hfinite

end Germ

end OnLeConjecture.Analytic
