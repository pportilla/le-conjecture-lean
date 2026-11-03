/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.SylvesterCokernel
public import OnLeConjecture.Analytic.AnalyticImplicitFunction
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Multiplication near coprime monic complex polynomials

Coefficient vectors of fixed finite length describe the lower terms of
monic polynomials. The derivative of multiplication at a coprime pair is
the Sylvester map, whose inverse is supplied by its adjugate and nonzero
resultant. All analytic maps below act on finite-dimensional complex
coefficient spaces.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial
open Filter
open scoped Topology

/-- The polynomial with the specified finite list of coefficients and
zero coefficients in all higher degrees. -/
@[expose] noncomputable def coefficientPolynomial
    {R : Type*} [CommRing R] (m : ℕ) : (Fin m → R) →ₗ[R] R[X] :=
  (degreeLT R m).subtype.comp (degreeLTEquiv R m).symm.toLinearMap

theorem coefficientPolynomial_eq_sum
    {R : Type*} [CommRing R] (m : ℕ) (u : Fin m → R) :
    coefficientPolynomial m u = ∑ j : Fin m, monomial j (u j) := rfl

theorem coefficientPolynomial_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) (u : Fin m → R) :
    (coefficientPolynomial m u).map φ = coefficientPolynomial m (fun j ↦ φ (u j)) := by
  simp only [coefficientPolynomial_eq_sum, Polynomial.map_sum, Polynomial.map_monomial]

theorem coefficientPolynomial_degree_lt
    {R : Type*} [CommRing R] (m : ℕ) (u : Fin m → R) :
    (coefficientPolynomial m u).degree < (m : ℕ) :=
  mem_degreeLT.mp ((degreeLTEquiv R m).symm u).property

@[simp] theorem coefficientPolynomial_coeff
    {R : Type*} [CommRing R] (m : ℕ) (u : Fin m → R) (j : Fin m) :
    (coefficientPolynomial m u).coeff j = u j := by
  exact congrFun ((degreeLTEquiv R m).apply_symm_apply u) j

/-- The finite coefficient vector reconstructs every polynomial satisfying
the stated degree bound. -/
theorem coefficientPolynomial_coefficients
    {R : Type*} [CommRing R] (m : ℕ) (P : R[X]) (hP : P.degree < (m : ℕ)) :
    coefficientPolynomial m (fun j : Fin m ↦ P.coeff j) = P := by
  exact congrArg Subtype.val ((degreeLTEquiv R m).symm_apply_apply
    ⟨P, mem_degreeLT.mpr hP⟩)

/-- Perturbing only coefficients strictly below the monic degree preserves
both monicity and that degree. -/
theorem monic_add_coefficientPolynomial
    {R : Type*} [CommRing R] [Nontrivial R] (m : ℕ) (P : R[X])
    (hP : P.Monic) (hPm : P.natDegree = m) (u : Fin m → R) :
    (P + coefficientPolynomial m u).Monic ∧ (P + coefficientPolynomial m u).natDegree = m := by
  have hdegree : (coefficientPolynomial m u).degree < P.degree := by
    rw [degree_eq_natDegree hP.ne_zero, hPm]
    exact coefficientPolynomial_degree_lt m u
  exact ⟨hP.add_of_left hdegree, (natDegree_add_eq_left_of_degree_lt hdegree).trans hPm⟩

/-- Coprimality makes the bounded polynomial Sylvester map bijective.
Both degree-zero cases are included. -/
theorem sylvesterMap_bijective_of_isCoprime
    (m n : ℕ) (P Q : ℂ[X]) (hP : P.Monic)
    (hPm : P.natDegree = m) (hQn : Q.natDegree = n) (hcoprime : IsCoprime P Q) :
    Function.Bijective (sylvesterMap P Q hPm.le hQn.le) := by
  let L := sylvesterMap P Q hPm.le hQn.le
  let A := adjSylvester (m := m) (n := n) P Q
  let c := P.resultant Q m n
  have hc : c ≠ 0 := by
    have hunit := (isUnit_resultant_iff_isCoprime hP).mpr hcoprime
    simpa only [c, ← hPm, ← hQn] using hunit.ne_zero
  have hleft (w : ℂ[X]_m × ℂ[X]_n) : A (L w) = c • w := by
    exact LinearMap.congr_fun (adjSylvester_comp_sylveserMap P Q hPm.le hQn.le) w
  have hright (w : ℂ[X]_(m + n)) : L (A w) = c • w := by
    exact LinearMap.congr_fun (sylveserMap_comp_adjSylvester P Q hPm.le hQn.le) w
  constructor
  · intro u v huv
    apply (smul_right_injective _ hc)
    change c • u = c • v
    rw [← hleft, ← hleft, huv]
  · intro w
    refine ⟨c⁻¹ • A w, ?_⟩
    rw [map_smul, hright, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The Sylvester isomorphism in finite coefficient coordinates. -/
@[expose] noncomputable def sylvesterCoefficientEquiv
    (m n : ℕ) (P Q : ℂ[X]) (hP : P.Monic)
    (hPm : P.natDegree = m) (hQn : Q.natDegree = n) (hcoprime : IsCoprime P Q) :
    ((Fin m → ℂ) × (Fin n → ℂ)) ≃L[ℂ] (Fin (m + n) → ℂ) :=
  ((((degreeLTEquiv ℂ m).prodCongr (degreeLTEquiv ℂ n)).symm.trans
    (LinearEquiv.ofBijective (sylvesterMap P Q hPm.le hQn.le)
      (sylvesterMap_bijective_of_isCoprime m n P Q hP hPm hQn hcoprime))).trans
        (degreeLTEquiv ℂ (m + n))).toContinuousLinearEquiv

@[simp] theorem sylvesterCoefficientEquiv_apply
    (m n : ℕ) (P Q : ℂ[X]) (hP : P.Monic)
    (hPm : P.natDegree = m) (hQn : Q.natDegree = n) (hcoprime : IsCoprime P Q)
    (w : (Fin m → ℂ) × (Fin n → ℂ)) (j : Fin (m + n)) :
    sylvesterCoefficientEquiv m n P Q hP hPm hQn hcoprime w j =
      (P * coefficientPolynomial n w.2 + Q * coefficientPolynomial m w.1).coeff j := by
  rfl

/-- Reconstructing the Sylvester output gives the polynomial linear term
in multiplication of the perturbed factors. -/
theorem coefficientPolynomial_sylvesterCoefficientEquiv
    (m n : ℕ) (P Q : ℂ[X]) (hP : P.Monic)
    (hPm : P.natDegree = m) (hQn : Q.natDegree = n) (hcoprime : IsCoprime P Q)
    (w : (Fin m → ℂ) × (Fin n → ℂ)) :
    coefficientPolynomial (m + n) (sylvesterCoefficientEquiv m n P Q hP hPm hQn hcoprime w) =
      P * coefficientPolynomial n w.2 + Q * coefficientPolynomial m w.1 := by
  exact congrArg Subtype.val ((degreeLTEquiv ℂ (m + n)).symm_apply_apply
    (sylvesterMap P Q hPm.le hQn.le
      ((degreeLTEquiv ℂ m).symm w.1, (degreeLTEquiv ℂ n).symm w.2)))

/-- Multiplication of the two lower coefficient polynomials is a bilinear
map to the coefficients of degree less than `m+n`. -/
@[expose] noncomputable def coefficientProductLinear (m n : ℕ) :
    (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] (Fin (m + n) → ℂ) :=
  LinearMap.mk₂ ℂ
    (fun u v j ↦ (coefficientPolynomial m u * coefficientPolynomial n v).coeff j)
    (by intro u v w; ext j; simp [add_mul])
    (by intro c u v; ext j; simp)
    (by intro u v w; ext j; simp [mul_add])
    (by intro c u v; ext j; simp)

/-- The finite-dimensional bilinear coefficient multiplication is
continuous, so its analytic inverse construction is over convergent
complex functions rather than a formal completion. -/
@[expose] noncomputable def coefficientProduct (m n : ℕ) :
    (Fin m → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] (Fin (m + n) → ℂ) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (coefficientProductLinear m n)).toContinuousLinearMap

@[simp] theorem coefficientProduct_apply (m n : ℕ)
    (u : Fin m → ℂ) (v : Fin n → ℂ) (j : Fin (m + n)) :
    coefficientProduct m n u v j =
      (coefficientPolynomial m u * coefficientPolynomial n v).coeff j := by
  rfl

/-- The product of the two lower-degree polynomials is fully recovered
from the bilinear coefficient map. -/
theorem coefficientPolynomial_coefficientProduct (m n : ℕ)
    (u : Fin m → ℂ) (v : Fin n → ℂ) :
    coefficientPolynomial (m + n) (coefficientProduct m n u v) =
      coefficientPolynomial m u * coefficientPolynomial n v := by
  apply coefficientPolynomial_coefficients
  change (coefficientPolynomial m u * coefficientPolynomial n v).degree < (m + n : ℕ)
  by_cases hu : coefficientPolynomial m u = 0
  · simp [hu]
  by_cases hv : coefficientPolynomial n v = 0
  · simp [hv]
  have hmu : (coefficientPolynomial m u).natDegree < m :=
    (natDegree_lt_iff_degree_lt hu).mpr (coefficientPolynomial_degree_lt m u)
  have hnv : (coefficientPolynomial n v).natDegree < n :=
    (natDegree_lt_iff_degree_lt hv).mpr (coefficientPolynomial_degree_lt n v)
  rw [degree_mul, degree_eq_natDegree hu, degree_eq_natDegree hv, ← Nat.cast_add]
  exact_mod_cast Nat.add_lt_add hmu hnv

private theorem exists_analytic_local_right_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : E → E) (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hderiv : HasFDerivAt F (ContinuousLinearMap.id ℂ E) 0) :
    ∃ ψ : E → E, AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      ∀ᶠ z in nhds 0, F (ψ z) = z := by
  have hstrict : HasStrictFDerivAt F
      (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E) 0 := by
    change HasStrictFDerivAt F (ContinuousLinearMap.id ℂ E) 0
    simpa only [hderiv.fderiv] using hF.hasStrictFDerivAt
  let R := hstrict.toOpenPartialHomeomorph F
  have hsource : (0 : E) ∈ R.source := hstrict.mem_toOpenPartialHomeomorph_source
  have htarget : (0 : E) ∈ R.target := by
    simpa only [hF0] using hstrict.image_mem_toOpenPartialHomeomorph_target
  have hR0 : R 0 = 0 := hF0
  have hψ : AnalyticAt ℂ R.symm 0 := by
    have h := R.analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E)
      hsource hF hstrict.hasFDerivAt.fderiv
    rwa [hR0] at h
  refine ⟨R.symm, hψ, ?_, ?_⟩
  · have h := R.left_inv hsource
    rwa [hR0] at h
  · filter_upwards [R.open_target.mem_nhds htarget] with z hz
    exact R.right_inv hz

/-- Multiplication of polynomial factors admits an analytic local inverse
in the lower coefficients at a coprime pair with monic first factor. The returned
coefficient vectors vanish at the base point and give an exact polynomial
factorization near zero. -/
theorem exists_analytic_polynomial_factor_coefficients
    (m n : ℕ) (P Q : ℂ[X]) (hP : P.Monic)
    (hPm : P.natDegree = m) (hQn : Q.natDegree = n) (hcoprime : IsCoprime P Q) :
    ∃ ψ : (Fin (m + n) → ℂ) → (Fin m → ℂ) × (Fin n → ℂ),
      AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      ∀ᶠ z in nhds 0,
        (P + coefficientPolynomial m (ψ z).1) * (Q + coefficientPolynomial n (ψ z).2) =
          P * Q + coefficientPolynomial (m + n) z := by
  let E := (Fin m → ℂ) × (Fin n → ℂ)
  let _ : NormedAddCommGroup E := inferInstance
  let _ : NormedSpace ℂ E := inferInstance
  let L := sylvesterCoefficientEquiv m n P Q hP hPm hQn hcoprime
  let B := coefficientProduct m n
  let T : E → (Fin (m + n) → ℂ) := fun w ↦ B w.1 w.2
  let F : E → E := fun w ↦ w + L.symm (T w)
  have hT : AnalyticAt ℂ T 0 := B.analyticAt_bilinear 0
  have hTderiv : HasFDerivAt T (0 : E →L[ℂ] (Fin (m + n) → ℂ)) 0 := by
    have hzero : B.isBoundedBilinearMap.deriv (0 : E) = 0 := by
      apply ContinuousLinearMap.ext
      intro w
      simp [IsBoundedBilinearMap.deriv_apply]
    simpa only [hzero] using B.isBoundedBilinearMap.hasFDerivAt (0 : E)
  have hF : AnalyticAt ℂ F 0 :=
    analyticAt_id.add ((L.symm.toContinuousLinearMap.analyticAt _).comp hT)
  have hF0 : F 0 = 0 := by simp [F, T]
  have hsecond := L.symm.toContinuousLinearMap.hasFDerivAt.comp 0 hTderiv
  have hFderiv := (hasFDerivAt_id (𝕜 := ℂ) (0 : E)).add hsecond
  simp only [ContinuousLinearMap.comp_zero, add_zero] at hFderiv
  obtain ⟨ρ, hρ, hρ0, hρinverse⟩ := exists_analytic_local_right_inverse F hF hF0 hFderiv
  let ψ := ρ ∘ L.symm
  have hψ : AnalyticAt ℂ ψ 0 := by
    have hρ' : AnalyticAt ℂ ρ (L.symm 0) := by simpa only [map_zero] using hρ
    exact hρ'.comp (L.symm.analyticAt 0)
  refine ⟨ψ, hψ, by simp [ψ, hρ0], ?_⟩
  have htend : Tendsto L.symm (nhds 0) (nhds (0 : E)) := by
    simpa only [map_zero] using (L.symm.continuousAt (x := 0)).tendsto
  have hnear : ∀ᶠ z in nhds 0, F (ψ z) = L.symm z := by
    simpa only [ψ, Function.comp_apply] using htend.eventually hρinverse
  filter_upwards [hnear] with z hz
  have hcoef : L (ψ z) + B (ψ z).1 (ψ z).2 = z := by
    have h := congrArg L hz
    simpa only [F, T, map_add, ContinuousLinearEquiv.apply_symm_apply] using h
  have hpoly := congrArg (coefficientPolynomial (m + n)) hcoef
  rw [map_add, coefficientPolynomial_sylvesterCoefficientEquiv,
    coefficientPolynomial_coefficientProduct] at hpoly
  change P * coefficientPolynomial n (ψ z).2 + Q * coefficientPolynomial m (ψ z).1 +
    coefficientPolynomial m (ψ z).1 * coefficientPolynomial n (ψ z).2 =
      coefficientPolynomial (m + n) z at hpoly
  linear_combination hpoly

/-- An analytic local factorization near a coprime monic pair preserves the
two prescribed monic degrees everywhere on the coefficient parameter space. -/
theorem exists_analytic_monic_polynomial_factor_coefficients
    (m n : ℕ) (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hPm : P.natDegree = m) (hQn : Q.natDegree = n) (hcoprime : IsCoprime P Q) :
    ∃ ψ : (Fin (m + n) → ℂ) → (Fin m → ℂ) × (Fin n → ℂ),
      AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      (∀ z, (P + coefficientPolynomial m (ψ z).1).Monic ∧
        (P + coefficientPolynomial m (ψ z).1).natDegree = m ∧
        (Q + coefficientPolynomial n (ψ z).2).Monic ∧
        (Q + coefficientPolynomial n (ψ z).2).natDegree = n) ∧
      ∀ᶠ z in nhds 0,
        (P + coefficientPolynomial m (ψ z).1) * (Q + coefficientPolynomial n (ψ z).2) =
          P * Q + coefficientPolynomial (m + n) z := by
  obtain ⟨ψ, hψ, hzero, hfactor⟩ :=
    exists_analytic_polynomial_factor_coefficients m n P Q hP hPm hQn hcoprime
  refine ⟨ψ, hψ, hzero, ?_, hfactor⟩
  intro z
  obtain ⟨hP', hPm'⟩ := monic_add_coefficientPolynomial m P hP hPm (ψ z).1
  obtain ⟨hQ', hQn'⟩ := monic_add_coefficientPolynomial n Q hQ hQn (ψ z).2
  exact ⟨hP', hPm', hQ', hQn'⟩

end OnLeConjecture.Polynomial
