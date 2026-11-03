/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EProjectiveSupport
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Homogeneity of the residual polynomial for the `E` pair

This file transports ordinary homogeneity through cubic descent and the
residual parametrization.  It then proves that the residual difference
factor has the required ordinary degree.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The weights of `x` and `w=t^3` after cubic descent. -/
def eSourceWeight : ESourceCoordinate → ℕ
  | ESourceCoordinate.x => 1
  | ESourceCoordinate.w => 3

/-- The same weights in the two variable form presentation. -/
def eCubicFormWeight : Fin 2 → ℕ := ![1, 3]

/-- The exponent pair used to compare the iterated and multivariate
presentations. -/
noncomputable def eFormExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b]

@[simp]
theorem eFormExponent_zero (a b : ℕ) : eFormExponent a b 0 = a := by
  simp [eFormExponent]

@[simp]
theorem eFormExponent_one (a b : ℕ) : eFormExponent a b 1 = b := by
  simp [eFormExponent]

theorem eFormExponent_eq_iff {a b m n : ℕ} :
    eFormExponent a b = eFormExponent m n ↔ a = m ∧ b = n := by
  constructor
  · intro h
    exact ⟨by simpa using DFunLike.congr_fun h (0 : Fin 2),
      by simpa using DFunLike.congr_fun h (1 : Fin 2)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem eFormExponent_apply (d : Fin 2 →₀ ℕ) :
    eFormExponent (d 0) (d 1) = d := by
  ext i
  fin_cases i <;> simp

@[simp]
theorem eFormExponent_weight (a b : ℕ) :
    Finsupp.weight eCubicFormWeight (eFormExponent a b) = a + 3 * b := by
  simp [eCubicFormWeight, eFormExponent, Finsupp.weight_apply,
    Finsupp.sum_fintype, Fin.sum_univ_two]
  omega

theorem eIteratedToForm_coeff (S : EIteratedSourceRing) (a b : ℕ) :
    MvPolynomial.coeff (eFormExponent a b) (eIteratedToForm S) =
      (S.coeff b).coeff a := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add,
        hp, hq]
  | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          have hmonomial :
              Polynomial.monomial n (p + q) =
                Polynomial.monomial n p + Polynomial.monomial n q := by
            ext j
            simp [Polynomial.coeff_monomial]
          rw [hmonomial, map_add, MvPolynomial.coeff_add,
            Polynomial.coeff_add, hp, hq]
          rw [Polynomial.coeff_add]
      | monomial m c =>
          have himage :
              eIteratedToForm
                  (Polynomial.monomial n (Polynomial.monomial m c)) =
                MvPolynomial.monomial (eFormExponent m n) c := by
            simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul,
              map_pow, eIteratedToForm_innerX, eIteratedToForm_outerX]
            rw [show eIteratedToForm (C (C c)) = MvPolynomial.C c by
              exact eIteratedToForm.commutes c]
            rw [MvPolynomial.monomial_eq]
            simp [formX, formT, eFormExponent,
              Finsupp.prod_fintype, Fin.prod_univ_two]
            ring
          rw [himage, MvPolynomial.coeff_monomial]
          by_cases hnb : n = b
          · subst b
            simp [Polynomial.coeff_monomial, eFormExponent_eq_iff]
          · simp [Polynomial.coeff_monomial, hnb,
              eFormExponent_eq_iff]

/-- Weighted homogeneity in the iterated presentation `C[x][w]`. -/
def EIteratedIsWeightedHomogeneous
    (S : EIteratedSourceRing) (N : ℕ) : Prop :=
  ∀ a b : ℕ, (S.coeff b).coeff a ≠ 0 → a + 3 * b = N

/-- Expanding the `w` exponent by three agrees with cubic substitution and
transport of the descended form. -/
theorem e_expand_sourceToIterated_eq_formToIterated
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R) :
    Polynomial.expand (Polynomial ℂ) 3 (eSourceToIterated Rzero) =
      eFormToIterated R := by
  let S := eSourceToIterated Rzero
  have hback : eIteratedToSource S = Rzero := by
    simpa only [S, AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eIteratedToSource_comp_sourceToIterated Rzero
  have hcube :
      eSourceCubeSubstitution Rzero =
        Polynomial.expand (Polynomial ℂ) 3 S := by
    calc
      eSourceCubeSubstitution Rzero =
          eSourceCubeSubstitution (eIteratedToSource S) := by rw [hback]
      _ = S.eval₂ C (X ^ 3) :=
        eSourceCubeSubstitution_iteratedToSource S
      _ = Polynomial.expand (Polynomial ℂ) 3 S := rfl
  calc
    Polynomial.expand (Polynomial ℂ) 3 S =
        eSourceCubeSubstitution Rzero := hcube.symm
    _ = eFormToIterated (eSourceCubeSubstitutionForm Rzero) := by
      symm
      exact AlgHom.congr_fun
        eFormToIterated_comp_sourceCubeSubstitutionForm Rzero
    _ = eFormToIterated R := by rw [hdescent]

/-- Ordinary homogeneity before cubic descent becomes weighted homogeneity
with weights one and three afterward. -/
theorem e_sourceToIterated_isWeightedHomogeneous_of_form
    {Rzero : ESourceRing ℂ} {R : Form ℂ} {N : ℕ}
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hhomogeneous : R.IsHomogeneous N) :
    EIteratedIsWeightedHomogeneous (eSourceToIterated Rzero) N := by
  let S := eSourceToIterated Rzero
  have hexpand :
      Polynomial.expand (Polynomial ℂ) 3 S = eFormToIterated R :=
    e_expand_sourceToIterated_eq_formToIterated Rzero R hdescent
  intro a b hab
  have houter :
      (Polynomial.expand (Polynomial ℂ) 3 S).coeff (b * 3) =
        S.coeff b := Polynomial.coeff_expand_mul (by norm_num) S b
  have hcoefficient :
      MvPolynomial.coeff (eFormExponent a (b * 3)) R ≠ 0 := by
    have hbackForm : eIteratedToForm (eFormToIterated R) = R := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eIteratedToForm_comp_formToIterated R
    have hiterated :=
      eIteratedToForm_coeff (eFormToIterated R) a (b * 3)
    rw [hbackForm, ← hexpand, houter] at hiterated
    exact hiterated.symm ▸ hab
  have hweight := hhomogeneous hcoefficient
  simpa [eFormExponent, Finsupp.degree_eq_weight_one,
    Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two,
    mul_comm, mul_left_comm, mul_assoc] using hweight

/-- The coefficient formulation of weighted homogeneity agrees with
weighted homogeneity of the associated two variable form. -/
theorem eIteratedToForm_isWeightedHomogeneous
    {S : EIteratedSourceRing} {N : ℕ}
    (hS : EIteratedIsWeightedHomogeneous S N) :
    (eIteratedToForm S).IsWeightedHomogeneous eCubicFormWeight N := by
  intro d hd
  have hnested : (S.coeff (d 1)).coeff (d 0) ≠ 0 := by
    rw [← eIteratedToForm_coeff S (d 0) (d 1),
      eFormExponent_apply]
    exact hd
  rw [← eFormExponent_apply d, eFormExponent_weight]
  exact hS (d 0) (d 1) hnested

/-- Substitution of homogeneous polynomials of the prescribed variable
degrees turns a weighted homogeneous polynomial into an ordinarily
homogeneous polynomial. -/
theorem isHomogeneous_eval₂_of_isWeightedHomogeneous
    {F : Form ℂ} {N : ℕ} (w : Fin 2 → ℕ)
    (hF : F.IsWeightedHomogeneous w N)
    (g : Fin 2 → Form ℂ)
    (hg : ∀ i, (g i).IsHomogeneous (w i)) :
    (MvPolynomial.eval₂ MvPolynomial.C g F).IsHomogeneous N := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      rw [MvPolynomial.eval₂_zero]
      exact MvPolynomial.isHomogeneous_zero (Fin 2) ℂ N
  | add p q hp hq ihp ihq =>
      rw [MvPolynomial.eval₂_add]
      exact ihp.add ihq
  | monomial d r hr =>
      have hproduct :
          (∏ i ∈ d.support, g i ^ d i).IsHomogeneous
            (∑ i ∈ d.support, w i * d i) := by
        apply MvPolynomial.IsHomogeneous.prod
        intro i _hi
        exact (hg i).pow (d i)
      have hdegree : ∑ i ∈ d.support, w i * d i = N := by
        calc
          ∑ i ∈ d.support, w i * d i =
              Finsupp.weight w d := by
            simp [Finsupp.weight_apply, Finsupp.sum, mul_comm]
          _ = N := hr
      rw [MvPolynomial.eval₂_monomial]
      rw [hdegree] at hproduct
      exact hproduct.C_mul r

/-- The first residual value of `w` as a polynomial in the two residual
coordinates. -/
noncomputable def eResidualFirstWPolynomial : EPairRing ℂ :=
  algebraMap ℂ (EPairRing ℂ) (12 : ℂ)⁻¹ *
    (ePairSecond ℂ ^ 3 +
      ePairSecond ℂ ^ 2 * ePairFirst ℂ +
      ePairSecond ℂ * ePairFirst ℂ ^ 2 -
      3 * ePairFirst ℂ ^ 3)

/-- The second residual value of `w`. -/
noncomputable def eResidualSecondWPolynomial : EPairRing ℂ :=
  algebraMap ℂ (EPairRing ℂ) (12 : ℂ)⁻¹ *
    (ePairFirst ℂ ^ 3 +
      ePairFirst ℂ ^ 2 * ePairSecond ℂ +
      ePairFirst ℂ * ePairSecond ℂ ^ 2 -
      3 * ePairSecond ℂ ^ 3)

/-- Evaluation on the first branch of the residual parametrization. -/
noncomputable def eIteratedResidualFirst :
    EIteratedSourceRing →ₐ[ℂ] EPairRing ℂ :=
  Polynomial.aevalAeval (ePairFirst ℂ) eResidualFirstWPolynomial

/-- Evaluation on the second branch of the residual parametrization. -/
noncomputable def eIteratedResidualSecond :
    EIteratedSourceRing →ₐ[ℂ] EPairRing ℂ :=
  Polynomial.aevalAeval (ePairSecond ℂ) eResidualSecondWPolynomial

@[simp]
theorem eIteratedResidualFirst_innerX :
    eIteratedResidualFirst (C X) = ePairFirst ℂ := by
  exact Polynomial.aevalAeval_X _ _

@[simp]
theorem eIteratedResidualFirst_outerX :
    eIteratedResidualFirst X = eResidualFirstWPolynomial := by
  exact Polynomial.aevalAeval_Y _ _

@[simp]
theorem eIteratedResidualSecond_innerX :
    eIteratedResidualSecond (C X) = ePairSecond ℂ := by
  exact Polynomial.aevalAeval_X _ _

@[simp]
theorem eIteratedResidualSecond_outerX :
    eIteratedResidualSecond X = eResidualSecondWPolynomial := by
  exact Polynomial.aevalAeval_Y _ _

/-- The first residual `w` polynomial is homogeneous of degree three. -/
theorem eResidualFirstWPolynomial_isHomogeneous :
    EPairIsHomogeneous eResidualFirstWPolynomial 3 := by
  apply (ePairIsHomogeneous_iff eResidualFirstWPolynomial 3).mpr
  simp only [eResidualFirstWPolynomial, map_mul, map_add, map_sub,
    map_pow, map_ofNat,
    show eIteratedToForm (ePairFirst ℂ) = formX by
      exact eIteratedToForm_innerX,
    show eIteratedToForm (ePairSecond ℂ) = formT by
      exact eIteratedToForm_outerX]
  have hscalar :
      eIteratedToForm (algebraMap ℂ (EPairRing ℂ) (12 : ℂ)⁻¹) =
        MvPolynomial.C (12 : ℂ)⁻¹ :=
    eIteratedToForm.commutes _
  rw [hscalar]
  have hx : (formX : Form ℂ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ 0
  have ht : (formT : Form ℂ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ 1
  have hsum := ((ht.pow 3).add ((ht.pow 2).mul hx)).add
    (ht.mul (hx.pow 2))
  exact (hsum.sub ((hx.pow 3).C_mul 3)).C_mul _

/-- The second residual `w` polynomial is homogeneous of degree three. -/
theorem eResidualSecondWPolynomial_isHomogeneous :
    EPairIsHomogeneous eResidualSecondWPolynomial 3 := by
  apply (ePairIsHomogeneous_iff eResidualSecondWPolynomial 3).mpr
  simp only [eResidualSecondWPolynomial, map_mul, map_add, map_sub,
    map_pow, map_ofNat,
    show eIteratedToForm (ePairFirst ℂ) = formX by
      exact eIteratedToForm_innerX,
    show eIteratedToForm (ePairSecond ℂ) = formT by
      exact eIteratedToForm_outerX]
  have hscalar :
      eIteratedToForm (algebraMap ℂ (EPairRing ℂ) (12 : ℂ)⁻¹) =
        MvPolynomial.C (12 : ℂ)⁻¹ :=
    eIteratedToForm.commutes _
  rw [hscalar]
  have hx : (formX : Form ℂ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ 0
  have ht : (formT : Form ℂ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ 1
  have hsum := ((hx.pow 3).add ((hx.pow 2).mul ht)).add
    (hx.mul (ht.pow 2))
  exact (hsum.sub ((ht.pow 3).C_mul 3)).C_mul _

/-- The form substitution associated with the first residual branch. -/
noncomputable def eResidualFirstFormSubstitution : Fin 2 → Form ℂ :=
  ![formX, eIteratedToForm eResidualFirstWPolynomial]

/-- The form substitution associated with the second residual branch. -/
noncomputable def eResidualSecondFormSubstitution : Fin 2 → Form ℂ :=
  ![formT, eIteratedToForm eResidualSecondWPolynomial]

theorem eIteratedToForm_residualFirst (S : EIteratedSourceRing) :
    eIteratedToForm (eIteratedResidualFirst S) =
      MvPolynomial.eval₂ MvPolynomial.C
        eResidualFirstFormSubstitution (eIteratedToForm S) := by
  let left : EIteratedSourceRing →ₐ[ℂ] Form ℂ :=
    eIteratedToForm.comp eIteratedResidualFirst
  let right : EIteratedSourceRing →ₐ[ℂ] Form ℂ :=
    (MvPolynomial.aeval eResidualFirstFormSubstitution).comp
      eIteratedToForm
  have heq : left = right := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      change left (C X) = right (C X)
      rw [show left (C X) = eIteratedToForm (ePairFirst ℂ) by
        simp [left]]
      rw [show ePairFirst ℂ = C X by rfl, eIteratedToForm_innerX]
      simp [right, eResidualFirstFormSubstitution, formX]
    · change left X = right X
      simp [left, right, eResidualFirstFormSubstitution, formT]
  have h := AlgHom.congr_fun heq S
  change eIteratedToForm (eIteratedResidualFirst S) =
    MvPolynomial.aeval eResidualFirstFormSubstitution
      (eIteratedToForm S) at h
  rw [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq] at h
  exact h

theorem eIteratedToForm_residualSecond (S : EIteratedSourceRing) :
    eIteratedToForm (eIteratedResidualSecond S) =
      MvPolynomial.eval₂ MvPolynomial.C
        eResidualSecondFormSubstitution (eIteratedToForm S) := by
  let left : EIteratedSourceRing →ₐ[ℂ] Form ℂ :=
    eIteratedToForm.comp eIteratedResidualSecond
  let right : EIteratedSourceRing →ₐ[ℂ] Form ℂ :=
    (MvPolynomial.aeval eResidualSecondFormSubstitution).comp
      eIteratedToForm
  have heq : left = right := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      change left (C X) = right (C X)
      rw [show left (C X) = eIteratedToForm (ePairSecond ℂ) by
        simp [left]]
      rw [show ePairSecond ℂ = X by rfl, eIteratedToForm_outerX]
      simp [right, eResidualSecondFormSubstitution, formX, formT]
    · change left X = right X
      simp [left, right, eResidualSecondFormSubstitution, formT]
  have h := AlgHom.congr_fun heq S
  change eIteratedToForm (eIteratedResidualSecond S) =
    MvPolynomial.aeval eResidualSecondFormSubstitution
      (eIteratedToForm S) at h
  rw [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq] at h
  exact h

/-- Weighted homogeneity is transported through the first residual
substitution. -/
theorem eIteratedResidualFirst_isHomogeneous
    {S : EIteratedSourceRing} {N : ℕ}
    (hS : EIteratedIsWeightedHomogeneous S N) :
    EPairIsHomogeneous (eIteratedResidualFirst S) N := by
  apply (ePairIsHomogeneous_iff (eIteratedResidualFirst S) N).mpr
  rw [eIteratedToForm_residualFirst]
  apply isHomogeneous_eval₂_of_isWeightedHomogeneous eCubicFormWeight
    (eIteratedToForm_isWeightedHomogeneous hS)
  intro i
  fin_cases i
  · exact MvPolynomial.isHomogeneous_X ℂ 0
  · exact (ePairIsHomogeneous_iff eResidualFirstWPolynomial 3).mp
      eResidualFirstWPolynomial_isHomogeneous

/-- Weighted homogeneity is transported through the second residual
substitution. -/
theorem eIteratedResidualSecond_isHomogeneous
    {S : EIteratedSourceRing} {N : ℕ}
    (hS : EIteratedIsWeightedHomogeneous S N) :
    EPairIsHomogeneous (eIteratedResidualSecond S) N := by
  apply (ePairIsHomogeneous_iff (eIteratedResidualSecond S) N).mpr
  rw [eIteratedToForm_residualSecond]
  apply isHomogeneous_eval₂_of_isWeightedHomogeneous eCubicFormWeight
    (eIteratedToForm_isWeightedHomogeneous hS)
  intro i
  fin_cases i
  · exact MvPolynomial.isHomogeneous_X ℂ 1
  · exact (ePairIsHomogeneous_iff eResidualSecondWPolynomial 3).mp
      eResidualSecondWPolynomial_isHomogeneous

/-- The first residual substitution as a map from the descended source
ring. -/
noncomputable def eSourceResidualFirst :
    ESourceRing ℂ →ₐ[ℂ] EPairRing ℂ :=
  eIteratedResidualFirst.comp eSourceToIterated

/-- The second residual substitution as a map from the descended source
ring. -/
noncomputable def eSourceResidualSecond :
    ESourceRing ℂ →ₐ[ℂ] EPairRing ℂ :=
  eIteratedResidualSecond.comp eSourceToIterated

@[simp]
theorem eSourceResidualFirst_x :
    eSourceResidualFirst (eSourceX ℂ) = ePairFirst ℂ := by
  simp [eSourceResidualFirst]

@[simp]
theorem eSourceResidualFirst_w :
    eSourceResidualFirst (eSourceW ℂ) =
      eResidualFirstWPolynomial := by
  simp [eSourceResidualFirst]

@[simp]
theorem eSourceResidualSecond_x :
    eSourceResidualSecond (eSourceX ℂ) = ePairSecond ℂ := by
  simp [eSourceResidualSecond]

@[simp]
theorem eSourceResidualSecond_w :
    eSourceResidualSecond (eSourceW ℂ) =
      eResidualSecondWPolynomial := by
  simp [eSourceResidualSecond]

private theorem e_algebraMap_inv_twelve_mul_three :
    algebraMap ℂ (EPairRing ℂ) (12 : ℂ)⁻¹ * 3 =
      algebraMap ℂ (EPairRing ℂ) (4 : ℂ)⁻¹ := by
  rw [← map_ofNat (algebraMap ℂ (EPairRing ℂ)) 3, ← map_mul]
  congr 1
  norm_num

private theorem e_algebraMap_inv_twelve_mul_four :
    algebraMap ℂ (EPairRing ℂ) (12 : ℂ)⁻¹ * 4 =
      algebraMap ℂ (EPairRing ℂ) (3 : ℂ)⁻¹ := by
  rw [← map_ofNat (algebraMap ℂ (EPairRing ℂ)) 4, ← map_mul]
  congr 1
  norm_num

private theorem e_algebraMap_inv_twelve_mul_twelve :
    algebraMap ℂ (EPairRing ℂ) (12 : ℂ)⁻¹ * 12 = 1 := by
  rw [← map_ofNat (algebraMap ℂ (EPairRing ℂ)) 12, ← map_mul]
  norm_num

theorem eSourceResidualFirst_sourceP :
    eSourceResidualFirst (eSourceP ℂ) = eResidualPairP ℂ := by
  simp only [eSourceP, map_add, map_pow, map_mul, map_ofNat,
    eSourceResidualFirst_x, eSourceResidualFirst_w,
    eResidualFirstWPolynomial, eResidualPairP]
  rw [← e_algebraMap_inv_twelve_mul_three]
  linear_combination
    -ePairFirst ℂ ^ 3 * e_algebraMap_inv_twelve_mul_twelve

theorem eSourceResidualFirst_sourceQ :
    eSourceResidualFirst (eSourceQ ℂ) = eResidualPairQ ℂ := by
  simp only [eSourceQ, map_add, map_pow, map_mul, map_ofNat,
    eSourceResidualFirst_x, eSourceResidualFirst_w,
    eResidualFirstWPolynomial, eResidualPairQ]
  rw [← e_algebraMap_inv_twelve_mul_four]
  linear_combination
    -ePairFirst ℂ ^ 4 * e_algebraMap_inv_twelve_mul_twelve

theorem eSourceResidualSecond_sourceP :
    eSourceResidualSecond (eSourceP ℂ) = eResidualPairP ℂ := by
  simp only [eSourceP, map_add, map_pow, map_mul, map_ofNat,
    eSourceResidualSecond_x, eSourceResidualSecond_w,
    eResidualSecondWPolynomial, eResidualPairP]
  rw [← e_algebraMap_inv_twelve_mul_three]
  linear_combination
    -ePairSecond ℂ ^ 3 * e_algebraMap_inv_twelve_mul_twelve

theorem eSourceResidualSecond_sourceQ :
    eSourceResidualSecond (eSourceQ ℂ) = eResidualPairQ ℂ := by
  simp only [eSourceQ, map_add, map_pow, map_mul, map_ofNat,
    eSourceResidualSecond_x, eSourceResidualSecond_w,
    eResidualSecondWPolynomial, eResidualPairQ]
  rw [← e_algebraMap_inv_twelve_mul_four]
  linear_combination
    -ePairSecond ℂ ^ 4 * e_algebraMap_inv_twelve_mul_twelve

theorem eSourceResidualFirst_comp_baseToSource :
    eSourceResidualFirst.comp (eBaseToSource ℂ) =
      eResidualBaseToPair ℂ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
      change eSourceResidualFirst (eBaseToSource ℂ (eBaseP ℂ)) =
        eResidualBaseToPair ℂ (eBaseP ℂ)
      rw [eBaseToSource_p, eResidualBaseToPair_p,
        eSourceResidualFirst_sourceP]
  | q =>
      change eSourceResidualFirst (eBaseToSource ℂ (eBaseQ ℂ)) =
        eResidualBaseToPair ℂ (eBaseQ ℂ)
      rw [eBaseToSource_q, eResidualBaseToPair_q,
        eSourceResidualFirst_sourceQ]

theorem eSourceResidualSecond_comp_baseToSource :
    eSourceResidualSecond.comp (eBaseToSource ℂ) =
      eResidualBaseToPair ℂ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
      change eSourceResidualSecond (eBaseToSource ℂ (eBaseP ℂ)) =
        eResidualBaseToPair ℂ (eBaseP ℂ)
      rw [eBaseToSource_p, eResidualBaseToPair_p,
        eSourceResidualSecond_sourceP]
  | q =>
      change eSourceResidualSecond (eBaseToSource ℂ (eBaseQ ℂ)) =
        eResidualBaseToPair ℂ (eBaseQ ℂ)
      rw [eBaseToSource_q, eResidualBaseToPair_q,
        eSourceResidualSecond_sourceQ]

/-- The first residual substitution evaluates a canonical source basis
decomposition at the first residual coordinate. -/
theorem eIteratedResidualFirst_sourceToIterated_of_basis
    {Rzero : ESourceRing ℂ} {c : Fin 4 → EBaseRing ℂ}
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ)) :
    eIteratedResidualFirst (eSourceToIterated Rzero) =
      eResidualBasisValue ℂ c (ePairFirst ℂ) := by
  change eSourceResidualFirst Rzero = _
  rw [hdecomposition, map_sum, Fin.sum_univ_four]
  simp only [map_mul, map_pow, eSourceResidualFirst_x]
  have hcoefficient (i : Fin 4) :
      eSourceResidualFirst (eBaseToSource ℂ (c i)) =
        eResidualBaseToPair ℂ (c i) := by
    exact AlgHom.congr_fun eSourceResidualFirst_comp_baseToSource (c i)
  simp_rw [hcoefficient]
  simp only [eResidualBasisValue]
  norm_num

/-- The second residual substitution evaluates a canonical source basis
decomposition at the second residual coordinate. -/
theorem eIteratedResidualSecond_sourceToIterated_of_basis
    {Rzero : ESourceRing ℂ} {c : Fin 4 → EBaseRing ℂ}
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ)) :
    eIteratedResidualSecond (eSourceToIterated Rzero) =
      eResidualBasisValue ℂ c (ePairSecond ℂ) := by
  change eSourceResidualSecond Rzero = _
  rw [hdecomposition, map_sum, Fin.sum_univ_four]
  simp only [map_mul, map_pow, eSourceResidualSecond_x]
  have hcoefficient (i : Fin 4) :
      eSourceResidualSecond (eBaseToSource ℂ (c i)) =
        eResidualBaseToPair ℂ (c i) := by
    exact AlgHom.congr_fun eSourceResidualSecond_comp_baseToSource (c i)
  simp_rw [hcoefficient]
  simp only [eResidualBasisValue]
  norm_num

/-- Homogeneity of the original form makes the residual difference,
including its diagonal factor, homogeneous of the same degree. -/
theorem ePairFirst_sub_second_mul_theta_isHomogeneous
    {Rzero : ESourceRing ℂ} {R : Form ℂ}
    {c : Fin 4 → EBaseRing ℂ} {N : ℕ}
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hhomogeneous : R.IsHomogeneous N)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ)) :
    EPairIsHomogeneous
      ((ePairFirst ℂ - ePairSecond ℂ) * eThetaPolynomial ℂ c) N := by
  have hweighted :
      EIteratedIsWeightedHomogeneous (eSourceToIterated Rzero) N :=
    e_sourceToIterated_isWeightedHomogeneous_of_form
      hdescent hhomogeneous
  have hfirst := eIteratedResidualFirst_isHomogeneous hweighted
  have hsecond := eIteratedResidualSecond_isHomogeneous hweighted
  have hdifference :
      EPairIsHomogeneous
        (eIteratedResidualFirst (eSourceToIterated Rzero) -
          eIteratedResidualSecond (eSourceToIterated Rzero)) N := by
    apply (ePairIsHomogeneous_iff _ N).mpr
    rw [map_sub]
    exact ((ePairIsHomogeneous_iff _ N).mp hfirst).sub
      ((ePairIsHomogeneous_iff _ N).mp hsecond)
  rw [eIteratedResidualFirst_sourceToIterated_of_basis hdecomposition,
    eIteratedResidualSecond_sourceToIterated_of_basis hdecomposition,
    e_residual_basis_difference_factorization] at hdifference
  exact hdifference

/-- A linear change of variables that sends the diagonal equation to the
first coordinate. -/
noncomputable def eDiagonalLinearChange : Form ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval ![formX + formT, formT]

/-- The inverse linear change of variables. -/
noncomputable def eDiagonalLinearInverse : Form ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval ![formX - formT, formT]

@[simp]
theorem eDiagonalLinearChange_x :
    eDiagonalLinearChange formX = formX + formT := by
  simp [eDiagonalLinearChange, formX]

@[simp]
theorem eDiagonalLinearChange_t :
    eDiagonalLinearChange formT = formT := by
  simp [eDiagonalLinearChange, formT]

@[simp]
theorem eDiagonalLinearInverse_x :
    eDiagonalLinearInverse formX = formX - formT := by
  simp [eDiagonalLinearInverse, formX]

@[simp]
theorem eDiagonalLinearInverse_t :
    eDiagonalLinearInverse formT = formT := by
  simp [eDiagonalLinearInverse, formT]

theorem eDiagonalLinearInverse_comp_change :
    eDiagonalLinearInverse.comp eDiagonalLinearChange =
      AlgHom.id ℂ (Form ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change eDiagonalLinearInverse (eDiagonalLinearChange formX) = formX
    rw [eDiagonalLinearChange_x, map_add,
      eDiagonalLinearInverse_x, eDiagonalLinearInverse_t]
    ring
  · change eDiagonalLinearInverse (eDiagonalLinearChange formT) = formT
    rw [eDiagonalLinearChange_t, eDiagonalLinearInverse_t]

theorem eDiagonalLinearChange_diagonal :
    eDiagonalLinearChange (formX - formT) = formX := by
  rw [map_sub, eDiagonalLinearChange_x, eDiagonalLinearChange_t]
  ring

/-- The linear change preserves ordinary homogeneity. -/
theorem eDiagonalLinearChange_isHomogeneous
    {F : Form ℂ} {N : ℕ} (hF : F.IsHomogeneous N) :
    (eDiagonalLinearChange F).IsHomogeneous N := by
  rw [eDiagonalLinearChange, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq]
  apply isHomogeneous_eval₂_of_isWeightedHomogeneous
    (1 : Fin 2 → ℕ) hF
  intro i
  fin_cases i
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).add
      (MvPolynomial.isHomogeneous_X ℂ 1)
  · exact MvPolynomial.isHomogeneous_X ℂ 1

/-- The inverse linear change preserves ordinary homogeneity. -/
theorem eDiagonalLinearInverse_isHomogeneous
    {F : Form ℂ} {N : ℕ} (hF : F.IsHomogeneous N) :
    (eDiagonalLinearInverse F).IsHomogeneous N := by
  rw [eDiagonalLinearInverse, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq]
  apply isHomogeneous_eval₂_of_isWeightedHomogeneous
    (1 : Fin 2 → ℕ) hF
  intro i
  fin_cases i
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).sub
      (MvPolynomial.isHomogeneous_X ℂ 1)
  · exact MvPolynomial.isHomogeneous_X ℂ 1

/-- Multiplication by a monomial reflects weighted homogeneity after the
weight of that monomial is subtracted. -/
theorem e_isWeightedHomogeneous_of_monomial_mul
    (w : Fin 2 → ℕ) (s : Fin 2 →₀ ℕ)
    (F : Form ℂ) (n M : ℕ)
    (hproduct :
      (MvPolynomial.monomial s 1 * F).IsWeightedHomogeneous w M)
    (hdegree : Finsupp.weight w s + n = M) :
    F.IsWeightedHomogeneous w n := by
  intro d hd
  have hcoefficient : MvPolynomial.coeff (s + d)
      (MvPolynomial.monomial s 1 * F) ≠ 0 := by
    simpa using hd
  have hweight := hproduct hcoefficient
  have hadd :
      Finsupp.weight w s + Finsupp.weight w d = M := by
    simpa only [map_add] using hweight
  exact Nat.add_left_cancel (hadd.trans hdegree.symm)

/-- Cancellation of the diagonal factor lowers the homogeneous degree by
one.  In degree zero the quotient is forced to be the zero polynomial. -/
theorem ePairIsHomogeneous_of_diagonal_mul
    {theta : EPairRing ℂ} {N : ℕ}
    (hproduct : EPairIsHomogeneous
      ((ePairFirst ℂ - ePairSecond ℂ) * theta) N) :
    EPairIsHomogeneous theta (N - 1) := by
  let F : Form ℂ := eIteratedToForm theta
  have hdiagonalForm :
      eIteratedToForm (ePairFirst ℂ - ePairSecond ℂ) =
        formX - formT := by
    rw [map_sub]
    change eIteratedToForm (C X) - eIteratedToForm X = formX - formT
    rw [eIteratedToForm_innerX, eIteratedToForm_outerX]
  have hproductForm : ((formX - formT) * F).IsHomogeneous N := by
    have h := (ePairIsHomogeneous_iff _ N).mp hproduct
    rw [map_mul, hdiagonalForm] at h
    exact h
  have hchanged := eDiagonalLinearChange_isHomogeneous hproductForm
  have hchangedProduct :
      (formX * eDiagonalLinearChange F).IsHomogeneous N := by
    simpa only [map_mul, eDiagonalLinearChange_diagonal] using hchanged
  let s : Fin 2 →₀ ℕ := Finsupp.single 0 1
  have hmonomial : MvPolynomial.monomial s (1 : ℂ) = formX := by
    simp [s, formX, ← MvPolynomial.C_mul_X_eq_monomial]
  have hchangedMonomial :
      (MvPolynomial.monomial s (1 : ℂ) *
        eDiagonalLinearChange F).IsHomogeneous N := by
    rw [hmonomial]
    exact hchangedProduct
  have hrecover : eDiagonalLinearInverse (eDiagonalLinearChange F) = F := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eDiagonalLinearInverse_comp_change F
  apply (ePairIsHomogeneous_iff theta (N - 1)).mpr
  change F.IsHomogeneous (N - 1)
  by_cases hN : N = 0
  · subst N
    have hchangedZero : eDiagonalLinearChange F = 0 := by
      have hproductZero :
          formX * eDiagonalLinearChange F = 0 := by
        ext d
        by_cases hd : d = 0
        · subst d
          change MvPolynomial.constantCoeff
            (formX * eDiagonalLinearChange F) = 0
          simp [formX]
        · exact hchangedProduct.coeff_eq_zero
            ((Finsupp.degree_eq_zero_iff d).not.mpr hd)
      exact (mul_eq_zero.mp hproductZero).resolve_left
        (show formX ≠ 0 from MvPolynomial.X_ne_zero (0 : Fin 2))
    have hFzero : F = 0 := by
      rw [← hrecover, hchangedZero, map_zero]
    rw [hFzero]
    exact MvPolynomial.isHomogeneous_zero (Fin 2) ℂ 0
  · have hpositive : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hsWeight : Finsupp.weight (1 : Fin 2 → ℕ) s = 1 := by
      simp [s, Finsupp.weight_apply]
    have hchangedHomogeneous :
        (eDiagonalLinearChange F).IsHomogeneous (N - 1) := by
      apply e_isWeightedHomogeneous_of_monomial_mul
        (1 : Fin 2 → ℕ) s (eDiagonalLinearChange F) (N - 1) N
        hchangedMonomial
      rw [hsWeight]
      omega
    have hinverse :=
      eDiagonalLinearInverse_isHomogeneous hchangedHomogeneous
    rwa [hrecover] at hinverse

/-- Ordinary homogeneity of the original form and a canonical source basis
decomposition give the required degree of the residual factor. -/
theorem eThetaPolynomial_isHomogeneous_of_form_and_basis
    {Rzero : ESourceRing ℂ} {R : Form ℂ}
    {c : Fin 4 → EBaseRing ℂ} {N : ℕ}
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hhomogeneous : R.IsHomogeneous N)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ)) :
    EPairIsHomogeneous (eThetaPolynomial ℂ c) (N - 1) := by
  apply ePairIsHomogeneous_of_diagonal_mul
  exact ePairFirst_sub_second_mul_theta_isHomogeneous
    hdescent hhomogeneous hdecomposition

/-- The invariant Jacobian branch produces a homogeneous residual factor
with a projective zero away from the diagonal.  The conclusion retains the
descent, basis, and diagonal divisibility data. -/
theorem exists_e_invariant_residual_off_diagonal_projective_zero
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm omega R)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R) :
    ∃ Rzero : ESourceRing ℂ, ∃ c : Fin 4 → EBaseRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R ∧
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ) ∧
      EPairIsHomogeneous (eThetaPolynomial ℂ c) (N - 1) ∧
      ePairDiagonal ℂ ^ 2 ∣ eThetaPolynomial ℂ c ∧
      ∃ x X : ℂ, (x ≠ 0 ∨ X ≠ 0) ∧
        ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0 ∧
        x ≠ X := by
  obtain ⟨Rzero, c, hdescent, hdecomposition, hdiagonal⟩ :=
    exists_e_theta_diagonal_square_of_rotationInvariant_and_jacobian_dvd
      R homega hinvariant hdiv
  have hthetaHomogeneous :
      EPairIsHomogeneous (eThetaPolynomial ℂ c) (N - 1) :=
    eThetaPolynomial_isHomogeneous_of_form_and_basis
      hdescent hhomogeneous hdecomposition
  have hcubeRoot : omega ^ 2 + omega + 1 = 0 := by
    have hsum := IsPrimitiveRoot.geom_sum_eq_zero homega
      (by norm_num : 1 < 3)
    norm_num [Finset.sum_range_succ] at hsum
    linear_combination hsum
  obtain ⟨x, X, hnonzero, htheta, hne⟩ :=
    eThetaPolynomial_exists_off_diagonal_projective_zero
      omega hcubeRoot c (N - 1) hthetaHomogeneous hdiagonal
  exact ⟨Rzero, c, hdescent, hdecomposition, hthetaHomogeneous,
    hdiagonal, x, X, hnonzero, htheta, hne⟩

end OnLeConjecture.DThree
