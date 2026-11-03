/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HomogenizedResiduePolynomialMap
public import OnLeConjecture.DThree.WeightedResidueDecomposition
public import OnLeConjecture.DThree.WeightedTwoFormsODE
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Chart polynomial of a weighted binary form

An ordinary homogeneous binary form is recovered by homogenizing its chart
polynomial. After the substitution `t = y^a`, this homogenization is the
polynomial used by the residue collision theorems.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Weighted dehomogenization is evaluation at `(X,1)`. -/
theorem weightedDehomogenize_eq_aeval (F : Form ℂ) :
    weightedDehomogenize F = MvPolynomial.aeval ![X, 1] F := by
  let left : Form ℂ →ₐ[ℂ] ℂ[X] := weightedDehomogenize
  let right : Form ℂ →ₐ[ℂ] ℂ[X] := MvPolynomial.aeval ![X, 1]
  have hequality : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [left, right, weightedDehomogenize]
    · simp [left, right, weightedDehomogenize]
  exact AlgHom.congr_fun hequality F

/-- The chart polynomial is obtained from `finSuccEquiv` by evaluating its
coefficient variable at one. -/
theorem weightedDehomogenize_eq_map_finSuccEquiv (F : Form ℂ) :
    weightedDehomogenize F =
      Polynomial.map (MvPolynomial.eval fun _ : Fin 1 ↦ (1 : ℂ))
        (MvPolynomial.finSuccEquiv ℂ 1 F) := by
  let left : Form ℂ →ₐ[ℂ] ℂ[X] := weightedDehomogenize
  let evaluation : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval fun _ ↦ (1 : ℂ)
  let right : Form ℂ →ₐ[ℂ] ℂ[X] :=
    (Polynomial.mapAlgHom evaluation).comp
      (MvPolynomial.finSuccEquiv ℂ 1).toAlgHom
  have hequality : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [left, right, weightedDehomogenize,
        Polynomial.coe_mapAlgHom, MvPolynomial.finSuccEquiv_X_zero]
    · simp only [left, right, weightedDehomogenize,
        MvPolynomial.aeval_X, AlgHom.coe_comp, Function.comp_apply,
        AlgEquiv.coe_toAlgHom, Polynomial.coe_mapAlgHom]
      change (if j.succ = 0 then X else 1) =
        Polynomial.map evaluation.toRingHom
          (MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X j.succ))
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
      fin_cases j
      simp [evaluation]
  change left F = right F
  exact AlgHom.congr_fun hequality F

/-- The chart degree does not exceed the degree of a homogeneous binary
form. -/
theorem weightedDehomogenize_natDegree_le
    {F : Form ℂ} {N : ℕ} (hF : F.IsHomogeneous N) :
    (weightedDehomogenize F).natDegree ≤ N := by
  rw [weightedDehomogenize_eq_map_finSuccEquiv]
  calc
    (Polynomial.map (MvPolynomial.eval fun _ : Fin 1 ↦ (1 : ℂ))
        (MvPolynomial.finSuccEquiv ℂ 1 F)).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1 F).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 0 F :=
      MvPolynomial.natDegree_finSuccEquiv F
    _ ≤ MvPolynomial.totalDegree F :=
      MvPolynomial.degreeOf_le_totalDegree F 0
    _ ≤ N := hF.totalDegree_le

/-- Homogenizing the chart polynomial recovers a homogeneous binary form. -/
theorem homogenize_weightedDehomogenize
    {F : Form ℂ} {N : ℕ} (hF : F.IsHomogeneous N) :
    (weightedDehomogenize F).homogenize N = F := by
  apply Polynomial.homogenize_eq_of_isHomogeneous hF
  rw [weightedDehomogenize_eq_aeval]

/-- Power substitution applied to a homogenized polynomial is the explicit
weighted homogenization used in the collision maps. -/
theorem weightedPowerSubstitutionForm_homogenize
    (a N : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ N) :
    weightedPowerSubstitutionForm a (p.homogenize N) =
      weightedHomogenizedPolynomial a N p := by
  refine Polynomial.induction_with_natDegree_le
    (motive := fun q ↦
      weightedPowerSubstitutionForm a (q.homogenize N) =
        weightedHomogenizedPolynomial a N q)
    N ?_ ?_ ?_ p hp
  · simp [weightedHomogenizedPolynomial]
  · intro n r hr hn
    rw [Polynomial.homogenize_C_mul,
      Polynomial.homogenize_X_pow hn, map_mul, map_mul, map_pow]
    have hnmem : n ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
    rw [weightedHomogenizedPolynomial,
      Finset.sum_eq_single n
        (fun i hi hin ↦ by
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hin])
        (fun hnot ↦ (hnot hnmem).elim)]
    simp [weightedPowerSubstitutionForm, formX, formT,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, pow_mul]
    ring
  · intro f g hdegree hgle ihf ihg
    rw [Polynomial.homogenize_add, map_add, ihf, ihg]
    simp [weightedHomogenizedPolynomial, Finset.sum_add_distrib,
      add_mul]

/-- Power substitution of a homogeneous form is the weighted homogenization
of its chart polynomial. -/
theorem weightedPowerSubstitutionForm_eq_weightedHomogenizedPolynomial
    (a : ℕ) {F : Form ℂ} {N : ℕ} (hF : F.IsHomogeneous N) :
    weightedPowerSubstitutionForm a F =
      weightedHomogenizedPolynomial a N (weightedDehomogenize F) := by
  calc
    weightedPowerSubstitutionForm a F =
        weightedPowerSubstitutionForm a
          ((weightedDehomogenize F).homogenize N) := by
      rw [homogenize_weightedDehomogenize hF]
    _ = weightedHomogenizedPolynomial a N (weightedDehomogenize F) :=
      weightedPowerSubstitutionForm_homogenize a N
        (weightedDehomogenize F) (weightedDehomogenize_natDegree_le hF)

/-- Every weighted homogeneous binary form has the chart presentation used
by the residue collision maps. -/
theorem exists_weightedResidueChartPolynomial
    (a D : ℕ) (ha : 0 < a) (P : Form ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) :
    ∃ p : ℂ[X], p.natDegree ≤ D / a ∧
      P = weightedThirdInitialPolynomial a (D / a) (D % a) p := by
  obtain ⟨F, hF, hdecomposition⟩ :=
    exists_weightedResidueDecomposition a D ha P hP
  let p := weightedDehomogenize F
  refine ⟨p, weightedDehomogenize_natDegree_le hF, ?_⟩
  rw [weightedThirdInitialPolynomial,
    ← weightedPowerSubstitutionForm_eq_weightedHomogenizedPolynomial a hF]
  exact hdecomposition

/-- A nonzero weighted homogeneous form has a nonzero chart polynomial in
its residue presentation. -/
theorem exists_nonzero_weightedResidueChartPolynomial
    (a D : ℕ) (ha : 0 < a) (P : Form ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) (hPzero : P ≠ 0) :
    ∃ p : ℂ[X], p.natDegree ≤ D / a ∧ p ≠ 0 ∧
      P = weightedThirdInitialPolynomial a (D / a) (D % a) p := by
  obtain ⟨F, hF, hdecomposition⟩ :=
    exists_weightedResidueDecomposition a D ha P hP
  let p := weightedDehomogenize F
  have hFzero : F ≠ 0 :=
    weightedResidueDecomposition_ne_zero hPzero hdecomposition
  have hpzero : p ≠ 0 := by
    intro hp
    apply hFzero
    rw [← homogenize_weightedDehomogenize hF]
    simp [p, hp]
  refine ⟨p, weightedDehomogenize_natDegree_le hF, hpzero, ?_⟩
  rw [weightedThirdInitialPolynomial,
    ← weightedPowerSubstitutionForm_eq_weightedHomogenizedPolynomial a hF]
  exact hdecomposition

end OnLeConjecture.DThree
