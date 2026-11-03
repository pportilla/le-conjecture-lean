/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.AnalyticRescaling
public import OnLeConjecture.DThree.WeightedResidueDecomposition
public import OnLeConjecture.DThree.WeightedQuarticInitialForm

/-!
# Analytic rescaling of weighted initial forms

Scaling the first source coordinate and the target coordinates preserves the
finite weighted order ideals. The same change carries the classified cubic
and quartic to the weighted versions of the E and H forms.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic
open _root_.Polynomial

/-- The algebra map which replaces the first variable by `s x` and fixes the
second variable. -/
@[expose]
noncomputable def sourceRescaleFormAlgHom (s : ℂ) :
    Form ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval fun i ↦
    if i = 0 then MvPolynomial.C s * formX else formT

@[simp]
theorem sourceRescaleFormAlgHom_x (s : ℂ) :
    sourceRescaleFormAlgHom s formX = MvPolynomial.C s * formX := by
  simp [sourceRescaleFormAlgHom, formX]

@[simp]
theorem sourceRescaleFormAlgHom_t (s : ℂ) :
    sourceRescaleFormAlgHom s formT = formT := by
  simp [sourceRescaleFormAlgHom, formT]

/-- The source rescaling commutes with replacing the second variable by its
`a`th power. -/
theorem sourceRescaleFormAlgHom_weightedPowerSubstitutionForm
    (a : ℕ) (s : ℂ) (F : Form ℂ) :
    sourceRescaleFormAlgHom s (weightedPowerSubstitutionForm a F) =
      weightedPowerSubstitutionForm a (sourceRescaleFormAlgHom s F) := by
  have hequality :
      (sourceRescaleFormAlgHom s).comp (weightedPowerSubstitutionForm a) =
        (weightedPowerSubstitutionForm a).comp
          (sourceRescaleFormAlgHom s) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [sourceRescaleFormAlgHom, weightedPowerSubstitutionForm,
        formX, formT]
    · simp [sourceRescaleFormAlgHom, weightedPowerSubstitutionForm,
        formX, formT]
  exact AlgHom.congr_fun hequality F

/-- `rescaleForm` is multiplication by the target scalar after source
rescaling. -/
theorem rescaleForm_eq_C_mul_sourceRescaleFormAlgHom
    (s u : ℂ) (F : Form ℂ) :
    rescaleForm s u F =
      MvPolynomial.C u * sourceRescaleFormAlgHom s F := by
  rfl

/-- Weighted power substitution commutes with the complete source and target
rescaling. -/
theorem rescaleForm_weightedPowerSubstitutionForm
    (a : ℕ) (s u : ℂ) (F : Form ℂ) :
    rescaleForm s u (weightedPowerSubstitutionForm a F) =
      weightedPowerSubstitutionForm a (rescaleForm s u F) := by
  rw [rescaleForm_eq_C_mul_sourceRescaleFormAlgHom,
    rescaleForm_eq_C_mul_sourceRescaleFormAlgHom, map_mul,
    sourceRescaleFormAlgHom_weightedPowerSubstitutionForm]
  simp

/-- The weighted cubic is the power substitution of its ordinary binary
form. -/
theorem weightedCubicPolynomial_eq_weightedPowerSubstitutionForm
    (a : ℕ) (A B : ℂ) :
    weightedCubicPolynomial a A B =
      weightedPowerSubstitutionForm a (cubicForm A B) := by
  simp [weightedCubicPolynomial, weightedPowerSubstitutionForm,
    cubicForm, formX, formT]
  ring

/-- The weighted quartic is the power substitution of its ordinary binary
form. -/
theorem weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm
    (a : ℕ) (c₄ c₃ c₂ c₁ c₀ : ℂ) :
    weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ =
      weightedPowerSubstitutionForm a
        (quarticForm c₄ c₃ c₂ c₁ c₀) := by
  simp [weightedQuarticPolynomial, weightedPowerSubstitutionForm,
    quarticForm, formX, formT]
  ring

/-- Source rescaling preserves weighted homogeneity. -/
theorem sourceRescaleFormAlgHom_isWeightedHomogeneous
    {a D : ℕ} {F : Form ℂ}
    (hF : F.IsWeightedHomogeneous ![a, 1] D) (s : ℂ) :
    (sourceRescaleFormAlgHom s F).IsWeightedHomogeneous ![a, 1] D := by
  have hx :
      (MvPolynomial.C s * formX : Form ℂ).IsWeightedHomogeneous
        ![a, 1] a :=
    (MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0).C_mul s
  have ht :
      (formT : Form ℂ).IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      rw [map_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ ![a, 1] D
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact ihp.add ihq
  | monomial d c hd =>
      rw [sourceRescaleFormAlgHom, MvPolynomial.aeval_def,
        MvPolynomial.eval₂_monomial]
      have hproduct : MvPolynomial.IsWeightedHomogeneous ![a, 1]
          (∏ i ∈ d.support,
            (if i = 0 then
              (MvPolynomial.C s * formX : Form ℂ) else formT) ^ d i)
          (∑ i ∈ d.support, d i * ![a, 1] i) := by
        apply MvPolynomial.IsWeightedHomogeneous.prod
        intro i hi
        fin_cases i
        · simpa using hx.pow (d 0)
        · simpa using ht.pow (d 1)
      have hdegree : ∑ i ∈ d.support, d i * ![a, 1] i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum] using hd
      rw [hdegree] at hproduct
      exact hproduct.C_mul c

/-- Complete rescaling preserves weighted homogeneity. -/
theorem rescaleForm_isWeightedHomogeneous
    {a D : ℕ} {F : Form ℂ}
    (hF : F.IsWeightedHomogeneous ![a, 1] D) (s u : ℂ) :
    (rescaleForm s u F).IsWeightedHomogeneous ![a, 1] D := by
  rw [rescaleForm_eq_C_mul_sourceRescaleFormAlgHom]
  exact (sourceRescaleFormAlgHom_isWeightedHomogeneous hF s).C_mul u

/-- Pullback by the first source coordinate scaling preserves every weighted
order ideal. -/
theorem sourceRescale_pullback_mem_weightedOrderIdeal
    (a D : ℕ) (s : ℂ) (hs : s ≠ 0) {f : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a D) :
    (diagonalPointedEquiv (sourceRescaleVector s)
      (sourceRescaleVector_ne_zero hs)).forward.pullbackRingHom f ∈
        Germ.weightedOrderIdeal a D := by
  rw [Germ.mem_weightedOrderIdeal_iff] at hf
  obtain ⟨c, hc⟩ := hf
  rw [← hc, map_sum]
  apply Ideal.sum_mem
  intro k hk
  rw [map_mul]
  apply Ideal.mul_mem_left
  have hgenerator : Germ.weightedOrderGenerator a D k ∈
      Germ.weightedOrderIdeal a D :=
    Germ.weightedOrderGenerator_mem a D k
  have hequality :
      (diagonalPointedEquiv (sourceRescaleVector s)
        (sourceRescaleVector_ne_zero hs)).forward.pullbackRingHom
          (Germ.weightedOrderGenerator a D k) =
        Germ.constRingHom 2 (s ^ (k : ℕ)) *
          Germ.weightedOrderGenerator a D k := by
    simp only [Germ.weightedOrderGenerator, map_mul, map_pow,
      PointedMapGerm.pullback_coordinate, diagonalPointedEquiv_component,
      sourceRescaleVector, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_one, one_mul]
    rw [mul_pow]
    ring
  rw [hequality]
  exact Ideal.mul_mem_left _ _ hgenerator

/-- A strict weighted tail remains a strict weighted tail after source and
target rescaling. -/
theorem rescaledPointedMap_component_weightedTail
    (g : PointedMapGerm 2 3) (a D : ℕ) (s u v w : ℂ)
    (hs : s ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (i : Fin 3) (F : Form ℂ)
    (htail : g.1.component i - Germ.coordinatePolynomialAlgHom 2 F ∈
      Germ.weightedOrderIdeal a D) :
    (rescaledPointedMap g s u v w hs hu hv hw).1.component i -
        Germ.coordinatePolynomialAlgHom 2
          (rescaleForm s (targetRescaleVector u v w i) F) ∈
      Germ.weightedOrderIdeal a D := by
  rw [rescaledPointedMap_component,
    coordinatePolynomial_rescaleForm s
      (targetRescaleVector u v w i) hs F, ← mul_sub]
  apply Ideal.mul_mem_left
  have hpull := sourceRescale_pullback_mem_weightedOrderIdeal
    a D s hs htail
  rw [map_sub] at hpull
  exact hpull

/-- The ordinary E or H rescaling induces the corresponding rescaling of
the weighted cubic and quartic. -/
theorem exists_weightedRescaling_to_E_or_H
    (a : ℕ) (A B c₄ c₃ c₂ c₁ c₀ c : ℂ)
    (hc : c ≠ 0)
    (hODE :
      4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
        3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative = C c) :
    ∃ s u v : ℂ, s ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      ((rescaleForm s u (weightedCubicPolynomial a A B) =
            weightedCubicPolynomial a 0 3 ∧
          rescaleForm s v
              (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) =
            weightedQuarticPolynomial a 1 0 0 4 0) ∨
       (rescaleForm s u (weightedCubicPolynomial a A B) =
            weightedCubicPolynomial a 3 0 ∧
          rescaleForm s v
              (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) =
            weightedQuarticPolynomial a 1 0 4 0 2)) := by
  obtain ⟨s, u, v, hs, hu, hv, hE | hH⟩ :=
    rescaleForms_to_E_or_H A B c₄ c₃ c₂ c₁ c₀ c hc hODE
  · rcases hE with ⟨hcubic, hquartic⟩
    refine ⟨s, u, v, hs, hu, hv, Or.inl ⟨?_, ?_⟩⟩
    · rw [weightedCubicPolynomial_eq_weightedPowerSubstitutionForm,
        rescaleForm_weightedPowerSubstitutionForm, hcubic,
        ← weightedCubicPolynomial_eq_weightedPowerSubstitutionForm]
    · rw [weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm,
        rescaleForm_weightedPowerSubstitutionForm, hquartic,
        ← weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm]
  · rcases hH with ⟨hcubic, hquartic⟩
    refine ⟨s, u, v, hs, hu, hv, Or.inr ⟨?_, ?_⟩⟩
    · rw [weightedCubicPolynomial_eq_weightedPowerSubstitutionForm,
        rescaleForm_weightedPowerSubstitutionForm, hcubic,
        ← weightedCubicPolynomial_eq_weightedPowerSubstitutionForm]
    · rw [weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm,
        rescaleForm_weightedPowerSubstitutionForm, hquartic,
        ← weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm]

/-- Analytic source and target rescaling carries weighted initial forms to
the E or H pair and preserves all three strict weighted tails. -/
theorem exists_rightLeft_weightedRescaling_to_E_or_H
    (g : PointedMapGerm 2 3) (a D : ℕ) (R : Form ℂ)
    (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (A B c₄ c₃ c₂ c₁ c₀ c : ℂ)
    (hc : c ≠ 0)
    (hODE :
      4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
        3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative = C c)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1)) :
    ∃ s : ℂ, ∃ h : PointedMapGerm 2 3,
      s ≠ 0 ∧ g.RightLeftEquivalent h ∧
      (h.HasInjectiveRepresentative ↔ g.HasInjectiveRepresentative) ∧
      (rescaleForm s 1 R).IsWeightedHomogeneous ![a, 1] D ∧
      ((h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (weightedCubicPolynomial a 0 3) ∈
            Germ.weightedOrderIdeal a (3 * a + 1) ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (weightedQuarticPolynomial a 1 0 0 4 0) ∈
            Germ.weightedOrderIdeal a (4 * a + 1) ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.weightedOrderIdeal a (D + 1)) ∨
       (h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (weightedCubicPolynomial a 3 0) ∈
            Germ.weightedOrderIdeal a (3 * a + 1) ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (weightedQuarticPolynomial a 1 0 4 0 2) ∈
            Germ.weightedOrderIdeal a (4 * a + 1) ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.weightedOrderIdeal a (D + 1))) := by
  obtain ⟨s, u, v, hs, hu, hv, hE | hH⟩ :=
    exists_weightedRescaling_to_E_or_H
      a A B c₄ c₃ c₂ c₁ c₀ c hc hODE
  all_goals
    let h := rescaledPointedMap g s u v 1 hs hu hv one_ne_zero
    have hequivalent : g.RightLeftEquivalent h :=
      rightLeftEquivalent_rescaledPointedMap
        g s u v 1 hs hu hv one_ne_zero
    have hinjective := hequivalent.hasInjectiveRepresentative_iff
    have hRscaled :
        (rescaleForm s 1 R).IsWeightedHomogeneous ![a, 1] D :=
      rescaleForm_isWeightedHomogeneous hR s 1
    refine ⟨s, h, hs, hequivalent, hinjective, hRscaled, ?_⟩
  · apply Or.inl
    rcases hE with ⟨hzeroForm, honeForm⟩
    refine ⟨?_, ?_, ?_⟩
    · have htail := rescaledPointedMap_component_weightedTail
          g a (3 * a + 1) s u v 1 hs hu hv one_ne_zero 0
            (weightedCubicPolynomial a A B) htailZero
      simpa [h, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (4 * a + 1) s u v 1 hs hu hv one_ne_zero 1
            (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) htailOne
      simpa [h, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (D + 1) s u v 1 hs hu hv one_ne_zero 2 R htailTwo
      simpa [h, targetRescaleVector] using htail
  · apply Or.inr
    rcases hH with ⟨hzeroForm, honeForm⟩
    refine ⟨?_, ?_, ?_⟩
    · have htail := rescaledPointedMap_component_weightedTail
          g a (3 * a + 1) s u v 1 hs hu hv one_ne_zero 0
            (weightedCubicPolynomial a A B) htailZero
      simpa [h, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (4 * a + 1) s u v 1 hs hu hv one_ne_zero 1
            (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) htailOne
      simpa [h, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_weightedTail
          g a (D + 1) s u v 1 hs hu hv one_ne_zero 2 R htailTwo
      simpa [h, targetRescaleVector] using htail

end OnLeConjecture.DThree
