/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedInitialFormExistence
public import OnLeConjecture.DThree.WeightedCubicInitialForm

/-!
# Weighted quartic initial forms

A plane analytic germ of weighted order at least `4a` has a quartic initial
form after the substitution `t = y^a`. Exact weighted order makes this
quartic nonzero.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The degree four form after replacing its second variable by the `a`th
power of the second source coordinate. -/
@[expose]
noncomputable def weightedQuarticPolynomial
    (a : ℕ) (c₄ c₃ c₂ c₁ c₀ : ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C c₄ * MvPolynomial.X 0 ^ 4 +
    MvPolynomial.C c₃ * MvPolynomial.X 0 ^ 3 *
      MvPolynomial.X 1 ^ a +
    MvPolynomial.C c₂ * MvPolynomial.X 0 ^ 2 *
      MvPolynomial.X 1 ^ (2 * a) +
    MvPolynomial.C c₁ * MvPolynomial.X 0 *
      MvPolynomial.X 1 ^ (3 * a) +
    MvPolynomial.C c₀ * MvPolynomial.X 1 ^ (4 * a)

/-- Coordinate evaluation of the weighted quartic is its displayed analytic
germ. -/
theorem coordinatePolynomial_weightedQuarticPolynomial
    (a : ℕ) (c₄ c₃ c₂ c₁ c₀ : ℂ) :
    Germ.coordinatePolynomialAlgHom 2
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) =
      Germ.constRingHom 2 c₄ * Germ.coordinate (0 : Fin 2) ^ 4 +
        Germ.constRingHom 2 c₃ * Germ.coordinate (0 : Fin 2) ^ 3 *
          Germ.coordinate (1 : Fin 2) ^ a +
        Germ.constRingHom 2 c₂ * Germ.coordinate (0 : Fin 2) ^ 2 *
          Germ.coordinate (1 : Fin 2) ^ (2 * a) +
        Germ.constRingHom 2 c₁ * Germ.coordinate (0 : Fin 2) *
          Germ.coordinate (1 : Fin 2) ^ (3 * a) +
        Germ.constRingHom 2 c₀ * Germ.coordinate (1 : Fin 2) ^ (4 * a) := by
  have hconst (c : ℂ) :
      algebraMap ℂ (Germ 2) c = Germ.constRingHom 2 c := by rfl
  simp [weightedQuarticPolynomial, hconst]

/-- Every displayed weighted quartic is homogeneous of weighted degree
`4a`. -/
theorem weightedQuarticPolynomial_isWeightedHomogeneous
    (a : ℕ) (c₄ c₃ c₂ c₁ c₀ : ℂ) :
    (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀)
      |>.IsWeightedHomogeneous ![a, 1] (4 * a) := by
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] a :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  have h₄ := (hx.pow 4).C_mul c₄
  have h₃ := ((hx.pow 3).mul (hy.pow a)).C_mul c₃
  have h₂ := ((hx.pow 2).mul (hy.pow (2 * a))).C_mul c₂
  have h₁ := (hx.mul (hy.pow (3 * a))).C_mul c₁
  have h₀ := (hy.pow (4 * a)).C_mul c₀
  have h₄' :
      (MvPolynomial.C c₄ * MvPolynomial.X (0 : Fin 2) ^ 4 :
          MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![a, 1] (4 * a) := by
    simpa [nsmul_eq_mul] using h₄
  have h₃' :
      (MvPolynomial.C c₃ * MvPolynomial.X (0 : Fin 2) ^ 3 *
          MvPolynomial.X (1 : Fin 2) ^ a : MvPolynomial (Fin 2) ℂ)
        |>.IsWeightedHomogeneous ![a, 1] (4 * a) := by
    rw [show (3 : ℕ) • a + a • 1 = 4 * a by
      simp
      omega] at h₃
    simpa only [mul_assoc] using h₃
  have h₂' :
      (MvPolynomial.C c₂ * MvPolynomial.X (0 : Fin 2) ^ 2 *
          MvPolynomial.X (1 : Fin 2) ^ (2 * a) :
        MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![a, 1] (4 * a) := by
    rw [show (2 : ℕ) • a + (2 * a) • 1 = 4 * a by
      simp
      omega] at h₂
    simpa only [mul_assoc] using h₂
  have h₁' :
      (MvPolynomial.C c₁ * MvPolynomial.X (0 : Fin 2) *
          MvPolynomial.X (1 : Fin 2) ^ (3 * a) :
          MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![a, 1] (4 * a) := by
    rw [show a + (3 * a) • 1 = 4 * a by
      simp
      omega] at h₁
    simpa only [mul_assoc] using h₁
  have h₀' :
      (MvPolynomial.C c₀ * MvPolynomial.X (1 : Fin 2) ^ (4 * a) :
          MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![a, 1] (4 * a) := by
    simpa [nsmul_eq_mul] using h₀
  simpa only [weightedQuarticPolynomial] using
    (((h₄'.add h₃').add h₂').add h₁').add h₀'

/-- A weighted homogeneous polynomial of degree `4a` has the displayed
quartic form. -/
theorem exists_eq_weightedQuarticPolynomial_of_isWeightedHomogeneous
    (a : ℕ) (ha : 0 < a) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] (4 * a)) :
    ∃ c₄ c₃ c₂ c₁ c₀ : ℂ,
      P = weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      exact ⟨0, 0, 0, 0, 0, by simp [weightedQuarticPolynomial]⟩
  | add p q hp hq ihp ihq =>
      obtain ⟨p₄, p₃, p₂, p₁, p₀, hpForm⟩ := ihp
      obtain ⟨q₄, q₃, q₂, q₁, q₀, hqForm⟩ := ihq
      refine ⟨p₄ + q₄, p₃ + q₃, p₂ + q₂, p₁ + q₁, p₀ + q₀, ?_⟩
      rw [hpForm, hqForm]
      simp only [weightedQuarticPolynomial, map_add]
      ring
  | monomial d c hd =>
      have hdegree : a * d 0 + d 1 = 4 * a := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
      have hd₀ : d 0 ≤ 4 := by
        nlinarith
      interval_cases hcase : d 0
      · have hd' : d = Finsupp.single (1 : Fin 2) (4 * a) := by
          ext i
          fin_cases i
          · simp [hcase]
          · simp
            omega
        subst d
        refine ⟨0, 0, 0, 0, c, ?_⟩
        rw [MvPolynomial.monomial_fin_two]
        simp [weightedQuarticPolynomial]
      · have hd' : d = Finsupp.single (0 : Fin 2) 1 +
            Finsupp.single (1 : Fin 2) (3 * a) := by
          ext i
          fin_cases i
          · simp [hcase]
          · simp
            omega
        subst d
        refine ⟨0, 0, 0, c, 0, ?_⟩
        rw [MvPolynomial.monomial_fin_two]
        simp [weightedQuarticPolynomial]
      · have hd' : d = Finsupp.single (0 : Fin 2) 2 +
            Finsupp.single (1 : Fin 2) (2 * a) := by
          ext i
          fin_cases i
          · simp [hcase]
          · simp
            omega
        subst d
        refine ⟨0, 0, c, 0, 0, ?_⟩
        rw [MvPolynomial.monomial_fin_two]
        simp [weightedQuarticPolynomial]
      · have hd' : d = Finsupp.single (0 : Fin 2) 3 +
            Finsupp.single (1 : Fin 2) a := by
          ext i
          fin_cases i
          · simp [hcase]
          · simp
            omega
        subst d
        refine ⟨0, c, 0, 0, 0, ?_⟩
        rw [MvPolynomial.monomial_fin_two]
        simp [weightedQuarticPolynomial]
      · have hd' : d = Finsupp.single (0 : Fin 2) 4 := by
          ext i
          fin_cases i
          · simp [hcase]
          · simp
            omega
        subst d
        refine ⟨c, 0, 0, 0, 0, ?_⟩
        rw [MvPolynomial.monomial_fin_two]
        simp [weightedQuarticPolynomial]

/-- Membership in weighted order `4a` produces a quartic initial form and a
tail of strict weighted order. -/
theorem exists_weightedQuarticInitialForm
    (a : ℕ) (ha : 0 < a) (q : Germ 2)
    (hq : q ∈ Germ.weightedOrderIdeal a (4 * a)) :
    ∃ c₄ c₃ c₂ c₁ c₀ : ℂ,
      q - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1) := by
  obtain ⟨P, hP, htail⟩ :=
    Germ.exists_weightedHomogeneous_coordinatePolynomial_mod_succ
      a (4 * a) ha q hq
  obtain ⟨c₄, c₃, c₂, c₁, c₀, rfl⟩ :=
    exists_eq_weightedQuarticPolynomial_of_isWeightedHomogeneous a ha P hP
  exact ⟨c₄, c₃, c₂, c₁, c₀, htail⟩

/-- Exact weighted order `4a` produces a nonzero quartic initial form. -/
theorem exists_nonzero_weightedQuarticInitialForm
    (a : ℕ) (ha : 0 < a) (q : Germ 2)
    (hq : q ∈ Germ.weightedOrderIdeal a (4 * a))
    (hnext : q ∉ Germ.weightedOrderIdeal a (4 * a + 1)) :
    ∃ c₄ c₃ c₂ c₁ c₀ : ℂ,
      weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0 ∧
      q - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1) := by
  obtain ⟨P, hPne, hP, htail⟩ :=
    Germ.exists_nonzero_weightedHomogeneous_coordinatePolynomial_mod_succ
      a (4 * a) ha q hq hnext
  obtain ⟨c₄, c₃, c₂, c₁, c₀, hform⟩ :=
    exists_eq_weightedQuarticPolynomial_of_isWeightedHomogeneous a ha P hP
  subst P
  exact ⟨c₄, c₃, c₂, c₁, c₀, hPne, htail⟩

/-- The second component of a pointed plane map has a nonzero weighted
quartic initial form when it has exact weighted order `4a`. -/
theorem PointedMapGerm.exists_secondComponent_nonzero_weightedQuarticInitialForm
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (hmem : g.1.component 1 ∈ Germ.weightedOrderIdeal a (4 * a))
    (hexact : g.1.component 1 ∉ Germ.weightedOrderIdeal a (4 * a + 1)) :
    ∃ c₄ c₃ c₂ c₁ c₀ : ℂ,
      weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0 ∧
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1) :=
  exists_nonzero_weightedQuarticInitialForm a ha (g.1.component 1)
    hmem hexact

/-- Prepared coefficient orders for the first component and exact weighted
order `4a` for the second component produce the two polynomial initial forms
used in the order three classification. -/
theorem PointedMapGerm.exists_weightedCubicAndQuarticInitialForms_of_preparedComponents
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (a₁ a₀ : Germ 1) (u : Germ 2)
    (hfirst : g.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u)
    (hu : IsUnit u)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (hcubicExact :
      a₁ ∉ Germ.maximalIdeal 1 ^ (2 * a + 1) ∨
        a₀ ∉ Germ.maximalIdeal 1 ^ (3 * a + 1))
    (hquartic : g.1.component 1 ∈
      Germ.weightedOrderIdeal a (4 * a))
    (hquarticExact : g.1.component 1 ∉
      Germ.weightedOrderIdeal a (4 * a + 1)) :
    ∃ A B c₄ c₃ c₂ c₁ c₀ : ℂ,
      (A ≠ 0 ∨ B ≠ 0) ∧
      Germ.valueRingHom 2 u ≠ 0 ∧
      weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0 ∧
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C (Germ.valueRingHom 2 u) *
            weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) ∧
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1) := by
  obtain ⟨A, B, hAB, hcubicTail⟩ :=
    exists_weightedCubicInitialForm_of_coefficientOrders
      a ha a₁ a₀ u ha₁ ha₀ hcubicExact
  obtain ⟨c₄, c₃, c₂, c₁, c₀, hQ, hquarticTail⟩ :=
    exists_nonzero_weightedQuarticInitialForm
      a ha (g.1.component 1) hquartic hquarticExact
  have hU : Germ.valueRingHom 2 u ≠ 0 :=
    Germ.valueRingHom_ne_zero_of_isUnit hu
  refine ⟨A, B, c₄, c₃, c₂, c₁, c₀, hAB, hU, hQ, ?_,
    hquarticTail⟩
  rw [hfirst]
  exact hcubicTail

/-- Constant rescaling of the first target coordinate makes the cubic initial
form monic while preserving the quartic and both strict weighted tails. -/
theorem PointedMapGerm.exists_monicWeightedCubicAndQuarticInitialForms_of_preparedComponents
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (hfinite : g.IsFiniteAtOrigin)
    (hinjective : g.HasInjectiveRepresentative)
    (hdifferential : g.differential = 0)
    (a₁ a₀ : Germ 1) (u : Germ 2)
    (hfirst : g.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u)
    (hu : IsUnit u)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (hcubicExact :
      a₁ ∉ Germ.maximalIdeal 1 ^ (2 * a + 1) ∨
        a₀ ∉ Germ.maximalIdeal 1 ^ (3 * a + 1))
    (hquartic : g.1.component 1 ∈
      Germ.weightedOrderIdeal a (4 * a))
    (hquarticExact : g.1.component 1 ∉
      Germ.weightedOrderIdeal a (4 * a + 1)) :
    ∃ h : PointedMapGerm 2 3, ∃ A B c₄ c₃ c₂ c₁ c₀ : ℂ,
      g.RightLeftEquivalent h ∧
      h.IsFiniteAtOrigin ∧
      h.HasInjectiveRepresentative ∧
      h.differential = 0 ∧
      (A ≠ 0 ∨ B ≠ 0) ∧
      weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0 ∧
      h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) ∧
      h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1) := by
  obtain ⟨A, B, c₄, c₃, c₂, c₁, c₀, hAB, hU, hQ,
      hcubicTail, hquarticTail⟩ :=
    PointedMapGerm.exists_weightedCubicAndQuarticInitialForms_of_preparedComponents
        g a ha a₁ a₀ u hfirst hu ha₁ ha₀ hcubicExact
          hquartic hquarticExact
  let targetScale : Fin 3 → ℂ :=
    ![(Germ.valueRingHom 2 u)⁻¹, 1, 1]
  have htargetScale : ∀ i, targetScale i ≠ 0 := by
    intro i
    fin_cases i
    · exact inv_ne_zero hU
    · exact one_ne_zero
    · exact one_ne_zero
  let target := diagonalPointedEquiv targetScale htargetScale
  let h : PointedMapGerm 2 3 := target.forward.comp g
  have hequivalent : g.RightLeftEquivalent h := by
    refine ⟨PointedEquivGerm.identity 2, target, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  have hcomponent (i : Fin 3) :
      h.1.component i =
        Germ.constRingHom 2 (targetScale i) * g.1.component i := by
    change (target.forward.comp g).1.component i = _
    rw [PointedMapGerm.component_comp_general]
    rw [show target.forward.1.component i =
      Germ.constRingHom 3 (targetScale i) * Germ.coordinate i by
        exact diagonalPointedEquiv_component targetScale htargetScale i]
    rw [map_mul, PointedMapGerm.pullback_constRingHom,
      PointedMapGerm.pullback_coordinate]
  have hcomponentZero : h.1.component 0 =
      Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
        g.1.component 0 := by
    simpa only [targetScale, Matrix.cons_val_zero] using hcomponent 0
  have hcomponentOne : h.1.component 1 = g.1.component 1 := by
    simpa [targetScale] using hcomponent 1
  have hcubicEvaluation :
      Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C (Germ.valueRingHom 2 u) *
            weightedCubicPolynomial a A B) =
        Germ.constRingHom 2 (Germ.valueRingHom 2 u) *
          Germ.coordinatePolynomialAlgHom 2
            (weightedCubicPolynomial a A B) := by
    rw [map_mul, Germ.coordinatePolynomialAlgHom_C]
  have hconstantProduct :
      Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
          Germ.constRingHom 2 (Germ.valueRingHom 2 u) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hU, map_one]
  have hcubicEquality :
      h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) =
        Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
          (g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
            (MvPolynomial.C (Germ.valueRingHom 2 u) *
              weightedCubicPolynomial a A B)) := by
    rw [hcomponentZero, hcubicEvaluation]
    calc
      Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
            g.1.component 0 -
          Germ.coordinatePolynomialAlgHom 2
            (weightedCubicPolynomial a A B) =
        Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
              g.1.component 0 -
            (Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
              Germ.constRingHom 2 (Germ.valueRingHom 2 u)) *
                Germ.coordinatePolynomialAlgHom 2
                  (weightedCubicPolynomial a A B) := by
          rw [hconstantProduct, one_mul]
      _ = _ := by ring
  have hcubicTailH :
      h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) := by
    rw [hcubicEquality]
    exact Ideal.mul_mem_left _ _ hcubicTail
  have hquarticTailH :
      h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1) := by
    rw [hcomponentOne]
    exact hquarticTail
  refine ⟨h, A, B, c₄, c₃, c₂, c₁, c₀, hequivalent,
    hequivalent.isFiniteAtOrigin_iff.mpr hfinite,
    hequivalent.hasInjectiveRepresentative hinjective,
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff
      hequivalent).mpr hdifferential,
    hAB, hQ, hcubicTailH, hquarticTailH⟩

end OnLeConjecture.DThree
