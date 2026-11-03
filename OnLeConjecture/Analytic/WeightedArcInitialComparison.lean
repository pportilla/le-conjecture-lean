/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ScalarTwoWeightRadialExpansion
public import OnLeConjecture.Analytic.OneVariablePowerComparison
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Comparing a weighted initial polynomial on two analytic arcs

An exact coordinate-power unit expression for the difference along two
weighted arcs bounds the weighted order. It determines the initial
polynomial difference when the orders agree, and forces that difference
to vanish when the polynomial order is smaller.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

@[expose] noncomputable def weightedSourceArc
    (a b p : ℕ) (A B : ℂ → ℂ) (q : Source 1) : Source 2 :=
  twoWeightRadialSourceVector a b (q 0 ^ p, (A (q 0), B (q 0)))

/-- Comparison with an exact radial unit order, without an assumption on
the initial polynomial difference. -/
theorem weightedArc_initial_polynomial_comparison
    (a b p d E : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![a, b] d)
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (htail : ofFunction F hF - coordinatePolynomialAlgHom 2 P ∈
      twoWeightOrderIdeal a b (d + 1))
    (A₁ B₁ A₂ B₂ : ℂ → ℂ)
    (hA₁ : AnalyticAt ℂ A₁ 0) (hB₁ : AnalyticAt ℂ B₁ 0)
    (hA₂ : AnalyticAt ℂ A₂ 0) (hB₂ : AnalyticAt ℂ B₂ 0)
    (U : Source 1 → ℂ) (hU : AnalyticAt ℂ U 0) (hU0 : U 0 ≠ 0)
    (hunit : ∀ᶠ q in 𝓝 (0 : Source 1),
      F (weightedSourceArc a b p A₁ B₁ q) - F (weightedSourceArc a b p A₂ B₂ q) =
        q 0 ^ (p * E) * U q) :
    d ≤ E ∧
      (d < E → MvPolynomial.eval (![A₁ 0, B₁ 0]) P -
        MvPolynomial.eval (![A₂ 0, B₂ 0]) P = 0) ∧
      (d = E → MvPolynomial.eval (![A₁ 0, B₁ 0]) P -
        MvPolynomial.eval (![A₂ 0, B₂ 0]) P = U 0) := by
  obtain ⟨R, hR⟩ := exists_scalar_twoWeight_radial_remainder a b d ha hb P hP F hF htail
  have ht : AnalyticAt ℂ (fun q : Source 1 => q 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0
  have hscalar (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) :
      AnalyticAt ℂ (fun q : Source 1 => A (q 0)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 1)) _ ht
    exact hA
  let C₁ := fun q : Source 1 => (q 0 ^ p, (A₁ (q 0), B₁ (q 0)))
  let C₂ := fun q : Source 1 => (q 0 ^ p, (A₂ (q 0), B₂ (q 0)))
  have hC₁ : AnalyticAt ℂ C₁ 0 :=
    (ht.pow p).prod ((hscalar A₁ hA₁).prod (hscalar B₁ hB₁))
  have hC₂ : AnalyticAt ℂ C₂ 0 :=
    (ht.pow p).prod ((hscalar A₂ hA₂).prod (hscalar B₂ hB₂))
  have hC₁0 : C₁ 0 = (0, (A₁ 0, B₁ 0)) := by simp [C₁, zero_pow hp.ne']
  have hC₂0 : C₂ 0 = (0, (A₂ 0, B₂ 0)) := by simp [C₂, zero_pow hp.ne']
  have hRC₁ : AnalyticAt ℂ (R ∘ C₁) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 1)) _ hC₁
    rw [hC₁0]
    exact (hR _).1
  have hRC₂ : AnalyticAt ℂ (R ∘ C₂) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 1)) _ hC₂
    rw [hC₂0]
    exact (hR _).1
  have hpoly (A B : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) :
      AnalyticAt ℂ (fun q : Source 1 => MvPolynomial.eval (![A (q 0), B (q 0)]) P) 0 := by
    have hv (i : Fin 2) : AnalyticAt ℂ
        (fun q : Source 1 => (![A (q 0), B (q 0)] : Source 2) i) 0 := by
      fin_cases i
      · exact hscalar A hA
      · exact hscalar B hB
    simpa [MvPolynomial.aeval_def] using AnalyticAt.aeval_mvPolynomial hv P
  let W := fun q : Source 1 =>
    MvPolynomial.eval (![A₁ (q 0), B₁ (q 0)]) P -
      MvPolynomial.eval (![A₂ (q 0), B₂ (q 0)]) P +
        q 0 ^ p * (R (C₁ q) - R (C₂ q))
  have hW : AnalyticAt ℂ W 0 :=
    ((hpoly A₁ B₁ hA₁ hB₁).sub (hpoly A₂ B₂ hA₂ hB₂)).add
      ((ht.pow p).mul (hRC₁.sub hRC₂))
  have hW0 : W 0 = MvPolynomial.eval (![A₁ 0, B₁ 0]) P -
      MvPolynomial.eval (![A₂ 0, B₂ 0]) P := by simp [W, zero_pow hp.ne']
  have hT₁ : Tendsto C₁ (𝓝 0) (𝓝 (0, (A₁ 0, B₁ 0))) := by
    simpa only [ContinuousAt, hC₁0] using hC₁.continuousAt
  have hT₂ : Tendsto C₂ (𝓝 0) (𝓝 (0, (A₂ 0, B₂ 0))) := by
    simpa only [ContinuousAt, hC₂0] using hC₂.continuousAt
  have heq : coordinate (0 : Fin 1) ^ (p * d) * ofFunction W hW =
      coordinate (0 : Fin 1) ^ (p * E) * ofFunction U hU := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hT₁.eventually (hR _).2, hT₂.eventually (hR _).2, hunit]
      with q h1 h2 hq
    change q 0 ^ (p * d) * W q = q 0 ^ (p * E) * U q
    rw [← hq]
    change _ = F (twoWeightRadialSourceVector a b (C₁ q)) -
      F (twoWeightRadialSourceVector a b (C₂ q))
    rw [h1, h2]
    simp only [C₁, C₂, W, ← pow_mul]
    have he (A B : ℂ) : (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm (A, B) =
        (![A, B] : Source 2) := by ext i; fin_cases i <;> rfl
    rw [he, he]
    ring
  have hu : IsUnit (ofFunction U hU) := isUnit_of_valueRingHom_ne_zero hU0
  have hdegrees := (coordinate_pow_comparison_with_unit (p * d) (p * E)
    (ofFunction W hW) (ofFunction U hU) hu heq).1
  refine ⟨by nlinarith, ?_, ?_⟩
  · intro hlt
    have h := value_eq_zero_of_strict_coordinate_pow_comparison (p * d) (p * E)
      (Nat.mul_lt_mul_of_pos_left hlt hp) (ofFunction W hW) (ofFunction U hU) hu heq
    simpa only [valueRingHom_ofFunction, hW0] using h
  · intro hsame
    subst E
    have h := value_eq_of_equal_coordinate_pow_comparison (p * d)
      (ofFunction W hW) (ofFunction U hU) heq
    simpa only [valueRingHom_ofFunction, hW0] using h

end OnLeConjecture.Analytic
