/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointedWeightedSubtraction
public import OnLeConjecture.Analytic.DiagonalCoordinates

/-!
# Replacing a third initial form modulo the initial-pair algebra

A homogeneous polynomial in the first two initial forms lifts to an
analytic target subtraction. A nonzero constant factor is removed by a
diagonal target equivalence. Both first components remain unchanged.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

open OnLeConjecture.Analytic.Germ

theorem exists_weighted_third_initial_replacement
    (g : PointedMapGerm 2 3)
    (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (w : Fin 2 → ℕ) (Q : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (hQ : ∀ i, (Q i).IsWeightedHomogeneous ![a, b] (w i))
    (hpair : ∀ i, g.firstTwo.1.component i - coordinatePolynomialAlgHom 2 (Q i) ∈
      twoWeightOrderIdeal a b (w i + 1))
    (P H : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, b] d)
    (hH : H.IsWeightedHomogeneous ![a, b] d)
    (c : ℂ) (hc : c ≠ 0)
    (hthird : g.1.component 2 - coordinatePolynomialAlgHom 2 P ∈
      twoWeightOrderIdeal a b (d + 1))
    (hquotient : P - MvPolynomial.C c * H ∈ Set.range (MvPolynomial.aeval Q :
      MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ)) :
    ∃ g' : PointedMapGerm 2 3, g.RightLeftEquivalent g' ∧
      g'.1.component 0 = g.1.component 0 ∧
      g'.1.component 1 = g.1.component 1 ∧
      g'.1.component 2 - coordinatePolynomialAlgHom 2 H ∈
        twoWeightOrderIdeal a b (d + 1) := by
  obtain ⟨R, hR, hReq⟩ := OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
    w ![a, b] Q hQ (hP.sub (hH.C_mul c)) hquotient
  let Ψ := coordinatePolynomialAlgHom 2 R
  have hpull : g.firstTwo.pullbackRingHom Ψ =
      MvPolynomial.aeval (fun i => g.firstTwo.1.component i) R := by
    rw [Germ.PointedMapGerm.pullback_coordinatePolynomialAlgHom]
    simp only [PointedMapGerm.pullback_coordinate]
    rfl
  have hsub := twoWeight_polynomial_expression_initial_form
    a b ha hb w (fun i => g.firstTwo.1.component i) Q hQ hpair hR
  rw [hReq, ← hpull] at hsub
  have htail : g.1.component 2 - g.firstTwo.pullbackRingHom Ψ -
      coordinatePolynomialAlgHom 2 (MvPolynomial.C c * H) ∈
        twoWeightOrderIdeal a b (d + 1) := by
    have h := (twoWeightOrderIdeal a b (d + 1)).sub_mem hthird hsub
    convert h using 1
    rw [map_sub]
    ring
  have hΨ := target_correction_mem_maximalIdeal_of_twoWeight_tail g.firstTwo
    (g.1.component 2) Ψ (g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal 2))
    a b d ha hb hd (MvPolynomial.C c * H) (hH.C_mul c) htail
  obtain ⟨f, hequiv, hf0, hf1, hf2⟩ := g.exists_target_subtraction Ψ hΨ
  have htailf : f.1.component 2 - coordinatePolynomialAlgHom 2 (MvPolynomial.C c * H) ∈
      twoWeightOrderIdeal a b (d + 1) := by rwa [hf2]
  let scales : Fin 3 → ℂ := ![1, 1, c⁻¹]
  have hscales : ∀ i, scales i ≠ 0 := by
    intro i
    fin_cases i
    · exact one_ne_zero
    · exact one_ne_zero
    · exact inv_ne_zero hc
  let e := diagonalPointedEquiv scales hscales
  let g' := e.forward.comp f
  have hequiv' : f.RightLeftEquivalent g' := by
    refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, comp_identity]
  have hcomponent (i : Fin 3) : g'.1.component i = constRingHom 2 (scales i) * f.1.component i := by
    rw [component_comp_eq_pullback, diagonalPointedEquiv_component, map_mul,
      pullback_constRingHom, pullback_coordinate]
  refine ⟨g', hequiv.trans hequiv', ?_, ?_, ?_⟩
  · rw [hcomponent, show scales 0 = 1 from rfl, map_one, one_mul, hf0]
  · rw [hcomponent, show scales 1 = 1 from rfl, map_one, one_mul, hf1]
  · have h := (twoWeightOrderIdeal a b (d + 1)).mul_mem_left (constRingHom 2 c⁻¹) htailf
    have hinverse : constRingHom 2 c⁻¹ * constRingHom 2 c = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    convert h using 1
    rw [hcomponent, show scales 2 = c⁻¹ from rfl, map_mul, coordinatePolynomialAlgHom_C]
    linear_combination coordinatePolynomialAlgHom 2 H * hinverse

end OnLeConjecture.Analytic.PointedMapGerm
