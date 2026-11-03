/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightPolynomialComposition

/-!
# Elimination outside the initial-pair algebra for two source weights

Finite analytic elimination and polynomial homogeneous lifting produce
a nonzero initial form outside the algebra of the two initial components.
All filtrations are the actual finite monomial ideals of analytic germs.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- A germ outside the analytic image of a finite plane pair admits an
analytic correction whose nonzero initial form lies outside the polynomial
algebra of the component initial forms, for any two positive source weights.
-/
theorem exists_twoWeight_initial_form_outside_pair_algebra
    (f : PointedMapGerm 2 2) (hfinite : f.IsFiniteAtOrigin)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (w : Fin 2 → ℕ)
    (G : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (hG : ∀ i, (G i).IsWeightedHomogeneous ![a, b] (w i))
    (htail : ∀ i, f.1.component i - Germ.coordinatePolynomialAlgHom 2 (G i) ∈
      Germ.twoWeightOrderIdeal a b (w i + 1))
    (H : Germ 2) (hnotimage : H ∉ f.ImageRing) :
    ∃ D : ℕ, ∃ Φ : Germ 2, ∃ R : MvPolynomial (Fin 2) ℂ,
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![a, b] D ∧
      H - f.pullbackRingHom Φ ∈ Germ.twoWeightOrderIdeal a b D ∧
      H - f.pullbackRingHom Φ - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal a b (D + 1) ∧
      R ∉ Set.range (MvPolynomial.aeval G :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
  rcases f.twoWeight_filtered_elimination hfinite a b ha H with hmem | hrem
  · exact (hnotimage hmem).elim
  · obtain ⟨D, Φ, horder, hterminal⟩ := hrem
    have hnext : H - f.pullbackRingHom Φ ∉ Germ.twoWeightOrderIdeal a b (D + 1) := by
      simpa only [map_zero, sub_zero] using hterminal 0
    obtain ⟨R, hRzero, hR, hRtail⟩ :=
      Germ.exists_nonzero_twoWeightHomogeneous_coordinatePolynomial_mod_succ
        a b D ha hb (H - f.pullbackRingHom Φ) horder hnext
    refine ⟨D, Φ, R, hRzero, hR, horder, hRtail, ?_⟩
    intro hbase
    obtain ⟨S, hS, hSR⟩ :=
      OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
        w ![a, b] G hG hR hbase
    have hsub := Germ.twoWeight_polynomial_expression_initial_form
      a b ha hb w (fun i => f.1.component i) G hG htail hS
    rw [hSR] at hsub
    have hpull : f.pullbackRingHom (Germ.coordinatePolynomialAlgHom 2 S) =
        MvPolynomial.aeval (fun i => f.1.component i) S := by
      rw [Germ.PointedMapGerm.pullback_coordinatePolynomialAlgHom]
      simp only [f.pullback_coordinate]
      rfl
    apply hterminal (Germ.coordinatePolynomialAlgHom 2 S)
    rw [hpull]
    have hdiff := (Germ.twoWeightOrderIdeal a b (D + 1)).sub_mem hRtail hsub
    convert hdiff using 1
    ring

end OnLeConjecture.Analytic.PointedMapGerm
