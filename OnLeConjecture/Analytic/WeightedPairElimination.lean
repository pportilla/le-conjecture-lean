/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedFilteredElimination
public import OnLeConjecture.Analytic.WeightedPolynomialComposition

/-!
# Elimination outside the algebra of the two initial forms

For a finite analytic plane pair, a third germ outside its analytic image
ring can be modified by an analytic expression in the pair so that its
nonzero weighted initial form is outside the polynomial algebra generated
by the two initial forms. Homogeneous lifting and analytic substitution
prove that polynomial algebra membership would improve the terminal
approximation, which is impossible.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- Finite analytic elimination produces the nonbase third initial form
used in the multiplicity-three argument. -/
theorem exists_initial_form_outside_pair_algebra
    (f : PointedMapGerm 2 2) (hfinite : f.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a) (w : Fin 2 → ℕ)
    (G : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (hG : ∀ i, (G i).IsWeightedHomogeneous ![a, 1] (w i))
    (htail : ∀ i, f.1.component i - Germ.coordinatePolynomialAlgHom 2 (G i) ∈
      Germ.weightedOrderIdeal a (w i + 1))
    (H : Germ 2) (hnotimage : H ∉ f.ImageRing) :
    ∃ D : ℕ, ∃ Φ : Germ 2, ∃ R : MvPolynomial (Fin 2) ℂ,
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![a, 1] D ∧
      H - f.pullbackRingHom Φ ∈ Germ.weightedOrderIdeal a D ∧
      H - f.pullbackRingHom Φ - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1) ∧
      R ∉ Set.range (MvPolynomial.aeval G :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
  rcases f.twoWeight_filtered_elimination hfinite a 1 ha H with hmem | hrem
  · exact (hnotimage hmem).elim
  · obtain ⟨D, Φ, horder, hterminal⟩ := hrem
    have hident (n : ℕ) := Germ.weightedOrderIdeal_eq_twoWeightOrderIdeal a n ha
    have horder' : H - f.pullbackRingHom Φ ∈ Germ.weightedOrderIdeal a D := by
      rwa [hident]
    have hnext : H - f.pullbackRingHom Φ ∉ Germ.weightedOrderIdeal a (D + 1) := by
      simpa only [hident, map_zero, sub_zero] using hterminal 0
    obtain ⟨R, hRzero, hR, hRtail⟩ :=
      Germ.exists_nonzero_weightedHomogeneous_coordinatePolynomial_mod_succ
        a D ha (H - f.pullbackRingHom Φ) horder' hnext
    refine ⟨D, Φ, R, hRzero, hR, horder', hRtail, ?_⟩
    intro hbase
    obtain ⟨S, hS, hSR⟩ :=
      OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
        w ![a, 1] G hG hR hbase
    have hsub := Germ.polynomial_expression_initial_form
      a ha w (fun i ↦ f.1.component i) G hG htail hS
    rw [hSR] at hsub
    have hpull : f.pullbackRingHom (Germ.coordinatePolynomialAlgHom 2 S) =
        MvPolynomial.aeval (fun i ↦ f.1.component i) S := by
      rw [Germ.PointedMapGerm.pullback_coordinatePolynomialAlgHom]
      simp only [f.pullback_coordinate]
      rfl
    apply hterminal (Germ.coordinatePolynomialAlgHom 2 S)
    rw [← hident, hpull]
    have hdiff := (Germ.weightedOrderIdeal a (D + 1)).sub_mem hRtail hsub
    convert hdiff using 1
    ring

end OnLeConjecture.Analytic.PointedMapGerm
