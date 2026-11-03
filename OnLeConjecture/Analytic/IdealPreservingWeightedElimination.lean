/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedPairElimination
public import OnLeConjecture.Analytic.WeightedInitialFormFactor

/-!
# Weighted elimination preserving a coordinate ideal

The finite-module argument applies to the intersection of the image ring
with any analytic ideal. When the two coordinates agree with their
polynomial initial forms modulo a coordinate power, the terminal remainder
has its initial form outside the polynomial algebra of the pair.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- Restrict analytic corrections to the prescribed ideal. -/
theorem weighted_ideal_filtered_elimination
    (f : PointedMapGerm 2 2) (hfinite : f.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a) (J : Ideal (Germ 2))
    (H : Germ 2) (hnot : H ∉ f.ImageRing) :
    ∃ D : ℕ, ∃ Φ : Germ 2,
      f.pullbackRingHom Φ ∈ J ∧
      H - f.pullbackRingHom Φ ∈ Germ.weightedOrderIdeal a D ∧
      ∀ Ψ : Germ 2, f.pullbackRingHom Ψ ∈ J →
        H - f.pullbackRingHom Φ - f.pullbackRingHom Ψ ∉
          Germ.weightedOrderIdeal a (D + 1) := by
  let _ : Module.Finite f.ImageRing (Germ 2) := hfinite
  let S : Submodule f.ImageRing (Germ 2) :=
    { carrier := {x | x ∈ f.ImageRing ∧ x ∈ J}
      zero_mem' := ⟨f.ImageRing.zero_mem, J.zero_mem⟩
      add_mem' := fun hx hy => ⟨f.ImageRing.add_mem hx.1 hy.1, J.add_mem hx.2 hy.2⟩
      smul_mem' := by
        intro c x hx
        change (c : Germ 2) * x ∈ f.ImageRing ∧ (c : Germ 2) * x ∈ J
        exact ⟨f.ImageRing.mul_mem c.2 hx.1, J.mul_mem_left _ hx.2⟩ }
  let F : ℕ → Submodule f.ImageRing (Germ 2) :=
    fun D => (Germ.twoWeightOrderIdeal a 1 D).restrictScalars f.ImageRing
  have hzero : F 0 = ⊤ := by simp [F, Germ.twoWeightOrderIdeal_zero]
  have hcofinal : ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ (IsLocalRing.maximalIdeal (Germ 2) ^ n).restrictScalars f.ImageRing := by
    intro n
    refine ⟨max a 1 * n, ?_⟩
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal (Germ 2) ^ n
    rw [← Germ.maximalIdeal_eq_isLocalRing]
    exact Germ.twoWeightOrderIdeal_le_maximalIdeal_pow a 1 n ha hx
  rcases filtered_elimination S F hzero
      (cofinal_source_maximalIdeal_of_target F hcofinal) H with hmem | hrem
  · exact (hnot hmem.1).elim
  · obtain ⟨D, u, hu, horder, hterminal⟩ := hrem
    obtain ⟨Φ, hΦ⟩ := hu.1
    refine ⟨D, Φ, ?_, ?_, ?_⟩
    · simpa only [hΦ] using hu.2
    · simpa only [hΦ, F, Submodule.restrictScalars_mem,
        Germ.weightedOrderIdeal_eq_twoWeightOrderIdeal a D ha]
        using horder
    · intro Ψ hΨ hnext
      apply hterminal (f.pullbackRingHom Ψ) ⟨⟨Ψ, rfl⟩, hΨ⟩
      simpa only [hΦ, F, Submodule.restrictScalars_mem,
        Germ.weightedOrderIdeal_eq_twoWeightOrderIdeal a (D + 1) ha]
        using hnext

end OnLeConjecture.Analytic.PointedMapGerm

namespace OnLeConjecture.Analytic.Germ

/-- Polynomial evaluation preserves congruence modulo any analytic ideal. -/
theorem polynomial_aeval_sub_mem_ideal
    {n : ℕ} (J : Ideal (Germ n)) (u v : Fin 2 → Germ n)
    (h : ∀ i, u i - v i ∈ J) (S : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval u S - MvPolynomial.aeval v S ∈ J := by
  let q := Ideal.Quotient.mkₐ ℂ J
  have heq : q.comp (MvPolynomial.aeval u) = q.comp (MvPolynomial.aeval v) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change (Ideal.Quotient.mk J) (u i) = (Ideal.Quotient.mk J) (v i)
    exact Ideal.Quotient.eq.mpr (h i)
  exact Ideal.Quotient.eq.mp (congrArg (fun e => e S) heq)

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- If the prepared coordinates agree with their initial polynomials
modulo `yᴺ`, finite elimination preserves `yᴺ` and escapes the pair algebra. -/
theorem exists_ideal_preserving_initial_form_outside_pair_algebra
    (f : PointedMapGerm 2 2) (hfinite : f.IsFiniteAtOrigin)
    (a N : ℕ) (ha : 0 < a) (w : Fin 2 → ℕ)
    (G : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (hG : ∀ i, (G i).IsWeightedHomogeneous ![a, 1] (w i))
    (htail : ∀ i, f.1.component i - Germ.coordinatePolynomialAlgHom 2 (G i) ∈
      Germ.weightedOrderIdeal a (w i + 1))
    (hmod : ∀ i, Germ.coordinate (1 : Fin 2) ^ N ∣
      f.1.component i - Germ.coordinatePolynomialAlgHom 2 (G i))
    (H : Germ 2) (hH : Germ.coordinate (1 : Fin 2) ^ N ∣ H)
    (hnot : H ∉ f.ImageRing) :
    ∃ D : ℕ, ∃ Φ : Germ 2, ∃ R : MvPolynomial (Fin 2) ℂ,
      Germ.coordinate (1 : Fin 2) ^ N ∣ f.pullbackRingHom Φ ∧
      Germ.coordinate (1 : Fin 2) ^ N ∣ H - f.pullbackRingHom Φ ∧
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![a, 1] D ∧
      H - f.pullbackRingHom Φ ∈ Germ.weightedOrderIdeal a D ∧
      H - f.pullbackRingHom Φ - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1) ∧
      MvPolynomial.X (1 : Fin 2) ^ N ∣ R ∧
      R ∉ Set.range (MvPolynomial.aeval G :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
  let J : Ideal (Germ 2) := Ideal.span {Germ.coordinate (1 : Fin 2) ^ N}
  obtain ⟨D, Φ, hΦ, horder, hterminal⟩ :=
    f.weighted_ideal_filtered_elimination hfinite a ha J H hnot
  have hΦdiv : Germ.coordinate (1 : Fin 2) ^ N ∣ f.pullbackRingHom Φ :=
    Ideal.mem_span_singleton.mp hΦ
  have hremdiv := dvd_sub hH hΦdiv
  have hnext : H - f.pullbackRingHom Φ ∉ Germ.weightedOrderIdeal a (D + 1) := by
    simpa only [map_zero, sub_zero] using hterminal 0 (by rw [map_zero]; exact J.zero_mem)
  obtain ⟨R, hRne, hRhom, hRtail⟩ :=
    Germ.exists_nonzero_weightedHomogeneous_coordinatePolynomial_mod_succ
      a D ha (H - f.pullbackRingHom Φ) horder hnext
  have hRdiv := Germ.secondVariable_pow_dvd_of_dvd_weighted_initial_form
    a D N (H - f.pullbackRingHom Φ) R hRhom hRtail hremdiv
  refine ⟨D, Φ, R, hΦdiv, hremdiv, hRne, hRhom, horder, hRtail, hRdiv, ?_⟩
  intro hbase
  obtain ⟨S, hShom, hSR⟩ :=
    OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
      w ![a, 1] G hG hRhom hbase
  have hpull : f.pullbackRingHom (Germ.coordinatePolynomialAlgHom 2 S) =
      MvPolynomial.aeval (fun i => f.1.component i) S := by
    rw [Germ.PointedMapGerm.pullback_coordinatePolynomialAlgHom]
    simp only [f.pullback_coordinate]
    rfl
  have hGsub : MvPolynomial.aeval (fun i => Germ.coordinatePolynomialAlgHom 2 (G i)) S =
      Germ.coordinatePolynomialAlgHom 2 R := by
    rw [← hSR]
    have heq : (Germ.coordinatePolynomialAlgHom 2).comp (MvPolynomial.aeval G) =
        MvPolynomial.aeval (fun i => Germ.coordinatePolynomialAlgHom 2 (G i)) := by
      ext i
      simp
    exact (congrArg (fun e => e S) heq).symm
  have hmodS := Germ.polynomial_aeval_sub_mem_ideal J
    (fun i => f.1.component i) (fun i => Germ.coordinatePolynomialAlgHom 2 (G i))
    (fun i => Ideal.mem_span_singleton.mpr (hmod i)) S
  rw [hGsub, ← hpull] at hmodS
  have hRmem : Germ.coordinatePolynomialAlgHom 2 R ∈ J := by
    apply Ideal.mem_span_singleton.mpr
    simpa only [map_pow, Germ.coordinatePolynomialAlgHom_X] using
      map_dvd (Germ.coordinatePolynomialAlgHom 2) hRdiv
  have hSmem : f.pullbackRingHom (Germ.coordinatePolynomialAlgHom 2 S) ∈ J := by
    simpa only [sub_add_cancel] using J.add_mem hmodS hRmem
  have hStail := Germ.polynomial_expression_initial_form
    a ha w (fun i => f.1.component i) G hG htail hShom
  rw [hSR, ← hpull] at hStail
  apply hterminal (Germ.coordinatePolynomialAlgHom 2 S) hSmem
  convert (Germ.weightedOrderIdeal a (D + 1)).sub_mem hRtail hStail using 1
  ring

end OnLeConjecture.Analytic.PointedMapGerm
