/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PreparedCyclicCollision
public import OnLeConjecture.Polynomial.CuspKernel
public import OnLeConjecture.Analytic.TwoWeightInitialFormFactor

/-!
# Elimination preserving the prepared third-coordinate ideal

Corrections are restricted to multiples of `Q²-Pᵖ` by analytic expressions
in `(P,Q)`. These corrections preserve `yᵏ` times the analytic maximal ideal.
Finite-module filtered elimination is applied to this smaller submodule.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- Finite weighted elimination restricted to multiples of one image-ring
element. The terminal remainder cannot be improved by another such multiple. -/
theorem twoWeight_multiple_filtered_elimination
    (f : PointedMapGerm 2 2) (hfinite : f.IsFiniteAtOrigin)
    (a b : ℕ) (ha : 0 < a) (r : Germ 2) (hr : r ∈ f.ImageRing)
    (H : Germ 2) (hH : H ∉ f.ImageRing) :
    ∃ D : ℕ, ∃ Φ : Germ 2,
      H - r * f.pullbackRingHom Φ ∈ Germ.twoWeightOrderIdeal a b D ∧
      ∀ Ψ : Germ 2, H - r * f.pullbackRingHom Φ - r * f.pullbackRingHom Ψ ∉
        Germ.twoWeightOrderIdeal a b (D + 1) := by
  let _ : Module.Finite f.ImageRing (Germ 2) := hfinite
  let S : Submodule f.ImageRing (Germ 2) := Submodule.span f.ImageRing {r}
  let F : ℕ → Submodule f.ImageRing (Germ 2) :=
    fun D => (Germ.twoWeightOrderIdeal a b D).restrictScalars f.ImageRing
  have hzero : F 0 = ⊤ := by simp [F, Germ.twoWeightOrderIdeal_zero]
  have hcofinal : ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ (IsLocalRing.maximalIdeal (Germ 2) ^ n).restrictScalars f.ImageRing := by
    intro n
    refine ⟨max a b * n, ?_⟩
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal (Germ 2) ^ n
    rw [← Germ.maximalIdeal_eq_isLocalRing]
    exact Germ.twoWeightOrderIdeal_le_maximalIdeal_pow a b n ha hx
  have hnot : H ∉ S := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    apply hH
    rw [← hc, Algebra.smul_def, Algebra.algebraMap_ofSubring]
    exact f.ImageRing.mul_mem c.2 hr
  rcases filtered_elimination S F hzero
      (cofinal_source_maximalIdeal_of_target F hcofinal) H with hmem | hrem
  · exact (hnot hmem).elim
  · obtain ⟨D, u, hu, horder, hterminal⟩ := hrem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨Φ, hΦ⟩ := f.pullbackToImageRing_surjective c
    have hu' : u = r * f.pullbackRingHom Φ := by
      rw [← hc, ← hΦ, Algebra.smul_def, Algebra.algebraMap_ofSubring]
      change f.pullbackRingHom Φ * r = r * f.pullbackRingHom Φ
      ring
    refine ⟨D, Φ, ?_, ?_⟩
    · simpa only [hu', F, Submodule.restrictScalars_mem] using horder
    · intro Ψ hΨ
      apply hterminal (r * f.pullbackRingHom Ψ)
      · change r * f.pullbackRingHom Ψ ∈ Submodule.span f.ImageRing {r}
        exact Submodule.mem_span_singleton.mpr ⟨f.pullbackToImageRing Ψ, by
          rw [Algebra.smul_def, Algebra.algebraMap_ofSubring]
          change f.pullbackRingHom Ψ * r = r * f.pullbackRingHom Ψ
          ring⟩
      · simpa only [hu', F, Submodule.restrictScalars_mem] using hΨ

end OnLeConjecture.Analytic.PointedMapGerm

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open scoped BigOperators

/-- The analytic cusp equation evaluated on the prepared pair. -/
@[expose] noncomputable def cyclicRelation (k p : ℕ) (β : Germ 2) : Germ 2 :=
  cyclicSecond k p β ^ 2 - cyclicFirst k ^ p

/-- Its explicit quotient by `yᵏ`. -/
@[expose] noncomputable def cyclicRelationQuotient (k p : ℕ) (β : Germ 2) : Germ 2 :=
  2 * Germ.coordinate 0 ^ p * β + Germ.coordinate 1 ^ k * β ^ 2 -
    ∑ i ∈ Finset.range p, cyclicFirst k ^ i * (Germ.coordinate 0 ^ 2) ^ (p - 1 - i)

/-- The cusp equation of the prepared pair is divisible by `yᵏ`. -/
theorem cyclicRelation_eq_coordinate_pow_mul (k p : ℕ) (β : Germ 2) :
    cyclicRelation k p β = Germ.coordinate 1 ^ k * cyclicRelationQuotient k p β := by
  have hgeom := geom_sum₂_mul (cyclicFirst k) (Germ.coordinate 0 ^ 2) p
  have hpower : (Germ.coordinate (0 : Fin 2) ^ 2) ^ p =
      (Germ.coordinate (0 : Fin 2) ^ p) ^ 2 := by simp [← pow_mul, mul_comm]
  simp only [cyclicFirst, add_sub_cancel_left, hpower] at hgeom
  dsimp only [cyclicRelation, cyclicRelationQuotient, cyclicSecond, cyclicFirst]
  linear_combination hgeom

/-- The quotient of the cusp equation vanishes at the origin. -/
theorem cyclicRelationQuotient_mem_maximalIdeal (k p : ℕ) (hk : 0 < k)
    (hp : 3 ≤ p) (β : Germ 2) : cyclicRelationQuotient k p β ∈ Germ.maximalIdeal 2 := by
  rw [Germ.mem_maximalIdeal_iff]
  simp only [cyclicRelationQuotient, map_sub, map_add, map_mul, map_pow,
    Germ.valueRingHom_coordinate, zero_pow hk.ne', zero_pow (show p ≠ 0 by omega),
    mul_zero, zero_mul, zero_add, map_sum]
  have hsum : ∑ i ∈ Finset.range p,
      Germ.valueRingHom 2 (cyclicFirst k ^ i * (Germ.coordinate 0 ^ 2) ^ (p - 1 - i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    by_cases hzero : i = 0
    · simp [hzero, show p - 1 ≠ 0 by omega]
    · simp [cyclicFirst, hk.ne', hzero]
  simpa only [map_mul, map_pow, Germ.valueRingHom_coordinate, zero_sub, neg_eq_zero] using hsum

/-- The evaluated cusp equation belongs to the analytic image of the pair. -/
theorem cyclicRelation_mem_imageRing (f : PointedMapGerm 2 2) (k p : ℕ) (β : Germ 2)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β) : cyclicRelation k p β ∈ f.ImageRing := by
  refine ⟨Germ.coordinatePolynomialAlgHom 2 (OnLeConjecture.Polynomial.cuspRelation p), ?_⟩
  change f.pullbackRingHom
    (Germ.coordinatePolynomialAlgHom 2 (OnLeConjecture.Polynomial.cuspRelation p)) = _
  simp only [OnLeConjecture.Polynomial.cuspRelation, map_sub, map_pow,
    Germ.coordinatePolynomialAlgHom_X, f.pullback_coordinate, hP, hQ, cyclicRelation]

private theorem cuspRelation_dvd_of_initial_secondVariable_dvd
    (k p : ℕ) (hk : 0 < k) (hodd : Odd p) (c : ℂ)
    (S : MvPolynomial (Fin 2) ℂ)
    (hdiv : MvPolynomial.X (1 : Fin 2) ^ k ∣
      MvPolynomial.aeval (cyclicInitialPair k p c) S) :
    OnLeConjecture.Polynomial.cuspRelation p ∣ S := by
  let ρ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] _root_.Polynomial ℂ :=
    MvPolynomial.aeval ![_root_.Polynomial.X, 0]
  have hcomp : ρ.comp (MvPolynomial.aeval (cyclicInitialPair k p c)) =
      OnLeConjecture.Polynomial.cuspParametrization p := by
    ext i
    fin_cases i <;> simp [ρ, cyclicInitialPair, OnLeConjecture.Polynomial.cuspParametrization,
      hk.ne']
  have hzero : ρ (MvPolynomial.aeval (cyclicInitialPair k p c) S) = 0 := by
    obtain ⟨C, hC⟩ := hdiv
    rw [hC, map_mul, map_pow]
    simp [ρ, hk.ne']
  apply (OnLeConjecture.Polynomial.cuspParametrization_eq_zero_iff p hodd S).mp
  simpa only [← hcomp, AlgHom.comp_apply] using hzero

/-- Restricted elimination retains the ideal `yᵏ𝔪` and ends with a
nonzero initial form outside the polynomial algebra of the prepared pair. -/
theorem cyclic_ideal_preserving_initial_remainder (f : PointedMapGerm 2 2)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hnot : Germ.coordinate (1 : Fin 2) ^ k * h ∉ f.ImageRing) :
    ∃ D : ℕ, ∃ Φ h' : Germ 2, ∃ R : MvPolynomial (Fin 2) ℂ,
      h' ∈ Germ.maximalIdeal 2 ∧ h' ≠ 0 ∧
      Germ.coordinate 1 ^ k * h - cyclicRelation k p β * f.pullbackRingHom Φ =
        Germ.coordinate 1 ^ k * h' ∧
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      Germ.coordinate 1 ^ k * h' ∈ Germ.twoWeightOrderIdeal k p D ∧
      Germ.coordinate 1 ^ k * h' - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      MvPolynomial.X (1 : Fin 2) ^ k ∣ R ∧
      R ∉ Set.range (MvPolynomial.aeval (cyclicInitialPair k p (Germ.valueRingHom 2 β)) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
  have hp' : 0 < p := by omega
  obtain ⟨D, Φ, horder, hterminal⟩ := f.twoWeight_multiple_filtered_elimination
    (cyclic_isFiniteAtOrigin f k p hp β hβ hP hQ) k p hk (cyclicRelation k p β)
    (cyclicRelation_mem_imageRing f k p β hP hQ) (Germ.coordinate 1 ^ k * h) hnot
  let h' : Germ 2 := h - cyclicRelationQuotient k p β * f.pullbackRingHom Φ
  have h'h : h' ∈ Germ.maximalIdeal 2 :=
    (Germ.maximalIdeal 2).sub_mem hh (Ideal.mul_mem_right _ _
      (cyclicRelationQuotient_mem_maximalIdeal k p hk hp β))
  have hremainder : Germ.coordinate 1 ^ k * h - cyclicRelation k p β * f.pullbackRingHom Φ =
      Germ.coordinate 1 ^ k * h' := by
    rw [cyclicRelation_eq_coordinate_pow_mul]
    dsimp only [h']
    ring
  rw [hremainder] at horder hterminal
  have hnext : Germ.coordinate 1 ^ k * h' ∉ Germ.twoWeightOrderIdeal k p (D + 1) := by
    simpa only [map_zero, mul_zero, sub_zero] using hterminal 0
  obtain ⟨R, hRne, hRhom, hRtail⟩ :=
    Germ.exists_nonzero_twoWeightHomogeneous_coordinatePolynomial_mod_succ
      k p D hk hp' (Germ.coordinate 1 ^ k * h') horder hnext
  have hRdiv := Germ.secondVariable_pow_dvd_of_dvd_twoWeight_initial_form
    k p D k hk hp' (Germ.coordinate 1 ^ k * h') R hRhom hRtail (dvd_mul_right _ _)
  refine ⟨D, Φ, h', R, h'h, ?_, hremainder, hRne, hRhom, horder, hRtail, hRdiv, ?_⟩
  · intro hzero
    apply hnext
    simp [hzero]
  · intro hbase
    obtain ⟨S, hShom, hSR⟩ :=
      OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
        ![2 * k, p * k] ![k, p] (cyclicInitialPair k p (Germ.valueRingHom 2 β))
        (cyclicInitialPair_homogeneous k p _) hRhom hbase
    obtain ⟨C, hC⟩ := cuspRelation_dvd_of_initial_secondVariable_dvd
      k p hk hodd (Germ.valueRingHom 2 β) S (by rwa [hSR])
    have hStail := Germ.twoWeight_polynomial_expression_initial_form
      k p hk hp' ![2 * k, p * k] (fun i => f.1.component i)
      (cyclicInitialPair k p (Germ.valueRingHom 2 β))
      (cyclicInitialPair_homogeneous k p _) (cyclic_pair_strict_tails f k p hk hp β hP hQ) hShom
    rw [hSR] at hStail
    have hpull : f.pullbackRingHom (Germ.coordinatePolynomialAlgHom 2 S) =
        MvPolynomial.aeval (fun i => f.1.component i) S := by
      rw [Germ.PointedMapGerm.pullback_coordinatePolynomialAlgHom]
      simp only [f.pullback_coordinate]
      rfl
    rw [← hpull, hC, map_mul, map_mul] at hStail
    have hpullRel : f.pullbackRingHom
        (Germ.coordinatePolynomialAlgHom 2 (OnLeConjecture.Polynomial.cuspRelation p)) =
          cyclicRelation k p β := by
      simp only [OnLeConjecture.Polynomial.cuspRelation, map_sub, map_pow,
        Germ.coordinatePolynomialAlgHom_X, f.pullback_coordinate, hP, hQ, cyclicRelation]
    rw [hpullRel] at hStail
    apply hterminal (Germ.coordinatePolynomialAlgHom 2 C)
    have hdiff := (Germ.twoWeightOrderIdeal k p (D + 1)).sub_mem hRtail hStail
    convert hdiff using 1
    ring

/-- For an injective prepared triple whose third component lies in `yᵏ𝔪`,
an analytic pointed target subtraction retains this ideal and produces a
nonzero initial form outside the initial-pair algebra. -/
theorem cyclic_injective_triple_ideal_preserving_initial_remainder
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hH : g.1.component 2 = Germ.coordinate 1 ^ k * h) :
    ∃ D : ℕ, ∃ Ψ h' : Germ 2, ∃ R : MvPolynomial (Fin 2) ℂ,
      Ψ ∈ Germ.maximalIdeal 2 ∧ h' ∈ Germ.maximalIdeal 2 ∧ h' ≠ 0 ∧
      g.1.component 2 - g.firstTwo.pullbackRingHom Ψ = Germ.coordinate 1 ^ k * h' ∧
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      Germ.coordinate 1 ^ k * h' ∈ Germ.twoWeightOrderIdeal k p D ∧
      Germ.coordinate 1 ^ k * h' - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      MvPolynomial.X (1 : Fin 2) ^ k ∣ R ∧
      R ∉ Set.range (MvPolynomial.aeval (cyclicInitialPair k p (Germ.valueRingHom 2 β)) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
  have hnot := cyclic_third_not_mem_imageRing g hg k p hk hp hodd β hβ hP hQ
  rw [hH] at hnot
  obtain ⟨D, Φ, h', R, h'max, h'ne, heq, hRne, hRhom, horder, htail, hdiv, hbase⟩ :=
    cyclic_ideal_preserving_initial_remainder g.firstTwo k p hk hp hodd β hβ
      (by simpa using hP) (by simpa using hQ) h hh hnot
  let targetRelation :=
    Germ.coordinatePolynomialAlgHom 2 (OnLeConjecture.Polynomial.cuspRelation p)
  have htmax : targetRelation ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp [targetRelation, OnLeConjecture.Polynomial.cuspRelation, show p ≠ 0 by omega]
  have hpull : g.firstTwo.pullbackRingHom targetRelation = cyclicRelation k p β := by
    simp only [targetRelation, OnLeConjecture.Polynomial.cuspRelation, map_sub, map_pow,
      Germ.coordinatePolynomialAlgHom_X, PointedMapGerm.pullback_coordinate]
    simp only [PointedMapGerm.firstTwo_component]
    change g.1.component 1 ^ 2 - g.1.component 0 ^ p = _
    rw [hP, hQ]
    rfl
  refine ⟨D, targetRelation * Φ, h', R, Ideal.mul_mem_right _ _ htmax,
    h'max, h'ne, ?_, hRne, hRhom, horder, htail, hdiv, hbase⟩
  simpa only [hH, map_mul, hpull] using heq

end OnLeConjecture.DTwo
