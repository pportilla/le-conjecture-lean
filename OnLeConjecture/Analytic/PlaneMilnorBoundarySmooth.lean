/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreBoundary
public import OnLeConjecture.DifferentialTopology.SmoothEvolution

/-!
# Smooth isotopy of the Milnor fibre boundary

The cutoff field used in `PlaneMilnorFibreBoundary` is smooth on its support:
analyticity makes its reciprocal kernel pairing smooth wherever the pairing
is nonzero. Its global evolution and reverse evolution therefore form a
native smooth diffeotopy of the Euclidean ambient space. The norm and level
identities for this same field prove the exact boundary-image statement.

This module does not identify the induced orientation of the fibre boundary
with the orientation of a parametrized branch link.
-/

@[expose] public noncomputable section

open Filter Metric Set Function Manifold
open scoped Topology ContDiff NNReal ComplexConjugate Manifold

namespace OnLeConjecture.DifferentialTopology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The smooth global evolution and its reverse form an ambient diffeotopy. -/
def timeDependentEvolutionDiffeotopy (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
    (hs : ContDiff ℝ ∞ (Function.uncurry X)) :
    TauCeti.Diffeotopy 𝓘(ℝ, E) ∞ E := by
  have hf : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : unitInterval × E => TauCeti.timeDependentFlow X hX 0 p.1 p.2) := by
    have harg : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, (ℝ × ℝ) × E) ∞
        (fun p : unitInterval × E => (((0 : ℝ), (p.1 : ℝ)), p.2)) :=
      (contMDiff_const.prodMk_space
        (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).prodMk_space contMDiff_snd
    exact (contDiff_timeDependentEvolution X hX hs).contMDiff.comp harg
  have hi : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : unitInterval × E => TauCeti.timeDependentFlow X hX p.1 0 p.2) := by
    have harg : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, (ℝ × ℝ) × E) ∞
        (fun p : unitInterval × E => (((p.1 : ℝ), (0 : ℝ)), p.2)) :=
      ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk_space
        contMDiff_const).prodMk_space contMDiff_snd
    exact (contDiff_timeDependentEvolution X hX hs).contMDiff.comp harg
  exact
    { toDiffeomorph :=
        { toEquiv :=
            { toFun := fun p => (p.1, TauCeti.timeDependentFlow X hX 0 p.1 p.2)
              invFun := fun p => (p.1, TauCeti.timeDependentFlow X hX p.1 0 p.2)
              left_inv := by
                intro p
                refine Prod.ext (by rfl) ?_
                exact (TauCeti.timeDependentFlow_trans X hX 0 p.1 0 p.2).trans
                  (TauCeti.timeDependentFlow_self X hX 0 p.2)
              right_inv := by
                intro p
                refine Prod.ext (by rfl) ?_
                exact (TauCeti.timeDependentFlow_trans X hX p.1 0 p.1 p.2).trans
                  (TauCeti.timeDependentFlow_self X hX p.1 p.2) }
          contMDiff_toFun := contMDiff_fst.prodMk hf
          contMDiff_invFun := contMDiff_fst.prodMk hi }
      fst_apply := fun _ => rfl
      snd_apply_zero' := fun x => TauCeti.timeDependentFlow_self X hX 0 x }

@[simp] theorem timeDependentEvolutionDiffeotopy_apply (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
    (hs : ContDiff ℝ ∞ (Function.uncurry X)) (t : unitInterval) (x : E) :
    timeDependentEvolutionDiffeotopy X hX hs (t, x) =
      TauCeti.timeDependentFlow X hX 0 t x := rfl

end Normed
end OnLeConjecture.DifferentialTopology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Analyticity and radial transversality yield a native smooth ambient diffeotopy
preserving every sphere and carrying the zero boundary onto the level boundary. -/
theorem milnorFibreBoundary_diffeotopy_with_level_of_transverse (H : Source 2 → ℂ) {ε c : ℝ}
    (han : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ ≤ ε → AnalyticAt ℂ (euclideanEquation H) z)
    (htr : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ = ε → ‖euclideanEquation H z‖ < c →
      Surjective (fderiv ℝ (radialPair H) z))
    (s : ℂ) (hs : ‖s‖ < c) :
    ∃ Φ : TauCeti.Diffeotopy 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
        (EuclideanSpace ℂ (Fin 2)),
      (∀ t x, ‖Φ (t, x)‖ = ‖x‖) ∧
      (∀ t : unitInterval, ∀ x ∈ milnorFibreBoundary H ε 0,
        euclideanEquation H (Φ (t, x)) = (t : ℝ) • s) ∧
      Φ.final '' milnorFibreBoundary H ε 0 = milnorFibreBoundary H ε s := by
  set E := euclideanEquation H with hEdef
  let U : Set (EuclideanSpace ℂ (Fin 2)) :=
    {z | AnalyticAt ℂ E z} ∩ euclideanKernelPairing E ⁻¹' {0}ᶜ
  have hUo : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_analyticAt ℂ E) isOpen_compl_singleton
    intro z hz
    exact (contDiffAt_euclideanKernelPairing (n := 0) hz).continuousAt.continuousWithinAt
  let K : Set (EuclideanSpace ℂ (Fin 2)) := sphere 0 ε ∩ E ⁻¹' closedBall 0 ‖s‖
  have hKc : IsCompact K := by
    have hEc : ContinuousOn E (sphere 0 ε) := fun z hz =>
      (han z (mem_sphere_zero_iff_norm.mp hz).le).continuousAt.continuousWithinAt
    exact (isCompact_sphere 0 ε).of_isClosed_subset
      (hEc.preimage_isClosed_of_isClosed isClosed_sphere isClosed_closedBall) inter_subset_left
  have hKU : K ⊆ U := by
    rintro z ⟨hzε, hzs⟩
    have hzε' : ‖z‖ = ε := mem_sphere_zero_iff_norm.mp hzε
    have hzs' : ‖E z‖ ≤ ‖s‖ := mem_closedBall_zero_iff.mp hzs
    exact ⟨han z hzε'.le, euclideanKernelPairing_ne_zero (han z hzε'.le).differentiableAt
      (htr z hzε' (hzs'.trans_lt hs))⟩
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχK⟩ := exists_contDiff_cutoff hKc hUo hKU
  let V : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
    fun z => χ z • s • euclideanLevelField E z
  have hV : ContDiff ℝ ∞ V :=
    contDiff_smul_of_tsupport hχ
      (fun z hz => (contDiffAt_euclideanLevelField (hχU hz).1 (hχU hz).2).const_smul s)
  have hVc : HasCompactSupport V := hχc.smul_right
  obtain ⟨C, hC⟩ := exists_lipschitz_autonomousSuspension (contDiff_infty.mp hV 1) hVc
  let φ : ℝ → ℝ → EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
    fun r t x => TauCeti.timeDependentFlow (fun _ => V) hC r t x
  -- the field is tangent to every sphere around the origin
  have htan : ∀ (t : ℝ) x, inner ℝ x ((fun _ : ℝ => V) t x) = 0 := by
    intro t x
    simp only [V]
    rw [real_inner_smul_right, real_inner_euclidean, inner_smul_right,
      inner_euclideanLevelField, mul_zero, Complex.zero_re, mul_zero]
  have hnorm : ∀ r t x, ‖φ r t x‖ = ‖x‖ := fun r t x =>
    DifferentialTopology.norm_timeDependentEvolution (fun _ => V) hC htan r t x
  -- the equation changes at rate `χ • s`
  have hlevel : ∀ r t x, E (φ r t x) = E x + (∫ u in r..t, χ (φ r u x)) • s := by
    refine apply_timeDependentFlow_autonomous_eq_add_integral hC E hχ.continuous s
      (fun z hz => by simp [V, hz]) (fun z hz => ?_)
    have hzU := hχU (subset_tsupport _ hz)
    refine ⟨(fderiv ℂ E z).restrictScalars ℝ,
      hzU.1.differentiableAt.hasFDerivAt.restrictScalars ℝ, ?_⟩
    simp [V, fderiv_euclideanLevelField hzU.2]
  have hcont : ∀ r x, Continuous fun u => χ (φ r u x) := fun r x =>
    hχ.continuous.comp ((TauCeti.continuous_timeDependentFlow _ hC).comp
      (by fun_prop : Continuous fun u : ℝ => ((r, u), x)))
  have hone : ∀ r x, (∀ u ∈ Icc (0 : ℝ) 1, φ r u x ∈ K) →
      ∫ u in (0 : ℝ)..1, χ (φ r u x) = 1 := by
    intro r x hK
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun u hu =>
      hχK _ (hK u (by rwa [uIcc_of_le zero_le_one] at hu))]
    simp
  have hlevel_trace : ∀ t : unitInterval, ∀ x ∈ milnorFibreBoundary H ε 0,
      E (φ 0 t x) = (t : ℝ) • s := by
    intro t x hx
    have hx0 : E x = 0 := hx.2
    have hK : ∀ u ∈ Icc (0 : ℝ) 1, φ 0 u x ∈ K := by
      intro u hu
      have hb := intervalIntegral_mem_Icc_of_mem_unit (hcont 0 x) (fun v => hχ01 _) hu.1
      refine ⟨mem_sphere_zero_iff_norm.mpr ((hnorm 0 u x).trans hx.1),
        mem_closedBall_zero_iff.mpr ?_⟩
      rw [hlevel, hx0, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hb.2, hu.2])
    have hi : (∫ u in (0 : ℝ)..(t : ℝ), χ (φ 0 u x)) = (t : ℝ) := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
      · simp
      · intro u hu
        rw [uIcc_of_le t.property.1] at hu
        exact hχK _ (hK u ⟨hu.1, hu.2.trans t.property.2⟩)
    rw [hlevel, hx0, zero_add, hi]
  let Φ := DifferentialTopology.timeDependentEvolutionDiffeotopy (fun _ => V) hC
    (hV.comp contDiff_snd)
  have hΦ : ∀ x, Φ.final x = φ 0 1 x := fun x => by
    rw [TauCeti.Diffeotopy.final_apply]
    exact DifferentialTopology.timeDependentEvolutionDiffeotopy_apply (fun _ => V) hC
      (hV.comp contDiff_snd) 1 x
  refine ⟨Φ, fun t x => hnorm 0 t x, hlevel_trace, ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨hxε, hx0⟩, rfl⟩
    have hx0 : E x = 0 := hx0
    rw [hΦ]
    have hK : ∀ t ∈ Icc (0 : ℝ) 1, φ 0 t x ∈ K := by
      intro t ht
      have hb := intervalIntegral_mem_Icc_of_mem_unit (hcont 0 x) (fun u => hχ01 _) ht.1
      refine ⟨mem_sphere_zero_iff_norm.mpr ((hnorm 0 t x).trans hxε),
        mem_closedBall_zero_iff.mpr ?_⟩
      rw [hlevel, hx0, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hb.2, ht.2])
    refine ⟨(hnorm 0 1 x).trans hxε, ?_⟩
    change E (φ 0 1 x) = s
    rw [hlevel, hx0, hone 0 x hK, one_smul, zero_add]
  · rintro ⟨hyε, hys⟩
    have hys : E y = s := hys
    refine ⟨φ 1 0 y, ⟨(hnorm 1 0 y).trans hyε, ?_⟩, ?_⟩
    · have hK : ∀ t ∈ Icc (0 : ℝ) 1, φ 1 t y ∈ K := by
        intro t ht
        have hb := intervalIntegral_mem_Icc_of_mem_unit (hcont 1 y) (fun u => hχ01 _) ht.2
        refine ⟨mem_sphere_zero_iff_norm.mpr ((hnorm 1 t y).trans hyε),
          mem_closedBall_zero_iff.mpr ?_⟩
        have heq : E (φ 1 t y) = (1 - ∫ u in t..1, χ (φ 1 u y)) • s := by
          rw [hlevel, hys, intervalIntegral.integral_symm, sub_smul, one_smul, neg_smul,
            sub_eq_add_neg]
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hb.2, ht.1])]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hb.1])
      change E (φ 1 0 y) = 0
      rw [hlevel, hys, intervalIntegral.integral_symm, hone 1 y hK, neg_smul, one_smul,
        add_neg_cancel]
    · rw [hΦ]
      exact (TauCeti.timeDependentFlow_trans _ hC 1 0 1 y).trans
        (TauCeti.timeDependentFlow_self _ hC 1 y)

/-- The endpoint-only form of the smooth boundary transport theorem. -/
theorem milnorFibreBoundary_diffeotopy_of_transverse (H : Source 2 → ℂ) {ε c : ℝ}
    (han : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ ≤ ε → AnalyticAt ℂ (euclideanEquation H) z)
    (htr : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ = ε → ‖euclideanEquation H z‖ < c →
      Surjective (fderiv ℝ (radialPair H) z))
    (s : ℂ) (hs : ‖s‖ < c) :
    ∃ Φ : TauCeti.Diffeotopy 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
        (EuclideanSpace ℂ (Fin 2)),
      (∀ t x, ‖Φ (t, x)‖ = ‖x‖) ∧
      Φ.final '' milnorFibreBoundary H ε 0 = milnorFibreBoundary H ε s := by
  obtain ⟨Φ, hnorm, -, himage⟩ :=
    milnorFibreBoundary_diffeotopy_with_level_of_transverse H han htr s hs
  exact ⟨Φ, hnorm, himage⟩

/-- **Smooth isotopy of the Milnor fibre boundary.** For every sufficiently small radius `ε`
there is `δ > 0` such that, for every level `s` with `‖s‖ < δ`, a native smooth diffeotopy
of `ℂ²` preserves every sphere around the origin and carries the zero-set link at radius `ε`
onto the boundary of the Milnor fibre of radius `ε` over `s`. -/
theorem exists_milnorFibreBoundary_diffeotopy (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, ‖s‖ < δ →
      ∃ Φ : TauCeti.Diffeotopy 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
        (EuclideanSpace ℂ (Fin 2)),
        (∀ t x, ‖Φ (t, x)‖ = ‖x‖) ∧
        Φ.final '' milnorFibreBoundary H ε 0 = milnorFibreBoundary H ε s := by
  obtain ⟨ε₀, hε₀, han, htr⟩ := exists_radial_transverse_neighbourhood H hH hH0 hsq
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨c, hc, hsurj⟩ := htr ε hε hεε₀ ε hε le_rfl
  exact ⟨c, hc, fun s hs => milnorFibreBoundary_diffeotopy_of_transverse H
    (fun z hz => (han z (by linarith)).1) (fun z hz hzc => hsurj z hz.ge hz.le hzc) s hs⟩

/-- The same smooth diffeotopy retains the exact equation level at every time. -/
theorem exists_milnorFibreBoundary_diffeotopy_with_level
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, ‖s‖ < δ →
      ∃ Φ : TauCeti.Diffeotopy 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
          (EuclideanSpace ℂ (Fin 2)),
        (∀ t x, ‖Φ (t, x)‖ = ‖x‖) ∧
        (∀ t : unitInterval, ∀ x ∈ milnorFibreBoundary H ε 0,
          euclideanEquation H (Φ (t, x)) = (t : ℝ) • s) ∧
        Φ.final '' milnorFibreBoundary H ε 0 = milnorFibreBoundary H ε s := by
  obtain ⟨ε₀, hε₀, han, htr⟩ := exists_radial_transverse_neighbourhood H hH hH0 hsq
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨c, hc, hsurj⟩ := htr ε hε hεε₀ ε hε le_rfl
  exact ⟨c, hc, fun s hs => milnorFibreBoundary_diffeotopy_with_level_of_transverse H
    (fun z hz => (han z (by linarith)).1) (fun z hz hzc => hsurj z hz.ge hz.le hzc) s hs⟩


end OnLeConjecture.Analytic
