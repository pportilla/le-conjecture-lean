/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidLinkIsotopy
public import OnLeConjecture.Analytic.PlaneBranchSolidTorus
public import Mathlib.Analysis.Convex.Basic

/-! # Convex interpolation of separated closed-braid heights

For each pair of distinct parameters with the same power coordinate, a common
strict real or imaginary ordering of the endpoint heights prevents collisions
throughout convex interpolation. The resulting smooth family extends to an
ambient diffeotopy of the unit three-sphere with the stated endpoint maps.
-/

@[expose] public noncomputable section

open Set Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance planeBraidConvexRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance planeBraidConvexRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

/-- Convex combinations of two nonzero real numbers with the same sign stay nonzero. -/
theorem convex_combination_ne_zero_of_mul_pos {x y s : ℝ}
    (hxy : 0 < x * y) (hs : s ∈ Icc 0 1) : (1 - s) * x + s * y ≠ 0 := by
  rcases mul_pos_iff.mp hxy with h | h
  · have hp := convex_Ioi (𝕜 := ℝ) (0 : ℝ) h.1 h.2 (sub_nonneg.mpr hs.2) hs.1
      (show (1 - s) + s = 1 by ring)
    exact (show 0 < (1 - s) * x + s * y from hp).ne'
  · have hn := convex_Iio (𝕜 := ℝ) (0 : ℝ) h.1 h.2 (sub_nonneg.mpr hs.2) hs.1
      (show (1 - s) + s = 1 by ring)
    exact (show (1 - s) * x + s * y < 0 from hn).ne

/-- A coordinate with the same strict sign at both endpoints prevents a complex
convex combination from vanishing. -/
theorem complex_convex_combination_ne_zero_of_coordinate_mul_pos {z w : ℂ} {s : ℝ}
    (hzw : 0 < z.re * w.re ∨ 0 < z.im * w.im) (hs : s ∈ Icc 0 1) :
    (1 - s) • z + s • w ≠ 0 := by
  intro h
  rcases hzw with hr | hi
  · apply convex_combination_ne_zero_of_mul_pos hr hs
    simpa using congrArg Complex.re h
  · apply convex_combination_ne_zero_of_mul_pos hi hs
    simpa using congrArg Complex.im h

/-- Interpolation of the complementary complex coordinate of a closed braid. -/
def planeBraidConvexHeight (w₀ w₁ : Circle → ℂ) (s : ℝ) (u : Circle) : ℂ :=
  (1 - s) • w₀ u + s • w₁ u

@[simp] theorem planeBraidConvexHeight_zero (w₀ w₁ : Circle → ℂ) (u : Circle) :
    planeBraidConvexHeight w₀ w₁ 0 u = w₀ u := by simp [planeBraidConvexHeight]

@[simp] theorem planeBraidConvexHeight_one (w₀ w₁ : Circle → ℂ) (u : Circle) :
    planeBraidConvexHeight w₀ w₁ 1 u = w₁ u := by simp [planeBraidConvexHeight]

theorem planeBraidConvexHeight_sub (w₀ w₁ : Circle → ℂ) (s : ℝ) (u v : Circle) :
    planeBraidConvexHeight w₀ w₁ s u - planeBraidConvexHeight w₀ w₁ s v =
      (1 - s) • (w₀ u - w₀ v) + s • (w₁ u - w₁ v) := by
  simp only [planeBraidConvexHeight, smul_sub]
  abel

/-- Each pair in a power-coordinate fibre stays separated throughout interpolation. -/
theorem planeBraidConvexHeight_ne {w₀ w₁ : Circle → ℂ} {s : ℝ}
    (hs : s ∈ Icc 0 1) {u v : Circle}
    (hsep : 0 < (w₀ u - w₀ v).re * (w₁ u - w₁ v).re ∨
      0 < (w₀ u - w₀ v).im * (w₁ u - w₁ v).im) :
    planeBraidConvexHeight w₀ w₁ s u ≠ planeBraidConvexHeight w₀ w₁ s v := by
  rw [← sub_ne_zero, planeBraidConvexHeight_sub]
  exact complex_convex_combination_ne_zero_of_coordinate_mul_pos hsep hs

/-- The interpolation, made constant outside the time interval by `smoothTransition`,
and mapped into the unit sphere using the selected solid-torus coordinate. -/
def planeBraidConvexSphereFamily (i : Fin 2) (a : ℕ) (w₀ w₁ : Circle → ℂ)
    (p : Circle × ℝ) : EuclideanSpace ℂ (Fin 2) :=
  planeSolidTorusMap i
    (p.1 ^ a, planeBraidConvexHeight w₀ w₁ (Real.smoothTransition p.2) p.1)

@[simp] theorem planeBraidConvexSphereFamily_zero
    (i : Fin 2) (a : ℕ) (w₀ w₁ : Circle → ℂ) (u : Circle) :
    planeBraidConvexSphereFamily i a w₀ w₁ (u, 0) =
      planeSolidTorusMap i (u ^ a, w₀ u) := by simp [planeBraidConvexSphereFamily]

@[simp] theorem planeBraidConvexSphereFamily_one
    (i : Fin 2) (a : ℕ) (w₀ w₁ : Circle → ℂ) (u : Circle) :
    planeBraidConvexSphereFamily i a w₀ w₁ (u, 1) =
      planeSolidTorusMap i (u ^ a, w₁ u) := by simp [planeBraidConvexSphereFamily]

theorem planeBraidConvexSphereFamily_contMDiff
    (i : Fin 2) (a : ℕ) {w₀ w₁ : Circle → ℂ}
    (hw₀ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₀)
    (hw₁ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₁) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (planeBraidConvexSphereFamily i a w₀ w₁) := by
  have hT : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun p : Circle × ℝ => Real.smoothTransition p.2) :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_snd
  have hh : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × ℝ => planeBraidConvexHeight w₀ w₁
        (Real.smoothTransition p.2) p.1) :=
    ((contMDiff_const.sub hT).smul (hw₀.comp contMDiff_fst)).add
      (hT.smul (hw₁.comp contMDiff_fst))
  exact (planeSolidTorusMap_isSmoothEmbedding i).contMDiff.comp
    (((contMDiff_pow a).comp contMDiff_fst).prodMk hh)

theorem planeBraidConvexSphereFamily_norm
    (i : Fin 2) (a : ℕ) (w₀ w₁ : Circle → ℂ) (p : Circle × ℝ) :
    ‖planeBraidConvexSphereFamily i a w₀ w₁ p‖ = 1 :=
  planeSolidTorusMap_norm i _

/-- The selected coordinate keeps the power phase throughout the interpolation. -/
theorem planeBraidConvexSphereFamily_phase
    (i : Fin 2) (a : ℕ) (w₀ w₁ : Circle → ℂ) (p : Circle × ℝ) :
    ‖planeBraidConvexSphereFamily i a w₀ w₁ p i‖⁻¹ •
      planeBraidConvexSphereFamily i a w₀ w₁ p i = (p.1 : ℂ) ^ a := by
  simpa only [planeBraidConvexSphereFamily, Circle.coe_pow] using
    congrArg Prod.fst (planeSolidTorusMap_recovery i
      (p.1 ^ a, planeBraidConvexHeight w₀ w₁ (Real.smoothTransition p.2) p.1))

theorem planeBraidConvexSphereFamily_injective
    (i : Fin 2) (a : ℕ) {w₀ w₁ : Circle → ℂ}
    (hsep : ∀ u v : Circle, u ≠ v → u ^ a = v ^ a →
      0 < (w₀ u - w₀ v).re * (w₁ u - w₁ v).re ∨
        0 < (w₀ u - w₀ v).im * (w₁ u - w₁ v).im) (t : ℝ) :
    Function.Injective (fun u => planeBraidConvexSphereFamily i a w₀ w₁ (u, t)) := by
  intro u v huv
  by_contra hne
  have heq := (planeSolidTorusMap_isSmoothEmbedding i).isEmbedding.injective huv
  have hpow : u ^ a = v ^ a := congrArg Prod.fst heq
  have hheight := congrArg Prod.snd heq
  exact planeBraidConvexHeight_ne
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
    (hsep u v hne hpow) hheight

/-- A common strict real or imaginary separation in each power fibre gives an
ambient diffeotopy between the exact solid-torus endpoint circles. -/
theorem exists_planeBraidConvex_endpoint_diffeotopy
    (i : Fin 2) {a : ℕ} (ha : 0 < a) {w₀ w₁ : Circle → ℂ}
    (hw₀ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₀)
    (hw₁ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₁)
    (hsep : ∀ u v : Circle, u ≠ v → u ^ a = v ^ a →
      0 < (w₀ u - w₀ v).re * (w₁ u - w₁ v).re ∨
        0 < (w₀ u - w₀ v).im * (w₁ u - w₁ v).im) :
    ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
      (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u ^ a, w₀ u)) ∧
      (∀ u, (L₁ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u ^ a, w₁ u)) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ u, Φ.final (L₀ u) = L₁ u := by
  let K := planeBraidConvexSphereFamily i a w₀ w₁
  have hs : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K :=
    planeBraidConvexSphereFamily_contMDiff i a hw₀ hw₁
  have hd : ∀ t u, Function.Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) (fun v => K (v, t)) u) :=
    planeSphereFamily_mfderiv_injective_of_power_phase K i ha hs
      (planeBraidConvexSphereFamily_phase i a w₀ w₁)
  have he : ∀ t, Topology.IsEmbedding (fun u => K (u, t)) := by
    intro t
    exact ((hs.comp (contMDiff_id.prodMk (contMDiff_const (c := t)))).continuous.isClosedEmbedding
      (planeBraidConvexSphereFamily_injective i a hsep t)).isEmbedding
  obtain ⟨L₀, L₁, h₀, h₁, Φ, hΦ⟩ := exists_plane_sphere_family_endpoint_diffeotopy K
    (fun t u => planeBraidConvexSphereFamily_norm i a w₀ w₁ (u, t)) hs hd he
  refine ⟨L₀, L₁, ?_, ?_, Φ, hΦ⟩
  · intro u
    simpa only [K, planeBraidConvexSphereFamily_zero] using h₀ u
  · intro u
    simpa only [K, planeBraidConvexSphereFamily_one] using h₁ u

end OnLeConjecture.Analytic
