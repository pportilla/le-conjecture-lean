/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DifferentialTopology.SphereAmbientEvolution

/-!
# Tangential projection of an ambient velocity extension

The polynomial expression `‖x‖² V(t,x) - ⟨x,V(t,x)⟩ x` is orthogonal to
`x` everywhere. It is smooth at zero, preserves compact support, and agrees
with every tangent velocity on the unit sphere. Thus a compactly supported
Euclidean velocity extension of a sphere motion can be integrated to an
ambient isotopy of the sphere.
-/

public noncomputable section

open Filter Function
open scoped Topology ContDiff

namespace OnLeConjecture.DifferentialTopology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A polynomial tangential projection that equals the orthogonal
projection on the unit sphere. -/
@[expose] def tangentVelocity (V : ℝ → E → E) (t : ℝ) (x : E) : E :=
  ‖x‖ ^ 2 • V t x - inner ℝ x (V t x) • x

/-- The projected field is orthogonal to the position vector everywhere. -/
theorem tangentVelocity_orthogonal (V : ℝ → E → E) (t : ℝ) (x : E) :
    inner ℝ x (tangentVelocity V t x) = 0 := by
  simp only [tangentVelocity, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- Joint differentiability is preserved by polynomial tangential projection. -/
theorem tangentVelocity_contDiff {V : ℝ → E → E} {n : WithTop ℕ∞}
    (hV : ContDiff ℝ n (Function.uncurry V)) :
    ContDiff ℝ n (Function.uncurry (tangentVelocity V)) := by
  have hs : ContDiff ℝ n (fun p : ℝ × E => p.2) := contDiff_snd
  exact ((hs.norm_sq (𝕜 := ℝ)).smul hV).sub ((hs.inner ℝ hV).smul hs)

/-- Tangential projection does not enlarge the support of the field. -/
theorem tangentVelocity_hasCompactSupport {V : ℝ → E → E}
    (hV : HasCompactSupport (Function.uncurry V)) :
    HasCompactSupport (Function.uncurry (tangentVelocity V)) := by
  apply HasCompactSupport.of_support_subset_isCompact hV
  intro p hp
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hp (by simp [Function.uncurry, tangentVelocity] at hz ⊢; simp [hz])

/-- A tangent vector based on the unit sphere is unchanged by the
polynomial projection. -/
theorem tangentVelocity_eq_of_unit_tangent (V : ℝ → E → E) (t : ℝ) (x : E)
    (hx : ‖x‖ = 1) (htangent : inner ℝ x (V t x) = 0) :
    tangentVelocity V t x = V t x := by
  simp only [tangentVelocity, hx, one_pow, one_smul, htangent, zero_smul, sub_zero]

/-- Differentiating constant squared norm proves that a curve in the
unit sphere has velocity orthogonal to its position. -/
theorem inner_velocity_eq_zero_of_unit_norm {γ : ℝ → E} {t : ℝ} {v : E}
    (hnorm : ∀ s, ‖γ s‖ = 1) (hd : HasDerivAt γ v t) :
    inner ℝ (γ t) v = 0 := by
  have he : (fun s => ‖γ s‖ ^ 2) = fun _ : ℝ => (1 : ℝ) := by
    funext s
    simp only [hnorm s, one_pow]
  have hc : HasDerivAt (fun s => ‖γ s‖ ^ 2) 0 t := by
    rw [he]
    exact hasDerivAt_const t 1
  have h := hd.norm_sq.unique hc
  linarith

/-- An arbitrary compactly supported `C¹` velocity extension of a motion
in the unit sphere produces an ambient isotopy following that motion.
The tangency condition is derived from the actual sphere equation. -/
theorem exists_sphereAmbientIsotopy_of_velocity_extension [CompleteSpace E]
    {V : ℝ → E → E} (hV : ContDiff ℝ 1 (Function.uncurry V))
    (hcompact : HasCompactSupport (Function.uncurry V))
    {M : Type*} (G : ℝ → M → E) (hGnorm : ∀ t x, ‖G t x‖ = 1)
    (hG : ∀ t x, HasDerivAt (fun s => G s x) (V t (G t x)) t) :
    ∃ Φ : TauCeti.AmbientIsotopy (Metric.sphere (0 : E) 1),
      ∀ t : unitInterval, ∀ x : M,
        (Φ.toContinuousMap (t, ⟨G 0 x, by
          simpa only [Metric.mem_sphere, dist_zero_right] using hGnorm 0 x⟩) : E) = G t x := by
  apply exists_sphereAmbientIsotopy_following (tangentVelocity V)
    (tangentVelocity_contDiff hV) (tangentVelocity_hasCompactSupport hcompact)
    (tangentVelocity_orthogonal V) G (hGnorm 0)
  intro t x
  rw [tangentVelocity_eq_of_unit_tangent V t (G t x) (hGnorm t x)
    (inner_velocity_eq_zero_of_unit_norm (fun s => hGnorm s x) (hG t x))]
  exact hG t x

end OnLeConjecture.DifferentialTopology
