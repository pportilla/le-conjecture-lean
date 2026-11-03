/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Dynamics.Flow.TimeDependent
public import OnLeConjecture.External.TauCeti.Topology.Homotopy.Isotopy.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Integration of compactly supported time-dependent vector fields

A jointly continuously differentiable vector field with compact support
in time and space has a globally Lipschitz autonomous suspension. The
proved Picard construction therefore supplies its evolution for all times,
and the inverse-time identities give an ambient isotopy. Orthogonality to
the position vector implies preservation of every norm sphere.
-/

public noncomputable section

open Filter Function
open scoped Topology ContDiff RealInnerProductSpace NNReal

namespace OnLeConjecture.DifferentialTopology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Compact support and joint `C¹` regularity supply the global Lipschitz
bound needed for the clock suspension. -/
theorem exists_lipschitz_timeDependentSuspension {X : ℝ → E → E}
    (hX : ContDiff ℝ 1 (Function.uncurry X))
    (hcompact : HasCompactSupport (Function.uncurry X)) :
    ∃ K, LipschitzWith K (TauCeti.timeDependentSuspension X) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hX one_ne_zero
  exact ⟨max 0 K, (LipschitzWith.const (1 : ℝ)).prodMk hK⟩

/-- Each time evolution is a homeomorphism with reverse-time inverse.
The evolution is obtained from the global Picard solution. -/
@[expose] def timeDependentEvolutionHomeomorph (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X)) (s t : ℝ) : E ≃ₜ E where
  toFun := TauCeti.timeDependentFlow X hX s t
  invFun := TauCeti.timeDependentFlow X hX t s
  left_inv := TauCeti.leftInverse_timeDependentFlow X hX s t
  right_inv := TauCeti.rightInverse_timeDependentFlow X hX s t
  continuous_toFun := (TauCeti.continuous_timeDependentFlow X hX).comp
    (by fun_prop : Continuous fun x : E => ((s, t), x))
  continuous_invFun := (TauCeti.continuous_timeDependentFlow X hX).comp
    (by fun_prop : Continuous fun x : E => ((t, s), x))

@[simp] theorem timeDependentEvolutionHomeomorph_apply (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X)) (s t : ℝ) (x : E) :
    timeDependentEvolutionHomeomorph X hX s t x = TauCeti.timeDependentFlow X hX s t x := rfl

/-- Integrating from time zero gives an ambient isotopy, including a
continuous inverse for its full level-preserving map. -/
@[expose] def timeDependentEvolutionAmbientIsotopy (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X)) : TauCeti.AmbientIsotopy E := by
  let Φ : unitInterval × E → E := fun p => TauCeti.timeDependentFlow X hX 0 p.1 p.2
  have hΦ : Continuous Φ := by
    simpa only [Φ, Function.comp_def] using (TauCeti.continuous_timeDependentFlow X hX).comp
      (by fun_prop : Continuous fun p : unitInterval × E => (((0 : ℝ), (p.1 : ℝ)), p.2))
  let total : (unitInterval × E) ≃ₜ (unitInterval × E) :=
    { toFun := fun p => (p.1, Φ p)
      invFun := fun p => (p.1, TauCeti.timeDependentFlow X hX p.1 0 p.2)
      left_inv := by intro p; ext <;> simp [Φ]
      right_inv := by intro p; ext <;> simp [Φ]
      continuous_toFun := continuous_fst.prodMk hΦ
      continuous_invFun := continuous_fst.prodMk
        ((TauCeti.continuous_timeDependentFlow X hX).comp
          (by fun_prop : Continuous fun p : unitInterval × E => (((p.1 : ℝ), (0 : ℝ)), p.2))) }
  exact ⟨⟨Φ, hΦ⟩, total.isHomeomorph, fun x => by simp [Φ]⟩

@[simp] theorem timeDependentEvolutionAmbientIsotopy_apply (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X)) (t : unitInterval) (x : E) :
    (timeDependentEvolutionAmbientIsotopy X hX).toContinuousMap (t, x) =
      TauCeti.timeDependentFlow X hX 0 t x := rfl

/-- The evolution follows every given global solution of the same
time-dependent equation, by uniqueness of the proved global solution. -/
theorem timeDependentEvolution_follows (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
    {M : Type*} {G : ℝ → M → E}
    (hG : ∀ t x, HasDerivAt (fun s => G s x) (X t (G t x)) t)
    (t : unitInterval) (x : M) :
    (timeDependentEvolutionAmbientIsotopy X hX).toContinuousMap (t, G 0 x) = G t x :=
  (TauCeti.eq_timeDependentFlow X hX (fun s => hG s x) 0 t).symm

/-- A point at which the field vanishes at all times is fixed by every
time evolution. -/
theorem timeDependentEvolution_eq_of_forall_zero (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X)) {x : E}
    (hx : ∀ t, X t x = 0) (s t : ℝ) : TauCeti.timeDependentFlow X hX s t x = x := by
  have hc : ∀ t, HasDerivAt (fun _ : ℝ => x) (X t x) t := by
    intro t
    simpa only [hx t] using hasDerivAt_const t x
  exact (TauCeti.eq_timeDependentFlow X hX hc s t).symm

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- If the vector field is orthogonal to the position vector, the
constructed evolution preserves the norm for every initial point. -/
theorem norm_timeDependentEvolution (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
    (htangent : ∀ t x, inner ℝ x (X t x) = 0) (s t : ℝ) (x : E) :
    ‖TauCeti.timeDependentFlow X hX s t x‖ = ‖x‖ := by
  let γ := fun u => TauCeti.timeDependentFlow X hX s u x
  have hd (u : ℝ) : HasDerivAt (fun v => ‖γ v‖ ^ 2) 0 u := by
    simpa only [htangent, mul_zero] using
      (TauCeti.hasDerivAt_timeDependentFlow X hX s u x).norm_sq
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t s
  have he' : ‖γ t‖ ^ 2 = ‖x‖ ^ 2 := by simpa only [γ, TauCeti.timeDependentFlow_self] using he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he'

end InnerProduct

end OnLeConjecture.DifferentialTopology
