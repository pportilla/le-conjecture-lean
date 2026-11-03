/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Analysis.ODE.InitialConditionGlobal
public import OnLeConjecture.DifferentialTopology.TangentVelocityExtension
public import OnLeConjecture.External.TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smooth dependence of the constructed time-dependent evolution

The autonomous Picard solution is smooth jointly in time and the initial
point. Applying that theorem to the clock suspension proves smoothness in
both endpoint times and the initial point for the constructed evolution.
Reverse evolution supplies the smooth inverse, including on the unit sphere.
-/

public noncomputable section

open Function Manifold
open scoped ContDiff Manifold NNReal

namespace OnLeConjecture.DifferentialTopology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The global Picard solution of a smooth Lipschitz field is jointly smooth. -/
theorem contDiff_infty_globalSolution (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hs : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2) := by
  rw [contDiff_infty]
  intro n
  exact (ODE.contDiff_globalSolution n v hv
    (hs.of_le (by exact_mod_cast (le_top : (n : ℕ∞) + 1 ≤ ⊤)))).of_le
    (by exact_mod_cast Nat.le_succ n)

/-- Evolution is smooth jointly in the starting time, ending time, and initial point. -/
theorem contDiff_timeDependentEvolution (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
    (hs : ContDiff ℝ ∞ (Function.uncurry X)) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E =>
      TauCeti.timeDependentFlow X hX p.1.1 p.1.2 p.2) := by
  have hclock : ContDiff ℝ ∞ (TauCeti.timeDependentSuspension X) :=
    contDiff_const.prodMk hs
  have harg : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E =>
      ((p.1.1, p.2), p.1.2 - p.1.1)) := by fun_prop
  exact ((contDiff_infty_globalSolution _ hX hclock).comp harg).snd

/-- Every evolution homeomorphism and its reverse-time inverse are smooth. -/
theorem contDiff_timeDependentEvolutionHomeomorph (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
    (hs : ContDiff ℝ ∞ (Function.uncurry X)) (s t : ℝ) :
    ContDiff ℝ ∞ (timeDependentEvolutionHomeomorph X hX s t) ∧
      ContDiff ℝ ∞ (timeDependentEvolutionHomeomorph X hX s t).symm := by
  constructor
  · exact (contDiff_timeDependentEvolution X hX hs).comp
      (by fun_prop : ContDiff ℝ ∞ (fun x : E => ((s, t), x)))
  · exact (contDiff_timeDependentEvolution X hX hs).comp
      (by fun_prop : ContDiff ℝ ∞ (fun x : E => ((t, s), x)))

end Normed

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  (X : ℝ → E → E) {K : ℝ≥0}
  (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
  (hs : ContDiff ℝ ∞ (Function.uncurry X))
  (htangent : ∀ t x, inner ℝ x (X t x) = 0)

include hs in
/-- The evolution on the unit sphere is jointly smooth in both times and its initial point. -/
theorem contMDiff_sphereEvolution :
    ContMDiff ((𝓘(ℝ, ℝ × ℝ)).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : (ℝ × ℝ) × Metric.sphere (0 : E) 1 =>
        sphereEvolution X hX htangent p.1.1 p.1.2 p.2) := by
  have ha : ContMDiff ((𝓘(ℝ, ℝ × ℝ)).prod (𝓡 n)) 𝓘(ℝ, E) ∞
      (fun p : (ℝ × ℝ) × Metric.sphere (0 : E) 1 =>
        TauCeti.timeDependentFlow X hX p.1.1 p.1.2 p.2) := by
    have harg : ContMDiff ((𝓘(ℝ, ℝ × ℝ)).prod (𝓡 n))
        𝓘(ℝ, (ℝ × ℝ) × E) ∞
        (fun p : (ℝ × ℝ) × Metric.sphere (0 : E) 1 => (p.1, (p.2 : E))) :=
      contMDiff_fst.prodMk_space ((contMDiff_coe_sphere (n := n)).comp contMDiff_snd)
    exact (contDiff_timeDependentEvolution X hX hs).contMDiff.comp harg
  exact ha.codRestrict_sphere (fun p => (sphereEvolution X hX htangent
    p.1.1 p.1.2 p.2).property)

/-- The smooth tangent evolution gives a diffeotopy of the sphere. Its total inverse
is the same evolution with the endpoint times reversed. -/
@[expose] def sphereEvolutionDiffeotopy : TauCeti.Diffeotopy (𝓡 n) ∞
    (Metric.sphere (0 : E) 1) := by
  have hf : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : unitInterval × Metric.sphere (0 : E) 1 =>
        sphereEvolution X hX htangent 0 p.1 p.2) := by
    have harg : ContMDiff ((𝓡∂ 1).prod (𝓡 n))
        ((𝓘(ℝ, ℝ × ℝ)).prod (𝓡 n)) ∞
        (fun p : unitInterval × Metric.sphere (0 : E) 1 =>
          (((0 : ℝ), (p.1 : ℝ)), p.2)) :=
      (contMDiff_const.prodMk_space (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).prodMk
        contMDiff_snd
    exact (contMDiff_sphereEvolution X hX hs htangent).comp harg
  have hi : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : unitInterval × Metric.sphere (0 : E) 1 =>
        sphereEvolution X hX htangent p.1 0 p.2) := by
    have harg : ContMDiff ((𝓡∂ 1).prod (𝓡 n))
        ((𝓘(ℝ, ℝ × ℝ)).prod (𝓡 n)) ∞
        (fun p : unitInterval × Metric.sphere (0 : E) 1 =>
          (((p.1 : ℝ), (0 : ℝ)), p.2)) :=
      ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk_space contMDiff_const).prodMk
        contMDiff_snd
    exact (contMDiff_sphereEvolution X hX hs htangent).comp harg
  exact
    { toDiffeomorph :=
        { toEquiv :=
            { toFun := fun p => (p.1, sphereEvolution X hX htangent 0 p.1 p.2)
              invFun := fun p => (p.1, sphereEvolution X hX htangent p.1 0 p.2)
              left_inv := by intro p; ext <;> simp
              right_inv := by intro p; ext <;> simp }
          contMDiff_toFun := contMDiff_fst.prodMk hf
          contMDiff_invFun := contMDiff_fst.prodMk hi }
      fst_apply := fun _ => rfl
      snd_apply_zero' := fun x => by
        change sphereEvolution X hX htangent 0 0 x = x
        simp }

@[simp] theorem sphereEvolutionDiffeotopy_coe (t : unitInterval)
    (x : Metric.sphere (0 : E) 1) :
    (sphereEvolutionDiffeotopy (n := n) X hX hs htangent (t, x) : E) =
      TauCeti.timeDependentFlow X hX 0 t x := rfl

end Sphere

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- A compactly supported smooth tangent field generates a smooth diffeotopy
following each prescribed integral trajectory in the sphere. -/
theorem exists_sphereDiffeotopy_following (X : ℝ → E → E)
    (hs : ContDiff ℝ ∞ (Function.uncurry X))
    (hcompact : HasCompactSupport (Function.uncurry X))
    (htangent : ∀ t x, inner ℝ x (X t x) = 0)
    {M : Type*} (G : ℝ → M → E)
    (hG0 : ∀ x, ‖G 0 x‖ = 1)
    (hG : ∀ t x, HasDerivAt (fun s => G s x) (X t (G t x)) t) :
    ∃ Φ : TauCeti.Diffeotopy (𝓡 n) ∞ (Metric.sphere (0 : E) 1),
      ∀ t : unitInterval, ∀ x : M,
        (Φ (t, ⟨G 0 x, by
          simpa only [Metric.mem_sphere, dist_zero_right] using hG0 x⟩) : E) = G t x := by
  obtain ⟨K, hK⟩ := exists_lipschitz_timeDependentSuspension
    (contDiff_infty.mp hs 1) hcompact
  refine ⟨sphereEvolutionDiffeotopy X hK hs htangent, ?_⟩
  intro t x
  exact (TauCeti.eq_timeDependentFlow X hK (fun s => hG s x) 0 t).symm

/-- A compactly supported smooth Euclidean velocity extension of a motion
in the unit sphere produces a smooth ambient diffeotopy following that motion.
Tangency is deduced by differentiating the sphere equation. -/
theorem exists_sphereDiffeotopy_of_velocity_extension
    {V : ℝ → E → E} (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hcompact : HasCompactSupport (Function.uncurry V))
    {M : Type*} (G : ℝ → M → E) (hGnorm : ∀ t x, ‖G t x‖ = 1)
    (hG : ∀ t x, HasDerivAt (fun s => G s x) (V t (G t x)) t) :
    ∃ Φ : TauCeti.Diffeotopy (𝓡 n) ∞ (Metric.sphere (0 : E) 1),
      ∀ t : unitInterval, ∀ x : M,
        (Φ (t, ⟨G 0 x, by
          simpa only [Metric.mem_sphere, dist_zero_right] using hGnorm 0 x⟩) : E) = G t x := by
  apply exists_sphereDiffeotopy_following (tangentVelocity V)
    (tangentVelocity_contDiff hV) (tangentVelocity_hasCompactSupport hcompact)
    (tangentVelocity_orthogonal V) G (hGnorm 0)
  intro t x
  rw [tangentVelocity_eq_of_unit_tangent V t (G t x) (hGnorm t x)
    (inner_velocity_eq_zero_of_unit_norm (fun s => hGnorm s x) (hG t x))]
  exact hG t x

end Existence

end OnLeConjecture.DifferentialTopology
