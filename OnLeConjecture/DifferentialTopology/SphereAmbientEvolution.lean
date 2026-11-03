/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DifferentialTopology.CompactSupportEvolution

/-!
# Ambient isotopies of a sphere obtained by integrating tangent fields

The constructed global evolution preserves the norm when the field is
orthogonal to position. Restriction to the unit sphere gives a genuine
ambient isotopy, with its continuous inverse obtained by reverse evolution.
The existence theorem starts with a compactly supported `C¹` field and
does not assume an evolution or an ambient extension.
-/

public noncomputable section

open Filter Function
open scoped Topology ContDiff NNReal

namespace OnLeConjecture.DifferentialTopology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : ℝ → E → E) {K : ℝ≥0}
    (hX : LipschitzWith K (TauCeti.timeDependentSuspension X))
    (htangent : ∀ t x, inner ℝ x (X t x) = 0)

/-- The proved time-dependent evolution restricted to the unit sphere. -/
@[expose] def sphereEvolution (s t : ℝ) (x : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 :=
  ⟨TauCeti.timeDependentFlow X hX s t x, by
    simp only [Metric.mem_sphere, dist_zero_right,
      norm_timeDependentEvolution X hX htangent]
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property⟩

@[simp] theorem sphereEvolution_coe (s t : ℝ) (x : Metric.sphere (0 : E) 1) :
    (sphereEvolution X hX htangent s t x : E) = TauCeti.timeDependentFlow X hX s t x := rfl

@[simp] theorem sphereEvolution_self (s : ℝ) (x : Metric.sphere (0 : E) 1) :
    sphereEvolution X hX htangent s s x = x := by
  apply Subtype.ext
  exact TauCeti.timeDependentFlow_self X hX s x

@[simp] theorem sphereEvolution_trans (r s t : ℝ) (x : Metric.sphere (0 : E) 1) :
    sphereEvolution X hX htangent s t (sphereEvolution X hX htangent r s x) =
      sphereEvolution X hX htangent r t x := by
  apply Subtype.ext
  exact TauCeti.timeDependentFlow_trans X hX r s t x

theorem sphereEvolution_continuous :
    Continuous fun p : (ℝ × ℝ) × Metric.sphere (0 : E) 1 =>
      sphereEvolution X hX htangent p.1.1 p.1.2 p.2 := by
  apply Continuous.subtype_mk
  exact (TauCeti.continuous_timeDependentFlow X hX).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- The norm-preserving global evolution gives an ambient isotopy of
the unit sphere. -/
@[expose] def sphereEvolutionAmbientIsotopy : TauCeti.AmbientIsotopy (Metric.sphere (0 : E) 1) := by
  let Φ : unitInterval × Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1 :=
    fun p => sphereEvolution X hX htangent 0 p.1 p.2
  have hΦ : Continuous Φ := by
    simpa only [Φ, Function.comp_def] using (sphereEvolution_continuous X hX htangent).comp
      (by fun_prop : Continuous fun p : unitInterval × Metric.sphere (0 : E) 1 =>
        (((0 : ℝ), (p.1 : ℝ)), p.2))
  let total : (unitInterval × Metric.sphere (0 : E) 1) ≃ₜ
      (unitInterval × Metric.sphere (0 : E) 1) :=
    { toFun := fun p => (p.1, Φ p)
      invFun := fun p => (p.1, sphereEvolution X hX htangent p.1 0 p.2)
      left_inv := by intro p; ext <;> simp [Φ]
      right_inv := by intro p; ext <;> simp [Φ]
      continuous_toFun := continuous_fst.prodMk hΦ
      continuous_invFun := continuous_fst.prodMk
        ((sphereEvolution_continuous X hX htangent).comp
          (by fun_prop : Continuous fun p : unitInterval × Metric.sphere (0 : E) 1 =>
            (((p.1 : ℝ), (0 : ℝ)), p.2))) }
  exact ⟨⟨Φ, hΦ⟩, total.isHomeomorph, fun x => by simp [Φ]⟩

@[simp] theorem sphereEvolutionAmbientIsotopy_coe (t : unitInterval)
    (x : Metric.sphere (0 : E) 1) :
    ((sphereEvolutionAmbientIsotopy X hX htangent).toContinuousMap (t, x) : E) =
      TauCeti.timeDependentFlow X hX 0 t x := rfl

omit hX htangent in
/-- A compactly supported jointly `C¹` tangent field generates an ambient
isotopy of the sphere following every prescribed integral trajectory. -/
theorem exists_sphereAmbientIsotopy_following
    (hregular : ContDiff ℝ 1 (Function.uncurry X))
    (hcompact : HasCompactSupport (Function.uncurry X))
    (htangent : ∀ t x, inner ℝ x (X t x) = 0)
    {M : Type*} (G : ℝ → M → E)
    (hG0 : ∀ x, ‖G 0 x‖ = 1)
    (hG : ∀ t x, HasDerivAt (fun s => G s x) (X t (G t x)) t) :
    ∃ Φ : TauCeti.AmbientIsotopy (Metric.sphere (0 : E) 1),
      ∀ t : unitInterval, ∀ x : M,
        (Φ.toContinuousMap (t, ⟨G 0 x, by
          simpa only [Metric.mem_sphere, dist_zero_right] using hG0 x⟩) : E) = G t x := by
  obtain ⟨K, hK⟩ := exists_lipschitz_timeDependentSuspension hregular hcompact
  refine ⟨sphereEvolutionAmbientIsotopy X hK htangent, ?_⟩
  intro t x
  exact (TauCeti.eq_timeDependentFlow X hK (fun s => hG s x) 0 t).symm

end OnLeConjecture.DifferentialTopology
