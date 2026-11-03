/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Immersion.FiniteDimensional
public import OnLeConjecture.External.TauCeti.Geometry.Manifold.SmoothEmbedding.Extension
public import OnLeConjecture.External.TauCeti.Topology.Maps.Proper.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Tracks and velocities of smooth motions

For a compact source, an injective immersed smooth motion has a smooth
embedded track in time times the ambient vector space. Its time velocity
is a smooth vector-valued function on the source of the track.
-/

public noncomputable section

open Set Manifold
open scoped ContDiff Manifold

namespace OnLeConjecture.DifferentialTopology

variable {E V H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {G : ℝ × M → E}

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [CompleteSpace V] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The derivative of the time-preserving track is injective whenever
the derivative of each time slice is injective. -/
theorem motion_track_mfderiv_injective
    (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G)
    (hd : ∀ t x, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun y => G (t, y)) x))
    (q : ℝ × M) :
    Function.Injective (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod 𝓘(ℝ, E))
      (fun p => (p.1, G p)) q) := by
  have hGd := hG.mdifferentiable (by simp)
  rw [mfderiv_prodMk mdifferentiableAt_fst (hGd q), mfderiv_fst]
  intro v w hvw
  change ℝ × V at v w
  change (v.1, mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ, E) G q v) =
    (w.1, mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ, E) G q w) at hvw
  have hv₁ : v.1 = w.1 := congrArg (fun p : ℝ × E => p.1) hvw
  have hGvw : mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ, E) G q v =
      mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ, E) G q w := congrArg (fun p : ℝ × E => p.2) hvw
  apply Prod.ext hv₁
  apply hd q.1 q.2
  have hslice := mfderiv_comp_of_eq (hGd q)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) (Prod.mk.eta (p := q))
  dsimp only [id_eq] at hslice
  rw [mfderiv_prod_right] at hslice
  change mfderiv I 𝓘(ℝ, E) (fun y => G (q.1, y)) q.2 = _ at hslice
  rw [hslice]
  have hv : (0, v.2) = v - (v.1, 0) := by ext <;> simp
  have hw : (0, w.2) = w - (v.1, 0) := by ext <;> simp [hv₁]
  change mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ, E) G q (0, v.2) =
    mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ, E) G q (0, w.2)
  rw [hv, hw, map_sub, map_sub, hGvw]

/-- A smooth motion with compact source and injective immersed slices
has a smooth embedded track. -/
theorem isSmoothEmbedding_motion_track [CompactSpace M]
    (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G)
    (hi : ∀ t, Function.Injective (fun x => G (t, x)))
    (hd : ∀ t x, Function.Injective (mfderiv I 𝓘(ℝ, E) (fun y => G (t, y)) x)) :
    IsSmoothEmbedding (𝓘(ℝ).prod I) (𝓘(ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p => (p.1, G p)) :=
  (contMDiff_fst.prodMk hG).isSmoothEmbedding_of_injective_mfderiv (by simp)
    (motion_track_mfderiv_injective hG hd)
    (hG.continuous.isClosedEmbedding_fst_prod hi).isEmbedding

/-- The time velocity is the time derivative evaluated on the unit vector. -/
@[expose] def motionTimeVelocity (G : ℝ × M → E) (q : ℝ × M) : E :=
  deriv (fun t => G (t, q.2)) q.1

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [CompleteSpace V] [I.Boundaryless] in
/-- The time velocity of a smooth Euclidean-valued motion is smooth. -/
theorem motionTimeVelocity_contMDiff
    (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ (motionTimeVelocity G) := by
  intro q
  have haux : ContMDiff ((𝓘(ℝ).prod I).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
      (fun p : (ℝ × M) × ℝ => G (p.2, p.1.2)) :=
    hG.comp (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst))
  have hv := (haux.contMDiffAt (x := (q, q.1))).mfderiv_apply (m := ∞)
    (fun p : ℝ × M => fun t : ℝ => G (t, p.2)) Prod.fst id (fun _ : ℝ × M => (1 : ℝ))
    contMDiffAt_fst contMDiffAt_id contMDiffAt_const (by simp)
  change ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞
    (fun p => (fderiv ℝ (fun t => G (t, p.2)) p.1) 1) q
  simpa only [inTangentCoordinates, inCoordinates_tangent_bundle_core_model_space,
    id_eq, mfderiv_eq_fderiv] using hv

end OnLeConjecture.DifferentialTopology
