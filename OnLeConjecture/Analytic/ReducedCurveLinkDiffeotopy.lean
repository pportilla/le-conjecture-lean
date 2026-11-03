/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveLinkFamily
public import OnLeConjecture.Analytic.UnitSphereFamilyAmbientIsotopy
public import OnLeConjecture.DifferentialTopology.SigmaManifold

/-!
# Simultaneous smooth ambient isotopy of reduced plane curve links

The disjoint branch circles form one compact smooth manifold. Their
simultaneous motion is an embedding at every radius. The compact velocity
extension and its flow therefore give one ambient diffeotopy transporting
every branch, with range equal to the entire normalized equation zero set.
-/

public noncomputable section

open Set Manifold OnLeConjecture.DifferentialTopology
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance reducedCurveLinkRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance reducedCurveLinkRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

namespace NormalizedPlaneCurveLinkFamily

variable {H : Source 2 → ℂ} {ι : Type*} (F : NormalizedPlaneCurveLinkFamily H ι)

/-- The map on the disjoint union evaluates the corresponding branch component. -/
@[expose] def disjointUnion : (Σ _ : ι, Metric.sphere (0 : ℂ) 1) × ℝ →
    EuclideanSpace ℂ (Fin 2) := fun p => F.component p.1.1 (p.1.2, p.2)

theorem disjointUnion_norm {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq)
    (x : Σ _ : ι, Metric.sphere (0 : ℂ) 1) : ‖F.disjointUnion (x, c)‖ = 1 :=
  F.norm_eq_one c hc x.1 x.2

/-- Joint smoothness on the branch circles gives joint smoothness on their union. -/
theorem disjointUnion_smooth {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq)
    (x : Σ _ : ι, Metric.sphere (0 : ℂ) 1) :
    ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      F.disjointUnion (x, c) :=
  contMDiffAt_sigma_prod_iff.mpr (F.smooth c hc x.1 x.2)

/-- Each branch derivative is the derivative of the assembled map in its local chart. -/
theorem disjointUnion_differential_injective {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq)
    (x : Σ _ : ι, Metric.sphere (0 : ℂ) 1) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      (fun y => F.disjointUnion (y, c)) x) := by
  rw [mfderiv_sigma]
  exact F.differential_injective c hc x.1 x.2

/-- Distinct components cannot collide, and each individual circle is embedded. -/
theorem disjointUnion_injective {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq) :
    Function.Injective (fun x => F.disjointUnion (x, c)) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  by_cases hij : i = j
  · subst j
    exact congrArg (Sigma.mk i) ((F.closedEmbedding c hc i).injective h)
  · exfalso
    apply Set.disjoint_left.mp (F.disjoint c hc hij)
      (Set.mem_range_self u)
    exact ⟨v, h.symm⟩

/-- The assembled map is a closed embedding because its finite source is compact. -/
theorem disjointUnion_closedEmbedding [Finite ι] {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq) :
    Topology.IsClosedEmbedding (fun x => F.disjointUnion (x, c)) := by
  have hcont : Continuous (fun x => F.disjointUnion (x, c)) :=
    continuous_sigma_iff.mpr fun i => (F.closedEmbedding c hc i).continuous
  exact hcont.isClosedEmbedding (F.disjointUnion_injective hc)

/-- The assembled map parametrizes the entire normalized equation link. -/
theorem disjointUnion_range {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq) :
    Set.range (fun x => F.disjointUnion (x, c)) =
      (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ''
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt c) ∩
          {y | H ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) := by
  rw [Set.range_sigma_eq_iUnion_range]
  exact F.range_eq c hc

variable [Finite ι]

/-- A normalized reduced-curve link is a smooth embedding of the finite
disjoint union of circles. -/
@[expose] def smoothSlice (c : Ioo 0 F.radiusSq) :
    TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞
      (Σ _ : ι, Metric.sphere (0 : ℂ) 1)
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  unitSphereFamilySlice F.disjointUnion
    (fun _ hc => F.disjointUnion_norm hc)
    (fun _ hc => F.disjointUnion_smooth hc)
    (fun _ hc => F.disjointUnion_differential_injective hc)
    (fun _ hc => (F.disjointUnion_closedEmbedding hc).isEmbedding) c.1 c.2

@[simp] theorem smoothSlice_coe_apply (c : Ioo 0 F.radiusSq)
    (x : Σ _ : ι, Metric.sphere (0 : ℂ) 1) :
    (F.smoothSlice c x : EuclideanSpace ℂ (Fin 2)) = F.component x.1 (x.2, c.1) := by
  simp only [smoothSlice, unitSphereFamilySlice_coe_apply, disjointUnion]

/-- One ambient diffeotopy transports all components simultaneously. -/
theorem exists_diffeotopy (c₀ c₁ : Ioo 0 F.radiusSq) :
    ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      ∀ x, Φ.final (F.smoothSlice c₀ x) = F.smoothSlice c₁ x := by
  exact exists_unitSphereFamilyDiffeotopy F.disjointUnion
    (fun _ hc => F.disjointUnion_norm hc)
    (fun _ hc => F.disjointUnion_smooth hc)
    (fun _ hc => F.disjointUnion_differential_injective hc)
    (fun _ hc => (F.disjointUnion_closedEmbedding hc).isEmbedding) c₀.1 c₁.1 c₀.2 c₁.2

end NormalizedPlaneCurveLinkFamily

namespace Germ

/-- Every reduced analytic plane equation has simultaneous smooth circle
parametrizations of its small-sphere links. A single ambient diffeotopy
transports all branches between any two sufficiently small radii. -/
theorem exists_smoothAmbientIsotopic_unit_sphere_links_of_squarefree
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ (s : Finset (Germ 2)) (δ : ℝ), 0 < δ ∧
      ∃ K : Ioo 0 δ → TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞
          (Σ _ : s, Metric.sphere (0 : ℂ) 1)
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ c, Set.range (fun x => (K c x : EuclideanSpace ℂ (Fin 2))) =
          (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c.1)⁻¹ • y) ''
            (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt c.1) ∩
              {y | H ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0})) ∧
        ∀ c₀ c₁, ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
            (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ x, Φ.final (K c₀ x) = K c₁ x := by
  obtain ⟨s, ⟨F⟩⟩ := exists_normalized_link_family_of_squarefree H hH hsq
  refine ⟨s, F.radiusSq, F.radiusSq_pos, F.smoothSlice, ?_, F.exists_diffeotopy⟩
  intro c
  simpa only [NormalizedPlaneCurveLinkFamily.smoothSlice_coe_apply,
    NormalizedPlaneCurveLinkFamily.disjointUnion] using F.disjointUnion_range c.2

end Germ

end OnLeConjecture.Analytic
