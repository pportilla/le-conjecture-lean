/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridWordModel
public import OnLeConjecture.Analytic.PlaneBranchBraidCircleFibres

/-! # The one-strand positive word is a coordinate unknot

The canonical one-strand word has zero height. More generally, any smooth
one-strand height graph in the solid torus is ambiently diffeotopic in the
unit three-sphere to the explicit coordinate great circle. No grid-diagram
realization is inferred from the empty word.
-/

@[expose] public noncomputable section

open Set Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance wordUnknotRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance wordUnknotRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

open Analytic DifferentialTopology

/-- The coordinate great circle, with its nonzero complex coordinate in position `i`. -/
def coordinateUnknotCircle (i : Fin 2) (u : Circle) : EuclideanSpace ℂ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℂ).symm (fun j => if j = i then (u : ℂ) else 0)

theorem coordinateUnknotCircle_eq_solidTorus (i : Fin 2) (u : Circle) :
    coordinateUnknotCircle i u = planeSolidTorusMap i (u, 0) := by
  simp [coordinateUnknotCircle, planeSolidTorusMap, complexSolidTorusScale]

@[simp] theorem coordinateUnknotCircle_selected (i : Fin 2) (u : Circle) :
    coordinateUnknotCircle i u i = (u : ℂ) := by simp [coordinateUnknotCircle]

@[simp] theorem coordinateUnknotCircle_other (i : Fin 2) (u : Circle) :
    coordinateUnknotCircle i u i.rev = 0 := by
  fin_cases i <;> simp [coordinateUnknotCircle]

theorem coordinateUnknotCircle_norm (i : Fin 2) (u : Circle) :
    ‖coordinateUnknotCircle i u‖ = 1 := by
  rw [coordinateUnknotCircle_eq_solidTorus]
  exact planeSolidTorusMap_norm i _

/-- There are no adjacent generators on one strand, so every such positive word is empty. -/
theorem positiveAdjacentWord_one_eq_nil (w : PositiveAdjacentWord 1) : w = [] := by
  cases w with
  | nil => rfl
  | cons i w => exact Fin.elim0 i

/-- The canonical height of the one-strand word is identically zero. -/
theorem positiveGridWord_one_strand_zero (w : PositiveAdjacentWord 1) (k : Fin 1) (t : ℝ) :
    positiveGridWord w k t = 0 := by
  rw [positiveAdjacentWord_one_eq_nil w]
  have hk : k = 0 := Subsingleton.elim _ _
  simp [positiveGridWord, positiveWordReal, positiveGridWordImaginary, hk]

/-- The event/gap canonical model is also literally zero for one strand, independently
of its finite indexing or event times. -/
theorem positiveGridGlobalWordModel_one_strand_zero {N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin 1)) (w : Fin N → PositiveAdjacentWord 1)
    (k : Fin 1) (t : ℝ) : positiveGridGlobalWordModel left right σ w k t = 0 := by
  simp [positiveGridGlobalWordModel, positiveGridEventPath,
    positiveGridWord_one_strand_zero]

/-- The exact circle height obtained by descending a one-strand canonical model is zero. -/
theorem one_strand_circle_height_eq_zero {N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin 1)) (w : Fin N → PositiveAdjacentWord 1)
    (b : ℝ) (height : Circle → ℂ)
    (heq : ∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
      height (braidCircleSheet 1 k θ) = positiveGridGlobalWordModel left right σ w k θ) :
    height = fun _ => 0 := by
  funext u
  obtain ⟨θ, hθ, hu⟩ := exists_circle_angle_in_period b u
  have hs : braidCircleSheet 1 0 θ = u := by simpa [braidCircleSheet] using hu
  rw [← hs, heq 0 θ hθ, positiveGridGlobalWordModel_one_strand_zero]

/-- Every smooth one-strand solid-torus graph is ambiently diffeotopic to the explicit
coordinate great circle. The fibre-separation condition is automatic in degree one. -/
theorem exists_one_strand_coordinate_unknot_diffeotopy
    (i : Fin 2) {height : Circle → ℂ}
    (hh : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ height) :
    ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
      (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u, height u)) ∧
      (∀ u, (L₁ u : EuclideanSpace ℂ (Fin 2)) = coordinateUnknotCircle i u) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ u, Φ.final (L₀ u) = L₁ u := by
  obtain ⟨L₀, L₁, h₀, h₁, Φ, hΦ⟩ :=
    exists_planeBraidConvex_endpoint_diffeotopy i (a := 1) zero_lt_one
      hh (contMDiff_const (c := (0 : ℂ))) (fun u v hne hp => by
        exact (hne (by simpa only [pow_one] using hp)).elim)
  refine ⟨L₀, L₁, ?_, ?_, Φ, hΦ⟩
  · intro u
    simpa only [pow_one] using h₀ u
  · intro u
    simpa only [pow_one, ← coordinateUnknotCircle_eq_solidTorus] using h₁ u

/-- The coordinate great circle is itself a native smooth embedding into the unit sphere. -/
theorem exists_coordinateUnknotCircle_smoothEmbedding (i : Fin 2) :
    ∃ L : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      ∀ u, (L u : EuclideanSpace ℂ (Fin 2)) = coordinateUnknotCircle i u := by
  obtain ⟨_, L, _, hL, _⟩ := exists_one_strand_coordinate_unknot_diffeotopy i
    (contMDiff_const (c := (0 : ℂ)))
  exact ⟨L, hL⟩

end OnLeConjecture.KnotTheory
