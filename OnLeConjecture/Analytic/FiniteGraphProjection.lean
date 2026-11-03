/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PreparedFiniteProjection
public import OnLeConjecture.Analytic.FiniteImageZeroSet
public import OnLeConjecture.Analytic.FiniteCoordinatePreparedEquation

/-!
# Equations for an analytic plane image from prepared coordinate relations

The graph equations, together with monic equations for both source
coordinates, permit two successive prepared projections. Their resultant
equations describe the actual image of a sufficiently small closed ball.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open LocalComplexGeometry

/-- Extract the base coordinates before the two appended coordinates. -/
noncomputable def graphBaseCLM (n : ℕ) : ComplexEuclidean (n + 1 + 1) →L[ℂ] Source n :=
  (dropLastCLM n).comp (dropLastCLM (n + 1))

/-- Extract the final two coordinates as a plane point. -/
noncomputable def graphSourceCLM (n : ℕ) : ComplexEuclidean (n + 1 + 1) →L[ℂ] Source 2 :=
  ContinuousLinearMap.pi fun j : Fin 2 =>
    if j = 0 then (lastCoordinateCLM n).comp (dropLastCLM (n + 1))
    else lastCoordinateCLM (n + 1)

@[simp]
theorem graphBaseCLM_appendTwoCoordinates (n : ℕ) (z : Source n) (u v : ℂ) :
    graphBaseCLM n (appendTwoCoordinates n z u v) = z := by
  simp only [graphBaseCLM, ContinuousLinearMap.comp_apply, appendTwoCoordinates,
    dropLastCLM_appendLastCLE]

@[simp]
theorem graphSourceCLM_appendTwoCoordinates (n : ℕ) (z : Source n) (u v : ℂ) :
    graphSourceCLM n (appendTwoCoordinates n z u v) = ![u, v] := by
  ext j
  fin_cases j
  · change lastCoordinateCLM n (dropLastCLM (n + 1)
      (appendTwoCoordinates n z u v)) = u
    simp only [appendTwoCoordinates, dropLastCLM_appendLastCLE, lastCoordinateCLM_appendLastCLE]
  · change lastCoordinateCLM (n + 1) (appendTwoCoordinates n z u v) = v
    exact lastCoordinateCLM_appendLastCLE (n + 1) _ _

/-- Two prepared coordinate relations yield finite analytic equations for
the image of a closed source ball. The ball can be confined in any prescribed
source neighborhood. -/
theorem exists_image_equations_of_prepared_coordinates
    {m d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (a₁ : Fin d₁ → Source m → ℂ) (a₂ : Fin d₂ → Source m → ℂ)
    (ha₁ : ∀ i, AnalyticAt ℂ (a₁ i) 0) (ha₁0 : ∀ i, a₁ i 0 = 0)
    (ha₂ : ∀ i, AnalyticAt ℂ (a₂ i) 0) (ha₂0 : ∀ i, a₂ i 0 = 0)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0)
    (hcoord₁ : ∀ᶠ x in 𝓝 0, preparedValue a₁ (G x) (x 0) = 0)
    (hcoord₂ : ∀ᶠ x in 𝓝 0, preparedValue a₂ (G x) (x 1) = 0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) :
    ∃ (r : ℝ) (s : ℕ) (E : Fin s → Source m → ℂ),
      0 < r ∧ closedBall (0 : Source 2) r ⊆ S ∧
      AnalyticOnNhd ℂ G (closedBall 0 r) ∧
      (∀ k, AnalyticAt ℂ (E k) 0) ∧
      ∀ᶠ y in 𝓝 0,
        (∀ k, E k y = 0) ↔ ∃ x ∈ closedBall (0 : Source 2) r, G x = y := by
  let H (j : Fin m) (z : ComplexEuclidean (m + 1 + 1)) :=
    G (graphSourceCLM m z) j - graphBaseCLM m z j
  have hH (j : Fin m) : AnalyticAt ℂ (H j) 0 := by
    have hcomp : AnalyticAt ℂ (fun z => G (graphSourceCLM m z)) 0 := by
      apply hG.comp_of_eq ((graphSourceCLM m).analyticAt 0)
      exact map_zero _
    exact (((ContinuousLinearMap.proj (R := ℂ) j).analyticAt _).comp hcomp).sub
      (((ContinuousLinearMap.proj (R := ℂ) j).comp (graphBaseCLM m)).analyticAt 0)
  obtain ⟨E, hE, hprojection⟩ :=
    exists_analytic_equations_for_two_prepared_projections hd₁ hd₂ a₁ a₂
      ha₁ ha₁0 ha₂ ha₂0 H hH
  obtain ⟨r, hr, hrsub⟩ := nhds_basis_closedBall.mem_iff.mp
    (inter_mem hS (hG.eventually_analyticAt.and (hcoord₁.and hcoord₂)))
  let K := closedBall (0 : Source 2) r
  let V := (graphSourceCLM m) ⁻¹' K
  have hV : V ∈ 𝓝 (0 : ComplexEuclidean (m + 1 + 1)) := by
    apply (graphSourceCLM m).continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using closedBall_mem_nhds (0 : Source 2) hr
  refine ⟨r, d₁ * (d₂ * m + 1) + 1, E, hr,
    fun x hx => (hrsub hx).1, fun x hx => (hrsub hx).2.1, hE, ?_⟩
  filter_upwards [hprojection V hV, hprojection Set.univ (Filter.univ_mem)] with y hyV hyAll
  constructor
  · intro hyE
    obtain ⟨u, v, huv, _, _, hzero⟩ := hyV.mp hyE
    refine ⟨![u, v], ?_, ?_⟩
    · simpa only [V, Set.mem_preimage, graphSourceCLM_appendTwoCoordinates, K] using huv
    · ext j
      have hj := hzero j
      simpa only [H, graphSourceCLM_appendTwoCoordinates,
        graphBaseCLM_appendTwoCoordinates, sub_eq_zero] using hj
  · rintro ⟨x, hx, rfl⟩
    apply hyAll.mpr
    refine ⟨x 0, x 1, Set.mem_univ _, (hrsub hx).2.2.1, (hrsub hx).2.2.2, ?_⟩
    intro j
    have hvec : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
    simp only [H, graphSourceCLM_appendTwoCoordinates, hvec,
      graphBaseCLM_appendTwoCoordinates, sub_self]

namespace PointedMapGerm

/-- The image of a finite plane germ has finitely many analytic equations
on representatives. These equations describe the image of a closed ball,
and the ball can be chosen inside any specified source neighborhood. -/
theorem exists_closedBall_image_equations_of_finite
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) :
    ∃ (r : ℝ) (s : ℕ) (E : Fin s → Source m → ℂ),
      0 < r ∧ closedBall (0 : Source 2) r ⊆ S ∧
      AnalyticOnNhd ℂ G (closedBall 0 r) ∧
      (∀ k, AnalyticAt ℂ (E k) 0) ∧
      ∀ᶠ y in 𝓝 0,
        (∀ k, E k y = 0) ↔ ∃ x ∈ closedBall (0 : Source 2) r, G x = y := by
  obtain ⟨d₁, hd₁, a₁, ha₁, ha₁0, hcoord₁⟩ :=
    g.exists_coordinate_prepared_equation_of_finite hf G hG hG0 hg 0
  obtain ⟨d₂, hd₂, a₂, ha₂, ha₂0, hcoord₂⟩ :=
    g.exists_coordinate_prepared_equation_of_finite hf G hG hG0 hg 1
  exact exists_image_equations_of_prepared_coordinates hd₁ hd₂ a₁ a₂ ha₁ ha₁0 ha₂ ha₂0
    G hG hcoord₁ hcoord₂ S hS

end PointedMapGerm

end OnLeConjecture.Analytic
