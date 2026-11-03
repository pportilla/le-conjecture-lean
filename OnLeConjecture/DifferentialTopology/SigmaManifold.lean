/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Geometry.Manifold.Instances.Sigma
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Differential calculus on disjoint unions of manifolds

The common chart model gives a smooth manifold structure on an indexed
disjoint union. Smoothness and derivatives of maps out of the union are
computed on each component. The product version assembles motions of
finitely many link components into a motion of their disjoint union.
-/

public noncomputable section

open Set Filter Function Topology Manifold
open scoped ContDiff Manifold Topology

namespace OnLeConjecture.DifferentialTopology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {ι : Type*} {M : ι → Type*}
  [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)] {n : ℕ∞ω}

/-- Disjoint unions inherit the smooth structure of their components. -/
instance sigmaIsManifold [hM : ∀ i, IsManifold I n (M i)] :
    IsManifold I n (Σ i, M i) where
  compatible {e} e' he he' := by
    classical
    obtain (h | h) := isEmpty_or_nonempty H
    · exact ContDiffGroupoid.mem_of_source_eq_empty _ (eq_empty_of_isEmpty _)
    obtain ⟨i, f, hf, rfl⟩ := ChartedSpace.mem_atlas_sigma he
    obtain ⟨j, g, hg, rfl⟩ := ChartedSpace.mem_atlas_sigma he'
    by_cases hij : i = j
    · subst j
      rw [f.lift_openEmbedding_trans g IsOpenEmbedding.sigmaMk]
      exact (hM i).compatible hf hg
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext x
      constructor
      · rintro ⟨hx, y, hy, heq⟩
        exact hij (congrArg Sigma.fst heq).symm
      · intro hx
        exact hx.elim

/-- The inverse chart of a disjoint union stays in its component. -/
@[simp, mfld_simps]
theorem sigma_extChartAt_symm {i : ι} (x : M i) (y : E) :
    (extChartAt I (⟨i, x⟩ : Σ i, M i)).symm y =
      ⟨i, (extChartAt I x).symm y⟩ := by
  simp only [extChartAt, ChartedSpace.sigma_chartAt]
  rfl

/-- Extended charts agree with the component chart. -/
@[simp, mfld_simps]
theorem sigma_extChartAt_apply {i : ι} (x y : M i) :
    extChartAt I (⟨i, x⟩ : Σ i, M i) ⟨i, y⟩ = extChartAt I x y := by
  simp [extChartAt]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- Smoothness at a point is exactly smoothness on its component. -/
theorem contMDiffAt_sigma_iff {f : (Σ i, M i) → N} {i : ι} {x : M i} :
    ContMDiffAt I J n f ⟨i, x⟩ ↔
      ContMDiffAt I J n (fun y => f ⟨i, y⟩) x := by
  rw [contMDiffAt_iff_source, contMDiffAt_iff_source]
  simp only [sigma_extChartAt_apply, sigma_extChartAt_symm, comp_def]

/-- Smooth maps from the components assemble to a smooth map. -/
theorem contMDiff_sigma_iff {f : (Σ i, M i) → N} :
    ContMDiff I J n f ↔ ∀ i, ContMDiff I J n (fun y => f ⟨i, y⟩) := by
  constructor
  · intro h i x
    exact contMDiffAt_sigma_iff.mp (h ⟨i, x⟩)
  · intro h ⟨i, x⟩
    exact contMDiffAt_sigma_iff.mpr (h i x)

/-- Differentiability at a point is computed in that component. -/
theorem mdifferentiableAt_sigma_iff {f : (Σ i, M i) → N} {i : ι} {x : M i} :
    MDifferentiableAt I J f ⟨i, x⟩ ↔
      MDifferentiableAt I J (fun y => f ⟨i, y⟩) x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff]
  simp only [writtenInExtChartAt, sigma_extChartAt_apply, sigma_extChartAt_symm, comp_def]
  exact and_congr IsOpenEmbedding.sigmaMk.continuousAt_iff.symm Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of an assembled map equals the derivative on the component. -/
theorem mfderiv_sigma {f : (Σ i, M i) → N} {i : ι} {x : M i} :
    (mfderiv I J f ⟨i, x⟩ : E →L[𝕜] E') =
      mfderiv I J (fun y => f ⟨i, y⟩) x := by
  have hd := mdifferentiableAt_sigma_iff (I := I) (J := J) (f := f) (x := x)
  by_cases h : MDifferentiableAt I J (fun y => f ⟨i, y⟩) x
  · rw [mfderiv, if_pos (hd.mpr h), mfderiv, if_pos h]
    simp only [writtenInExtChartAt, sigma_extChartAt_apply, sigma_extChartAt_symm, comp_def]
  · rw [mfderiv, if_neg (mt hd.mp h), mfderiv, if_neg h]

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {L : ModelWithCorners 𝕜 E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- Joint smoothness of a family is checked separately on every component. -/
theorem contMDiffAt_sigma_prod_iff {f : (Σ i, M i) × P → N} {i : ι}
    {x : M i} {p : P} :
    ContMDiffAt (I.prod L) J n f (⟨i, x⟩, p) ↔
      ContMDiffAt (I.prod L) J n (fun q : M i × P => f (⟨i, q.1⟩, q.2)) (x, p) := by
  rw [contMDiffAt_iff_source, contMDiffAt_iff_source]
  simp only [extChartAt_prod, PartialEquiv.prod_coe, PartialEquiv.prod_coe_symm,
    sigma_extChartAt_apply, sigma_extChartAt_symm, comp_def]

end OnLeConjecture.DifferentialTopology
