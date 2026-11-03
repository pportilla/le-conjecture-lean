/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionAssembly
public import OnLeConjecture.Analytic.CriticalJacobianFloerReduction

/-!
# The Floer comparison for the assembled analytic sections

A nonzero nearby level of the analytic assembly supplies its finite set of
singular image branches and their delta invariants. These numbers, the assembly's
resolution tree, and its candidate genus fix the numerical parameters of the
remaining grid comparison. Its genus identity follows from the proved analytic
assembly and is not an additional Floer hypothesis.

The existence of the grid maps and spectral estimates remains a construction
obligation. In particular, no assertion here identifies the candidate genus with
the genus of a geometric cobordism.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.Analytic

open Filter Metric Set TauCeti CategoryTheory HomologicalComplex
open KnotFloer KnotFloer.GridFull KnotFloer.Staircase
open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve
open scoped Topology

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- One genuine nearby nonzero section level, with the properties supplied by
`ResolutionSectionAssembly.levels`. -/
structure ResolutionSectionLevel (A : ResolutionSectionAssembly g hd hi) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ A.radius
  parameter : ℂ
  parameter_ne_zero : parameter ≠ 0
  points : Finset (Source 2)
  points_iff : ∀ x, x ∈ points ↔ x ∈ ball (0 : Source 2) radius ∧
    A.H x 0 = parameter ∧ ¬ Function.Injective (fderiv ℂ A.H x)
  card_eq : points.card = A.count
  injective : InjOn A.H (ball (0 : Source 2) radius)
  closedEmbedding : Topology.IsClosedEmbedding
    ((closedBall (0 : Source 2) radius ∩ (fun x => A.H x 0) ⁻¹' {parameter}).domRestrict A.H)
  regular : ∀ x ∈ ball (0 : Source 2) radius, A.H x 0 = parameter →
    fderiv ℂ (fun y => A.H y 0) x ≠ 0 ∧
      (localSectionEquation A.H x ∈ Germ.maximalIdeal 2 ^ 2 ↔ x ∈ points)
  singular : ∀ x ∈ points,
    SingularSectionPointData A.H x (g.criticalJacobianFactorization hi).maxMultiplicity
  delta_sum : ∑ x ∈ points, deltaInvariant (localSectionEquation A.H x) = A.singularDelta

namespace ResolutionSectionAssembly

/-- Every permitted radius has a genuine nonzero level with the assembled local data. -/
theorem exists_level_at_radius (A : ResolutionSectionAssembly g hd hi)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ A.radius) :
    ∃ L : ResolutionSectionLevel A, L.radius = r := by
  have hlevels := (A.levels r hr hle).filter_mono
    (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs
  obtain ⟨s, hs, hsne⟩ := (hlevels.and hne).exists
  obtain ⟨Z, hZ, hcard, hinj, hembed, hregular, hsingular, hsum⟩ := hs hsne
  exact ⟨⟨r, hr, hle, s, hsne, Z, hZ, hcard, hinj, hembed, hregular, hsingular, hsum⟩, rfl⟩

/-- The analytic assembly supplies a nearby nonzero level without additional hypotheses. -/
theorem exists_level (A : ResolutionSectionAssembly g hd hi) :
    Nonempty (ResolutionSectionLevel A) := by
  obtain ⟨L, -⟩ := A.exists_level_at_radius A.radius A.radius_pos le_rfl
  exact ⟨L⟩

end ResolutionSectionAssembly

namespace ResolutionSectionLevel

variable {A : ResolutionSectionAssembly g hd hi} (L : ResolutionSectionLevel A)

/-- The singular points are indexed by the finite set actually occurring on this level. -/
def point (j : Fin L.points.card) : Source 2 := L.points.equivFin.symm j

/-- The local genera in the Floer comparison are the actual section delta invariants. -/
def genera (j : Fin L.points.card) : ℝ := deltaInvariant (localSectionEquation A.H (L.point j))

theorem genera_sum : ∑ j, L.genera j = (A.localGenus : ℝ) := by
  unfold genera point
  rw [Equiv.sum_comp L.points.equivFin.symm
    (fun x : L.points => (deltaInvariant (localSectionEquation A.H x) : ℝ))]
  rw [Finset.sum_coe_sort L.points (fun x => (deltaInvariant (localSectionEquation A.H x) : ℝ))]
  rw [ResolutionSectionAssembly.localGenus, ← L.delta_sum]
  push_cast
  rfl

/-- The numerical identity required by the Floer estimate follows from this actual level. -/
theorem genusIdentity :
    (((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) *
        ((((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) / 2 -
      (∑ j, L.genera j) + (A.candidateGenus : ℝ) =
        ((((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) -
          ((∑ p, A.tree.multiplicity p : ℕ) : ℝ) :=
  A.genusIdentity_real L.genera L.genera_sum

end ResolutionSectionLevel

/-- The remaining grid construction for one assembled section level. All numerical
parameters are fixed by the analytic data. Its existence is proved by
`exists_resolutionSectionFloerData_of_nativeRouteInputs` (see `LeConjectureNative.lean`). -/
structure ResolutionSectionFloerData (A : ResolutionSectionAssembly g hd hi)
    (L : ResolutionSectionLevel A) where
  sizes : Fin L.points.card → ℕ
  diagrams : ∀ j, GridDiagram (sizes j)
  map : laurentMaslovComplex (reflectedTorusGrid (A.squareSum - 1)) (ZMod 2) ⟶
    laurentFiniteMaslovComplex (K := ZMod 2) diagrams
  shift : (laurentMaslovBifiltration (reflectedTorusGrid (A.squareSum - 1)) (ZMod 2)).Shifts
    (laurentFiniteMaslovBifiltration diagrams) map 0 (A.candidateGenus : ℝ)
  secondRepresentative :
    2 * (g.criticalJacobianFactorization hi).maxMultiplicity < A.squareSum →
    ((laurentMaslovBifiltration (reflectedTorusGrid (A.squareSum - 1)) (ZMod 2)).weighted
      (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))).RepresentedBelow 0
    (reflectedTorusAnchorClass (A.squareSum - 1) (ZMod 2))
    (consecutiveWeight (A.squareSum - 1)
      (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))
      ⟨2, by have := A.tree.four_le_square_sum_of_differential_eq_zero hd
             change 2 < (∑ p, (A.tree.multiplicity p) ^ 2) - 1 + 1
             omega⟩)
  cycles : ∀ j, (laurentMaslovComplex (diagrams j) (ZMod 2)).cycles 0
  lowerBounds : ∀ j,
    ((L.genera j * (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ)) / 2 : ℝ) :
        EReal) ≤
      ((laurentMaslovBifiltration (diagrams j) (ZMod 2)).weighted
        (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))).spectralThreshold 0
        ((laurentMaslovComplex (diagrams j) (ZMod 2)).homologyπ 0 (cycles j))
  mapClass : homologyMap map 0 (reflectedTorusAnchorClass (A.squareSum - 1) (ZMod 2)) =
    laurentFiniteNativeClass diagrams cycles

namespace ResolutionSectionFloerData

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  (D : ResolutionSectionFloerData A L)

/-- The genus identity is proved internally when passing to the existing Floer reduction. -/
def toCriticalJacobianFloerData : CriticalJacobianFloerData g hd hi A.tree where
  count := L.points.card
  sizes := D.sizes
  diagrams := D.diagrams
  cobordismGenus := A.candidateGenus
  genera := L.genera
  map := D.map
  shift := D.shift
  secondRepresentative := D.secondRepresentative
  cycles := D.cycles
  lowerBounds := D.lowerBounds
  mapClass := D.mapClass
  genusIdentity := L.genusIdentity

include D in
/-- The remaining grid construction yields the exact two canonical critical-divisor bounds. -/
theorem criticalJacobian_bounds :
    (∑ p, A.tree.multiplicity p) ≤ (g.criticalJacobianFactorization hi).maxMultiplicity ∧
      (∑ p, (A.tree.multiplicity p) ^ 2) + (∑ p, A.tree.multiplicity p) ≤
        3 * (g.criticalJacobianFactorization hi).maxMultiplicity :=
  criticalJacobian_bounds_of_floer_data g hd hi A.tree D.toCriticalJacobianFloerData

end ResolutionSectionFloerData
end OnLeConjecture.Analytic

namespace OnLeConjecture
open Analytic

/-- A grid construction on one assembled level for each germ suffices for the conjecture.
No independently supplied genus identity occurs in this hypothesis. -/
theorem leConjecture_of_resolutionSection_floer_data
    (hdata : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative),
        ∃ (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A),
          Nonempty (ResolutionSectionFloerData A L)) : LeConjecture := by
  apply leConjecture_of_criticalJacobian_floer_data
  intro g hd hi
  obtain ⟨A, L, ⟨D⟩⟩ := hdata g hd hi
  exact ⟨A.tree, ⟨D.toCriticalJacobianFloerData⟩⟩

/-- The analytic assembly can be chosen internally before constructing a Floer comparison
on one of its actual nearby levels. -/
theorem leConjecture_of_resolutionSection_floer_construction
    (hconstruct : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative) (A : ResolutionSectionAssembly g hd hi),
        ∃ L : ResolutionSectionLevel A, Nonempty (ResolutionSectionFloerData A L)) :
    LeConjecture := by
  apply leConjecture_of_resolutionSection_floer_data
  intro g hd hi
  obtain ⟨A⟩ := g.exists_resolutionSectionAssembly hd hi
  obtain ⟨L, hL⟩ := hconstruct g hd hi A
  exact ⟨A, L, hL⟩

end OnLeConjecture
