/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionFloerReduction
public import OnLeConjecture.KnotFloer.GridCanonicalTensorClass

/-!
# The assembled comparison with canonical grid classes

The branch cycles are now constructed from their unique normalized
classes. A geometric construction only needs to supply the diagrams,
the map with its filtration estimate and canonical-class identity,
the factor lower bounds, and the strict-range torus representative.
The cycle representatives and the genus identity are filled internally.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open TauCeti CategoryTheory HomologicalComplex
open KnotFloer KnotFloer.GridFull KnotFloer.Staircase

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}
  (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A)

/-- Canonical normalized classes supply the cycle fields of the existing
comparison. The remaining map, spectral bounds and strict-range source
representative are explicit construction obligations. -/
def ResolutionSectionFloerData.ofCanonicalClasses
    (sizes : Fin L.points.card → ℕ) (diagrams : ∀ j, GridDiagram (sizes j))
    (hn : ∀ j, 2 ≤ sizes j)
    (map : laurentMaslovComplex (reflectedTorusGrid (A.squareSum - 1)) (ZMod 2) ⟶
      laurentFiniteMaslovComplex (K := ZMod 2) diagrams)
    (shift : (laurentMaslovBifiltration (reflectedTorusGrid (A.squareSum - 1))
      (ZMod 2)).Shifts (laurentFiniteMaslovBifiltration diagrams) map 0
        (A.candidateGenus : ℝ))
    (second : 2 * (g.criticalJacobianFactorization hi).maxMultiplicity < A.squareSum →
      ((laurentMaslovBifiltration (reflectedTorusGrid (A.squareSum - 1)) (ZMod 2)).weighted
        (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))).RepresentedBelow 0
        (reflectedTorusAnchorClass (A.squareSum - 1) (ZMod 2))
        (consecutiveWeight (A.squareSum - 1)
          (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))
          ⟨2, by have := A.tree.four_le_square_sum_of_differential_eq_zero hd
                 change 2 < (∑ p, (A.tree.multiplicity p) ^ 2) - 1 + 1
                 omega⟩))
    (lower : ∀ j,
      ((L.genera j * (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ)) / 2 : ℝ) :
          EReal) ≤
        ((laurentMaslovBifiltration (diagrams j) (ZMod 2)).weighted
          (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))).spectralThreshold 0
          (gridCanonicalClass (diagrams j) (hn j)))
    (mapClass : homologyMap map 0 (reflectedTorusAnchorClass (A.squareSum - 1) (ZMod 2)) =
      gridCanonicalFiniteTensorClass diagrams hn) :
    ResolutionSectionFloerData A L where
  sizes := sizes
  diagrams := diagrams
  map := map
  shift := shift
  secondRepresentative := second
  cycles := fun j => gridCanonicalCycle (diagrams j) (hn j)
  lowerBounds := by
    intro j
    rw [gridCanonicalCycle_class]
    exact lower j
  mapClass := mapClass

end OnLeConjecture.Analytic
