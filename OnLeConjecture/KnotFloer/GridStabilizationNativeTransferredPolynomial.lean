/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationNativeTransferred
public import OnLeConjecture.KnotFloer.PolynomialLatticeMap

/-!
# Polynomial homology under the transferred stabilization equivalence

The full stabilization inclusion and projection preserve the first filtration
coordinate. They therefore restrict to the polynomial complexes and transport
their homology images. The target carries its constructed transferred
differential. No identification with the old grid differential is used.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (s a : Fin n) (b : Fin (n + 1))

/-- The constructed native projection preserves the polynomial coefficient lattice. -/
theorem stabilizationTransferredNativeProjection_preserves_polynomial :
    PolynomialLattice.Preserves
      (polynomialLatticeInclusion R (G.stabilizeX s.castSucc (G.X s).castSucc s) b)
      (stabilizationTransferredPolynomialInclusion R G s a)
      (stabilizationTransferredNativeProjection R G s) := by
  intro m x hx
  obtain ⟨B, hB⟩ := (mem_polynomialLattice_iff_exists_zero_level R _ b m x).mp hx
  apply (mem_range_stabilizationTransferredPolynomialInclusion_iff R G s a m _).mpr
  refine ⟨B, ?_⟩
  change (fullStabilizationTransferredRetraction G s R).proj x.val ∈ _
  exact fullStabilizationTransferredRetraction_proj_mem_bifiltrationLevel G s R hB

/-- The constructed native inclusion preserves the polynomial coefficient lattice. -/
theorem stabilizationTransferredNativeInclusion_preserves_polynomial :
    PolynomialLattice.Preserves
      (stabilizationTransferredPolynomialInclusion R G s a)
      (polynomialLatticeInclusion R (G.stabilizeX s.castSucc (G.X s).castSucc s) b)
      (stabilizationTransferredNativeInclusion R G s) := by
  intro m x hx
  obtain ⟨B, hB⟩ :=
    (mem_range_stabilizationTransferredPolynomialInclusion_iff R G s a m x).mp hx
  apply (mem_polynomialLattice_iff_exists_zero_level R _ b m _).mpr
  refine ⟨B, ?_⟩
  change (fullStabilizationTransferredRetraction G s R).incl
    (stabilizationNativePair R G m x) ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R 0 B
  exact fullStabilizationTransferredRetraction_incl_mem_bifiltrationLevel G s R hB

/-- The full projection restricts to the actual transferred polynomial complex. -/
def stabilizationTransferredPolynomialProjection :
    oneVariableMaslovComplex R (G.stabilizeX s.castSucc (G.X s).castSucc s) b ⟶
      stabilizationTransferredPolynomialComplex R G s a :=
  PolynomialLattice.restrictMap
    (polynomialLatticeInclusion R _ b)
    (stabilizationTransferredPolynomialInclusion R G s a)
    (stabilizationTransferredPolynomialInclusion_injective R G s a)
    (stabilizationTransferredNativeProjection R G s)
    (stabilizationTransferredNativeProjection_preserves_polynomial R G s a b)

/-- The full inclusion restricts from the actual transferred polynomial complex. -/
def stabilizationTransferredPolynomialInclusionMap :
    stabilizationTransferredPolynomialComplex R G s a ⟶
      oneVariableMaslovComplex R (G.stabilizeX s.castSucc (G.X s).castSucc s) b :=
  PolynomialLattice.restrictMap
    (stabilizationTransferredPolynomialInclusion R G s a)
    (polynomialLatticeInclusion R _ b)
    (polynomialLatticeInclusion_injective R _ b)
    (stabilizationTransferredNativeInclusion R G s)
    (stabilizationTransferredNativeInclusion_preserves_polynomial R G s a b)

/-- Inclusion of coefficients commutes with the restricted projection. -/
theorem stabilizationTransferredPolynomialProjection_comm :
    stabilizationTransferredPolynomialProjection R G s a b ≫
        stabilizationTransferredPolynomialInclusion R G s a =
      polynomialLatticeInclusion R _ b ≫ stabilizationTransferredNativeProjection R G s :=
  PolynomialLattice.restrictMap_comm _ _ _ _ _

/-- Inclusion of coefficients commutes with the restricted inclusion map. -/
theorem stabilizationTransferredPolynomialInclusionMap_comm :
    stabilizationTransferredPolynomialInclusionMap R G s a b ≫
        polynomialLatticeInclusion R _ b =
      stabilizationTransferredPolynomialInclusion R G s a ≫
        stabilizationTransferredNativeInclusion R G s :=
  PolynomialLattice.restrictMap_comm _ _ _ _ _

/-- Projection transports the polynomial homology image onto that of the actual target. -/
theorem stabilizationTransferredPolynomialHomologyImage_map (m : ℤ) :
    (polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m).map
        (homologyMap (stabilizationTransferredNativeProjection R G s) m).hom =
      stabilizationTransferredPolynomialHomologyImage R G s a m :=
  PolynomialLattice.homologyImage_map_eq
    (polynomialLatticeInclusion R _ b)
    (stabilizationTransferredPolynomialInclusion R G s a)
    (polynomialLatticeInclusion_injective R _ b)
    (stabilizationTransferredPolynomialInclusion_injective R G s a)
    (stabilizationTransferredNativeHomotopyEquiv R G s)
    (stabilizationTransferredNativeProjection_preserves_polynomial R G s a b)
    (stabilizationTransferredNativeInclusion_preserves_polynomial R G s a b) m

/-- The native homology equivalence restricts to the polynomial homology images. -/
def stabilizationTransferredPolynomialHomologyImageEquiv (m : ℤ) :
    polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m ≃ₗ[R]
      stabilizationTransferredPolynomialHomologyImage R G s a m :=
  PolynomialLattice.homologyImageEquiv
    (polynomialLatticeInclusion R _ b)
    (stabilizationTransferredPolynomialInclusion R G s a)
    (polynomialLatticeInclusion_injective R _ b)
    (stabilizationTransferredPolynomialInclusion_injective R G s a)
    (stabilizationTransferredNativeHomotopyEquiv R G s)
    (stabilizationTransferredNativeProjection_preserves_polynomial R G s a b)
    (stabilizationTransferredNativeInclusion_preserves_polynomial R G s a b) m

/-- The restricted equivalence acts by the constructed projection on homology. -/
theorem stabilizationTransferredPolynomialHomologyImageEquiv_apply (m : ℤ)
    (ξ : polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m) :
    (stabilizationTransferredPolynomialHomologyImageEquiv R G s a b m ξ :
      (stabilizationTransferredMaslovComplex R G s).homology m) =
        homologyMap (stabilizationTransferredNativeProjection R G s) m ξ := rfl

end OnLeConjecture.KnotFloer.GridFull
