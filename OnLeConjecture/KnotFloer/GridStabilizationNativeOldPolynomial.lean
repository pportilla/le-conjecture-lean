/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationNativeOld
public import OnLeConjecture.KnotFloer.GridStabilizationNativeTransferredPolynomial

/-!
# Polynomial homology images under full grid stabilization

The actual projection and inclusion preserve the polynomial lattices. After the
proved identification of the transferred differential, they identify the stabilized
polynomial homology image in degree m with the product of the old images in
degrees m and m+1.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (s a : Fin n) (b : Fin (n + 1))

/-- The actual projection to the old double preserves the polynomial lattice. -/
theorem stabilizationNativeOldProjection_preserves_polynomial :
    PolynomialLattice.Preserves
      (polynomialLatticeInclusion R (G.stabilizeX s.castSucc (G.X s).castSucc s) b)
      (polynomialDoubleInclusion R G a)
      (stabilizationNativeOldHomotopyEquiv R G s).hom :=
  stabilizationTransferredNativeProjection_preserves_polynomial R G s a b

/-- The actual inclusion from the old double preserves the polynomial lattice. -/
theorem stabilizationNativeOldInclusion_preserves_polynomial :
    PolynomialLattice.Preserves
      (polynomialDoubleInclusion R G a)
      (polynomialLatticeInclusion R (G.stabilizeX s.castSucc (G.X s).castSucc s) b)
      (stabilizationNativeOldHomotopyEquiv R G s).inv :=
  stabilizationTransferredNativeInclusion_preserves_polynomial R G s a b

/-- The constructed full projection restricts to the old doubled polynomial complex. -/
def stabilizationNativeOldPolynomialProjection :
    oneVariableMaslovComplex R (G.stabilizeX s.castSucc (G.X s).castSucc s) b ⟶
      shiftedDouble (oneVariableMaslovComplex R G a) :=
  PolynomialLattice.restrictMap (polynomialLatticeInclusion R _ b)
    (polynomialDoubleInclusion R G a) (polynomialDoubleInclusion_injective R G a)
    (stabilizationNativeOldHomotopyEquiv R G s).hom
    (stabilizationNativeOldProjection_preserves_polynomial R G s a b)

/-- The constructed full inclusion restricts from the old doubled polynomial complex. -/
def stabilizationNativeOldPolynomialInclusion :
    shiftedDouble (oneVariableMaslovComplex R G a) ⟶
      oneVariableMaslovComplex R (G.stabilizeX s.castSucc (G.X s).castSucc s) b :=
  PolynomialLattice.restrictMap (polynomialDoubleInclusion R G a)
    (polynomialLatticeInclusion R _ b) (polynomialLatticeInclusion_injective R _ b)
    (stabilizationNativeOldHomotopyEquiv R G s).inv
    (stabilizationNativeOldInclusion_preserves_polynomial R G s a b)

/-- Coefficient inclusion intertwines the polynomial and Laurent projection. -/
theorem stabilizationNativeOldPolynomialProjection_comm :
    stabilizationNativeOldPolynomialProjection R G s a b ≫ polynomialDoubleInclusion R G a =
      polynomialLatticeInclusion R _ b ≫ (stabilizationNativeOldHomotopyEquiv R G s).hom :=
  PolynomialLattice.restrictMap_comm _ _ _ _ _

/-- Coefficient inclusion intertwines the polynomial and Laurent inclusion. -/
theorem stabilizationNativeOldPolynomialInclusion_comm :
    stabilizationNativeOldPolynomialInclusion R G s a b ≫ polynomialLatticeInclusion R _ b =
      polynomialDoubleInclusion R G a ≫ (stabilizationNativeOldHomotopyEquiv R G s).inv :=
  PolynomialLattice.restrictMap_comm _ _ _ _ _

/-- The actual projection transports polynomial homology onto the old doubled image. -/
theorem stabilizationNativeOldPolynomialHomologyImage_map_double (m : ℤ) :
    (polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m).map
        (homologyMap (stabilizationNativeOldHomotopyEquiv R G s).hom m).hom =
      polynomialDoubleHomologyImage R G a m :=
  PolynomialLattice.homologyImage_map_eq
    (polynomialLatticeInclusion R _ b) (polynomialDoubleInclusion R G a)
    (polynomialLatticeInclusion_injective R _ b) (polynomialDoubleInclusion_injective R G a)
    (stabilizationNativeOldHomotopyEquiv R G s)
    (stabilizationNativeOldProjection_preserves_polynomial R G s a b)
    (stabilizationNativeOldInclusion_preserves_polynomial R G s a b) m

/-- The native homology splitting transports polynomial images in precisely degrees m and m+1. -/
theorem stabilizationNativeOldPolynomialHomologyImage_map (m : ℤ) :
    (polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m).map
        (stabilizationNativeOldHomologyEquiv R G s m).toLinearMap =
      (polynomialHomologyImage R G a m).prod (polynomialHomologyImage R G a (m + 1)) := by
  change (polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m).map
    ((polynomialDoubleHomologyEquiv R G m).toLinearMap.comp
      (homologyMap (stabilizationNativeOldHomotopyEquiv R G s).hom m).hom) = _
  rw [Submodule.map_comp, stabilizationNativeOldPolynomialHomologyImage_map_double,
    polynomialDoubleHomologyImage_map]

/-- Exact decomposition of the stabilized polynomial homology image into the two old images. -/
def stabilizationNativeOldPolynomialHomologyImageEquiv (m : ℤ) :
    polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m ≃ₗ[R]
      polynomialHomologyImage R G a m × polynomialHomologyImage R G a (m + 1) :=
  ((stabilizationNativeOldHomologyEquiv R G s m).ofSubmodules _ _
    (stabilizationNativeOldPolynomialHomologyImage_map R G s a b m)).trans
      { toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
        invFun x := ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }

/-- The image equivalence is the actual native homology splitting on underlying classes. -/
theorem stabilizationNativeOldPolynomialHomologyImageEquiv_apply (m : ℤ)
    (ξ : polynomialHomologyImage R (G.stabilizeX s.castSucc (G.X s).castSucc s) b m) :
    ((stabilizationNativeOldPolynomialHomologyImageEquiv R G s a b m ξ).1.val,
      (stabilizationNativeOldPolynomialHomologyImageEquiv R G s a b m ξ).2.val) =
        stabilizationNativeOldHomologyEquiv R G s m ξ := rfl

end OnLeConjecture.KnotFloer.GridFull
