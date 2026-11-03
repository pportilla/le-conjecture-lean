/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeRestriction
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Polynomial homology images under Laurent maps

A Laurent chain map preserving the polynomial lattice preserves its homology
image. A Laurent homotopy equivalence whose two maps have zero first-coordinate
shift therefore gives a linear equivalence of the polynomial homology images.
No dimension, tower or homotopy-filtration hypothesis is needed.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n k : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (H : GridDiagram k) (a : Fin n) (b : Fin k)

/-- Restriction and coefficient inclusion commute on native homology. -/
theorem polynomialLatticeRestrictMap_homology_comm
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R)
    (hφ : ∀ m x, x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom →
      φ.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom) (m : ℤ) :
    homologyMap (polynomialLatticeRestrictMap R G H a b φ hφ) m ≫
        homologyMap (polynomialLatticeInclusion R H b) m =
      homologyMap (polynomialLatticeInclusion R G a) m ≫ homologyMap φ m := by
  rw [← homologyMap_comp, ← homologyMap_comp, polynomialLatticeRestrictMap_comm]

/-- A map preserving the polynomial chains preserves their image in Laurent homology. -/
theorem polynomialHomologyImage_map_le
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R)
    (hφ : ∀ m x, x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom →
      φ.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom) (m : ℤ) :
    (polynomialHomologyImage R G a m).map (homologyMap φ m).hom ≤
      polynomialHomologyImage R H b m := by
  unfold polynomialHomologyImage
  rw [← LinearMap.range_comp]
  have hc := congrArg (fun f => f.hom) (polynomialLatticeRestrictMap_homology_comm R G H a b φ hφ m)
  change (homologyMap (polynomialLatticeInclusion R H b) m).hom.comp
      (homologyMap (polynomialLatticeRestrictMap R G H a b φ hφ) m).hom =
      (homologyMap φ m).hom.comp (homologyMap (polynomialLatticeInclusion R G a) m).hom at hc
  rw [← hc]
  exact LinearMap.range_comp_le_range _ _

/-- The zero first-coordinate shift suffices for preservation on homology. -/
theorem polynomialHomologyImage_map_le_of_shifts
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R) (s : ℝ)
    (hφ : (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R) φ 0 s) (m : ℤ) :
    (polynomialHomologyImage R G a m).map (homologyMap φ m).hom ≤
      polynomialHomologyImage R H b m :=
  polynomialHomologyImage_map_le R G H a b φ
    (polynomialLattice_preserved_of_shifts R G H a b φ s hφ) m

/-- A Laurent homotopy equivalence with both maps preserving the lattice maps its homology image
onto the target image. No restriction of its homotopies is needed for this conclusion. -/
theorem polynomialHomologyImage_map_eq_of_homotopyEquiv
    (e : HomotopyEquiv (laurentMaslovComplex G R) (laurentMaslovComplex H R))
    (he : ∀ m x, x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom →
      e.hom.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom)
    (hei : ∀ m x, x ∈ LinearMap.range ((polynomialLatticeInclusion R H b).f m).hom →
      e.inv.f m x ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom) (m : ℤ) :
    (polynomialHomologyImage R G a m).map (homologyMap e.hom m).hom =
      polynomialHomologyImage R H b m := by
  apply le_antisymm (polynomialHomologyImage_map_le R G H a b e.hom he m)
  intro ξ hξ
  refine ⟨homologyMap e.inv m ξ, ?_, ?_⟩
  · exact polynomialHomologyImage_map_le R H G b a e.inv hei m ⟨ξ, hξ, rfl⟩
  · exact congrArg (fun f : (laurentMaslovComplex H R).homology m ⟶
      (laurentMaslovComplex H R).homology m => f ξ) (e.toHomologyIso m).inv_hom_id

/-- Zero first shifts in both directions give exact transport of the polynomial homology image. -/
theorem polynomialHomologyImage_map_eq_of_shifted_homotopyEquiv
    (e : HomotopyEquiv (laurentMaslovComplex G R) (laurentMaslovComplex H R))
    (s t : ℝ)
    (he : (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R) e.hom 0 s)
    (hei : (laurentMaslovBifiltration H R).Shifts (laurentMaslovBifiltration G R) e.inv 0 t)
    (m : ℤ) :
    (polynomialHomologyImage R G a m).map (homologyMap e.hom m).hom =
      polynomialHomologyImage R H b m :=
  polynomialHomologyImage_map_eq_of_homotopyEquiv R G H a b e
    (polynomialLattice_preserved_of_shifts R G H a b e.hom s he)
    (polynomialLattice_preserved_of_shifts R H G b a e.inv t hei) m

/-- The homology isomorphism restricts to a genuine linear equivalence of polynomial images. -/
def polynomialHomologyImageEquivOfShiftedHomotopyEquiv
    (e : HomotopyEquiv (laurentMaslovComplex G R) (laurentMaslovComplex H R))
    (s t : ℝ)
    (he : (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R) e.hom 0 s)
    (hei : (laurentMaslovBifiltration H R).Shifts (laurentMaslovBifiltration G R) e.inv 0 t)
    (m : ℤ) :
    polynomialHomologyImage R G a m ≃ₗ[R] polynomialHomologyImage R H b m :=
  (e.toHomologyIso m).toLinearEquiv.ofSubmodules _ _
    (polynomialHomologyImage_map_eq_of_shifted_homotopyEquiv R G H a b e s t he hei m)

/-- The restricted equivalence acts by the given Laurent homology map. -/
theorem polynomialHomologyImageEquivOfShiftedHomotopyEquiv_apply
    (e : HomotopyEquiv (laurentMaslovComplex G R) (laurentMaslovComplex H R))
    (s t : ℝ)
    (he : (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R) e.hom 0 s)
    (hei : (laurentMaslovBifiltration H R).Shifts (laurentMaslovBifiltration G R) e.inv 0 t)
    (m : ℤ) (ξ : polynomialHomologyImage R G a m) :
    (polynomialHomologyImageEquivOfShiftedHomotopyEquiv R G H a b e s t he hei m ξ :
      (laurentMaslovComplex H R).homology m) = homologyMap e.hom m ξ := rfl

end OnLeConjecture.KnotFloer.GridFull
