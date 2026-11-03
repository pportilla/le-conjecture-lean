/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeNative

/-!
# The polynomial homology image under X-marking switches

The submodule is the image of polynomial homology under the constructed native
coefficient inclusion. The Laurent marking isomorphism maps it onto the same
submodule for the target diagram. These statements do not compute its dimension
or select a normalized nonzero class.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]

/-- The image of polynomial grid homology in Laurent grid homology. -/
def polynomialHomologyImage (G : GridDiagram n) (a : Fin n) (m : ℤ) :
    Submodule R ((laurentMaslovComplex G R).homology m) :=
  LinearMap.range (homologyMap (polynomialLatticeInclusion R G a) m).hom

variable {G H : GridDiagram n}

/-- Coefficient inclusion commutes with the two marking maps on homology. -/
theorem polynomialLattice_homology_marking (hO : G.O = H.O) (a b : Fin n) (m : ℤ) :
    homologyMap (polynomialLatticeInclusion R G a) m ≫
        homologyMap (laurentMaslovMarkingIso R hO).hom m =
      homologyMap (polynomialMaslovMarkingIso R hO a b).hom m ≫
        homologyMap (polynomialLatticeInclusion R H b) m := by
  rw [← homologyMap_comp, ← homologyMap_comp, polynomialLatticeInclusion_markingIso R hO a b]

/-- The Laurent marking isomorphism maps the polynomial homology image onto its target image. -/
theorem polynomialHomologyImage_map_markingIso (hO : G.O = H.O) (a b : Fin n) (m : ℤ) :
    (polynomialHomologyImage R G a m).map
      (homologyMap (laurentMaslovMarkingIso R hO).hom m).hom =
        polynomialHomologyImage R H b m := by
  unfold polynomialHomologyImage
  rw [← LinearMap.range_comp]
  have hcomm := congrArg (fun f => f.hom) (polynomialLattice_homology_marking R hO a b m)
  change (homologyMap (laurentMaslovMarkingIso R hO).hom m).hom.comp
      (homologyMap (polynomialLatticeInclusion R G a) m).hom =
      (homologyMap (polynomialLatticeInclusion R H b) m).hom.comp
        (homologyMap (polynomialMaslovMarkingIso R hO a b).hom m).hom at hcomm
  rw [hcomm]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr
    (homologyMapIso (polynomialMaslovMarkingIso R hO a b) m).toLinearEquiv.surjective

/-- Membership in the polynomial homology image is preserved and reflected by marking transport. -/
theorem homology_marking_mem_polynomialHomologyImage_iff (hO : G.O = H.O)
    (a b : Fin n) (m : ℤ) (ξ : (laurentMaslovComplex G R).homology m) :
    homologyMap (laurentMaslovMarkingIso R hO).hom m ξ ∈ polynomialHomologyImage R H b m ↔
      ξ ∈ polynomialHomologyImage R G a m := by
  rw [← polynomialHomologyImage_map_markingIso R hO a b m]
  constructor
  · rintro ⟨η, hη, hηξ⟩
    have heq : η = ξ :=
      (homologyMapIso (laurentMaslovMarkingIso R hO) m).toLinearEquiv.injective hηξ
    change η ∈ polynomialHomologyImage R G a m at hη
    exact heq ▸ hη
  · intro hξ
    exact ⟨ξ, hξ, rfl⟩

/-- A finite X-switch sequence preserves the image of polynomial homology, in every degree. -/
theorem XSwitchSequence.polynomialHomologyImage_map {l : ℕ}
    (s : XSwitchSequence G H l) (a b : Fin n) (m : ℤ) :
    (polynomialHomologyImage R G a m).map (homologyMap (s.chainIso R).hom m).hom =
      polynomialHomologyImage R H b m :=
  polynomialHomologyImage_map_markingIso R s.O_eq a b m

/-- In particular, a sequence transports exactly the degree-zero polynomial homology image. -/
theorem XSwitchSequence.homology_zero_mem_polynomialImage_iff {l : ℕ}
    (s : XSwitchSequence G H l) (a b : Fin n)
    (ξ : (laurentMaslovComplex G R).homology 0) :
    homologyMap (s.chainIso R).hom 0 ξ ∈ polynomialHomologyImage R H b 0 ↔
      ξ ∈ polynomialHomologyImage R G a 0 :=
  homology_marking_mem_polynomialHomologyImage_iff R s.O_eq a b 0 ξ

end OnLeConjecture.KnotFloer.GridFull
