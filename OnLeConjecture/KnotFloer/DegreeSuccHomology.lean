/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.DegreeSuccComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology under the degree reindexing in the stabilization summand

The explicitly reindexed complex has degree `m` homology naturally isomorphic
to the original degree `m+1` homology. The proof uses Mathlib's homology of
short complexes and checks naturality for the actual reindexed chain map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace OnLeConjecture.KnotFloer

open CategoryTheory HomologicalComplex

variable {R : Type*} [CommRing R]

/-- Computing homology using specified neighboring degrees is natural in chain maps. -/
theorem homologyIsoSc'_hom_naturality {C D : ChainComplex (ModuleCat R) ℤ}
    (φ : C ⟶ D) (i j k : ℤ)
    (hi : (ComplexShape.down ℤ).prev j = i) (hk : (ComplexShape.down ℤ).next j = k) :
    homologyMap φ j ≫ (D.homologyIsoSc' i j k hi hk).hom =
      (C.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor' (ModuleCat R)
          (ComplexShape.down ℤ) i j k).map φ) := by
  change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (natIsoSc' (ModuleCat R) (ComplexShape.down ℤ) i j k hi hk).hom.naturality φ

/-- The second stabilization summand contributes homology in degree `m+1`. -/
def degreeSuccHomologyIso (C : ChainComplex (ModuleCat R) ℤ) (m : ℤ) :
    (degreeSuccComplex C).homology m ≅ C.homology (m + 1) :=
  (degreeSuccComplex C).homologyIsoSc' (m + 1) m (m - 1)
      (by rw [ChainComplex.prev]) (by rw [ChainComplex.next]) ≪≫
    (C.homologyIsoSc' ((m + 1) + 1) (m + 1) ((m - 1) + 1)
      (by rw [ChainComplex.prev]) (by rw [ChainComplex.next]; omega)).symm

/-- The degree identification commutes with the reindexed native chain map. -/
theorem degreeSuccHomologyIso_naturality {C D : ChainComplex (ModuleCat R) ℤ}
    (φ : C ⟶ D) (m : ℤ) :
    homologyMap (degreeSuccMap φ) m ≫ (degreeSuccHomologyIso D m).hom =
      (degreeSuccHomologyIso C m).hom ≫ homologyMap φ (m + 1) := by
  simp only [degreeSuccHomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, ← Category.assoc,
    homologyIsoSc'_hom_naturality (degreeSuccMap φ)]
  rw [Category.assoc]
  congr 1
  rw [← cancel_mono (D.homologyIsoSc' ((m + 1) + 1) (m + 1) ((m - 1) + 1)
    (by rw [ChainComplex.prev]) (by rw [ChainComplex.next]; omega)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [homologyIsoSc'_hom_naturality φ]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- The native linear equivalence for the degree shift. -/
def degreeSuccHomologyEquiv (C : ChainComplex (ModuleCat R) ℤ) (m : ℤ) :
    (degreeSuccComplex C).homology m ≃ₗ[R] C.homology (m + 1) :=
  (degreeSuccHomologyIso C m).toLinearEquiv

/-- Naturality in the elementwise form used by the two-copy homology decomposition. -/
theorem degreeSuccHomologyEquiv_naturality {C D : ChainComplex (ModuleCat R) ℤ}
    (φ : C ⟶ D) (m : ℤ) (ξ : (degreeSuccComplex C).homology m) :
    degreeSuccHomologyEquiv D m (homologyMap (degreeSuccMap φ) m ξ) =
      homologyMap φ (m + 1) (degreeSuccHomologyEquiv C m ξ) :=
  congrArg (fun f : (degreeSuccComplex C).homology m ⟶ D.homology (m + 1) => f ξ)
    (degreeSuccHomologyIso_naturality φ m)

end OnLeConjecture.KnotFloer
