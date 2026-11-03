/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLattice
public import OnLeConjecture.KnotFloer.GridXSwitchSequence

/-!
# The native polynomial lattice and marking isomorphisms

The polynomial inclusion is a map of integer-graded chain complexes. Moving
only the X markings gives a polynomial chain isomorphism commuting with the
previously constructed Laurent marking isomorphism.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]

/-- Include the polynomial grid complex in the Laurent grid complex. -/
def polynomialLatticeInclusion (G : GridDiagram n) (a : Fin n) :
    oneVariableMaslovComplex R G a ⟶ laurentMaslovComplex G R where
  f m := ModuleCat.ofHom (polynomialLatticePieceMap R G a m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [oneVariableMaslovComplex_d, laurentMaslovComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact (oneVariableToLaurentChain_differential R G c.val).symm

/-- The native inclusion is coefficientwise polynomial inclusion on its underlying chains. -/
theorem polynomialLatticeInclusion_apply (G : GridDiagram n) (a : Fin n) (m : ℤ)
    (c : (oneVariableMaslovComplex R G a).X m) :
    (laurentMaslovChainEquiv G R m ((polynomialLatticeInclusion R G a).f m c) :
      LaurentChain R n) =
      oneVariableToLaurentChain R
        ((show oneVariableMaslovPiece R G a m from c) : OneVariableChain R n) := rfl

/-- The native coefficient inclusion is injective in every degree. -/
theorem polynomialLatticeInclusion_injective (G : GridDiagram n) (a : Fin n) (m : ℤ) :
    Function.Injective ((polynomialLatticeInclusion R G a).f m) := by
  intro c d h
  apply Subtype.ext
  apply oneVariableToLaurentChain_injective R
  exact congrArg (fun z =>
    (laurentMaslovChainEquiv G R m z : LaurentChain R n)) h

/-- Native degreewise image equals the homogeneous polynomial lattice. -/
theorem mem_range_polynomialLatticeInclusion_iff (G : GridDiagram n) (a : Fin n) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    c ∈ LinearMap.range ((polynomialLatticeInclusion R G a).f m).hom ↔
      ∀ x k, k ∈ ((laurentMaslovChainEquiv G R m c : LaurentChain R n) x).coeff.support →
        0 ≤ k :=
  mem_range_polynomialLatticePieceMap_iff R G a m c

variable {G H : GridDiagram n}

omit [CharP R 2] in
/-- Moving only X markings leaves the one-variable differential unchanged. -/
theorem oneVariableDifferential_eq_of_O_eq (hO : G.O = H.O) :
    oneVariableDifferential R G = oneVariableDifferential R H := by
  apply LinearMap.ext
  intro c
  apply oneVariableToLaurentChain_injective R
  rw [oneVariableToLaurentChain_differential, oneVariableToLaurentChain_differential,
    laurentDifferential_eq_of_O_eq R hO]

omit [CharP R 2] in
/-- The homogeneous polynomial lattice does not depend on the X markings or selected O variable. -/
theorem oneVariableMaslovPiece_eq_of_O_eq (hO : G.O = H.O) (a b : Fin n) (m : ℤ) :
    oneVariableMaslovPiece R G a m = oneVariableMaslovPiece R H b m := by
  ext c
  simp only [mem_oneVariableMaslovPiece_iff, maslovO_eq_of_O_eq hO]

/-- The identity on polynomial chains transports equal Maslov pieces. -/
def polynomialMaslovMarkingPieceEquiv (hO : G.O = H.O) (a b : Fin n) (m : ℤ) :
    oneVariableMaslovPiece R G a m ≃ₗ[R] oneVariableMaslovPiece R H b m where
  toFun c := ⟨c.val, by simpa only [oneVariableMaslovPiece_eq_of_O_eq R hO a b] using c.property⟩
  invFun c := ⟨c.val, by simpa only [oneVariableMaslovPiece_eq_of_O_eq R hO a b] using c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The native polynomial marking isomorphism, allowing different selected O variables. -/
def polynomialMaslovMarkingIso (hO : G.O = H.O) (a b : Fin n) :
    oneVariableMaslovComplex R G a ≅ oneVariableMaslovComplex R H b :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (polynomialMaslovMarkingPieceEquiv R hO a b m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [oneVariableMaslovComplex_d, oneVariableMaslovComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact (LinearMap.congr_fun (oneVariableDifferential_eq_of_O_eq R hO) c.val).symm)

/-- The polynomial and Laurent marking isomorphisms commute with coefficient inclusion. -/
theorem polynomialLatticeInclusion_markingIso (hO : G.O = H.O) (a b : Fin n) :
    polynomialLatticeInclusion R G a ≫ (laurentMaslovMarkingIso R hO).hom =
      (polynomialMaslovMarkingIso R hO a b).hom ≫ polynomialLatticeInclusion R H b := by
  apply HomologicalComplex.Hom.ext
  funext m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

end OnLeConjecture.KnotFloer.GridFull
