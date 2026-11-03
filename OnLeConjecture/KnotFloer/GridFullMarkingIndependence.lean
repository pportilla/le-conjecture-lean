/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridSelectedVariableComplex
public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov

/-!
# Independence of the full differential from the X markings

Two diagrams with the same O markings have the same full rectangle differential
and the same Maslov grading. This is the first algebraic step in the proof of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Proposition 14.1.1.
Their Alexander filtrations can differ. The tower computation additionally
requires reducing a suitable unknot diagram to the two-by-two diagram.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {G H : GridDiagram n}

/-- The marked columns of a rectangle depend only on the O markings. -/
theorem OColumns_eq_of_O_eq (h : G.O = H.O) (r : GridRectangle n) :
    G.OColumns r = H.OColumns r := by
  ext c
  simp only [GridDiagram.mem_OColumns, h]

/-- The full rectangle matrix is independent of the X markings. -/
theorem coefficient_eq_of_O_eq (R : Type*) [CommSemiring R] (h : G.O = H.O)
    (x y : GridState n) : coefficient G R x y = coefficient H R x y := by
  simp only [coefficient, OMonomial_eq_monomial_oExponent, oExponent, OColumns_eq_of_O_eq h]

/-- Equality of O markings gives equality of the full polynomial differential. -/
theorem differential_eq_of_O_eq (R : Type*) [CommSemiring R] (h : G.O = H.O) :
    differential G R = differential H R := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  simp only [differential_apply_apply, coefficient_eq_of_O_eq R h]

/-- Equality of O markings gives equality of the full Laurent differential. -/
theorem laurentDifferential_eq_of_O_eq (R : Type*) [CommSemiring R] (h : G.O = H.O) :
    laurentDifferential G R = laurentDifferential H R := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  simp only [laurentDifferential_apply_apply, laurentCoefficient, coefficient_eq_of_O_eq R h]

/-- The integer Maslov grading depends only on the O markings. -/
theorem maslovO_eq_of_O_eq (h : G.O = H.O) (x : GridState n) :
    G.maslovOℤ x = H.maslovOℤ x := by
  simp only [GridDiagram.maslovOℤ_def, GridDiagram.OSet_def, h]

/-- The homogeneous Laurent modules are unchanged when only X markings are moved. -/
theorem laurentMaslovPiece_eq_of_O_eq (R : Type*) [CommSemiring R] (h : G.O = H.O) (m : ℤ) :
    laurentMaslovPiece G R m = laurentMaslovPiece H R m := by
  ext c
  simp only [mem_laurentMaslovPiece, laurentMaslovDegree, maslovO_eq_of_O_eq h]

/-- The identity on Laurent chains is a linear equivalence of the equal homogeneous pieces. -/
noncomputable def laurentMaslovMarkingPieceEquiv (R : Type*) [CommRing R]
    (h : G.O = H.O) (m : ℤ) : laurentMaslovPiece G R m ≃ₗ[R] laurentMaslovPiece H R m where
  toFun c := ⟨c.val, by simpa only [laurentMaslovPiece_eq_of_O_eq R h] using c.property⟩
  invFun c := ⟨c.val, by simpa only [laurentMaslovPiece_eq_of_O_eq R h] using c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Moving X markings preserves the genuine Maslov-graded full Laurent complex. -/
noncomputable def laurentMaslovMarkingIso (R : Type*) [CommRing R] [CharP R 2]
    (h : G.O = H.O) : laurentMaslovComplex G R ≅ laurentMaslovComplex H R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (laurentMaslovMarkingPieceEquiv R h m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [laurentMaslovComplex_d, laurentMaslovComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact (LinearMap.congr_fun (laurentDifferential_eq_of_O_eq R h) c.val).symm)

/-- The retained-variable polynomial complex is unchanged by moving the X markings. -/
noncomputable def selectedIdentifiedMarkingIso (R : Type*) [CommRing R] [CharP R 2]
    (h : G.O = H.O) (a : Fin n) (s : Finset (Fin n)) :
    selectedIdentifiedComplex R G a s ≅ selectedIdentifiedComplex R H a s :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro _ _ _
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change identifyVariablesChain R a s (differential H R c.val) =
      identifyVariablesChain R a s (differential G R c.val)
    rw [differential_eq_of_O_eq R h])

end OnLeConjecture.KnotFloer.GridFull
