/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullDifferentialOffDiagonal
public import OnLeConjecture.KnotFloer.GridFullDifferentialAnnulus

/-!
# The square-zero full rectangle differential

The full differential counts every empty grid rectangle, including
rectangles containing X markings, with its O-monomial weight. The
annular cancellation proves diagonal entries of its square vanish, while
commuting and recutting prove the other entries vanish. Linearity extends
the identity from grid states to every chain.

The total module and differential are packaged as a one-object homological
complex. Separate modules construct the integer Maslov grading and the Laurent extension.
The normalized knot homology class and invariance under geometric knot moves still require
proofs. This file does not identify total homology with a knot
invariant or prove a geometric cobordism estimate.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ}

section Differential

variable (G : GridDiagram n) (R : Type*) [CommSemiring R] [CharP R 2]

/-- Every two-step full rectangle count vanishes in characteristic two. -/
theorem sum_emptyDecompositionWeight_eq_zero (x z : GridState n) :
    ∑ D ∈ emptyDecompositions x z, G.unblockedDecompositionWeight R D = 0 := by
  rcases eq_or_ne z x with rfl | hzx
  · exact sum_emptyDecompositionWeight_self_eq_zero G R z
  · exact sum_emptyDecompositionWeight_eq_zero_of_ne G R hzx

/-- The square of the full differential vanishes at every coordinate of
every grid-state generator. -/
theorem differential_sq_single_apply_eq_zero (x z : GridState n) :
    differential G R (differential G R (Finsupp.single x 1)) z = 0 := by
  rw [differential_sq_single_apply]
  exact sum_emptyDecompositionWeight_eq_zero G R x z

/-- The square of the full differential kills every grid-state generator. -/
theorem differential_sq_single_eq_zero (x : GridState n) :
    differential G R (differential G R (Finsupp.single x 1)) = 0 := by
  refine Finsupp.ext fun z => ?_
  exact differential_sq_single_apply_eq_zero G R x z

/-- The full grid rectangle differential squares to zero. -/
theorem differential_comp_self_eq_zero :
    differential G R ∘ₗ differential G R =
      (0 : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply]
  exact differential_sq_single_eq_zero G R x

/-- The square-zero identity on an arbitrary full grid chain. -/
theorem differential_sq_eq_zero (c : GridChainMinus R n) :
    differential G R (differential G R c) = 0 :=
  LinearMap.congr_fun (differential_comp_self_eq_zero G R) c

end Differential

section Complex

variable (G : GridDiagram n) {R : Type*} [CommRing R] [CharP R 2]

/-- The full grid module with its actual rectangle-counting differential,
viewed as a one-object homological complex over the O-variable ring. -/
noncomputable def complex :
    HomologicalComplex (ModuleCat (MvPolynomial (Fin n) R)) (ComplexShape.refl Unit) :=
  oneObjectHomologicalComplex (ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n))
    (ModuleCat.ofHom (differential G R)) (by
      rw [← ModuleCat.ofHom_comp, differential_comp_self_eq_zero G R,
        ModuleCat.ofHom_zero])

@[simp]
theorem complex_X (i : Unit) :
    (complex G (R := R)).X i = ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n) :=
  oneObjectHomologicalComplex_X _ _ _ _

@[simp]
theorem complex_d :
    (complex G (R := R)).d () () =
      eqToHom (complex_X G ()) ≫ ModuleCat.ofHom (differential G R) ≫
        eqToHom (complex_X G ()).symm := by
  unfold complex
  exact oneObjectHomologicalComplex_d _ _ _

end Complex

end OnLeConjecture.KnotFloer.GridFull
