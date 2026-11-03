/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridOneVariablePolynomialNormalization
public import OnLeConjecture.KnotFloer.GridFullLaurent
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Laurent extension of the concrete polynomial normalization

The actual polynomial-linear comparisons and homotopies extend by scalar
extension along R[U] → R[U,U⁻¹]. The left-hand differential is identified with
the full Laurent rectangle differential on the same grid states. The right
side inverts the selected original O variable and retains the n−1 two-copy
factors. No cancellation of these factors or choice of homology class is made.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (R : Type*) [CommRing R]

/-- The free grid-state basis identifies scalar extension with Laurent grid chains. -/
noncomputable def oneVariableLaurentBaseChangeEquiv :
    (ModuleCat.extendScalars (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)).obj
      (ModuleCat.of (Polynomial R) (OneVariableChain R n)) ≃ₗ[LaurentPolynomial R]
        LaurentChain R n :=
  ((Finsupp.basisSingleOne :
    Module.Basis (GridState n) (Polynomial R) (OneVariableChain R n)).baseChange
      (LaurentPolynomial R)).repr

/-- On a pure tensor the basis comparison applies the Laurent coefficient inclusion. -/
theorem oneVariableLaurentBaseChangeEquiv_tmul (p : LaurentPolynomial R)
    (c : OneVariableChain R n) (x : GridState n) :
    oneVariableLaurentBaseChangeEquiv R (p ⊗ₜ[Polynomial R] c) x =
      Polynomial.toLaurent (c x) * p := by
  exact Module.Basis.baseChange_repr_tmul (LaurentPolynomial R)
    (Finsupp.basisSingleOne :
      Module.Basis (GridState n) (Polynomial R) (OneVariableChain R n)) p c x

/-- Each actual one-variable rectangle coefficient specializes to the Laurent coefficient. -/
theorem oneVariableCoefficient_toLaurent (G : GridDiagram n) (x y : GridState n) :
    Polynomial.toLaurent (oneVariableCoefficient R G x y) = laurentCoefficient G R x y := by
  classical
  rw [oneVariableCoefficient_eq, laurentCoefficient_eq, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact Polynomial.toLaurent_X_pow _

/-- The pure-tensor basis comparison intertwines the two explicit rectangle differentials. -/
theorem oneVariableLaurentBaseChangeEquiv_differential (G : GridDiagram n)
    (p : LaurentPolynomial R) (c : OneVariableChain R n) :
    oneVariableLaurentBaseChangeEquiv R (p ⊗ₜ[Polynomial R] oneVariableDifferential R G c) =
      laurentDifferential G R (oneVariableLaurentBaseChangeEquiv R (p ⊗ₜ[Polynomial R] c)) := by
  classical
  apply Finsupp.ext
  intro y
  rw [oneVariableLaurentBaseChangeEquiv_tmul, oneVariableDifferential_apply_apply,
    laurentDifferential_apply_apply]
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_mul, oneVariableCoefficient_toLaurent, oneVariableLaurentBaseChangeEquiv_tmul]
  ring

/-- Extend the retained-variable scalar ring by inverting U. -/
noncomputable abbrev laurentScalarExtension :
    ModuleCat (Polynomial R) ⥤ ModuleCat (LaurentPolynomial R) :=
  ModuleCat.extendScalars (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)

instance : (laurentScalarExtension R).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul p c => exact TensorProduct.tmul_add p (f c) (g c)
    | add c d hc hd =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hc hd

variable [CharP R 2] (G : GridDiagram n)

/-- The full Laurent differential in an explicit constant-object total complex. -/
noncomputable def explicitLaurentTotalComplex :
    HomologicalComplex (ModuleCat (LaurentPolynomial R)) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of (LaurentPolynomial R) (LaurentChain R n)
  d _ _ := ModuleCat.ofHom (laurentDifferential G R)
  shape i j h := by cases i; cases j; exact False.elim (h rfl)
  d_comp_d' _ _ _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact laurentDifferential_sq_eq_zero G R

/-- The explicit constant-object presentation is the existing native Laurent complex. -/
noncomputable def explicitLaurentTotalIso :
    explicitLaurentTotalComplex R G ≅ laurentComplex G R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (eqToIso (show (laurentComplex G R).X i =
      ModuleCat.of (LaurentPolynomial R) (LaurentChain R n) from
        oneObjectHomologicalComplex_X _ _ _ i)).symm) (by
      intro i j _
      cases i
      cases j
      change _ ≫ (laurentComplex G R).d () () =
        ModuleCat.ofHom (laurentDifferential G R) ≫ _
      have hd := oneObjectHomologicalComplex_d
        (ModuleCat.of (LaurentPolynomial R) (LaurentChain R n))
        (ModuleCat.ofHom (laurentDifferential G R))
        (show ModuleCat.ofHom (laurentDifferential G R) ≫
          ModuleCat.ofHom (laurentDifferential G R) = 0 by
            rw [← ModuleCat.ofHom_comp, laurentDifferential_comp_self_eq_zero,
              ModuleCat.ofHom_zero])
      change (laurentComplex G R).d () () = _ at hd
      rw [hd]
      simp)

/-- Scalar extension of the one-U complex is the actual Laurent rectangle complex. -/
noncomputable def oneVariableLaurentBaseChangeIso (a : Fin n) :
    ((laurentScalarExtension R).mapHomologicalComplex (ComplexShape.refl Unit)).obj
      (oneVariableTotalComplex R G a) ≅
        explicitLaurentTotalComplex R G :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (oneVariableLaurentBaseChangeEquiv R).toModuleIso) (by
      intro _ _ _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul p c => exact (oneVariableLaurentBaseChangeEquiv_differential R G p c).symm
      | add c d hc hd =>
        simpa only [map_add] using congrArg₂ (· + ·) hc hd)

/-- The actual full Laurent complex has the scalar-extended n−1 normalization factors. -/
noncomputable def oneVariableLaurentNormalizationEquiv (hG : G.IsKnot) (a : Fin n) :
    HomotopyEquiv (explicitLaurentTotalComplex R G)
      (((laurentScalarExtension R).mapHomologicalComplex (ComplexShape.refl Unit)).obj
          (iteratedModuleDouble (selectedIdentifiedComplex R G a ∅) (n - 1))) :=
  (HomotopyEquiv.ofIso (oneVariableLaurentBaseChangeIso R G a).symm).trans
    ((laurentScalarExtension R).mapHomotopyEquiv (oneVariablePolynomialNormalizationEquiv R G hG a))

/-- The existing full Laurent rectangle complex satisfies the actual scalar-linear normalization. -/
noncomputable def fullLaurentNormalizationEquiv (hG : G.IsKnot) (a : Fin n) :
    HomotopyEquiv (laurentComplex G R)
      (((laurentScalarExtension R).mapHomologicalComplex (ComplexShape.refl Unit)).obj
        (iteratedModuleDouble (selectedIdentifiedComplex R G a ∅) (n - 1))) :=
  (HomotopyEquiv.ofIso (explicitLaurentTotalIso R G).symm).trans
    (oneVariableLaurentNormalizationEquiv R G hG a)

end OnLeConjecture.KnotFloer.GridFull
