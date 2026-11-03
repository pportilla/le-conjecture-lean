/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPartialVariableComplex

/-!
# The full grid differential over R[U]

This is the free polynomial module on the actual grid states. Its matrix
coefficient is the sum of `U^(number of O markings)` over all empty rectangles,
including rectangles containing X markings. The graded module and Alexander
filtration are obtained from the explicit inclusion `U ↦ V_a`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory MvPolynomial

variable {n : ℕ} (R : Type*) [CommRing R]

/-- The free R[U]-module on grid states. -/
abbrev OneVariableChain (n : ℕ) := GridState n →₀ Polynomial R

/-- The coefficient of the full rectangle differential after identifying all O variables. -/
noncomputable def oneVariableCoefficient (G : GridDiagram n) (x y : GridState n) : Polynomial R :=
  collapseToOneVariable R (coefficient G R x y)

/-- Every rectangle is weighted by U raised to its number of O markings. -/
theorem collapseToOneVariable_OMonomial (G : GridDiagram n) (r : GridRectangle n) :
    collapseToOneVariable R (G.OMonomial R r) = Polynomial.X ^ (G.OColumns r).card := by
  classical
  rw [OMonomial_eq_monomial_oExponent, collapseToOneVariable, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, Finset.prod_pow_eq_pow_sum]
  change Polynomial.X ^ exponentSize (oExponent G r) = _
  rw [exponentSize_oExponent]

/-- The one-variable matrix coefficient counts the same actual empty rectangles. -/
theorem oneVariableCoefficient_eq (G : GridDiagram n) (x y : GridState n) :
    oneVariableCoefficient R G x y =
      ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        Polynomial.X ^ (G.OColumns r.toGridRectangle).card := by
  simp [oneVariableCoefficient, coefficient, map_sum, collapseToOneVariable_OMonomial]

/-- The one-variable differential on one grid-state generator. -/
noncomputable def oneVariableOnGenerator (G : GridDiagram n) (x : GridState n) :
    OneVariableChain R n :=
  ∑ y : GridState n, Finsupp.single y (oneVariableCoefficient R G x y)

@[simp]
theorem oneVariableOnGenerator_apply (G : GridDiagram n) (x y : GridState n) :
    oneVariableOnGenerator R G x y = oneVariableCoefficient R G x y := by
  classical
  rw [oneVariableOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The full R[U]-linear empty-rectangle differential. -/
noncomputable def oneVariableDifferential (G : GridDiagram n) :
    OneVariableChain R n →ₗ[Polynomial R] OneVariableChain R n :=
  Finsupp.lsum (Polynomial R) fun x : GridState n =>
    (LinearMap.id : Polynomial R →ₗ[Polynomial R] Polynomial R).smulRight
      (oneVariableOnGenerator R G x)

/-- The matrix evaluation of the actual one-variable rectangle differential. -/
theorem oneVariableDifferential_apply_apply (G : GridDiagram n)
    (c : OneVariableChain R n) (y : GridState n) :
    oneVariableDifferential R G c y = c.sum fun x p => p * oneVariableCoefficient R G x y := by
  simp [oneVariableDifferential, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    LinearMap.smulRight_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Collapse every coefficient of a grid chain to R[U]. -/
noncomputable def collapseOneVariableChain : GridChainMinus R n →ₗ[R] OneVariableChain R n :=
  Finsupp.mapRange.linearMap (collapseToOneVariable R).toLinearMap

/-- Include coefficients in the selected O variable. -/
noncomputable def oneVariableChainSection (a : Fin n) :
    OneVariableChain R n →ₗ[R] GridChainMinus R n :=
  Finsupp.mapRange.linearMap (oneVariableSection R a).toLinearMap

@[simp]
theorem collapseOneVariableChain_apply (c : GridChainMinus R n) (x : GridState n) :
    collapseOneVariableChain R c x = collapseToOneVariable R (c x) := rfl

@[simp]
theorem oneVariableChainSection_apply (a : Fin n) (c : OneVariableChain R n) (x : GridState n) :
    oneVariableChainSection R a c x = oneVariableSection R a (c x) := rfl

/-- Collapse and the selected-variable section are inverse on R[U]-chains. -/
theorem collapseOneVariableChain_section (a : Fin n) (c : OneVariableChain R n) :
    collapseOneVariableChain R (oneVariableChainSection R a c) = c := by
  apply Finsupp.ext
  intro x
  exact collapseToOneVariable_section R a (c x)

/-- Including the collapsed chain gives its fully identified coefficient representative. -/
theorem oneVariableChainSection_collapse (a : Fin n) (c : GridChainMinus R n) :
    oneVariableChainSection R a (collapseOneVariableChain R c) =
      identifyVariablesChain R a Finset.univ c := by
  apply Finsupp.ext
  intro x
  exact oneVariableSection_collapse R a (c x)

/-- The coefficient inclusion is injective on actual grid chains. -/
theorem oneVariableChainSection_injective (a : Fin n) :
    Function.Injective (oneVariableChainSection R a (n := n)) :=
  Function.LeftInverse.injective (collapseOneVariableChain_section R a)

/-- Coefficient collapse intertwines the full rectangle differentials. -/
theorem collapseOneVariableChain_differential (G : GridDiagram n) (c : GridChainMinus R n) :
    collapseOneVariableChain R (differential G R c) =
      oneVariableDifferential R G (collapseOneVariableChain R c) := by
  classical
  apply Finsupp.ext
  intro y
  rw [collapseOneVariableChain_apply, differential_apply_apply,
    oneVariableDifferential_apply_apply]
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [map_sum, map_mul, collapseOneVariableChain_apply, oneVariableCoefficient]

/-- The actual one-variable differential includes as the fully identified rectangle differential. -/
theorem oneVariableChainSection_differential (G : GridDiagram n) (a : Fin n)
    (c : OneVariableChain R n) :
    oneVariableChainSection R a (oneVariableDifferential R G c) =
      identifiedDifferential R G a Finset.univ (oneVariableChainSection R a c) := by
  rw [identifiedDifferential_apply, ← oneVariableChainSection_collapse,
    collapseOneVariableChain_differential, collapseOneVariableChain_section]

/-- The Maslov-homogeneous part of the actual R[U]-state module. -/
noncomputable def oneVariableMaslovPiece (G : GridDiagram n) (a : Fin n) (m : ℤ) :
    Submodule R (OneVariableChain R n) :=
  (maslovPiece G R m).comap (oneVariableChainSection R a)

/-- The actual one-variable differential lowers Maslov degree by one. -/
theorem oneVariableDifferential_mem_maslovPiece (G : GridDiagram n) (a : Fin n)
    {m : ℤ} {c : OneVariableChain R n} (hc : c ∈ oneVariableMaslovPiece R G a m) :
    oneVariableDifferential R G c ∈ oneVariableMaslovPiece R G a (m - 1) := by
  change oneVariableChainSection R a (oneVariableDifferential R G c) ∈
    maslovPiece G R (m - 1)
  rw [oneVariableChainSection_differential]
  exact identifiedDifferential_mem_maslovPiece R G a Finset.univ hc

variable [CharP R 2]

/-- The full one-variable differential squares to zero. -/
theorem oneVariableDifferential_sq (G : GridDiagram n) (a : Fin n) (c : OneVariableChain R n) :
    oneVariableDifferential R G (oneVariableDifferential R G c) = 0 := by
  apply oneVariableChainSection_injective R a
  rw [map_zero, oneVariableChainSection_differential, oneVariableChainSection_differential,
    identifiedDifferential_sq]

/-- Restrict the full R[U] differential to consecutive Maslov degrees. -/
noncomputable def oneVariableGradedDifferential (G : GridDiagram n) (a : Fin n) (m : ℤ) :
    oneVariableMaslovPiece R G a (m + 1) →ₗ[R] oneVariableMaslovPiece R G a m :=
  ((oneVariableDifferential R G).restrictScalars R).restrict fun _ hc => by
    simpa using oneVariableDifferential_mem_maslovPiece R G a hc

/-- The genuine R[U]-state differential packaged as a native integer-graded complex. -/
noncomputable def oneVariableMaslovComplex (G : GridDiagram n) (a : Fin n) :
    ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (oneVariableMaslovPiece R G a m))
    (fun m => ModuleCat.ofHom (oneVariableGradedDifferential R G a m))
    (fun m => by
      ext c : 2
      exact Subtype.ext (oneVariableDifferential_sq R G a c))

theorem oneVariableMaslovComplex_d (G : GridDiagram n) (a : Fin n) (m : ℤ) :
    (oneVariableMaslovComplex R G a).d (m + 1) m =
      ModuleCat.ofHom (oneVariableGradedDifferential R G a m) := by
  simp only [oneVariableMaslovComplex, ChainComplex.of_d]

/-- Alexander filtration on R[U]-states through the explicit coefficient inclusion. -/
noncomputable def oneVariableAlexanderFiltration (G : GridDiagram n) (a : Fin n) :
    RealFiltration (oneVariableMaslovComplex R G a) where
  level v m := ((bifiltrationLevel G R 0 v).restrictScalars R).comap
    ((oneVariableChainSection R a).comp (oneVariableMaslovPiece R G a m).subtype)
  mono m v v' hv := Submodule.comap_mono (bifiltrationLevel_mono G R le_rfl hv)
  differential_mem v i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      rw [oneVariableMaslovComplex_d]
      change oneVariableChainSection R a
        (oneVariableDifferential R G ((show oneVariableMaslovPiece R G a (j + 1) from c) :
          OneVariableChain R n)) ∈ bifiltrationLevel G R 0 v
      rw [oneVariableChainSection_differential]
      exact identifiedDifferential_mem_bifiltrationLevel R G a Finset.univ hc
    · rw [(oneVariableMaslovComplex R G a).shape i j h]
      exact Submodule.zero_mem _

end OnLeConjecture.KnotFloer.GridFull
