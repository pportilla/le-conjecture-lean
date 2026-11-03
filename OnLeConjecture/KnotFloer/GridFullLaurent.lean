/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullMaslovComplex
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# The full grid differential with Laurent coefficients

Every O variable is sent to `T 1` in the Laurent polynomial ring. The free
module on grid states therefore has rectangle coefficient `T (#O)`. Its
square-zero identity follows by applying the specialization homomorphism
to the already proved polynomial matrix identity.

These definitions depend on the grid diagram. Identification of their
homology with a knot invariant requires additional invariance theorems.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ}

/-- The free Laurent polynomial module on grid states. -/
abbrev LaurentChain (R : Type*) [CommSemiring R] (n : ℕ) :=
  GridState n →₀ LaurentPolynomial R

/-- Collapse all O variables to the invertible Laurent variable. -/
noncomputable def laurentSpecialization (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin n) R →ₐ[R] LaurentPolynomial R :=
  MvPolynomial.aeval fun _ => LaurentPolynomial.T 1

@[simp]
theorem laurentSpecialization_X (R : Type*) [CommSemiring R] (i : Fin n) :
    laurentSpecialization R (MvPolynomial.X i) = LaurentPolynomial.T 1 := by
  simp [laurentSpecialization]

/-- The common image of the O variables is a unit. -/
theorem isUnit_laurentVariable (R : Type*) [CommSemiring R] :
    IsUnit (LaurentPolynomial.T 1 : LaurentPolynomial R) :=
  LaurentPolynomial.isUnit_T 1

variable (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The specialized coefficient of the full rectangle differential. -/
noncomputable def laurentCoefficient (x y : GridState n) : LaurentPolynomial R :=
  laurentSpecialization R (coefficient G R x y)

theorem laurentSpecialization_OMonomial (r : GridRectangle n) :
    laurentSpecialization R (G.OMonomial R r) =
      LaurentPolynomial.T ((G.OColumns r).card : ℤ) := by
  classical
  rw [OMonomial_eq_monomial_oExponent, laurentSpecialization,
    MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, Finset.prod_pow_eq_pow_sum]
  simp only [LaurentPolynomial.T_pow, mul_one]
  change LaurentPolynomial.T (exponentSize (oExponent G r) : ℤ) = _
  rw [exponentSize_oExponent]

theorem laurentCoefficient_eq (x y : GridState n) :
    laurentCoefficient G R x y =
      ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  simp [laurentCoefficient, coefficient, map_sum, laurentSpecialization_OMonomial]

/-- The full Laurent differential evaluated at a state. -/
noncomputable def laurentOnGenerator (x : GridState n) : LaurentChain R n :=
  ∑ y : GridState n, Finsupp.single y (laurentCoefficient G R x y)

@[simp]
theorem laurentOnGenerator_apply (x y : GridState n) :
    laurentOnGenerator G R x y = laurentCoefficient G R x y := by
  classical
  rw [laurentOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The Laurent-linear full rectangle differential. -/
noncomputable def laurentDifferential :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  Finsupp.lsum (LaurentPolynomial R) fun x : GridState n =>
    (LinearMap.id : LaurentPolynomial R →ₗ[LaurentPolynomial R]
      LaurentPolynomial R).smulRight (laurentOnGenerator G R x)

@[simp]
theorem laurentDifferential_single (x : GridState n) :
    laurentDifferential G R (Finsupp.single x 1) = laurentOnGenerator G R x := by
  rw [laurentDifferential, Finsupp.lsum_single]
  simp

theorem laurentDifferential_apply_apply (c : LaurentChain R n) (y : GridState n) :
    laurentDifferential G R c y = c.sum fun x a => a * laurentCoefficient G R x y := by
  simp [laurentDifferential, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    LinearMap.smulRight_apply]

/-- A coefficient in the Laurent rectangle sum comes from a rectangle's O count. -/
theorem exists_rectangle_of_mem_support_laurentCoefficient {x y : GridState n} {k : ℤ}
    (hk : k ∈ (laurentCoefficient G R x y).coeff.support) :
    ∃ r ∈ GridRectangleBetween.emptyRectangles x y,
      k = ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [laurentCoefficient_eq, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨r, hr, hkr⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  refine ⟨r, hr, ?_⟩
  change k ∈ (Finsupp.single ((G.OColumns r.toGridRectangle).card : ℤ) (1 : R)).support
    at hkr
  exact Finset.mem_singleton.mp (Finsupp.support_single_subset hkr)

/-- Every exponent in the differential is an input exponent plus a rectangle's O count. -/
theorem exists_rectangle_of_mem_support_laurentDifferential
    (c : LaurentChain R n) {y : GridState n} {k : ℤ}
    (hk : k ∈ (laurentDifferential G R c y).coeff.support) :
    ∃ x : GridState n, ∃ j ∈ (c x).coeff.support,
      ∃ r ∈ GridRectangleBetween.emptyRectangles x y,
        k = j + ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [laurentDifferential_apply_apply, Finsupp.sum, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  obtain ⟨r, hr, rfl⟩ := exists_rectangle_of_mem_support_laurentCoefficient G R hd
  exact ⟨x, j, hj, r, hr, rfl⟩

/-- Square-zero survives specialization of every polynomial matrix entry. -/
theorem laurentDifferential_sq_single_apply_eq_zero [CharP R 2] (x z : GridState n) :
    laurentDifferential G R (laurentDifferential G R (Finsupp.single x 1)) z = 0 := by
  classical
  have h := differential_sq_single_apply_eq_zero G R x z
  rw [differential_single, differential_apply_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _] at h
  simp only [onGenerator_apply] at h
  have hs := congrArg (laurentSpecialization R) h
  rw [laurentDifferential_single, laurentDifferential_apply_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simpa only [laurentOnGenerator_apply, laurentCoefficient, map_sum, map_mul, map_zero]
    using hs

theorem laurentDifferential_comp_self_eq_zero [CharP R 2] :
    laurentDifferential G R ∘ₗ laurentDifferential G R = 0 := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply]
  exact Finsupp.ext fun z => laurentDifferential_sq_single_apply_eq_zero G R x z

theorem laurentDifferential_sq_eq_zero [CharP R 2] (c : LaurentChain R n) :
    laurentDifferential G R (laurentDifferential G R c) = 0 :=
  LinearMap.congr_fun (laurentDifferential_comp_self_eq_zero G R) c

/-- Specialize the coefficients of a polynomial grid chain. -/
noncomputable def polynomialToLaurentChain : GridChainMinus R n →ₗ[R] LaurentChain R n :=
  Finsupp.mapRange.linearMap (laurentSpecialization R).toLinearMap

@[simp]
theorem polynomialToLaurentChain_apply (c : GridChainMinus R n) (x : GridState n) :
    polynomialToLaurentChain R c x = laurentSpecialization R (c x) := rfl

/-- Coefficient specialization intertwines the full differentials. -/
theorem polynomialToLaurentChain_differential (c : GridChainMinus R n) :
    polynomialToLaurentChain R (differential G R c) =
      laurentDifferential G R (polynomialToLaurentChain R c) := by
  classical
  apply Finsupp.ext
  intro y
  rw [polynomialToLaurentChain_apply, differential_apply_apply,
    laurentDifferential_apply_apply]
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [map_sum, map_mul, polynomialToLaurentChain_apply, laurentCoefficient]

/-- A Laurent monomial multiple of a grid-state generator. -/
noncomputable def laurentMonomialGenerator (k : ℤ) (x : GridState n) : LaurentChain R n :=
  Finsupp.single x (LaurentPolynomial.T k)

/-- The differential on every Laurent monomial state, including negative exponents. -/
theorem laurentDifferential_monomialGenerator (k : ℤ) (x : GridState n) :
    laurentDifferential G R (laurentMonomialGenerator R k x) =
      ∑ y : GridState n, ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        laurentMonomialGenerator R (k + ((G.OColumns r.toGridRectangle).card : ℤ)) y := by
  classical
  rw [laurentMonomialGenerator, ← Finsupp.smul_single_one, map_smul,
    laurentDifferential_single]
  simp only [laurentOnGenerator, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul,
    laurentCoefficient_eq, Finsupp.single_finsetSum,
    ← LaurentPolynomial.T_add, laurentMonomialGenerator]

/-- The full Laurent differential as a one-object homological complex. -/
noncomputable def laurentComplex (S : Type*) [CommRing S] [CharP S 2] :
    HomologicalComplex (ModuleCat (LaurentPolynomial S)) (ComplexShape.refl Unit) :=
  oneObjectHomologicalComplex (ModuleCat.of (LaurentPolynomial S) (LaurentChain S n))
    (ModuleCat.ofHom (laurentDifferential G S)) (by
      rw [← ModuleCat.ofHom_comp, laurentDifferential_comp_self_eq_zero,
        ModuleCat.ofHom_zero])

end OnLeConjecture.KnotFloer.GridFull
