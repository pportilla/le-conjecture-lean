/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: Pablo Portilla Cuadrado, The Tau Ceti contributors
-/
module

public import OnLeConjecture.KnotFloer.GridComplex

/-!
# The full grid rectangle map

This map counts every empty rectangle and weights its O markings by their polynomial variables.
Rectangles may contain X markings. Its square-zero proof is supplied separately by the
annular and off-diagonal cancellation theorems.

The finite-sum and free-module construction follows the attributed TauCeti unblocked map,
with the X-avoidance condition removed. The adapted constructions originate in
`TauCeti/KnotTheory/Grid/Unblocked.lean` at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`, under Apache 2.0.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-- All composable pairs of empty rectangles, with no marking-avoidance condition. -/
noncomputable def emptyDecompositions (x z : GridState n) :
    Finset (GridRectangleDecomposition x z) :=
  GridTwoStepDecomposition.decompositionsOf
    GridRectangleBetween.emptyRectangles GridRectangleBetween.emptyRectangles x z

@[simp]
theorem mem_emptyDecompositions {x z : GridState n} (D : GridRectangleDecomposition x z) :
    D ∈ emptyDecompositions x z ↔ D.first.IsEmpty ∧ D.second.IsEmpty := by
  classical
  simp [emptyDecompositions]

/-- Summing over empty decompositions is summing over their intermediate state and rectangles. -/
theorem sum_emptyDecompositions {M : Type*} [AddCommMonoid M] (x z : GridState n)
    (w : ∀ y, GridRectangleBetween x y → GridRectangleBetween y z → M) :
    ∑ D ∈ emptyDecompositions x z, w D.middle D.first D.second =
      ∑ y, ∑ r₁ ∈ GridRectangleBetween.emptyRectangles x y,
        ∑ r₂ ∈ GridRectangleBetween.emptyRectangles y z, w y r₁ r₂ :=
  GridTwoStepDecomposition.sum_decompositionsOf
    GridRectangleBetween.emptyRectangles GridRectangleBetween.emptyRectangles w

variable (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The O-weighted sum over all empty rectangles from one state to another. -/
noncomputable def coefficient (x y : GridState n) : MvPolynomial (Fin n) R :=
  ∑ r ∈ GridRectangleBetween.emptyRectangles x y, G.OMonomial R r.toGridRectangle

/-- The full rectangle map applied to a grid-state generator. -/
noncomputable def onGenerator (x : GridState n) : GridChainMinus R n :=
  ∑ y : GridState n, Finsupp.single y (coefficient G R x y)

@[simp]
theorem onGenerator_apply (x y : GridState n) :
    onGenerator G R x y = coefficient G R x y := by
  classical
  rw [onGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The polynomial-linear map defined by the O-weighted empty rectangle count. -/
noncomputable def differential :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.lsum (MvPolynomial (Fin n) R) fun x : GridState n =>
    (LinearMap.id : MvPolynomial (Fin n) R →ₗ[MvPolynomial (Fin n) R]
      MvPolynomial (Fin n) R).smulRight (onGenerator G R x)

@[simp]
theorem differential_single (x : GridState n) :
    differential G R (Finsupp.single x 1) = onGenerator G R x := by
  rw [differential, Finsupp.lsum_single]
  simp

/-- The matrix formula for the full rectangle map on an arbitrary chain. -/
theorem differential_apply_apply (c : GridChainMinus R n) (y : GridState n) :
    differential G R c y = c.sum fun x a => a * coefficient G R x y := by
  simp [differential, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    LinearMap.smulRight_apply]

/-- The matrix coefficient of the square is the sum of all empty two-step weights. -/
theorem differential_sq_single_apply (x z : GridState n) :
    differential G R (differential G R (Finsupp.single x 1)) z =
      ∑ D ∈ emptyDecompositions x z, G.unblockedDecompositionWeight R D := by
  rw [differential_single, differential_apply_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [onGenerator_apply, coefficient, Finset.sum_mul_sum,
    GridDiagram.unblockedDecompositionWeight_def]
  exact (sum_emptyDecompositions x z fun _ r₁ r₂ =>
    G.OMonomial R r₁.toGridRectangle * G.OMonomial R r₂.toGridRectangle).symm

/-- Total exponent of an O-variable monomial. -/
def exponentSize (e : Fin n →₀ ℕ) : ℕ := ∑ c : Fin n, e c

@[simp] theorem exponentSize_add (e f : Fin n →₀ ℕ) :
    exponentSize (e + f) = exponentSize e + exponentSize f := by
  simp [exponentSize, Finset.sum_add_distrib]

@[simp] theorem exponentSize_zero : exponentSize (0 : Fin n →₀ ℕ) = 0 := by
  simp [exponentSize]

/-- The explicit monomial multiple of a grid-state generator. -/
noncomputable def monomialGenerator (e : Fin n →₀ ℕ) (x : GridState n) :
    GridChainMinus R n := Finsupp.single x (MvPolynomial.monomial e (1 : R))

/-- The exponent vector recording the O markings covered by a rectangle. -/
noncomputable def oExponent (r : GridRectangle n) : Fin n →₀ ℕ :=
  ∑ c ∈ G.OColumns r, Finsupp.single c 1

/-- The total O exponent is the number of covered O markings. -/
theorem exponentSize_oExponent (r : GridRectangle n) :
    exponentSize (oExponent G r) = (G.OColumns r).card := by
  classical
  simp only [exponentSize, oExponent, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

/-- The rectangle weight is exactly the monomial of its O exponent vector. -/
theorem OMonomial_eq_monomial_oExponent (r : GridRectangle n) :
    G.OMonomial R r = MvPolynomial.monomial (oExponent G r) (1 : R) :=
  G.OMonomial_eq_monomial R r

/-- The full differential of a monomial state is the sum of the corresponding
O-weighted monomial states over every empty rectangle. -/
theorem differential_monomialGenerator (e : Fin n →₀ ℕ) (x : GridState n) :
    differential G R (monomialGenerator R e x) =
      ∑ y : GridState n, ∑ r ∈ GridRectangleBetween.emptyRectangles x y,
        monomialGenerator R (e + oExponent G r.toGridRectangle) y := by
  classical
  rw [monomialGenerator, ← Finsupp.smul_single_one, map_smul, differential_single]
  simp only [onGenerator, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul,
    coefficient, Finsupp.single_finsetSum,
    OMonomial_eq_monomial_oExponent, MvPolynomial.monomial_mul, mul_one,
    monomialGenerator]

end OnLeConjecture.KnotFloer.GridFull
