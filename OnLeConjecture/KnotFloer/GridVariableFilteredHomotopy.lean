/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableHomotopy
public import OnLeConjecture.KnotFloer.GridFullMaslovComplex
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Diagram.Components

/-!
# Filtered O-variable homotopies through X markings

The derivative at an X-marked square counts exactly the empty rectangles containing that
marking. Each term has Maslov degree one less and Alexander filtration at least one less.
The associated O variables lie in consecutive columns along the component permutation.

This is the marking-count argument of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Lemma 13.2.5, allowing arbitrary additional X markings in the rectangles.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The next O column when following a row from its X marking to its O marking. -/
def basepointPermutation : Equiv.Perm (Fin n) := G.O.toPerm⁻¹ * G.X.toPerm

@[simp]
theorem basepointPermutation_apply (a : Fin n) :
    basepointPermutation G a = G.O.toPerm.symm (G.X a) := rfl

/-- This traversal is the inverse of the component convention used by the grid library. -/
theorem basepointPermutation_eq : basepointPermutation G = G.componentPerm⁻¹ := by
  simp only [basepointPermutation, GridDiagram.componentPerm_def, mul_inv_rev, inv_inv]

/-- The full rectangle derivative at the X marking in the given column. -/
noncomputable def xMarkingHomotopy (a : Fin n) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  squareDerivative (polynomialOSquareWeight G R) a (G.X a)

open Classical in
/-- The matrix entries count precisely all empty rectangles containing the selected X marking. -/
theorem xMarkingHomotopy_apply_apply (a : Fin n) (c : GridChainMinus R n) (y : GridState n) :
    xMarkingHomotopy G R a c y = c.sum fun x p => p *
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => (a, G.X a) ∈ r.toGridRectangle.coveredSquares),
          G.OMonomial R r.toGridRectangle := by
  simp only [xMarkingHomotopy, squareDerivative, polynomialCoefficientOperator_apply_apply,
    coeff_one_squareWeightedCoefficient_deformAtSquare, squareWeight_polynomialOSquareWeight]

/-- Every nonzero output monomial comes from one counted X-crossing rectangle. -/
theorem exists_rectangle_of_mem_support_xMarkingHomotopy (a : Fin n) (c : GridChainMinus R n)
    {y : GridState n} {f : Fin n →₀ ℕ} (hf : f ∈ (xMarkingHomotopy G R a c y).support) :
    ∃ x : GridState n, ∃ e ∈ (c x).support, ∃ r : GridRectangleBetween x y,
      r.IsEmpty ∧ (a, G.X a) ∈ r.toGridRectangle.coveredSquares ∧
        f = e + oExponent G r.toGridRectangle := by
  classical
  rw [xMarkingHomotopy_apply_apply, Finsupp.sum] at hf
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hf)
  obtain ⟨e, he, d, hd, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hx)
  obtain ⟨r, hr, hrd⟩ := G.exists_mem_of_mem_support_sum_OMonomial R hd
  obtain ⟨hre, hrX⟩ := Finset.mem_filter.mp hr
  exact ⟨x, e, he, r, (GridRectangleBetween.mem_emptyRectangles r).mp hre, hrX,
    congrArg (fun d => e + d) hrd⟩

/-- The X-square derivative lowers Maslov degree by exactly one. -/
theorem xMarkingHomotopy_mem_maslovPiece (a : Fin n) {m : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ maslovPiece G R m) : xMarkingHomotopy G R a c ∈ maslovPiece G R (m - 1) := by
  rw [mem_maslovPiece] at hc ⊢
  intro y f hf
  obtain ⟨x, e, he, r, hre, _, rfl⟩ :=
    exists_rectangle_of_mem_support_xMarkingHomotopy G R a c hf
  rw [maslovDegree_add_oExponent G r hre, hc x e he]

/-- A rectangle containing the chosen X-marked square has at least one X marking. -/
theorem one_le_card_X_of_mem (a : Fin n) {x y : GridState n} (r : GridRectangleBetween x y)
    (hr : (a, G.X a) ∈ r.toGridRectangle.coveredSquares) :
    1 ≤ (G.XSet ∩ r.toGridRectangle.coveredSquares).card := by
  classical
  exact Finset.one_le_card.mpr ⟨(a, G.X a), Finset.mem_inter.mpr
    ⟨(G.mem_XSet _).mpr rfl, hr⟩⟩

/-- The derivative at an X marking preserves the first coordinate and lowers the second by one. -/
theorem xMarkingHomotopy_mem_bifiltrationLevel (S : Type*) [CommRing S] (a : Fin n)
    {u v : ℝ} {c : GridChainMinus S n} (hc : c ∈ bifiltrationLevel G S u v) :
    xMarkingHomotopy G S a c ∈ bifiltrationLevel G S u (v - 1) := by
  rw [mem_bifiltrationLevel_iff] at hc ⊢
  intro y f hf
  obtain ⟨x, e, he, r, _, hrX, rfl⟩ :=
    exists_rectangle_of_mem_support_xMarkingHomotopy G S a c hf
  obtain ⟨hfirst, hsecond⟩ := hc x e he
  constructor
  · rw [exponentSize_add, Nat.cast_add]
    have ho := Nat.cast_nonneg (α := ℝ) (exponentSize (oExponent G r.toGridRectangle))
    linarith
  · rw [alexanderCoordinate_change]
    have hx : (1 : ℝ) ≤ ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) :=
      by exact_mod_cast one_le_card_X_of_mem G a r hrX
    linarith

/-- The X-square derivative connects the two consecutive O-variable actions. -/
theorem differential_xMarkingHomotopy [CharP R 2] (a : Fin n) :
    differential G R ∘ₗ xMarkingHomotopy G R a +
      xMarkingHomotopy G R a ∘ₗ differential G R =
      (MvPolynomial.X a + MvPolynomial.X (basepointPermutation G a) : MvPolynomial (Fin n) R) •
        (LinearMap.id : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  have h := squareDerivative_homotopy (polynomialOSquareWeight G R) a (G.X a)
  simpa only [squareWeightedDifferential_polynomialOSquareWeight, xMarkingHomotopy,
    polynomialOSquareWeight_column, polynomialOSquareWeight_row, basepointPermutation_apply] using h

/-- Add the X-square homotopies along an explicit finite component orbit. -/
noncomputable def basepointOrbitHomotopy (a : Fin n) : ℕ →
    (GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
  | 0 => 0
  | k + 1 => basepointOrbitHomotopy a k +
      xMarkingHomotopy G R ((basepointPermutation G ^ k) a)

/-- The orbit sum retains Maslov degree minus one. -/
theorem basepointOrbitHomotopy_mem_maslovPiece (a : Fin n) (k : ℕ)
    {m : ℤ} {c : GridChainMinus R n} (hc : c ∈ maslovPiece G R m) :
    basepointOrbitHomotopy G R a k c ∈ maslovPiece G R (m - 1) := by
  induction k with
  | zero => exact Submodule.zero_mem _
  | succ k ih =>
    exact Submodule.add_mem _ ih (xMarkingHomotopy_mem_maslovPiece G R _ hc)

/-- Summing X-square homotopies preserves the same strict Alexander bound. -/
theorem basepointOrbitHomotopy_mem_bifiltrationLevel (S : Type*) [CommRing S]
    (a : Fin n) (k : ℕ) {u v : ℝ} {c : GridChainMinus S n}
    (hc : c ∈ bifiltrationLevel G S u v) :
    basepointOrbitHomotopy G S a k c ∈ bifiltrationLevel G S u (v - 1) := by
  induction k with
  | zero => exact Submodule.zero_mem _
  | succ k ih =>
    exact Submodule.add_mem _ ih (xMarkingHomotopy_mem_bifiltrationLevel G S _ hc)

/-- The boundary of the orbit sum telescopes to its endpoint O-variable actions. -/
theorem differential_basepointOrbitHomotopy [CharP R 2] (a : Fin n) (k : ℕ) :
    differential G R ∘ₗ basepointOrbitHomotopy G R a k +
      basepointOrbitHomotopy G R a k ∘ₗ differential G R =
      (MvPolynomial.X a + MvPolynomial.X ((basepointPermutation G ^ k) a) :
        MvPolynomial (Fin n) R) •
          (LinearMap.id : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  induction k with
  | zero =>
    simp only [basepointOrbitHomotopy, LinearMap.comp_zero, LinearMap.zero_comp,
      add_zero, pow_zero, Equiv.Perm.one_apply, CharTwo.add_self_eq_zero, zero_smul]
  | succ k ih =>
    rw [basepointOrbitHomotopy]
    have he : (basepointPermutation G ^ (k + 1)) a =
        basepointPermutation G ((basepointPermutation G ^ k) a) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    calc
      _ = (differential G R ∘ₗ basepointOrbitHomotopy G R a k +
          basepointOrbitHomotopy G R a k ∘ₗ differential G R) +
          (differential G R ∘ₗ xMarkingHomotopy G R ((basepointPermutation G ^ k) a) +
            xMarkingHomotopy G R ((basepointPermutation G ^ k) a) ∘ₗ differential G R) := by
        simp only [LinearMap.comp_add, LinearMap.add_comp]
        abel
      _ = _ := by
        rw [ih, differential_xMarkingHomotopy, ← add_smul, he]
        congr 1
        have h (p q r : MvPolynomial (Fin n) R) : (p + q) + (q + r) = p + r := by
          calc
            _ = p + (q + q) + r := by ac_rfl
            _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
        exact h _ _ _

/-- For a knot grid, the inverse component permutation reaches every other column. -/
theorem exists_basepoint_orbit (hG : G.IsKnot) (a b : Fin n) :
    ∃ k : ℕ, (basepointPermutation G ^ k) a = b := by
  have hcycle : (basepointPermutation G).IsCycle := by
    rw [basepointPermutation_eq]
    exact (G.isKnot_iff_componentPerm_isCycle.mp hG).inv
  have hmove (a : Fin n) : basepointPermutation G a ≠ a := by
    rw [basepointPermutation_eq]
    intro h
    have hh := congrArg G.componentPerm h
    have hh' : a = G.componentPerm a := by simpa using hh
    exact G.componentPerm_apply_ne_self a hh'.symm
  exact hcycle.exists_pow_eq (hmove a) (hmove b)

/-- Choose a finite component traversal between the given O columns in a knot grid. -/
noncomputable def knotBasepointPathLength (hG : G.IsKnot) (a b : Fin n) : ℕ :=
  Classical.choose (exists_basepoint_orbit G hG a b)

theorem knotBasepointPathLength_spec (hG : G.IsKnot) (a b : Fin n) :
    (basepointPermutation G ^ knotBasepointPathLength G hG a b) a = b :=
  Classical.choose_spec (exists_basepoint_orbit G hG a b)

/-- The finite sum of explicit X-square derivatives joining two O columns of a knot grid. -/
noncomputable def knotVariableActionHomotopy (hG : G.IsKnot) (a b : Fin n) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  basepointOrbitHomotopy G R a (knotBasepointPathLength G hG a b)

/-- The chosen geometric sum is a homotopy between any two O-variable actions for a knot grid. -/
theorem differential_knotVariableActionHomotopy [CharP R 2] (hG : G.IsKnot) (a b : Fin n) :
    differential G R ∘ₗ knotVariableActionHomotopy G R hG a b +
      knotVariableActionHomotopy G R hG a b ∘ₗ differential G R =
      (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) •
        (LinearMap.id : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  rw [knotVariableActionHomotopy, differential_basepointOrbitHomotopy,
    knotBasepointPathLength_spec]

/-- Every chosen knot homotopy lowers Maslov degree by one. -/
theorem knotVariableActionHomotopy_mem_maslovPiece (hG : G.IsKnot) (a b : Fin n)
    {m : ℤ} {c : GridChainMinus R n} (hc : c ∈ maslovPiece G R m) :
    knotVariableActionHomotopy G R hG a b c ∈ maslovPiece G R (m - 1) :=
  basepointOrbitHomotopy_mem_maslovPiece G R a _ hc

/-- Every chosen knot homotopy preserves the first coordinate and lowers Alexander by one. -/
theorem knotVariableActionHomotopy_mem_bifiltrationLevel (S : Type*) [CommRing S]
    (hG : G.IsKnot) (a b : Fin n) {u v : ℝ} {c : GridChainMinus S n}
    (hc : c ∈ bifiltrationLevel G S u v) :
    knotVariableActionHomotopy G S hG a b c ∈ bifiltrationLevel G S u (v - 1) :=
  basepointOrbitHomotopy_mem_bifiltrationLevel G S a _ hc

end OnLeConjecture.KnotFloer.GridFull
