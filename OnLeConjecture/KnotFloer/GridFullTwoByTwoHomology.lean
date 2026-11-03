/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullTwoByTwo
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Native Laurent homology of the two-by-two grid

The differential computed from all four rectangles vanishes after the O variables are
identified. The native homology of this complex is therefore the free Laurent module on
the two states. We give an explicit equivalence with two copies of the Laurent ring,
ordered by the X-state and then the O-state. Their initial Maslov and Alexander degrees
are `(0,0)` and `(-1,-1)`, respectively.

This is a computation for a specific grid complex. It supplies no identification of all
multipointed grid homologies with a rank-one tower.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The chain object of the native one-object Laurent complex. -/
@[simp]
theorem laurentComplex_X {n : ℕ} (G : GridDiagram n) (i : Unit) :
    (laurentComplex G R).X i = ModuleCat.of (LaurentPolynomial R) (LaurentChain R n) :=
  oneObjectHomologicalComplex_X _ _ _ _

/-- The native Laurent differential transported to its chain module. -/
theorem laurentComplex_d {n : ℕ} (G : GridDiagram n) :
    (laurentComplex G R).d () () = eqToHom (laurentComplex_X R G ()) ≫
      ModuleCat.ofHom (laurentDifferential G R) ≫ eqToHom (laurentComplex_X R G ()).symm := by
  unfold laurentComplex
  exact oneObjectHomologicalComplex_d _ _ _

/-- The single native differential of the two-by-two Laurent complex is zero. -/
theorem laurentComplex_twoByTwo_d_eq_zero :
    (laurentComplex GridDiagram.twoByTwo R).d () () = 0 := by
  rw [laurentComplex_d, laurentDifferential_twoByTwo_eq_zero, ModuleCat.ofHom_zero]
  simp

/-- Native homology identifies with the Laurent chain module because both adjacent maps vanish. -/
noncomputable def twoByTwoLaurentHomologyEquivChain :
    (laurentComplex GridDiagram.twoByTwo R).homology () ≃ₗ[LaurentPolynomial R]
      LaurentChain R 2 :=
  (((laurentComplex GridDiagram.twoByTwo R).isoHomologyπ () () rfl
      (laurentComplex_twoByTwo_d_eq_zero R)).symm ≪≫
    (laurentComplex GridDiagram.twoByTwo R).iCyclesIso () () rfl
      (laurentComplex_twoByTwo_d_eq_zero R) ≪≫
    eqToIso (laurentComplex_X R GridDiagram.twoByTwo ())).toLinearEquiv

/-- Read a Laurent chain's X-state and O-state coefficients. -/
noncomputable def twoByTwoLaurentChainEquivProduct :
    LaurentChain R 2 ≃ₗ[LaurentPolynomial R] (LaurentPolynomial R × LaurentPolynomial R) where
  toFun c := (c GridState.twoByTwoSwap, c GridState.twoByTwoId)
  invFun p := Finsupp.single GridState.twoByTwoSwap p.1 + Finsupp.single GridState.twoByTwoId p.2
  left_inv c := by
    ext x
    rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl <;>
      simp [GridState.twoByTwoId_ne_twoByTwoSwap.symm]
  right_inv p := by
    simp [GridState.twoByTwoId_ne_twoByTwoSwap.symm]
  map_add' c d := rfl
  map_smul' a c := rfl

/-- The all-O-collapsed native Laurent homology is two copies of the Laurent ring. -/
noncomputable def twoByTwoLaurentHomologyEquiv :
    (laurentComplex GridDiagram.twoByTwo R).homology () ≃ₗ[LaurentPolynomial R]
      (LaurentPolynomial R × LaurentPolynomial R) :=
  (twoByTwoLaurentHomologyEquivChain R).trans (twoByTwoLaurentChainEquivProduct R)

/-- In particular this homology has Laurent rank two, rather than one. -/
theorem finrank_twoByTwoLaurentHomology [Nontrivial R] :
    Module.finrank (LaurentPolynomial R)
      ((laurentComplex GridDiagram.twoByTwo R).homology ()) = 2 := by
  rw [(twoByTwoLaurentHomologyEquiv R).finrank_eq, Module.finrank_prod]
  simp

/-- The X-state tower has Maslov degrees `-2k`. -/
theorem laurentMaslovDegree_twoByTwo_X (k : ℤ) :
    laurentMaslovDegree GridDiagram.twoByTwo k GridState.twoByTwoSwap = -2 * k := by
  rw [laurentMaslovDegree, GridDiagram.maslovOℤ_twoByTwo_twoByTwoSwap]
  omega

/-- The O-state tower has Maslov degrees `-1-2k`. -/
theorem laurentMaslovDegree_twoByTwo_O (k : ℤ) :
    laurentMaslovDegree GridDiagram.twoByTwo k GridState.twoByTwoId = -1 - 2 * k := by
  rw [laurentMaslovDegree, GridDiagram.maslovOℤ_twoByTwo_twoByTwoId]

omit [CharP R 2] in
/-- A monomial state lies at precisely its two coefficient bounds. -/
theorem laurentMonomialGenerator_mem_bifiltrationLevel_iff {n : ℕ} (G : GridDiagram n)
    [Nontrivial R] (k : ℤ) (x : GridState n) (a b : ℝ) :
    laurentMonomialGenerator R k x ∈ laurentBifiltrationLevel G R a b ↔
      -(k : ℝ) ≤ a ∧ (G.alexander x : ℝ) - k ≤ b := by
  classical
  constructor
  · intro h
    apply h x k
    simp only [laurentMonomialGenerator, Finsupp.single_eq_same]
    change k ∈ (Finsupp.single k (1 : R)).support
    simp
  · intro h y j hj
    by_cases hy : y = x
    · subst y
      simp only [laurentMonomialGenerator, Finsupp.single_eq_same] at hj
      change j ∈ (Finsupp.single k (1 : R)).support at hj
      have hjk : j = k := by simpa using hj
      simpa [hjk] using h
    · simp [laurentMonomialGenerator, Finsupp.single_eq_of_ne hy] at hj

omit [CharP R 2] in
/-- The X-state tower has filtration coordinates `(-k,-k)`. -/
theorem laurentMonomialGenerator_twoByTwo_X_mem_iff [Nontrivial R] (k : ℤ) (a b : ℝ) :
    laurentMonomialGenerator R k GridState.twoByTwoSwap ∈
      laurentBifiltrationLevel GridDiagram.twoByTwo R a b ↔
        -(k : ℝ) ≤ a ∧ -(k : ℝ) ≤ b := by
  rw [laurentMonomialGenerator_mem_bifiltrationLevel_iff]
  simp only [GridDiagram.alexander_twoByTwo_twoByTwoSwap, Rat.cast_zero, zero_sub]

omit [CharP R 2] in
/-- The O-state tower has filtration coordinates `(-k,-1-k)`. -/
theorem laurentMonomialGenerator_twoByTwo_O_mem_iff [Nontrivial R] (k : ℤ) (a b : ℝ) :
    laurentMonomialGenerator R k GridState.twoByTwoId ∈
      laurentBifiltrationLevel GridDiagram.twoByTwo R a b ↔
        -(k : ℝ) ≤ a ∧ -1 - (k : ℝ) ≤ b := by
  rw [laurentMonomialGenerator_mem_bifiltrationLevel_iff]
  simp only [GridDiagram.alexander_twoByTwo_twoByTwoId, Rat.cast_neg, Rat.cast_one]

end OnLeConjecture.KnotFloer.GridFull
