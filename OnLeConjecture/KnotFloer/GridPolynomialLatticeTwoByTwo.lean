/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeCycles
public import OnLeConjecture.KnotFloer.GridFullTwoByTwoHomology

/-!
# The degree-zero polynomial class of the two-by-two grid

The explicit two-state grading and zero differential identify native Laurent
homology in degree zero with the coefficient ring. Every such class belongs
to the polynomial homology image. Over the two-element field this gives a
proved unique nonzero class, represented by the X state with coefficient one.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable (R : Type*) [CommRing R]

/-- A degree-zero Laurent chain in the two-by-two grid has only its constant X-state term. -/
theorem twoByTwo_laurentMaslovZero_eq_single
    (c : laurentMaslovPiece GridDiagram.twoByTwo R 0) :
    c.val = Finsupp.single GridState.twoByTwoSwap
      (LaurentPolynomial.C ((c.val GridState.twoByTwoSwap).coeff 0)) := by
  apply Finsupp.ext
  intro x
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · rw [Finsupp.single_eq_of_ne GridState.twoByTwoId_ne_twoByTwoSwap]
    apply LaurentPolynomial.ext
    intro k
    change (c.val GridState.twoByTwoId).coeff k = 0
    by_contra h
    have hdeg := c.property GridState.twoByTwoId k (Finsupp.mem_support_iff.mpr h)
    rw [laurentMaslovDegree_twoByTwo_O] at hdeg
    change -1 - 2 * k = 0 at hdeg
    omega
  · rw [Finsupp.single_eq_same]
    apply LaurentPolynomial.ext
    intro k
    by_cases hk : k = 0
    · subst k
      simp [← LaurentPolynomial.single_eq_C, -LaurentPolynomial.single_eq_C_mul_T]
    · have hc : (c.val GridState.twoByTwoSwap).coeff k = 0 := by
        by_contra h
        have hdeg := c.property GridState.twoByTwoSwap k (Finsupp.mem_support_iff.mpr h)
        rw [laurentMaslovDegree_twoByTwo_X] at hdeg
        change -2 * k = 0 at hdeg
        omega
      simp [hc, ← LaurentPolynomial.single_eq_C, hk, -LaurentPolynomial.single_eq_C_mul_T]

/-- Constant X-state coefficient identifies the native Laurent degree-zero piece with R. -/
def twoByTwoLaurentMaslovZeroPieceEquiv :
    laurentMaslovPiece GridDiagram.twoByTwo R 0 ≃ₗ[R] R where
  toFun c := (c.val GridState.twoByTwoSwap).coeff 0
  invFun r := ⟨Finsupp.single GridState.twoByTwoSwap (LaurentPolynomial.C r), by
    simpa only [LaurentPolynomial.single_eq_C, laurentMaslovDegree_zero,
      GridDiagram.maslovOℤ_twoByTwo_twoByTwoSwap] using
      single_monomial_mem_laurentMaslovPiece GridDiagram.twoByTwo R 0 GridState.twoByTwoSwap r⟩
  left_inv c := Subtype.ext (twoByTwo_laurentMaslovZero_eq_single R c).symm
  right_inv r := by simp [← LaurentPolynomial.single_eq_C, -LaurentPolynomial.single_eq_C_mul_T]
  map_add' c d := by simp
  map_smul' r c := by simp

variable [CharP R 2]

/-- All native graded differentials of the two-by-two Laurent complex vanish. -/
theorem laurentMaslovComplex_twoByTwo_d_eq_zero (i j : ℤ) :
    (laurentMaslovComplex GridDiagram.twoByTwo R).d i j = 0 := by
  by_cases hij : j + 1 = i
  · subst i
    rw [laurentMaslovComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change laurentDifferential GridDiagram.twoByTwo R c.val = 0
    rw [laurentDifferential_twoByTwo_eq_zero]
    rfl
  · exact (laurentMaslovComplex GridDiagram.twoByTwo R).shape i j hij

/-- Native Laurent homology in degree zero of the computed grid is exactly R. -/
def twoByTwoLaurentMaslovZeroHomologyEquiv :
    (laurentMaslovComplex GridDiagram.twoByTwo R).homology 0 ≃ₗ[R] R :=
  (((laurentMaslovComplex GridDiagram.twoByTwo R).isoHomologyπ 1 0
      (by rw [ChainComplex.prev]; rfl) (laurentMaslovComplex_twoByTwo_d_eq_zero R 1 0)).symm ≪≫
    (laurentMaslovComplex GridDiagram.twoByTwo R).iCyclesIso 0 (-1)
      (by rw [ChainComplex.next]; rfl)
      (laurentMaslovComplex_twoByTwo_d_eq_zero R 0 (-1))).toLinearEquiv
    |>.trans (laurentMaslovChainEquiv GridDiagram.twoByTwo R 0)
    |>.trans (twoByTwoLaurentMaslovZeroPieceEquiv R)

/-- On a native cycle, the computed equivalence reads the constant X-state coefficient. -/
theorem twoByTwoLaurentMaslovZeroHomologyEquiv_homologyπ
    (z : (laurentMaslovComplex GridDiagram.twoByTwo R).cycles 0) :
    twoByTwoLaurentMaslovZeroHomologyEquiv R
      ((laurentMaslovComplex GridDiagram.twoByTwo R).homologyπ 0 z) =
        ((laurentMaslovChainEquiv GridDiagram.twoByTwo R 0
          ((laurentMaslovComplex GridDiagram.twoByTwo R).iCycles 0 z) : LaurentChain R 2)
            GridState.twoByTwoSwap).coeff 0 := by
  let L := laurentMaslovComplex GridDiagram.twoByTwo R
  have hp : (ComplexShape.down ℤ).prev 0 = 1 := by rw [ChainComplex.prev]; rfl
  have hd : L.d 1 0 = 0 := laurentMaslovComplex_twoByTwo_d_eq_zero R 1 0
  have h := congrArg (fun f : L.cycles 0 ⟶ L.cycles 0 => f z)
    (L.isoHomologyπ_hom_inv_id 1 0 hp hd)
  change (L.isoHomologyπ 1 0 hp hd).inv (L.homologyπ 0 z) = z at h
  change ((laurentMaslovChainEquiv GridDiagram.twoByTwo R 0
    (L.iCycles 0 ((L.isoHomologyπ 1 0 hp hd).inv (L.homologyπ 0 z))) :
      LaurentChain R 2) GridState.twoByTwoSwap).coeff 0 = _
  rw [h]

/-- The constant X-state term as a native cycle. -/
def twoByTwoLaurentPolynomialCycle :
    (laurentMaslovComplex GridDiagram.twoByTwo R).cycles 0 :=
  (laurentMaslovComplex GridDiagram.twoByTwo R).cyclesMk
    ((laurentMaslovChainEquiv GridDiagram.twoByTwo R 0).symm
      ((twoByTwoLaurentMaslovZeroPieceEquiv R).symm 1)) (-1)
    (by rw [ChainComplex.next]; rfl) (by rw [laurentMaslovComplex_twoByTwo_d_eq_zero]; rfl)

/-- The chosen cycle has exactly the X-state coefficient one. -/
theorem twoByTwoLaurentPolynomialCycle_apply :
    (laurentMaslovChainEquiv GridDiagram.twoByTwo R 0
      ((laurentMaslovComplex GridDiagram.twoByTwo R).iCycles 0
        (twoByTwoLaurentPolynomialCycle R)) : LaurentChain R 2) =
          Finsupp.single GridState.twoByTwoSwap 1 := by
  have h := (laurentMaslovComplex GridDiagram.twoByTwo R).i_cyclesMk
    ((laurentMaslovChainEquiv GridDiagram.twoByTwo R 0).symm
      ((twoByTwoLaurentMaslovZeroPieceEquiv R).symm 1)) (-1)
    (by rw [ChainComplex.next]; rfl)
    (show (laurentMaslovComplex GridDiagram.twoByTwo R).d 0 (-1) _ = 0 by
      rw [laurentMaslovComplex_twoByTwo_d_eq_zero]; rfl)
  change (laurentMaslovComplex GridDiagram.twoByTwo R).iCycles 0
    (twoByTwoLaurentPolynomialCycle R) = _ at h
  rw [h, LinearEquiv.apply_symm_apply]
  change Finsupp.single GridState.twoByTwoSwap (LaurentPolynomial.C 1) = _
  rw [map_one]

/-- Every degree-zero Laurent homology class in the two-by-two grid has a
polynomial representative. -/
theorem twoByTwo_polynomialHomologyImage_eq_top (a : Fin 2) :
    polynomialHomologyImage R GridDiagram.twoByTwo a 0 = ⊤ := by
  apply top_unique
  intro ξ _
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((laurentMaslovComplex GridDiagram.twoByTwo R).homologyπ 0)).mp inferInstance ξ
  apply (mem_polynomialHomologyImage_iff_exists_cycle R GridDiagram.twoByTwo a 0 _).mpr
  refine ⟨z, ?_, rfl⟩
  let c := laurentMaslovChainEquiv GridDiagram.twoByTwo R 0
    ((laurentMaslovComplex GridDiagram.twoByTwo R).iCycles 0 z)
  intro x k hk
  change k ∈ (c.val x).coeff.support at hk
  rw [twoByTwo_laurentMaslovZero_eq_single R c] at hk
  by_cases hx : x = GridState.twoByTwoSwap
  · subst x
    rw [Finsupp.single_eq_same, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.coeff_single] at hk
    have : k = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    omega
  · simp [Finsupp.single_eq_of_ne hx] at hk

omit [CharP R 2] in
/-- Positive Maslov degrees contain no polynomial chains in the two-by-two grid. -/
theorem twoByTwo_oneVariableMaslovPiece_eq_bot (a : Fin 2) (m : ℤ) (hm : 0 < m) :
    oneVariableMaslovPiece R GridDiagram.twoByTwo a m = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  change c = 0
  apply Finsupp.ext
  intro x
  apply Polynomial.ext
  intro k
  change (c x).coeff k = 0
  by_contra h
  have hd := (mem_oneVariableMaslovPiece_iff R GridDiagram.twoByTwo a m c).mp hc
    x k (Polynomial.mem_support_iff.mpr h)
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · rw [GridDiagram.maslovOℤ_twoByTwo_twoByTwoId] at hd
    omega
  · rw [GridDiagram.maslovOℤ_twoByTwo_twoByTwoSwap] at hd
    omega

/-- Positive-degree polynomial homology vanishes in the explicitly computed base grid. -/
theorem twoByTwo_oneVariable_homology_eq_zero (a : Fin 2) (m : ℤ) (hm : 0 < m)
    (ξ : (oneVariableMaslovComplex R GridDiagram.twoByTwo a).homology m) : ξ = 0 := by
  let P := oneVariableMaslovComplex R GridDiagram.twoByTwo a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (P.homologyπ m)).mp inferInstance ξ
  have hz : z = 0 := by
    apply (ModuleCat.mono_iff_injective (P.iCycles m)).mp inferInstance
    rw [map_zero]
    apply Subtype.ext
    exact (twoByTwo_oneVariableMaslovPiece_eq_bot R a m hm).le (P.iCycles m z).property
  rw [hz, map_zero]

/-- The class with constant X-state coefficient one in the computed native homology. -/
def twoByTwoLaurentPolynomialClass :
    (laurentMaslovComplex GridDiagram.twoByTwo R).homology 0 :=
  (twoByTwoLaurentMaslovZeroHomologyEquiv R).symm 1

/-- The homology class defined by its coefficient is represented by the stated cycle. -/
theorem twoByTwoLaurentPolynomialClass_eq_homologyπ :
    twoByTwoLaurentPolynomialClass R =
      (laurentMaslovComplex GridDiagram.twoByTwo R).homologyπ 0
        (twoByTwoLaurentPolynomialCycle R) := by
  apply (twoByTwoLaurentMaslovZeroHomologyEquiv R).injective
  rw [twoByTwoLaurentPolynomialClass, LinearEquiv.apply_symm_apply,
    twoByTwoLaurentMaslovZeroHomologyEquiv_homologyπ,
    twoByTwoLaurentPolynomialCycle_apply]
  simp

/-- The computed class is nonzero. -/
theorem twoByTwoLaurentPolynomialClass_ne_zero [Nontrivial R] :
    twoByTwoLaurentPolynomialClass R ≠ 0 := by
  intro h
  have hh := congrArg (twoByTwoLaurentMaslovZeroHomologyEquiv R) h
  exact one_ne_zero (by
    simpa only [twoByTwoLaurentPolynomialClass, LinearEquiv.apply_symm_apply, map_zero] using hh)

/-- The computed nonzero class lies in the image of polynomial homology. -/
theorem twoByTwoLaurentPolynomialClass_mem_image (a : Fin 2) :
    twoByTwoLaurentPolynomialClass R ∈ polynomialHomologyImage R GridDiagram.twoByTwo a 0 := by
  rw [twoByTwo_polynomialHomologyImage_eq_top]
  trivial

/-- Over the two-element field, every nonzero native degree-zero class is the computed class. -/
theorem twoByTwoLaurentPolynomialClass_unique
    (ξ : (laurentMaslovComplex GridDiagram.twoByTwo (ZMod 2)).homology 0) (hξ : ξ ≠ 0) :
    ξ = twoByTwoLaurentPolynomialClass (ZMod 2) := by
  apply (twoByTwoLaurentMaslovZeroHomologyEquiv (ZMod 2)).injective
  rw [twoByTwoLaurentPolynomialClass, LinearEquiv.apply_symm_apply]
  have hnonzero : twoByTwoLaurentMaslovZeroHomologyEquiv (ZMod 2) ξ ≠ 0 :=
    (map_ne_zero_iff _ (twoByTwoLaurentMaslovZeroHomologyEquiv (ZMod 2)).injective).mpr hξ
  have hcases (r : ZMod 2) : r = 0 ∨ r = 1 := by
    fin_cases r
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact (hcases _).resolve_left hnonzero

/-- The actual polynomial homology image of the two-by-two grid has a unique nonzero class. -/
theorem existsUnique_twoByTwo_nonzero_polynomialHomologyImage (a : Fin 2) :
    ∃! ξ : (laurentMaslovComplex GridDiagram.twoByTwo (ZMod 2)).homology 0,
      ξ ≠ 0 ∧ ξ ∈ polynomialHomologyImage (ZMod 2) GridDiagram.twoByTwo a 0 := by
  refine ⟨twoByTwoLaurentPolynomialClass (ZMod 2),
    ⟨twoByTwoLaurentPolynomialClass_ne_zero (ZMod 2),
      twoByTwoLaurentPolynomialClass_mem_image (ZMod 2) a⟩, ?_⟩
  intro ξ hξ
  exact twoByTwoLaurentPolynomialClass_unique ξ hξ.1

end OnLeConjecture.KnotFloer.GridFull
