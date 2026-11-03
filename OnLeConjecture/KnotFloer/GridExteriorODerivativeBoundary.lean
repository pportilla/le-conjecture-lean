/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOColour

/-!
# Derivatives of polynomial degree-zero cycles are boundaries

For a grid diagram `G` of size `n ≥ 2` over `ZMod 2`, every polynomial cycle of Maslov degree one
is a boundary, because the degree-one polynomial homology image vanishes
(`grid_polynomialHomologyImage_eq_bot`). Consequently, for a polynomial cycle `c` of Maslov degree
zero and every set `P` of columns, the colour derivative `Φ_P c` is a boundary
(`exists_oDerivative_eq_laurentDifferential`). This is the chain-level form of the statement
"every derivative annihilates the canonical class" of Section 4 of the written proof of
Statement E (`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`).

The colour derivatives raise the Maslov degree by one and preserve polynomial chains
(`oDerivative_mem_maslovPiece`, `isPolynomialChain_oDerivative_set`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Colour derivatives raise the Maslov degree by one. -/
theorem oDerivative_mem_maslovPiece (G : GridDiagram n) (P : Finset (Fin n)) {m : ℤ}
    {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    oDerivative R G P c ∈ laurentMaslovPiece G R (m + 1) := by
  rw [oDerivative_eq_sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun h _ => oDerivative_singleton_mem_maslovPiece G h hc

/-- Polynomial chains are closed under addition. -/
theorem IsPolynomialChain.add {c c' : LaurentChain R n} (hc : IsPolynomialChain c)
    (hc' : IsPolynomialChain c') : IsPolynomialChain (c + c') := by
  intro x k hk
  rw [Finsupp.add_apply, AddMonoidAlgebra.coeff_add] at hk
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with h | h
  · exact hc x k h
  · exact hc' x k h

theorem isPolynomialChain_zero : IsPolynomialChain (0 : LaurentChain R n) := by
  intro x k hk
  simp at hk

/-- Colour derivatives preserve polynomial chains. -/
theorem isPolynomialChain_oDerivative_set {G : GridDiagram n} (P : Finset (Fin n))
    {c : LaurentChain R n} (hc : IsPolynomialChain c) :
    IsPolynomialChain (oDerivative R G P c) := by
  classical
  rw [oDerivative_eq_sum, LinearMap.sum_apply]
  induction P using Finset.induction_on with
  | empty => simpa using isPolynomialChain_zero
  | insert h P hP ih =>
    rw [Finset.sum_insert hP]
    exact (isPolynomialChain_oDerivative h hc).add ih

/-- Every polynomial cycle of Maslov degree one is a boundary. -/
theorem exists_eq_laurentDifferential_of_polynomial_degree_one {G : GridDiagram n} (hn : 2 ≤ n)
    {e : LaurentChain (ZMod 2) n} (he : e ∈ laurentMaslovPiece G (ZMod 2) 1)
    (heD : laurentDifferential G (ZMod 2) e = 0) (hepoly : IsPolynomialChain e) :
    ∃ w : LaurentChain (ZMod 2) n, e = laurentDifferential G (ZMod 2) w := by
  let C := laurentMaslovComplex G (ZMod 2)
  let eNative : C.X 1 := (laurentMaslovChainEquiv G (ZMod 2) 1).symm ⟨e, he⟩
  have heNative : C.d 1 0 eNative = 0 := by
    apply (laurentMaslovChainEquiv G (ZMod 2) 0).injective
    apply Subtype.ext
    rw [map_zero]
    exact (laurentMaslovChainEquiv_d G (ZMod 2) 0 eNative).trans
      (by
        change laurentDifferential G (ZMod 2) (laurentMaslovChainEquiv G (ZMod 2) 1 eNative) = 0
        simpa only [eNative, LinearEquiv.apply_symm_apply] using heD)
  let w := C.cyclesMk eNative 0 (by simp [ChainComplex.next]) heNative
  have hw : C.iCycles 1 w = eNative :=
    C.i_cyclesMk eNative 0 (by simp [ChainComplex.next]) heNative
  have hwc : (laurentMaslovChainEquiv G (ZMod 2) 1 (C.iCycles 1 w) : LaurentChain (ZMod 2) n) =
      e := by
    rw [hw]
    exact congrArg Subtype.val ((laurentMaslovChainEquiv G (ZMod 2) 1).apply_symm_apply ⟨e, he⟩)
  have hwimage : C.homologyπ 1 w ∈ polynomialHomologyImage (ZMod 2) G ⟨0, by omega⟩ 1 := by
    apply (mem_polynomialHomologyImage_iff_exists_cycle (ZMod 2) G ⟨0, by omega⟩ 1 _).mpr
    refine ⟨w, ?_, rfl⟩
    intro x k hk
    rw [hwc] at hk
    exact hepoly x k hk
  have hwzero : C.homologyπ 1 w = 0 := by
    rw [grid_polynomialHomologyImage_eq_bot (ZMod 2) G hn ⟨0, by omega⟩ 1 one_pos] at hwimage
    exact hwimage
  obtain ⟨b, hb⟩ := RealFiltration.exists_boundary_of_homologyπ_eq
    (C := C) (i := (1 : ℤ)) (j := (2 : ℤ)) (by simp [ChainComplex.prev])
    (z := w) (z' := 0) (by simpa only [map_zero] using hwzero)
  simp only [map_zero, zero_add] at hb
  refine ⟨laurentMaslovChainEquiv G (ZMod 2) 2 b, ?_⟩
  rw [← hwc, hb]
  exact laurentMaslovChainEquiv_d G (ZMod 2) 1 b

/-- The colour derivative of a polynomial cycle of Maslov degree zero is a boundary. -/
theorem exists_oDerivative_eq_laurentDifferential {G : GridDiagram n} (hn : 2 ≤ n)
    (P : Finset (Fin n)) {c : LaurentChain (ZMod 2) n} (hc : c ∈ laurentMaslovPiece G (ZMod 2) 0)
    (hcD : laurentDifferential G (ZMod 2) c = 0) (hcpoly : IsPolynomialChain c) :
    ∃ w : LaurentChain (ZMod 2) n,
      oDerivative (ZMod 2) G P c = laurentDifferential G (ZMod 2) w := by
  refine exists_eq_laurentDifferential_of_polynomial_degree_one hn ?_ ?_
    (isPolynomialChain_oDerivative_set P hcpoly)
  · simpa using oDerivative_mem_maslovPiece (R := ZMod 2) G P hc
  · have hcomm := LinearMap.congr_fun
      (laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G P) c
    simp only [LinearMap.comp_apply] at hcomm
    rw [hcomm, hcD, map_zero]

end OnLeConjecture.KnotFloer.GridFull
