/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusNormalization
public import OnLeConjecture.KnotFloer.SpectralDualCertificate

/-!
# Spectral normalization at zero for anti-diagonal grids

A degree-zero cycle with strictly negative first filtration coordinate is U times
a polynomial cycle of degree two. Vanishing of the degree-two polynomial homology
image therefore excludes such a representative of a nonzero class. The selected
anti-diagonal class has a polynomial representative and has threshold zero at t = 0.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2] (G : GridDiagram n)

/-- At parameter zero the weighted filtration bounds the first coordinate itself. -/
theorem weighted_zero_laurentMaslov_level_le (m : ℤ) (s : ℝ) :
    ((laurentMaslovBifiltration G R).weighted 0).level s m ≤
      (laurentMaslovBifiltration G R).level s (maslovCoordinateBound G m) m := by
  apply Submodule.span_le.mpr
  rintro c ⟨a, b, hc, hweight⟩ x k hk
  exact ⟨(hc x k hk).1.trans (by simpa using hweight),
    (laurentMaslovBifiltration_bound G R m c x k hk).2⟩

/-- If the degree-two polynomial image vanishes, a degree-zero cycle divisible by U
as a polynomial chain represents zero in Laurent homology. -/
theorem homologyπ_eq_zero_of_positive_exponents (a : Fin n)
    (himage : polynomialHomologyImage R G a 2 = ⊥)
    (z : (laurentMaslovComplex G R).cycles 0)
    (hz : ∀ x k, k ∈ ((laurentMaslovChainEquiv G R 0
      ((laurentMaslovComplex G R).iCycles 0 z) : LaurentChain R n) x).coeff.support →
        1 ≤ k) :
    (laurentMaslovComplex G R).homologyπ 0 z = 0 := by
  classical
  let C := laurentMaslovComplex G R
  let c : LaurentChain R n := laurentMaslovChainEquiv G R 0 (C.iCycles 0 z)
  have hc : c ∈ laurentMaslovPiece G R 0 :=
    (laurentMaslovChainEquiv G R 0 (C.iCycles 0 z)).property
  have hcD : laurentDifferential G R c = 0 := by
    have h := congrArg (fun f : C.cycles 0 ⟶ C.X (-1) => f z) (C.iCycles_d 0 (-1))
    change C.d 0 (-1) (C.iCycles 0 z) = 0 at h
    have hd := laurentMaslovChainEquiv_d G R (-1) (C.iCycles 0 z)
    change (laurentMaslovChainEquiv G R (-1) (C.d 0 (-1) (C.iCycles 0 z)) :
      LaurentChain R n) = laurentDifferential G R c at hd
    rw [h, map_zero] at hd
    exact hd.symm
  let d : LaurentChain R n := (LaurentPolynomial.T (-1) : LaurentPolynomial R) • c
  have hd : d ∈ laurentMaslovPiece G R 2 := by
    exact laurentMonomial_smul_mem_maslovPiece G (-1) (1 : R) hc
  have hdD : laurentDifferential G R d = 0 := by
    dsimp only [d]
    rw [map_smul, hcD, smul_zero]
  let dNative : C.X 2 := (laurentMaslovChainEquiv G R 2).symm ⟨d, hd⟩
  have hdNative : C.d 2 1 dNative = 0 := by
    apply (laurentMaslovChainEquiv G R 1).injective
    apply Subtype.ext
    rw [map_zero]
    exact (laurentMaslovChainEquiv_d G R 1 dNative).trans
      (by
        change laurentDifferential G R (laurentMaslovChainEquiv G R 2 dNative) = 0
        simpa only [dNative, LinearEquiv.apply_symm_apply] using hdD)
  let w := C.cyclesMk dNative 1 (by simp [ChainComplex.next]) hdNative
  have hw : C.iCycles 2 w = dNative :=
    C.i_cyclesMk dNative 1 (by simp [ChainComplex.next]) hdNative
  have hwc : (laurentMaslovChainEquiv G R 2 (C.iCycles 2 w) : LaurentChain R n) = d := by
    rw [hw]
    exact congrArg Subtype.val ((laurentMaslovChainEquiv G R 2).apply_symm_apply ⟨d, hd⟩)
  have hwimage : C.homologyπ 2 w ∈ polynomialHomologyImage R G a 2 := by
    apply (mem_polynomialHomologyImage_iff_exists_cycle R G a 2 _).mpr
    refine ⟨w, ?_, rfl⟩
    intro x k hk
    rw [hwc] at hk
    change k ∈ (((LaurentPolynomial.T (-1) : LaurentPolynomial R) • c) x).coeff.support at hk
    rw [Finsupp.smul_apply, smul_eq_mul] at hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp
      (AddMonoidAlgebra.support_coeff_single_mul_subset (c x) (1 : R) (-1) hk)
    have hlpos := hz x l hl
    omega
  have hwzero : C.homologyπ 2 w = 0 := by
    rw [himage] at hwimage
    exact hwimage
  obtain ⟨b, hb⟩ := RealFiltration.exists_boundary_of_homologyπ_eq
    (C := C) (i := (2 : ℤ)) (j := (3 : ℤ)) (by simp [ChainComplex.prev])
    (z := w) (z' := 0) (by simpa only [map_zero] using hwzero)
  simp only [map_zero, zero_add] at hb
  have hdb : d = laurentDifferential G R (laurentMaslovChainEquiv G R 3 b) := by
    rw [← hwc, hb]
    exact laurentMaslovChainEquiv_d G R 2 b
  let vchain : LaurentChain R n :=
    (LaurentPolynomial.T 1 : LaurentPolynomial R) •
      (laurentMaslovChainEquiv G R 3 b : LaurentChain R n)
  have hv : vchain ∈ laurentMaslovPiece G R 1 :=
    laurentMonomial_smul_mem_maslovPiece G 1 (1 : R)
      (laurentMaslovChainEquiv G R 3 b).property
  have hvD : laurentDifferential G R vchain = c := by
    dsimp only [vchain]
    rw [map_smul, ← hdb]
    dsimp only [d]
    rw [smul_smul, ← LaurentPolynomial.T_add]
    simp
  let v : C.X 1 := (laurentMaslovChainEquiv G R 1).symm ⟨vchain, hv⟩
  have hzboundary : z = C.toCycles 1 0 v := by
    apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
    have hi : C.iCycles 0 (C.toCycles 1 0 v) = C.d 1 0 v :=
      congrArg (fun f : C.X 1 ⟶ C.X 0 => f v) (C.toCycles_i 1 0)
    rw [hi]
    apply (laurentMaslovChainEquiv G R 0).injective
    apply Subtype.ext
    exact (show c = laurentDifferential G R (laurentMaslovChainEquiv G R 1 v) by
      simpa only [v, LinearEquiv.apply_symm_apply] using hvD.symm).trans
        (laurentMaslovChainEquiv_d G R 0 v).symm
  rw [hzboundary]
  exact congrArg (fun f : C.X 1 ⟶ C.homology 0 => f v) (C.toCycles_comp_homologyπ 1 0)

/-- Every polynomial degree-zero class has a representative at weighted level zero
when the parameter is zero. -/
theorem representedBelow_zero_of_mem_polynomialHomologyImage (a : Fin n)
    (ξ : (laurentMaslovComplex G R).homology 0)
    (hξ : ξ ∈ polynomialHomologyImage R G a 0) :
    ((laurentMaslovBifiltration G R).weighted 0).RepresentedBelow 0 ξ 0 := by
  obtain ⟨z, hz, hclass⟩ := (mem_polynomialHomologyImage_iff_exists_cycle R G a 0 ξ).mp hξ
  refine ⟨z, Submodule.subset_span ⟨0, maslovCoordinateBound G 0, ?_, by simp⟩, hclass⟩
  intro x k hk
  refine ⟨?_, (laurentMaslovBifiltration_bound G R 0
    ((laurentMaslovComplex G R).iCycles 0 z) x k hk).2⟩
  exact neg_nonpos.mpr (by exact_mod_cast hz x k hk)

/-- Vanishing of the positive polynomial image excludes every negative-level
representative of a nonzero class at parameter zero. -/
theorem zero_le_weighted_zero_spectralThreshold (a : Fin n)
    (himage : polynomialHomologyImage R G a 2 = ⊥)
    (ξ : (laurentMaslovComplex G R).homology 0) (hξ : ξ ≠ 0) :
    0 ≤ ((laurentMaslovBifiltration G R).weighted 0).spectralThreshold 0 ξ := by
  apply RealFiltration.le_spectralThreshold
  rintro s ⟨z, hz, hclass⟩
  rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
  by_contra hs
  have hsneg : s < 0 := lt_of_not_ge hs
  have hcoeff := weighted_zero_laurentMaslov_level_le R G 0 s hz
  have hzpos : ∀ x k, k ∈ ((laurentMaslovChainEquiv G R 0
      ((laurentMaslovComplex G R).iCycles 0 z) : LaurentChain R n) x).coeff.support →
        1 ≤ k := by
    intro x k hk
    have hkreal := (hcoeff x k hk).1
    have hkpos : (0 : ℝ) < k := by linarith
    have hkint : (0 : ℤ) < k := by exact_mod_cast hkpos
    omega
  exact hξ (hclass.symm.trans (homologyπ_eq_zero_of_positive_exponents R G a himage z hzpos))

/-- A nonzero polynomial class has threshold zero at parameter zero whenever the
degree-two polynomial homology image vanishes. -/
theorem weighted_zero_spectralThreshold_eq_zero_of_polynomialImage (a : Fin n)
    (himage : polynomialHomologyImage R G a 2 = ⊥)
    (ξ : (laurentMaslovComplex G R).homology 0) (hξ : ξ ≠ 0)
    (hmem : ξ ∈ polynomialHomologyImage R G a 0) :
    ((laurentMaslovBifiltration G R).weighted 0).spectralThreshold 0 ξ = 0 := by
  apply le_antisymm
  · simpa only [EReal.coe_zero] using RealFiltration.spectralThreshold_le_of_representedBelow
      (representedBelow_zero_of_mem_polynomialHomologyImage R G a ξ hmem)
  · exact zero_le_weighted_zero_spectralThreshold R G a himage ξ hξ

/-- The selected corner class of every anti-diagonal O grid has threshold zero at t = 0. -/
theorem antiDiagonalCornerNativeClass_spectralThreshold_zero [Nontrivial R]
    (hN : 2 ≤ n) (hO : ∀ c, G.O c = c.rev) :
    ((laurentMaslovBifiltration G R).weighted 0).spectralThreshold 0
      (antiDiagonalCornerNativeClass R G hN hO) = 0 := by
  let a : Fin n := ⟨0, by omega⟩
  exact weighted_zero_spectralThreshold_eq_zero_of_polynomialImage R G a
    (antiDiagonal_polynomialHomologyImage_eq_bot R G hN hO a 2 (by decide))
    _ (antiDiagonalCornerNativeClass_ne_zero R G hN hO)
    (antiDiagonalCornerNativeClass_mem_polynomialHomologyImage R G hN hO a)

/-- The selected class tracked through the auxiliary stabilizations is normalized at zero. -/
theorem antiDiagonalAuxiliaryNativeClass_spectralThreshold_zero [Nontrivial R] (n : ℕ) :
    ((laurentMaslovBifiltration (antiDiagonalAuxiliaryGrid n) R).weighted 0).spectralThreshold 0
      (antiDiagonalAuxiliaryNativeClass n R) = 0 := by
  exact weighted_zero_spectralThreshold_eq_zero_of_polynomialImage R
    (antiDiagonalAuxiliaryGrid n) 0
    (antiDiagonalAuxiliary_polynomialHomologyImage_eq_bot R n 0 2 (by decide))
    _ (antiDiagonalAuxiliaryNativeClass_ne_zero R n)
    (antiDiagonalAuxiliaryNativeClass_mem_polynomialImage n R 0)

/-- The native reflected torus anchor has the required U-normalization at t = 0. -/
theorem reflectedTorusAnchorClass_spectralThreshold_zero [Nontrivial R] (n : ℕ) :
    ((laurentMaslovBifiltration (reflectedTorusGrid n) R).weighted 0).spectralThreshold 0
      (reflectedTorusAnchorClass n R) = 0 := by
  rw [reflectedTorusAnchorClass_eq_antiDiagonalCornerNativeClass]
  exact antiDiagonalCornerNativeClass_spectralThreshold_zero R _ _ _

end OnLeConjecture.KnotFloer.GridFull
