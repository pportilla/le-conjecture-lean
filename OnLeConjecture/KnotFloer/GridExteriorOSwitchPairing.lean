/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOSwitchClass
public import OnLeConjecture.KnotFloer.GridPolynomialLatticeCycles
public import OnLeConjecture.KnotFloer.GridAntiDiagonalSpectralNormalization

/-!
# The O-switch pairing identities

Let `G` and `H` be grid diagrams of size `n ≥ 2` with the same X markings, where `H` is `G`
with the O markings of the columns `a` and `a + 1` exchanged, and let `F : C(G) → C(H)` be the
O-switch map of Maslov degree `-1`. For a column `h`, the composite `F Φ^G_h` and the composite
`Φ^H_h F` are chain maps of Maslov degree zero (`oSwitchDerivativeHom`, `oDerivativeSwitchHom`).

* `homologyMap_oSwitchDerivative_gridCanonicalClass`: `(F Φ^G_h)_* can(G) = 0` for every
  column `h`. The derivative of a polynomial degree-zero cycle is a polynomial degree-one
  cycle, and the degree-one polynomial homology image vanishes.
* `homologyMap_oDerivativeSwitch_gridCanonicalClass`: `(Φ^H_{a+1} F)_* can(G) = can(H)`.
  This is the first identity of equation `O-switch-top-pairing` of the written proof of
  Statement E (`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`) for the label
  carried by the O marking of column `a` of `G`.
* `homologyMap_oDerivativeSwitch_gridCanonicalClass_of_ne`: `(Φ^H_k F)_* can(G) = 0` for every
  column `k` whose O marking is not moved by the switch (third identity of
  `O-switch-top-pairing`).

The identity for the other moved label, `(Φ^H_a F)_* can(G) = can(H)`, is not proved here.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n : ℕ} {R : Type*} [CommRing R] [CharP R 2]

/-! ### Polynomial chains -/

/-- A Laurent chain is polynomial when every exponent is nonnegative. -/
def IsPolynomialChain (c : LaurentChain R n) : Prop :=
  ∀ x k, k ∈ (c x).coeff.support → 0 ≤ k

omit [CharP R 2] in
/-- The derivative at one column preserves polynomial chains. -/
theorem isPolynomialChain_oDerivative {G : GridDiagram n} (h : Fin n) {c : LaurentChain R n}
    (hc : IsPolynomialChain c) : IsPolynomialChain (oDerivative R G {h} c) := by
  intro y k hk
  obtain ⟨x, j, hj, d, hd, rfl⟩ := exists_support_laurentMap (oDerivative R G {h}) c hk
  obtain ⟨r, _, hh, hkr⟩ := exists_rectangle_of_mem_support_oDerivative G h hd
  have hpos : 1 ≤ ((G.OColumns r.toGridRectangle).card : ℤ) := by
    have : 0 < (G.OColumns r.toGridRectangle).card := Finset.card_pos.mpr ⟨h, hh⟩
    exact_mod_cast this
  have := hc x j hj
  omega

/-! ### The two composites as native morphisms -/

section Composites

variable {G H : GridDiagram n} {a : Fin n}

omit [CharP R 2] in
theorem oSwitchDerivative_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) (m : ℤ) (c : LaurentChain R n)
    (hc : c ∈ laurentMaslovPiece G R m) :
    (oSwitchMap R G a ∘ₗ oDerivative R G {h}) c ∈ laurentMaslovPiece H R m := by
  have h1 := oDerivative_singleton_mem_maslovPiece (R := R) G h hc
  have h2 := oSwitchMap_mem_maslovPiece R ha hO h1
  simpa using h2

omit [CharP R 2] in
theorem oDerivativeSwitch_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) (m : ℤ) (c : LaurentChain R n)
    (hc : c ∈ laurentMaslovPiece G R m) :
    (oDerivative R H {h} ∘ₗ oSwitchMap R G a) c ∈ laurentMaslovPiece H R m := by
  have h1 := oSwitchMap_mem_maslovPiece R ha hO hc
  have h2 := oDerivative_singleton_mem_maslovPiece (R := R) H h h1
  simpa using h2

theorem laurentDifferential_comp_oSwitchDerivative (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) :
    laurentDifferential H R ∘ₗ (oSwitchMap R G a ∘ₗ oDerivative R G {h}) =
      (oSwitchMap R G a ∘ₗ oDerivative R G {h}) ∘ₗ laurentDifferential G R := by
  rw [← LinearMap.comp_assoc, laurentDifferential_comp_oSwitchMap R ha hO, LinearMap.comp_assoc,
    laurentDifferential_comp_oDerivative_eq, LinearMap.comp_assoc]

theorem laurentDifferential_comp_oDerivativeSwitch (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) :
    laurentDifferential H R ∘ₗ (oDerivative R H {h} ∘ₗ oSwitchMap R G a) =
      (oDerivative R H {h} ∘ₗ oSwitchMap R G a) ∘ₗ laurentDifferential G R := by
  rw [← LinearMap.comp_assoc, laurentDifferential_comp_oDerivative_eq, LinearMap.comp_assoc,
    laurentDifferential_comp_oSwitchMap R ha hO, LinearMap.comp_assoc]

variable (R) in
/-- The degree-zero composite `F Φ^G_h` as a morphism of native complexes. -/
def oSwitchDerivativeHom (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) :
    laurentMaslovComplex G R ⟶ laurentMaslovComplex H R :=
  laurentMaslovHomOfMap G H (oSwitchMap R G a ∘ₗ oDerivative R G {h})
    (oSwitchDerivative_mem_maslovPiece ha hO h) (laurentDifferential_comp_oSwitchDerivative ha hO h)

variable (R) in
/-- The degree-zero composite `Φ^H_h F` as a morphism of native complexes. -/
def oDerivativeSwitchHom (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) :
    laurentMaslovComplex G R ⟶ laurentMaslovComplex H R :=
  laurentMaslovHomOfMap G H (oDerivative R H {h} ∘ₗ oSwitchMap R G a)
    (oDerivativeSwitch_mem_maslovPiece ha hO h) (laurentDifferential_comp_oDerivativeSwitch ha hO h)

/-- The detecting morphism is the sum of the two composites. -/
theorem laurentMaslovODetectingHom_eq_add (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    laurentMaslovODetectingHom R ha hO =
      oDerivativeSwitchHom R ha hO (finRotate n a) + oSwitchDerivativeHom R ha hO a := by
  ext m c : 3
  apply Subtype.ext
  rfl

end Composites

/-! ### The pairing identities -/

section Pairing

variable {G H : GridDiagram n} {a : Fin n}

/-- `(F Φ^G_h)_* can(G) = 0`: the derivative of the canonical class vanishes in Laurent
homology. -/
theorem homologyMap_oSwitchDerivative_gridCanonicalClass (hn : 2 ≤ n)
    (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a)) (h : Fin n) :
    homologyMap (oSwitchDerivativeHom (ZMod 2) ha hO h) 0 (gridCanonicalClass G hn) = 0 := by
  classical
  let C := laurentMaslovComplex G (ZMod 2)
  let D := laurentMaslovComplex H (ZMod 2)
  obtain ⟨z, hzpoly, hz⟩ := (mem_polynomialHomologyImage_iff_exists_cycle (ZMod 2) G
    ⟨0, by omega⟩ 0 _).mp (gridCanonicalClass_mem_polynomialImage G hn ⟨0, by omega⟩)
  -- the underlying cycle
  let c : LaurentChain (ZMod 2) n := laurentMaslovChainEquiv G (ZMod 2) 0 (C.iCycles 0 z)
  have hc : c ∈ laurentMaslovPiece G (ZMod 2) 0 :=
    (laurentMaslovChainEquiv G (ZMod 2) 0 (C.iCycles 0 z)).property
  have hcD : laurentDifferential G (ZMod 2) c = 0 := by
    have h0 := congrArg (fun f : C.cycles 0 ⟶ C.X (-1) => f z) (C.iCycles_d 0 (-1))
    change C.d 0 (-1) (C.iCycles 0 z) = 0 at h0
    have hd := laurentMaslovChainEquiv_d G (ZMod 2) (-1) (C.iCycles 0 z)
    change (laurentMaslovChainEquiv G (ZMod 2) (-1) (C.d 0 (-1) (C.iCycles 0 z)) :
      LaurentChain (ZMod 2) n) = laurentDifferential G (ZMod 2) c at hd
    rw [h0, map_zero] at hd
    exact hd.symm
  -- its derivative is a polynomial cycle of degree one
  let e : LaurentChain (ZMod 2) n := oDerivative (ZMod 2) G {h} c
  have he : e ∈ laurentMaslovPiece G (ZMod 2) 1 := by
    simpa using oDerivative_singleton_mem_maslovPiece (R := ZMod 2) G h hc
  have heD : laurentDifferential G (ZMod 2) e = 0 := by
    have hcomm := LinearMap.congr_fun (laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G {h})
      c
    simp only [LinearMap.comp_apply] at hcomm
    change laurentDifferential G (ZMod 2) (oDerivative (ZMod 2) G {h} c) = 0
    rw [hcomm, hcD, map_zero]
  have hepoly : IsPolynomialChain e := isPolynomialChain_oDerivative h hzpoly
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
  have heb : e = laurentDifferential G (ZMod 2) (laurentMaslovChainEquiv G (ZMod 2) 2 b) := by
    rw [← hwc, hb]
    exact laurentMaslovChainEquiv_d G (ZMod 2) 1 b
  -- the image of the cycle is a boundary in the target
  let vchain : LaurentChain (ZMod 2) n :=
    oSwitchMap (ZMod 2) G a (laurentMaslovChainEquiv G (ZMod 2) 2 b)
  have hv : vchain ∈ laurentMaslovPiece H (ZMod 2) 1 := by
    have h21 := oSwitchMap_mem_maslovPiece (ZMod 2) ha hO
      (laurentMaslovChainEquiv G (ZMod 2) 2 b).property
    rw [show (2 : ℤ) - 1 = 1 by norm_num] at h21
    exact h21
  have hvD : laurentDifferential H (ZMod 2) vchain = oSwitchMap (ZMod 2) G a e := by
    have hcomm := LinearMap.congr_fun (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO)
      (laurentMaslovChainEquiv G (ZMod 2) 2 b : LaurentChain (ZMod 2) n)
    simp only [LinearMap.comp_apply] at hcomm
    rw [heb]
    exact hcomm
  let v : D.X 1 := (laurentMaslovChainEquiv H (ZMod 2) 1).symm ⟨vchain, hv⟩
  have hφformula : ∀ y : C.X 0, (laurentMaslovChainEquiv H (ZMod 2) 0
      ((oSwitchDerivativeHom (ZMod 2) ha hO h).f 0 y) : LaurentChain (ZMod 2) n) =
        oSwitchMap (ZMod 2) G a (oDerivative (ZMod 2) G {h}
          (laurentMaslovChainEquiv G (ZMod 2) 0 y)) := fun y =>
    laurentMaslovChainEquiv_homOfMap G H _ _ _ 0 y
  obtain ⟨φ, hφdef⟩ : ∃ φ, oSwitchDerivativeHom (ZMod 2) ha hO h = φ := ⟨_, rfl⟩
  rw [hφdef] at hφformula ⊢
  have hboundary : cyclesMap φ 0 z = D.toCycles 1 0 v := by
    apply (ModuleCat.mono_iff_injective (D.iCycles 0)).mp inferInstance
    have hi : D.iCycles 0 (D.toCycles 1 0 v) = D.d 1 0 v :=
      congrArg (fun f : D.X 1 ⟶ D.X 0 => f v) (D.toCycles_i 1 0)
    have hi' := congrArg (fun f : (laurentMaslovComplex G (ZMod 2)).cycles 0 ⟶
        (laurentMaslovComplex H (ZMod 2)).X 0 => f z) (cyclesMap_i φ 0)
    change (laurentMaslovComplex H (ZMod 2)).iCycles 0 (cyclesMap φ 0 z) =
      φ.f 0 ((laurentMaslovComplex G (ZMod 2)).iCycles 0 z) at hi'
    rw [hi, hi']
    apply (laurentMaslovChainEquiv H (ZMod 2) 0).injective
    apply Subtype.ext
    have hφ : (laurentMaslovChainEquiv H (ZMod 2) 0 (φ.f 0 (C.iCycles 0 z)) :
        LaurentChain (ZMod 2) n) = oSwitchMap (ZMod 2) G a (oDerivative (ZMod 2) G {h} c) :=
      hφformula (C.iCycles 0 z)
    have hv' : (laurentMaslovChainEquiv H (ZMod 2) 1 v : LaurentChain (ZMod 2) n) = vchain :=
      congrArg Subtype.val ((laurentMaslovChainEquiv H (ZMod 2) 1).apply_symm_apply ⟨vchain, hv⟩)
    rw [hφ]
    have hd := laurentMaslovChainEquiv_d H (ZMod 2) 0 v
    exact hvD.symm.trans ((congrArg (laurentDifferential H (ZMod 2)) hv'.symm).trans hd.symm)
  rw [← hz]
  have hnat := congrArg (fun f : (laurentMaslovComplex G (ZMod 2)).cycles 0 ⟶
      (laurentMaslovComplex H (ZMod 2)).homology 0 => f z) (homologyπ_naturality φ 0)
  have hzero := congrArg (fun f : (laurentMaslovComplex H (ZMod 2)).X 1 ⟶
      (laurentMaslovComplex H (ZMod 2)).homology 0 => f v)
    ((laurentMaslovComplex H (ZMod 2)).toCycles_comp_homologyπ 1 0)
  have hzero' : (laurentMaslovComplex H (ZMod 2)).homologyπ 0 (cyclesMap φ 0 z) = 0 := by
    rw [hboundary]
    exact hzero
  change homologyMap φ 0 ((laurentMaslovComplex G (ZMod 2)).homologyπ 0 z) =
    (laurentMaslovComplex H (ZMod 2)).homologyπ 0 (cyclesMap φ 0 z) at hnat
  exact hnat.trans hzero'

/-- The O-switch pairing identity `(Φ^H_{a+1} F)_* can(G) = can(H)`. -/
theorem homologyMap_oDerivativeSwitch_gridCanonicalClass (hn : 2 ≤ n)
    (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) :
    homologyMap (oDerivativeSwitchHom (ZMod 2) ha hO (finRotate n a)) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn := by
  have hK := homologyMap_oDetecting_gridCanonicalClass hn ha hO hX
  rw [laurentMaslovODetectingHom_eq_add, homologyMap_add] at hK
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hK
  rw [homologyMap_oSwitchDerivative_gridCanonicalClass hn ha hO a, add_zero] at hK
  exact hK

/-- For a column whose O marking is not moved, `(Φ^H_k F)_* can(G) = 0`. -/
theorem homologyMap_oDerivativeSwitch_gridCanonicalClass_of_ne (hn : 2 ≤ n)
    (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a)) {k : Fin n}
    (hk : H.O k = G.O k) :
    homologyMap (oDerivativeSwitchHom (ZMod 2) ha hO k) 0 (gridCanonicalClass G hn) = 0 := by
  have heq : oDerivativeSwitchHom (ZMod 2) ha hO k = oSwitchDerivativeHom (ZMod 2) ha hO k := by
    ext m c : 3
    apply Subtype.ext
    exact LinearMap.congr_fun (oDerivative_comp_oSwitchMap (R := ZMod 2) ha hO hk) _
  rw [heq]
  exact homologyMap_oSwitchDerivative_gridCanonicalClass hn ha hO k

end Pairing

end OnLeConjecture.KnotFloer.GridFull
