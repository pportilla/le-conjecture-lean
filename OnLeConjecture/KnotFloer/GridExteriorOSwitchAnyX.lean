/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorODerivativeBoundary

/-!
# O-switch class identities with arbitrary X markings

The chain complex, the polynomial subcomplex and the canonical class of a grid depend only on its
O markings. The canonical-class identities of the O-switch calculus therefore hold for every
choice of X markings on the source and the target. This matters for the auxiliary marking pairs of
Sections 5 and 6 of the written proof of Statement E (`statement_E_complete_proof.tex`), whose X
markings may coincide with O markings: their canonical class is defined through any valid grid
with the same O markings.

* `exists_shifts_of_polynomial`: a degree-preserving Laurent chain map sending each state to a
  polynomial chain has filtration shifts `(0, s)` for some real `s`, whatever the X markings.
* `homologyMap_labelDetecting_gridCanonicalClass_anyX` and
  `homologyMap_labelDerivativeSwitch_gridCanonicalClass_anyX`: the identities
  `K_* can(G) = can(H)` and `(Φ^H_{cH} F)_* can(G) = can(H)` for an O switch between grids whose
  X markings are arbitrary.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The O-switch map sends polynomial chains to polynomial chains. -/
theorem isPolynomialChain_oSwitchMap {G : GridDiagram n} (a : Fin n) {c : LaurentChain R n}
    (hc : IsPolynomialChain c) : IsPolynomialChain (oSwitchMap R G a c) := by
  intro y k hk
  rw [oSwitchMap, laurentDiagonalMap_apply, mul_comm] at hk
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp
    (AddMonoidAlgebra.support_coeff_single_mul_subset (c y) (1 : R) (oSwitchIndicator G a y) hk)
  have := hc y l hl
  have := oSwitchIndicator_nonneg G a y
  omega

theorem isPolynomialChain_single (x : GridState n) :
    IsPolynomialChain (single x 1 : LaurentChain R n) := by
  intro y k hk
  rw [Finsupp.single_apply] at hk
  split_ifs at hk
  · change k ∈ (Finsupp.single (0 : ℤ) (1 : R)).support at hk
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hk)]
  · simp at hk

variable [CharP R 2]

/-- A Laurent chain map preserving Maslov degree and sending each state to a polynomial chain has
filtration shifts `(0, s)` for some `s`. -/
theorem exists_shifts_of_polynomial (G H : GridDiagram n)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hpoly : ∀ x, IsPolynomialChain (f (single x 1))) :
    ∃ s : ℝ, (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (laurentMaslovHomOfMap G H f hdeg hcomm) 0 s := by
  let s : ℚ := (∑ y, |H.alexander y|) + ∑ x, |G.alexander x|
  refine ⟨s, laurentMaslovHomOfMap_shifts G H f hdeg hcomm s ?_⟩
  intro u v c hc
  have h := laurentMap_mem_bifiltrationLevel G H f s ?_ hc
  · exact_mod_cast h
  intro x y k hk
  have hk0 : 0 ≤ k := hpoly x y k hk
  refine ⟨by exact_mod_cast neg_nonpos.mpr hk0, ?_⟩
  have h1 : H.alexander y ≤ ∑ y, |H.alexander y| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (H.alexander i))
      (Finset.mem_univ y))
  have h2 : -G.alexander x ≤ ∑ x, |G.alexander x| :=
    (neg_le_abs _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (G.alexander i))
      (Finset.mem_univ x))
  have hk0' : (0 : ℚ) ≤ k := by exact_mod_cast hk0
  linarith

variable {G H : GridDiagram n} {a : Fin n}

omit [CharP R 2] in
/-- The detecting map of a label sends each state to a polynomial chain. -/
theorem isPolynomialChain_labelDetecting (cG cH : Fin n) (x : GridState n) :
    IsPolynomialChain (labelDetecting R G H a cG cH (single x 1)) := by
  rw [labelDetecting, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (isPolynomialChain_oDerivative cH (isPolynomialChain_oSwitchMap a
    (isPolynomialChain_single x))).add
    (isPolynomialChain_oSwitchMap a
      (isPolynomialChain_oDerivative cG (isPolynomialChain_single x)))

/-- The detecting map of a label carries the canonical class to the canonical class, for
arbitrary X markings on both grids. -/
theorem homologyMap_labelDetecting_gridCanonicalClass_anyX (hn : 2 ≤ n)
    (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a)) {cG cH : Fin n}
    (hc : cH ≠ cG) (hrow : H.O cH = G.O cG) :
    homologyMap (laurentMaslovLabelDetectingHom (ZMod 2) ha hO cG cH) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn := by
  obtain ⟨s, hs⟩ := exists_shifts_of_polynomial G H (labelDetecting (ZMod 2) G H a cG cH)
    (labelDetecting_mem_maslovPiece ha hO cG cH)
    (laurentDifferential_comp_labelDetecting ha hO cG cH)
    (isPolynomialChain_labelDetecting cG cH)
  exact gridCanonicalClass_homotopyEquiv G H hn hn
    (labelDetectingHomotopyEquiv (ZMod 2) ha hO hc hrow) s hs

/-- The O-switch pairing identity `(Φ^H_{cH} F)_* can(G) = can(H)` for arbitrary X markings. -/
theorem homologyMap_labelDerivativeSwitch_gridCanonicalClass_anyX (hn : 2 ≤ n)
    (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a)) {cG cH : Fin n}
    (hc : cH ≠ cG) (hrow : H.O cH = G.O cG) :
    homologyMap (oDerivativeSwitchHom (ZMod 2) ha hO cH) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn := by
  have hK := homologyMap_labelDetecting_gridCanonicalClass_anyX hn ha hO hc hrow
  rw [laurentMaslovLabelDetectingHom_eq_add, homologyMap_add] at hK
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hK
  rw [homologyMap_oSwitchDerivative_gridCanonicalClass hn ha hO cG, add_zero] at hK
  exact hK

end OnLeConjecture.KnotFloer.GridFull
