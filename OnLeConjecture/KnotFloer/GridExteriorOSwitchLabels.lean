/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOSwitchPairing

/-!
# The detecting maps of both labels of an O switch

Let `G` and `H` be grid diagrams of size `n` with the same X markings, where `H` is `G` with the
O markings of the columns `a` and `a + 1` exchanged, and let `F : C(G) → C(H)` be the O-switch map.
Each of the two exchanged O markings is a label: it occupies a column `cG` of `G` and a column
`cH ≠ cG` of `H`, in the same row. This file defines, for every pair of columns `(cG, cH)` with
`cG ≠ cH` and `H.O cH = G.O cG`, the detecting map `K = Φ^H_{cH} F + F Φ^G_{cG}` and its reverse,
and proves the results of Section 4 of the written proof of Statement E
(`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`) for both labels.

* `labelDetectingReverse_comp_labelDetecting`, `labelDetecting_comp_labelDetectingReverse`:
  `K' K ≃ id` and `K K' ≃ id`, with the Clifford homotopies.
* `homologyMap_labelDetecting_gridCanonicalClass`: `K_* can(G) = can(H)`.
* `homologyMap_labelDerivativeSwitch_gridCanonicalClass`: `(Φ^H_{cH} F)_* can(G) = can(H)`.
  For the label of column `a + 1` of `G` this is the second identity of equation
  `O-switch-top-pairing`, which the file `GridExteriorOSwitchPairing` leaves open.
* `oSwitchLabel_left`, `oSwitchLabel_right`: the two exchanged O markings are labels.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n : ℕ} {R : Type*} [CommRing R]

variable {G H : GridDiagram n} {a : Fin n}

/-! ### The two labels of an O switch -/

/-- The O marking of column `a` of `G` lies in column `a + 1` of `H`, in the same row. -/
theorem oSwitchLabel_left (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    H.O (finRotate n a) = G.O a := by
  rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_right]

/-- The O marking of column `a + 1` of `G` lies in column `a` of `H`, in the same row. -/
theorem oSwitchLabel_right (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    H.O a = G.O (finRotate n a) := by
  rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_left]

/-! ### Detecting maps of a label -/

variable (R) in
/-- The detecting map `K = Φ^H_{cH} F + F Φ^G_{cG}` of a label. -/
def labelDetecting (G H : GridDiagram n) (a cG cH : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  oDerivative R H {cH} ∘ₗ oSwitchMap R G a + oSwitchMap R G a ∘ₗ oDerivative R G {cG}

variable (R) in
/-- The reverse detecting map `K' = Φ^G_{cG} F' + F' Φ^H_{cH}` of a label. -/
def labelDetectingReverse (G H : GridDiagram n) (a cG cH : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  oDerivative R G {cG} ∘ₗ oSwitchMap R H a + oSwitchMap R H a ∘ₗ oDerivative R H {cH}

/-- The detecting map of the label of column `a` is the map `oDetecting`. -/
theorem labelDetecting_left :
    labelDetecting R G H a a (finRotate n a) = oDetecting R G H a := rfl

variable [CharP R 2]

theorem laurentDifferential_comp_labelDetecting (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (cG cH : Fin n) :
    laurentDifferential H R ∘ₗ labelDetecting R G H a cG cH =
      labelDetecting R G H a cG cH ∘ₗ laurentDifferential G R := by
  have e1 := laurentDifferential_comp_oDerivative_eq (R := R) H {cH}
  have e2 := laurentDifferential_comp_oDerivative_eq (R := R) G {cG}
  have e3 := laurentDifferential_comp_oSwitchMap (R := R) ha hO
  simp only [labelDetecting, ← Module.End.mul_eq_comp] at e1 e2 e3 ⊢
  exact detecting_chain_algebra e1 e2 e3

theorem laurentDifferential_comp_labelDetectingReverse (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (cG cH : Fin n) :
    laurentDifferential G R ∘ₗ labelDetectingReverse R G H a cG cH =
      labelDetectingReverse R G H a cG cH ∘ₗ laurentDifferential H R := by
  have e1 := laurentDifferential_comp_oDerivative_eq (R := R) H {cH}
  have e2 := laurentDifferential_comp_oDerivative_eq (R := R) G {cG}
  have e3 := laurentDifferential_comp_oSwitchMap (R := R) ha (oSwitch_reverse_O hO)
  simp only [labelDetectingReverse, ← Module.End.mul_eq_comp] at e1 e2 e3 ⊢
  exact detecting_chain_algebra e2 e1 e3

/-- `K' K = id + d B + B d` for a label. -/
theorem labelDetectingReverse_comp_labelDetecting (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) {cG cH : Fin n} (hc : cH ≠ cG)
    (hrow : H.O cH = G.O cG) :
    labelDetectingReverse R G H a cG cH ∘ₗ labelDetecting R G H a cG cH +
        (laurentDifferential G R ∘ₗ cliffordHomotopy R G cG cH +
          cliffordHomotopy R G cG cH ∘ₗ laurentDifferential G R) = LinearMap.id := by
  have hconj := oSwitch_conj_oDerivative (R := R) ha hO cH
  rw [hrow] at hconj
  have hFF := oSwitchMap_comp_oSwitchMap (R := R) ha hO
  have hS := smul_oDerivative_add_squareCount (R := R) G cG cH
  have hcl := oDerivative_clifford (R := R) G hc
  have hΨ := oDerivative_singleton_comp_self (R := R) H cH
  have hΦ := oDerivative_singleton_comp_self (R := R) G cG
  simp only [labelDetecting, labelDetectingReverse, relativeRectangleAction,
    ← Module.End.mul_eq_comp, ← Module.End.one_eq_id, ← mul_assoc] at hconj hFF hS hcl hΨ hΦ ⊢
  exact detecting_algebra hconj hFF hΨ hΦ hS hcl

/-- `K K' = id + d B' + B' d` for a label. -/
theorem labelDetecting_comp_labelDetectingReverse (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) {cG cH : Fin n} (hc : cH ≠ cG)
    (hrow : H.O cH = G.O cG) :
    labelDetecting R G H a cG cH ∘ₗ labelDetectingReverse R G H a cG cH +
        (laurentDifferential H R ∘ₗ cliffordHomotopy R H cH cG +
          cliffordHomotopy R H cH cG ∘ₗ laurentDifferential H R) = LinearMap.id := by
  have hconj := oSwitch_conj_oDerivative (R := R) ha (oSwitch_reverse_O hO) cG
  rw [← hrow] at hconj
  have hFF := oSwitchMap_comp_oSwitchMap_reverse (R := R) ha hO
  have hS := smul_oDerivative_add_squareCount (R := R) H cH cG
  have hcl := oDerivative_clifford (R := R) H (Ne.symm hc)
  have hΨ := oDerivative_singleton_comp_self (R := R) G cG
  have hΦ := oDerivative_singleton_comp_self (R := R) H cH
  simp only [labelDetecting, labelDetectingReverse, relativeRectangleAction,
    ← Module.End.mul_eq_comp, ← Module.End.one_eq_id, ← mul_assoc] at hconj hFF hS hcl hΨ hΦ ⊢
  exact detecting_algebra hconj hFF hΨ hΦ hS hcl

/-! ### Gradings -/

omit [CharP R 2] in
theorem labelDetecting_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (cG cH : Fin n) (m : ℤ)
    (c : LaurentChain R n) (hc : c ∈ laurentMaslovPiece G R m) :
    labelDetecting R G H a cG cH c ∈ laurentMaslovPiece H R m := by
  rw [labelDetecting, LinearMap.add_apply]
  exact Submodule.add_mem _ (oDerivativeSwitch_mem_maslovPiece ha hO cH m c hc)
    (oSwitchDerivative_mem_maslovPiece ha hO cG m c hc)

omit [CharP R 2] in
theorem labelDetectingReverse_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (cG cH : Fin n) (m : ℤ)
    (c : LaurentChain R n) (hc : c ∈ laurentMaslovPiece H R m) :
    labelDetectingReverse R G H a cG cH c ∈ laurentMaslovPiece G R m := by
  rw [labelDetectingReverse, LinearMap.add_apply]
  exact Submodule.add_mem _ (oDerivativeSwitch_mem_maslovPiece ha (oSwitch_reverse_O hO) cG m c hc)
    (oSwitchDerivative_mem_maslovPiece ha (oSwitch_reverse_O hO) cH m c hc)

omit [CharP R 2] in
theorem labelDetecting_mem_bifiltrationLevel (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) (cG cH : Fin n)
    (u v : ℝ) (c : LaurentChain R n) (hc : c ∈ laurentBifiltrationLevel G R u v) :
    labelDetecting R G H a cG cH c ∈ laurentBifiltrationLevel H R u (v + 1 / 2) := by
  rw [labelDetecting, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have h1 := oSwitchMap_mem_bifiltrationLevel R ha hO hX hc
    have h2 := oDerivative_singleton_mem_bifiltrationLevel (R := R) H cH h1
    convert h2 using 2
    ring
  · have h1 := oDerivative_singleton_mem_bifiltrationLevel (R := R) G cG hc
    have h2 := oSwitchMap_mem_bifiltrationLevel R ha hO hX h1
    convert h2 using 2
    ring

/-! ### Homology -/

variable (R) in
/-- The detecting map of a label as a morphism of native complexes. -/
def laurentMaslovLabelDetectingHom (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (cG cH : Fin n) :
    laurentMaslovComplex G R ⟶ laurentMaslovComplex H R :=
  laurentMaslovHomOfMap G H (labelDetecting R G H a cG cH)
    (labelDetecting_mem_maslovPiece ha hO cG cH)
    (laurentDifferential_comp_labelDetecting ha hO cG cH)

variable (R) in
/-- The reverse detecting map of a label as a morphism of native complexes. -/
def laurentMaslovLabelDetectingReverseHom (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (cG cH : Fin n) :
    laurentMaslovComplex H R ⟶ laurentMaslovComplex G R :=
  laurentMaslovHomOfMap H G (labelDetectingReverse R G H a cG cH)
    (labelDetectingReverse_mem_maslovPiece ha hO cG cH)
    (laurentDifferential_comp_labelDetectingReverse ha hO cG cH)

variable (R) in
/-- The detecting map of a label is a homotopy equivalence. -/
def labelDetectingHomotopyEquiv (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) {cG cH : Fin n} (hc : cH ≠ cG)
    (hrow : H.O cH = G.O cG) :
    HomotopyEquiv (laurentMaslovComplex G R) (laurentMaslovComplex H R) where
  hom := laurentMaslovLabelDetectingHom R ha hO cG cH
  inv := laurentMaslovLabelDetectingReverseHom R ha hO cG cH
  homotopyHomInvId := laurentMaslovHomotopyOfMap G
    (labelDetectingReverse R G H a cG cH ∘ₗ labelDetecting R G H a cG cH) (fun _ _ => rfl)
    (cliffordHomotopy R G cG cH) (cliffordHomotopy_mem_maslovPiece G cG cH)
    (labelDetectingReverse_comp_labelDetecting ha hO hc hrow)
  homotopyInvHomId := laurentMaslovHomotopyOfMap H
    (labelDetecting R G H a cG cH ∘ₗ labelDetectingReverse R G H a cG cH) (fun _ _ => rfl)
    (cliffordHomotopy R H cH cG) (cliffordHomotopy_mem_maslovPiece H cH cG)
    (labelDetecting_comp_labelDetectingReverse ha hO hc hrow)

/-- The detecting morphism of a label has filtration shifts `(0, 1/2)`. -/
theorem laurentMaslovLabelDetectingHom_shifts (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) (cG cH : Fin n) :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (laurentMaslovLabelDetectingHom R ha hO cG cH) 0 (1 / 2) :=
  laurentMaslovHomOfMap_shifts G H _ _ _ (1 / 2)
    (labelDetecting_mem_bifiltrationLevel ha hO hX cG cH)

/-- The detecting map of a label carries the canonical class to the canonical class. -/
theorem homologyMap_labelDetecting_gridCanonicalClass (hn : 2 ≤ n) (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) {cG cH : Fin n}
    (hc : cH ≠ cG) (hrow : H.O cH = G.O cG) :
    homologyMap (laurentMaslovLabelDetectingHom (ZMod 2) ha hO cG cH) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn :=
  gridCanonicalClass_homotopyEquiv G H hn hn (labelDetectingHomotopyEquiv (ZMod 2) ha hO hc hrow)
    (1 / 2) (laurentMaslovLabelDetectingHom_shifts ha hO hX cG cH)

/-- The detecting morphism of a label is the sum of the two composites. -/
theorem laurentMaslovLabelDetectingHom_eq_add (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (cG cH : Fin n) :
    laurentMaslovLabelDetectingHom R ha hO cG cH =
      oDerivativeSwitchHom R ha hO cH + oSwitchDerivativeHom R ha hO cG := by
  ext m c : 3
  apply Subtype.ext
  rfl

/-- The O-switch pairing identity for a label: `(Φ^H_{cH} F)_* can(G) = can(H)`. -/
theorem homologyMap_labelDerivativeSwitch_gridCanonicalClass (hn : 2 ≤ n)
    (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X)
    {cG cH : Fin n} (hc : cH ≠ cG) (hrow : H.O cH = G.O cG) :
    homologyMap (oDerivativeSwitchHom (ZMod 2) ha hO cH) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn := by
  have hK := homologyMap_labelDetecting_gridCanonicalClass hn ha hO hX hc hrow
  rw [laurentMaslovLabelDetectingHom_eq_add, homologyMap_add] at hK
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hK
  rw [homologyMap_oSwitchDerivative_gridCanonicalClass hn ha hO cG, add_zero] at hK
  exact hK

/-- The second O-switch pairing identity: for the label of column `a + 1` of `G`,
`(Φ^H_a F)_* can(G) = can(H)`. -/
theorem homologyMap_oDerivativeSwitch_gridCanonicalClass_right (hn : 2 ≤ n)
    (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) :
    homologyMap (oDerivativeSwitchHom (ZMod 2) ha hO a) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn :=
  homologyMap_labelDerivativeSwitch_gridCanonicalClass hn ha hO hX ha (oSwitchLabel_right hO)

end OnLeConjecture.KnotFloer.GridFull
