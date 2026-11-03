/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOClifford
public import OnLeConjecture.KnotFloer.GridCanonicalClass

/-!
# The detecting map of an O switch carries the canonical class to the canonical class

This file packages the chain-level results of `GridExteriorOClifford` as native maps of the
integer-graded Laurent complexes over `ZMod 2`, following Section 4 of the written proof of
Statement E (`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`).

Let `G` and `H` be grid diagrams of size `n ≥ 2` with the same X markings, where `H` is `G`
with the O markings of the columns `a` and `a + 1` exchanged. The detecting map
`K = Φ^H_{a+1} F + F Φ^G_a` has Maslov degree zero, filtration shifts `(0, 1/2)`, and the reverse
detecting map is a homotopy inverse, with the explicit Clifford homotopies
(`oDetectingHomotopyEquiv`). Hence `K` carries the canonical class of `G` to the canonical class
of `H` (`homologyMap_oDetecting_gridCanonicalClass`). This is the statement
`(K_i)_* can(G) = can(H)` of the written proof.

Generic constructions used here: `laurentMaslovHomOfMap` makes a morphism of native complexes
from a degree-preserving Laurent chain map, and `laurentMaslovHomotopyOfMap` makes a homotopy
from a degree-raising Laurent map satisfying the homotopy identity.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n : ℕ} {R : Type*} [CommRing R] [CharP R 2]

/-! ### Native morphisms and homotopies from Laurent maps -/

section Generic

variable (G H : GridDiagram n)

/-- The restriction of a degree-preserving Laurent map to a Maslov piece. -/
def laurentPieceMap (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m) (m : ℤ) :
    laurentMaslovPiece G R m →ₗ[R] laurentMaslovPiece H R m :=
  LinearMap.codRestrict _ ((f.restrictScalars R).comp (laurentMaslovPiece G R m).subtype)
    (fun c => hdeg m c c.property)

omit [CharP R 2] in
/-- The restricted map commutes with the graded differentials. -/
theorem laurentGradedDifferential_pieceMap
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (m : ℤ)
    (c : laurentMaslovPiece G R (m + 1)) :
    laurentGradedDifferential H R m (laurentPieceMap G H f hdeg (m + 1) c) =
      laurentPieceMap G H f hdeg m (laurentGradedDifferential G R m c) := by
  apply Subtype.ext
  exact LinearMap.congr_fun hcomm (c : LaurentChain R n)

/-- A degree-preserving Laurent chain map as a morphism of native complexes. -/
def laurentMaslovHomOfMap (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentMaslovComplex G R ⟶ laurentMaslovComplex H R where
  f m := ModuleCat.ofHom (laurentPieceMap G H f hdeg m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    simp only [laurentMaslovComplex_d]
    ext c : 2
    exact laurentGradedDifferential_pieceMap G H f hdeg hcomm j c

theorem laurentMaslovChainEquiv_homOfMap
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv H R m ((laurentMaslovHomOfMap G H f hdeg hcomm).f m c) :
      LaurentChain R n) = f (laurentMaslovChainEquiv G R m c) := rfl

/-- Filtration shifts of a native morphism made from a Laurent map. -/
theorem laurentMaslovHomOfMap_shifts
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (s : ℝ)
    (hlev : ∀ (u v : ℝ) (c : LaurentChain R n), c ∈ laurentBifiltrationLevel G R u v →
      f c ∈ laurentBifiltrationLevel H R u (v + s)) :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (laurentMaslovHomOfMap G H f hdeg hcomm) 0 s := by
  intro u v m c hc
  have h := hlev u v (laurentMaslovChainEquiv G R m c) hc
  rw [add_zero]
  exact h

/-- The restriction of a degree-raising Laurent map to a Maslov piece. -/
def laurentRaisingPieceMap (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece G R (m + 1)) (m : ℤ) :
    laurentMaslovPiece G R m →ₗ[R] laurentMaslovPiece G R (m + 1) :=
  LinearMap.codRestrict _ ((h.restrictScalars R).comp (laurentMaslovPiece G R m).subtype)
    (fun c => hdeg m c c.property)

/-- The homotopy components of a degree-raising Laurent map, extended by zero. -/
def laurentRaisingComponent (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece G R (m + 1)) (i j : ℤ) :
    (laurentMaslovComplex G R).X i ⟶ (laurentMaslovComplex G R).X j :=
  if hj : j = i + 1 then by
    subst j
    exact ModuleCat.ofHom (laurentRaisingPieceMap G h hdeg i)
  else 0

theorem laurentRaisingComponent_succ
    (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece G R (m + 1)) (i : ℤ) :
    laurentRaisingComponent G h hdeg i (i + 1) =
      ModuleCat.ofHom (laurentRaisingPieceMap G h hdeg i) := by
  simp [laurentRaisingComponent]

/-- A homotopy between a native endomorphism and the identity, from the Laurent identity
`f + (d h + h d) = id` in characteristic two. -/
def laurentMaslovHomotopyOfMap {φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex G R}
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : ∀ m (c : (laurentMaslovComplex G R).X m),
      (laurentMaslovChainEquiv G R m (φ.f m c) : LaurentChain R n) =
        f (laurentMaslovChainEquiv G R m c))
    (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      h c ∈ laurentMaslovPiece G R (m + 1))
    (hid : f + (laurentDifferential G R ∘ₗ h + h ∘ₗ laurentDifferential G R) = LinearMap.id) :
    Homotopy φ (𝟙 (laurentMaslovComplex G R)) where
  hom := laurentRaisingComponent G h hdeg
  zero i j hij := by
    have hj : ¬ j = i + 1 := by
      intro hj
      exact hij (by rw [ComplexShape.down_Rel]; omega)
    rw [laurentRaisingComponent, dif_neg hj]
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel ((m + 1) + 1) (m + 1) from rfl)]
    simp only [laurentRaisingComponent_succ, laurentMaslovComplex_d]
    ext c : 2
    apply Subtype.ext
    let c' : LaurentChain R n := laurentMaslovChainEquiv G R (m + 1) c
    have hφ := hf (m + 1) c
    change (laurentMaslovChainEquiv G R (m + 1) (φ.f (m + 1) c) : LaurentChain R n) =
      h (laurentDifferential G R c') + laurentDifferential G R (h c') + c'
    rw [hφ]
    have h2 : ∀ z : LaurentChain R n, z + z = 0 := fun z => by
      rw [← two_smul (LaurentPolynomial R), CharTwo.two_eq_zero, zero_smul]
    have hc := LinearMap.congr_fun hid c'
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hc
    have hc2 : f c' = (laurentDifferential G R (h c') + h (laurentDifferential G R c')) + c' := by
      have e := congrArg (· + (laurentDifferential G R (h c') + h (laurentDifferential G R c'))) hc
      simp only [add_assoc, h2, add_zero] at e
      rw [e]
      abel
    change f c' = _
    rw [hc2]
    abel

end Generic

/-! ### Gradings of the detecting maps -/

section Detecting

variable {G H : GridDiagram n} {a : Fin n}

omit [CharP R 2] in
/-- The detecting map preserves the Maslov degree. -/
theorem oDetecting_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (m : ℤ) (c : LaurentChain R n)
    (hc : c ∈ laurentMaslovPiece G R m) : oDetecting R G H a c ∈ laurentMaslovPiece H R m := by
  rw [oDetecting, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have h1 := oSwitchMap_mem_maslovPiece R ha hO hc
    have h2 := oDerivative_singleton_mem_maslovPiece (R := R) H (finRotate n a) h1
    simpa using h2
  · have h1 := oDerivative_singleton_mem_maslovPiece (R := R) G a hc
    have h2 := oSwitchMap_mem_maslovPiece R ha hO h1
    simpa using h2

omit [CharP R 2] in
/-- The reverse detecting map preserves the Maslov degree. -/
theorem oDetectingReverse_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (m : ℤ) (c : LaurentChain R n)
    (hc : c ∈ laurentMaslovPiece H R m) :
    oDetectingReverse R G H a c ∈ laurentMaslovPiece G R m := by
  have hO' := oSwitch_reverse_O hO
  rw [oDetectingReverse, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have h1 := oSwitchMap_mem_maslovPiece R ha hO' hc
    have h2 := oDerivative_singleton_mem_maslovPiece (R := R) G a h1
    simpa using h2
  · have h1 := oDerivative_singleton_mem_maslovPiece (R := R) H (finRotate n a) hc
    have h2 := oSwitchMap_mem_maslovPiece R ha hO' h1
    simpa using h2

omit [CharP R 2] in
/-- The detecting map is polynomial and has filtration shifts `(0, 1/2)`. -/
theorem oDetecting_mem_bifiltrationLevel (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) (u v : ℝ)
    (c : LaurentChain R n) (hc : c ∈ laurentBifiltrationLevel G R u v) :
    oDetecting R G H a c ∈ laurentBifiltrationLevel H R u (v + 1 / 2) := by
  rw [oDetecting, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have h1 := oSwitchMap_mem_bifiltrationLevel R ha hO hX hc
    have h2 := oDerivative_singleton_mem_bifiltrationLevel (R := R) H (finRotate n a) h1
    convert h2 using 2
    ring
  · have h1 := oDerivative_singleton_mem_bifiltrationLevel (R := R) G a hc
    have h2 := oSwitchMap_mem_bifiltrationLevel R ha hO hX h1
    convert h2 using 2
    ring

omit [CharP R 2] in
/-- The reverse detecting map is polynomial and has filtration shifts `(0, 1/2)`. -/
theorem oDetectingReverse_mem_bifiltrationLevel (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) (u v : ℝ)
    (c : LaurentChain R n) (hc : c ∈ laurentBifiltrationLevel H R u v) :
    oDetectingReverse R G H a c ∈ laurentBifiltrationLevel G R u (v + 1 / 2) := by
  have hO' := oSwitch_reverse_O hO
  rw [oDetectingReverse, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have h1 := oSwitchMap_mem_bifiltrationLevel R ha hO' hX.symm hc
    have h2 := oDerivative_singleton_mem_bifiltrationLevel (R := R) G a h1
    convert h2 using 2
    ring
  · have h1 := oDerivative_singleton_mem_bifiltrationLevel (R := R) H (finRotate n a) hc
    have h2 := oSwitchMap_mem_bifiltrationLevel R ha hO' hX.symm h1
    convert h2 using 2
    ring

end Detecting

/-! ### The Clifford homotopy raises the Maslov degree by one -/

omit [CharP R 2] in
theorem squareWeight_oDeformWeight_singleton_coeff_one_eq (G : GridDiagram n) (h : Fin n)
    (r : GridRectangle n) :
    (squareWeight (oDeformWeight R G {h}) r).coeff 1 =
      if (h, G.O h) ∈ r.coveredSquares then
        LaurentPolynomial.T (((G.OColumns r).card : ℤ) - 1) else 0 := by
  have hT := squareWeight_oDeformWeight_singleton_coeff_one (R := R) G h r
  have hinv : (LaurentPolynomial.T (-1) : LaurentPolynomial R) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  calc (squareWeight (oDeformWeight R G {h}) r).coeff 1
      = LaurentPolynomial.T (-1) *
          (LaurentPolynomial.T 1 * (squareWeight (oDeformWeight R G {h}) r).coeff 1) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = _ := by
        rw [hT]
        split_ifs
        · rw [squareWeight_oSquareWeight, laurentSpecialization_OMonomial,
            ← LaurentPolynomial.T_add]
          congr 1
        · rw [mul_zero]

omit [CharP R 2] in
/-- The support of the Clifford homotopy comes from rectangles through the O square of `c`. -/
theorem exists_rectangle_of_mem_support_cliffordHomotopy (G : GridDiagram n) (c c' : Fin n)
    {x y : GridState n} {k : ℤ}
    (hk : k ∈ (cliffordHomotopy R G c c' (single x 1) y).coeff.support) :
    ∃ r ∈ GridRectangleBetween.emptyRectangles x y,
      c ∈ G.OColumns r.toGridRectangle ∧ k + 1 = ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [cliffordHomotopy, gridMatrixMap_single_apply, Polynomial.coeff_add,
    Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff] at hk
  simp only [squareWeight_oDeformWeight_singleton_coeff_one_eq] at hk
  rw [AddMonoidAlgebra.coeff_add] at hk
  have hk' := Finsupp.support_add hk
  rcases Finset.mem_union.mp hk' with hk1 | hk1 <;>
  · rw [AddMonoidAlgebra.coeff_sum] at hk1
    obtain ⟨r, hr, hkr⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk1)
    have hr' := (Finset.mem_filter.mp hr).1
    by_cases hs : (c, G.O c) ∈ r.toGridRectangle.coveredSquares
    · rw [if_pos hs] at hkr
      refine ⟨r, hr', (GridDiagram.mem_OColumns G).mpr hs, ?_⟩
      change k ∈ (Finsupp.single (((G.OColumns r.toGridRectangle).card : ℤ) - 1)
        (1 : R)).support at hkr
      have := Finset.mem_singleton.mp (Finsupp.support_single_subset hkr)
      omega
    · rw [if_neg hs] at hkr
      simp at hkr

omit [CharP R 2] in
/-- The Clifford homotopy raises the Maslov degree by one. -/
theorem cliffordHomotopy_mem_maslovPiece (G : GridDiagram n) (c c' : Fin n) (m : ℤ)
    (z : LaurentChain R n) (hz : z ∈ laurentMaslovPiece G R m) :
    cliffordHomotopy R G c c' z ∈ laurentMaslovPiece G R (m + 1) := by
  refine laurentMap_mem_maslovPiece G G (cliffordHomotopy R G c c') 1 ?_ hz
  intro x y k hk
  obtain ⟨r, hr, -, hkr⟩ := exists_rectangle_of_mem_support_cliffordHomotopy G c c' hk
  have hdeg := laurentMaslovDegree_add_card_OColumns G r
    ((GridRectangleBetween.mem_emptyRectangles r).mp hr) 0
  simp only [laurentMaslovDegree, zero_add, mul_zero, sub_zero] at hdeg
  omega

/-! ### The homotopy equivalence and the canonical class -/

section Equivalence

variable {G H : GridDiagram n} {a : Fin n}

variable (R) in
/-- The detecting map as a morphism of native complexes. -/
def laurentMaslovODetectingHom (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    laurentMaslovComplex G R ⟶ laurentMaslovComplex H R :=
  laurentMaslovHomOfMap G H (oDetecting R G H a) (oDetecting_mem_maslovPiece ha hO)
    (laurentDifferential_comp_oDetecting ha hO)

variable (R) in
/-- The reverse detecting map as a morphism of native complexes. -/
def laurentMaslovODetectingReverseHom (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    laurentMaslovComplex H R ⟶ laurentMaslovComplex G R :=
  laurentMaslovHomOfMap H G (oDetectingReverse R G H a) (oDetectingReverse_mem_maslovPiece ha hO)
    (laurentDifferential_comp_oDetectingReverse ha hO)

variable (R) in
/-- The detecting map of an O switch is a homotopy equivalence, with the reverse detecting map
as homotopy inverse and the two Clifford homotopies. -/
def oDetectingHomotopyEquiv (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    HomotopyEquiv (laurentMaslovComplex G R) (laurentMaslovComplex H R) where
  hom := laurentMaslovODetectingHom R ha hO
  inv := laurentMaslovODetectingReverseHom R ha hO
  homotopyHomInvId := laurentMaslovHomotopyOfMap G
    (oDetectingReverse R G H a ∘ₗ oDetecting R G H a) (fun _ _ => rfl)
    (cliffordHomotopy R G a (finRotate n a))
    (cliffordHomotopy_mem_maslovPiece G a (finRotate n a))
    (oDetectingReverse_comp_oDetecting ha hO)
  homotopyInvHomId := laurentMaslovHomotopyOfMap H
    (oDetecting R G H a ∘ₗ oDetectingReverse R G H a) (fun _ _ => rfl)
    (cliffordHomotopy R H (finRotate n a) a)
    (cliffordHomotopy_mem_maslovPiece H (finRotate n a) a)
    (oDetecting_comp_oDetectingReverse ha hO)

/-- The detecting morphism has filtration shifts `(0, 1/2)`. -/
theorem laurentMaslovODetectingHom_shifts (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (laurentMaslovODetectingHom R ha hO) 0 (1 / 2) :=
  laurentMaslovHomOfMap_shifts G H _ _ _ (1 / 2) (oDetecting_mem_bifiltrationLevel ha hO hX)

/-- The reverse detecting morphism has filtration shifts `(0, 1/2)`. -/
theorem laurentMaslovODetectingReverseHom_shifts (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) :
    (laurentMaslovBifiltration H R).Shifts (laurentMaslovBifiltration G R)
      (laurentMaslovODetectingReverseHom R ha hO) 0 (1 / 2) :=
  laurentMaslovHomOfMap_shifts H G _ _ _ (1 / 2) (oDetectingReverse_mem_bifiltrationLevel ha hO hX)

/-- The detecting map of an adjacent O switch with fixed X markings carries the canonical class
to the canonical class: `(K_i)_* can(G) = can(H)`. -/
theorem homologyMap_oDetecting_gridCanonicalClass (hn : 2 ≤ n) (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) :
    homologyMap (laurentMaslovODetectingHom (ZMod 2) ha hO) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn :=
  gridCanonicalClass_homotopyEquiv G H hn hn (oDetectingHomotopyEquiv (ZMod 2) ha hO) (1 / 2)
    (laurentMaslovODetectingHom_shifts ha hO hX)

end Equivalence

end OnLeConjecture.KnotFloer.GridFull
