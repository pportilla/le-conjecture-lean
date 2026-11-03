/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalClass
public import OnLeConjecture.KnotFloer.GridFullCyclicFiltration

/-!
# Transposition and normalized grid classes

Diagonal transposition bijects all empty rectangles and preserves their O counts,
Maslov degrees and Alexander gradings. It induces a native chain isomorphism
preserving both filtrations. The canonical class and its spectral threshold are
preserved. The rectangle and grading identities used here are the vendored
TauCeti results at `eb4dd2412a1cd62f73128361bfd3cb422df32e37`.

This also proves invariance under row commutations by transposition. It does not
assert invariance under stabilization corner types beyond those already proved.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex GridRectangleBetween

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- Transposition preserves the number of O markings covered by a rectangle. -/
theorem card_OColumns_transpose (r : GridRectangle n) :
    (G.transpose.OColumns r.transpose).card = (G.OColumns r).card := by
  classical
  rw [GridDiagram.card_OColumns, GridDiagram.card_OColumns,
    GridDiagram.transpose_OSet, GridRectangle.coveredSquares_transpose,
    ← Finset.image_inter _ _ Prod.swap_injective,
    Finset.card_image_of_injective _ Prod.swap_injective]

/-- Transposition preserves every full Laurent matrix coefficient. -/
@[simp] theorem laurentCoefficient_transpose (x y : GridState n) :
    laurentCoefficient G.transpose R x.transpose y.transpose = laurentCoefficient G R x y := by
  classical
  rw [laurentCoefficient_eq, laurentCoefficient_eq]
  refine (Finset.sum_equiv (transposeEquiv x y) (fun r => ?_) (fun r _ => ?_)).symm
  · simp only [mem_emptyRectangles, transposeEquiv_apply, isEmpty_transpose]
  · rw [transposeEquiv_apply, transpose_toGridRectangle, card_OColumns_transpose]

/-- Laurent-linear relabeling by diagonal transposition. -/
def laurentTransposeEquiv : LaurentChain R n ≃ₗ[LaurentPolynomial R] LaurentChain R n :=
  GridChain.transposeEquiv (LaurentPolynomial R) n

@[simp] theorem laurentTransposeEquiv_apply (c : LaurentChain R n) (x : GridState n) :
    laurentTransposeEquiv R c x = c x.transpose := GridChain.transposeEquiv_apply c x

/-- The full differential intertwines diagonal transposition, including X-crossing terms. -/
theorem laurentDifferential_transpose :
    laurentDifferential G.transpose R ∘ₗ (laurentTransposeEquiv R).toLinearMap =
      (laurentTransposeEquiv R).toLinearMap ∘ₗ laurentDifferential G R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.transpose = y := ⟨y.transpose, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    laurentTransposeEquiv, GridChain.transposeEquiv_single, laurentDifferential_single,
    laurentOnGenerator_apply, GridChain.transposeEquiv_apply,
    GridState.transpose_transpose, laurentCoefficient_transpose]

@[simp] theorem laurentDifferential_transpose_apply (c : LaurentChain R n) :
    laurentDifferential G.transpose R (laurentTransposeEquiv R c) =
      laurentTransposeEquiv R (laurentDifferential G R c) :=
  LinearMap.congr_fun (laurentDifferential_transpose G R) c

omit R in
@[simp] theorem laurentMaslovDegree_transpose (k : ℤ) (x : GridState n) :
    laurentMaslovDegree G.transpose k x.transpose = laurentMaslovDegree G k x := by
  simp only [laurentMaslovDegree, GridDiagram.maslovOℤ_transpose]

/-- Transposition preserves and reflects the homogeneous submodules. -/
theorem laurentTransposeEquiv_mem_maslovPiece_iff (m : ℤ) (c : LaurentChain R n) :
    laurentTransposeEquiv R c ∈ laurentMaslovPiece G.transpose R m ↔
      c ∈ laurentMaslovPiece G R m := by
  simp only [mem_laurentMaslovPiece]
  constructor
  · intro h x k hk
    simpa using h x.transpose k (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.transpose = y := ⟨y.transpose, by simp⟩
    simpa using h x k (by simpa using hk)

/-- Transposition restricted to an integer Maslov degree. -/
def laurentTransposePieceEquiv (m : ℤ) :
    laurentMaslovPiece G R m ≃ₗ[R] laurentMaslovPiece G.transpose R m :=
  ((laurentTransposeEquiv R).restrictScalars R).ofSubmodules _ _ (by
    ext c
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (laurentTransposeEquiv_mem_maslovPiece_iff G R m d).mpr hd
    · intro hc
      refine ⟨(laurentTransposeEquiv R).symm c, ?_,
        (laurentTransposeEquiv R).apply_symm_apply c⟩
      exact (laurentTransposeEquiv_mem_maslovPiece_iff G R m _).mp (by simpa using hc))

@[simp] theorem coe_laurentTransposePieceEquiv (m : ℤ) (c : laurentMaslovPiece G R m) :
    (laurentTransposePieceEquiv G R m c : LaurentChain R n) = laurentTransposeEquiv R c := rfl

/-- Transposition commutes with the restricted differential. -/
theorem laurentGradedDifferential_transpose (m : ℤ) (c : laurentMaslovPiece G R (m + 1)) :
    laurentGradedDifferential G.transpose R m (laurentTransposePieceEquiv G R (m + 1) c) =
      laurentTransposePieceEquiv G R m (laurentGradedDifferential G R m c) := by
  apply Subtype.ext
  simp

/-- Transposition gives an isomorphism of native Maslov-graded complexes. -/
def laurentMaslovTransposeIso (S : Type*) [CommRing S] [CharP S 2] :
    laurentMaslovComplex G S ≅ laurentMaslovComplex G.transpose S :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (laurentTransposePieceEquiv G S m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      simp only [laurentMaslovComplex_d]
      ext c : 2
      exact laurentGradedDifferential_transpose G S j c)

/-- The total chain map preserves and reflects both filtration bounds. -/
theorem laurentTransposeEquiv_mem_bifiltrationLevel_iff (a b : ℝ) (c : LaurentChain R n) :
    laurentTransposeEquiv R c ∈ laurentBifiltrationLevel G.transpose R a b ↔
      c ∈ laurentBifiltrationLevel G R a b := by
  simp only [mem_laurentBifiltrationLevel_iff]
  constructor
  · intro h x k hk
    simpa only [GridDiagram.alexander_transpose] using h x.transpose k (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.transpose = y := ⟨y.transpose, by simp⟩
    simpa only [GridDiagram.alexander_transpose] using h x k (by simpa using hk)

variable [CharP R 2]

/-- Native transposition preserves and reflects both filtration levels. -/
theorem laurentMaslovTranspose_mem_level_iff (a b : ℝ) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovTransposeIso G R).hom.f m c ∈
        (laurentMaslovBifiltration G.transpose R).level a b m ↔
      c ∈ (laurentMaslovBifiltration G R).level a b m := by
  change laurentTransposeEquiv R (laurentMaslovChainEquiv G R m c) ∈
    laurentBifiltrationLevel G.transpose R a b ↔ _
  rw [laurentTransposeEquiv_mem_bifiltrationLevel_iff]
  rfl

/-- The native forward transpose map preserves both filtrations. -/
theorem laurentMaslovTranspose_preserves :
    (laurentMaslovBifiltration G R).Preserves (laurentMaslovBifiltration G.transpose R)
      (laurentMaslovTransposeIso G R).hom := by
  intro a b m c hc
  exact (laurentMaslovTranspose_mem_level_iff G R a b m c).mpr hc

/-- The native inverse transpose map preserves both filtrations. -/
theorem laurentMaslovTranspose_inv_preserves :
    (laurentMaslovBifiltration G.transpose R).Preserves (laurentMaslovBifiltration G R)
      (laurentMaslovTransposeIso G R).inv := by
  intro a b m c hc
  apply (laurentMaslovTranspose_mem_level_iff G R a b m _).mp
  have h := congrArg (fun f => f.f m c) (laurentMaslovTransposeIso G R).inv_hom_id
  change (laurentMaslovTransposeIso G R).hom.f m
    ((laurentMaslovTransposeIso G R).inv.f m c) = c at h
  rwa [h]

/-- Transposition preserves the weighted threshold of every specified native class. -/
theorem spectralThreshold_laurentMaslovTranspose (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    ((laurentMaslovBifiltration G.transpose R).weighted t).spectralThreshold m
      (homologyMap (laurentMaslovTransposeIso G R).hom m ξ) =
        ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ :=
  RealFiltration.spectralThreshold_eq_of_homotopyEquiv
    (HomotopyEquiv.ofIso (laurentMaslovTransposeIso G R))
    ((laurentMaslovTranspose_preserves G R).weighted t)
    ((laurentMaslovTranspose_inv_preserves G R).weighted t) m ξ

omit R [CharP R 2] in
/-- Transposition transports the unique nonzero polynomial-image class. -/
theorem gridCanonicalClass_transpose (hn : 2 ≤ n) :
    homologyMap (laurentMaslovTransposeIso G (ZMod 2)).hom 0 (gridCanonicalClass G hn) =
      gridCanonicalClass G.transpose hn :=
  gridCanonicalClass_homotopyEquiv G G.transpose hn hn
    (HomotopyEquiv.ofIso (laurentMaslovTransposeIso G (ZMod 2))) 0
    (Bifiltration.shifts_zero_zero_iff.mpr (laurentMaslovTranspose_preserves G (ZMod 2)))

omit R [CharP R 2] in
/-- The normalized spectral threshold is invariant under transposition. -/
theorem gridCanonicalClass_spectralThreshold_transpose (hn : 2 ≤ n) (t : ℝ) :
    ((laurentMaslovBifiltration G.transpose (ZMod 2)).weighted t).spectralThreshold 0
      (gridCanonicalClass G.transpose hn) =
        ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_transpose G hn]
  exact spectralThreshold_laurentMaslovTranspose G (ZMod 2) 0 _ t

/-- A validated row commutation is transposition, the full column map, then transposition back. -/
def laurentMaslovRowCommutationHomotopyEquiv
    (C : GridDiagram.ColumnCommutationData G.transpose) :
    HomotopyEquiv (laurentMaslovComplex G R)
      (laurentMaslovComplex (G.swapRows C.column (finRotate n C.column)) R) :=
  ((HomotopyEquiv.ofIso (laurentMaslovTransposeIso G R)).trans
    (laurentMaslovCommutationHomotopyEquiv G.transpose R C)).trans
      (HomotopyEquiv.ofIso
        (laurentMaslovTransposeIso (G.swapRows C.column (finRotate n C.column)) R).symm)

/-- The row commutation map preserves both filtration coordinates. -/
theorem laurentMaslovRowCommutation_preserves
    (C : GridDiagram.ColumnCommutationData G.transpose) :
    (laurentMaslovBifiltration G R).Preserves
      (laurentMaslovBifiltration (G.swapRows C.column (finRotate n C.column)) R)
      (laurentMaslovRowCommutationHomotopyEquiv G R C).hom := by
  intro a b m c hc
  exact laurentMaslovTranspose_inv_preserves _ R a b m _
    (laurentMaslovCommutationHom_preserves G.transpose R C a b m _
      (laurentMaslovTranspose_preserves G R a b m c hc))

/-- The inverse row commutation map also preserves both coordinates. -/
theorem laurentMaslovRowCommutation_inv_preserves
    (C : GridDiagram.ColumnCommutationData G.transpose) :
    (laurentMaslovBifiltration (G.swapRows C.column (finRotate n C.column)) R).Preserves
      (laurentMaslovBifiltration G R)
      (laurentMaslovRowCommutationHomotopyEquiv G R C).inv := by
  intro a b m c hc
  exact laurentMaslovTranspose_inv_preserves G R a b m _
    (laurentMaslovReverseCommutationHom_preserves G.transpose R C a b m _
      (laurentMaslovTranspose_preserves _ R a b m c hc))

/-- The row commutation homotopy equivalence preserves each specified spectral threshold. -/
theorem spectralThreshold_laurentMaslovRowCommutation
    (C : GridDiagram.ColumnCommutationData G.transpose) (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration (G.swapRows C.column (finRotate n C.column)) R).weighted t) m
      (homologyMap (laurentMaslovRowCommutationHomotopyEquiv G R C).hom m ξ) =
        ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ :=
  Bifiltration.weighted_spectralThreshold_eq_of_homotopyEquiv
    (laurentMaslovRowCommutationHomotopyEquiv G R C)
    (laurentMaslovRowCommutation_preserves G R C)
    (laurentMaslovRowCommutation_inv_preserves G R C) m ξ t

omit R [CharP R 2] in
/-- The row commutation map transports the normalized class. -/
theorem gridCanonicalClass_rowCommutation (hn : 2 ≤ n)
    (C : GridDiagram.ColumnCommutationData G.transpose) :
    homologyMap (laurentMaslovRowCommutationHomotopyEquiv G (ZMod 2) C).hom 0
      (gridCanonicalClass G hn) =
        gridCanonicalClass (G.swapRows C.column (finRotate n C.column)) hn :=
  gridCanonicalClass_homotopyEquiv G _ hn hn
    (laurentMaslovRowCommutationHomotopyEquiv G (ZMod 2) C) 0
    (Bifiltration.shifts_zero_zero_iff.mpr
      (laurentMaslovRowCommutation_preserves G (ZMod 2) C))

omit R [CharP R 2] in
/-- The normalized threshold is invariant under validated row commutations. -/
theorem gridCanonicalClass_spectralThreshold_rowCommutation (hn : 2 ≤ n)
    (C : GridDiagram.ColumnCommutationData G.transpose) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration
        (G.swapRows C.column (finRotate n C.column)) (ZMod 2)).weighted t) 0
        (gridCanonicalClass (G.swapRows C.column (finRotate n C.column)) hn) =
      ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
        (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_rowCommutation G hn C]
  exact spectralThreshold_laurentMaslovRowCommutation G (ZMod 2) C 0 _ t

omit R [CharP R 2] in
/-- Both constructors of the elementary commutation relation preserve the normalized threshold. -/
theorem gridCanonicalClass_spectralThreshold_of_isCommutation (H : GridDiagram n)
    (hn : 2 ≤ n) (h : GridDiagram.IsCommutation G H) (t : ℝ) :
    ((laurentMaslovBifiltration H (ZMod 2)).weighted t).spectralThreshold 0
      (gridCanonicalClass H hn) =
        ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) := by
  rcases (GridDiagram.isCommutation_iff G H).mp h with h | h
  · rw [← gridCanonicalClass_spectralThreshold_transpose H hn t,
      ← gridCanonicalClass_spectralThreshold_transpose G hn t]
    obtain ⟨C, hC⟩ := GridDiagram.isColumnCommutation_iff_exists_columnCommutationData.mp
      ((GridDiagram.isColumnCommutation_transpose G H).mpr h)
    rw [hC]
    exact gridCanonicalClass_spectralThreshold_commutation G.transpose hn C t
  · obtain ⟨C, rfl⟩ := GridDiagram.isColumnCommutation_iff_exists_columnCommutationData.mp h
    exact gridCanonicalClass_spectralThreshold_commutation G hn C t

omit R [CharP R 2] in
/-- The cyclic row isomorphism transports the normalized class. -/
theorem gridCanonicalClass_cyclicRows (hn : 2 ≤ n) :
    homologyMap (laurentMaslovCyclicRowsIso G (ZMod 2)).hom 0 (gridCanonicalClass G hn) =
      gridCanonicalClass (G.relabelRows (finRotate n)) hn :=
  gridCanonicalClass_homotopyEquiv G _ hn hn
    (HomotopyEquiv.ofIso (laurentMaslovCyclicRowsIso G (ZMod 2))) 0
    (Bifiltration.shifts_zero_zero_iff.mpr (laurentMaslovCyclicRows_preserves G (ZMod 2)))

omit R [CharP R 2] in
/-- The cyclic column isomorphism transports the normalized class. -/
theorem gridCanonicalClass_cyclicColumns (hn : 2 ≤ n) :
    homologyMap (laurentMaslovCyclicColumnsIso G (ZMod 2)).hom 0 (gridCanonicalClass G hn) =
      gridCanonicalClass (G.relabelColumns (finRotate n)) hn :=
  gridCanonicalClass_homotopyEquiv G _ hn hn
    (HomotopyEquiv.ofIso (laurentMaslovCyclicColumnsIso G (ZMod 2))) 0
    (Bifiltration.shifts_zero_zero_iff.mpr (laurentMaslovCyclicColumns_preserves G (ZMod 2)))

omit R [CharP R 2] in
/-- The normalized threshold is unchanged by cyclic row translation. -/
theorem gridCanonicalClass_spectralThreshold_cyclicRows (hn : 2 ≤ n) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration (G.relabelRows (finRotate n)) (ZMod 2)).weighted t) 0
      (gridCanonicalClass (G.relabelRows (finRotate n)) hn) =
        ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_cyclicRows G hn]
  exact spectralThreshold_laurentMaslovCyclicRows G (ZMod 2) 0 _ t

omit R [CharP R 2] in
/-- The normalized threshold is unchanged by cyclic column translation. -/
theorem gridCanonicalClass_spectralThreshold_cyclicColumns (hn : 2 ≤ n) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration (G.relabelColumns (finRotate n)) (ZMod 2)).weighted t) 0
      (gridCanonicalClass (G.relabelColumns (finRotate n)) hn) =
        ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_cyclicColumns G hn]
  exact spectralThreshold_laurentMaslovCyclicColumns G (ZMod 2) 0 _ t

end OnLeConjecture.KnotFloer.GridFull
