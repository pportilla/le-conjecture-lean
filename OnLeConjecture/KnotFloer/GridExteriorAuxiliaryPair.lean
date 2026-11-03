/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOSwitchAnyX
public import OnLeConjecture.KnotFloer.GridMovesToCanonicalMap

/-!
# Auxiliary marking pairs and the paired contraction

Section 5 of the written proof of Statement E (`statement_E_complete_proof.tex`) uses auxiliary
marking pairs: pairs of marking states `(O, X)` in which an O marking and an X marking may occupy
the same square. This file formalizes them and proves Lemma `aux-death` and Corollary
`paired-aux-contraction` of that section.

* `markingMaslovℤ S x` is the Maslov grading of `x` with respect to an arbitrary marking state `S`
  (the formula of `GridDiagram.maslovOℤ`). Its change across an empty rectangle
  (`markingMaslovℤ_sub_of_isEmpty`) and across an adjacent column swap
  (`markingMaslovℤ_swapColumns`) are read off from a valid carrier grid with the same O markings.
* `AuxiliaryPair` with its Alexander function `(M_O - M_X)/2 - (n - 1)/2`. Its native complex and
  canonical class are those of the carrier grid `markingCarrier B.O`, whose X markings lie in the
  cyclically next rows. Its bifiltration `AuxiliaryPair.bifiltration` is built from its own
  Alexander function.
* `laurentMaslovBifiltrationOf` builds the bifiltration of a native complex from any Alexander
  function that does not increase along the differential, and `LevelShift` records the filtration
  shift of a Laurent map with respect to two Alexander functions.
* `nativeAuxiliaryContraction` (Lemma `aux-death`): for the auxiliary pair `B` obtained from `G` by
  inserting an O and an X together next to an X marking, there is a native map `ρ_B : C(B) → C(G)`
  with shifts `(0, 1/2)` and `ρ_{B*} can(B) = can(G)`. The derivative `Φ_i` at the coincident
  square has shifts `(0, 0)` (`levelShift_oDerivative_of_coincident`).
* `pairedAuxiliaryContraction` (Corollary `paired-aux-contraction`) and its instance for an actual
  O switch, `pairedAuxiliaryContraction_oSwitch`.

The map `ρ_B` is obtained from the move transport `exists_movesTo_canonical_map_of_two_le` applied
to the X stabilization `A` of `G`, composed with the literal identification `C(B) = C(A)`. The
written proof uses instead an explicit type-R count for the second factor. Both satisfy the
assertions of Lemma `aux-death`. The explicit count matters only for the labelled naturality of
Section 5.2, which is not covered here.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n : ℕ}

/-! ### Maslov gradings with respect to an arbitrary marking state -/

/-- The integer Maslov grading of `x` with respect to the marking state `S`: the formula of
`GridDiagram.maslovOℤ` with the O markings replaced by the points of `S`. -/
def markingMaslovℤ (S x : GridState n) : ℤ :=
  (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.JNumCenter x.pointSet S.pointSet
    + GridPoint.I S.pointSet S.pointSet + 1

theorem maslovOℤ_eq_markingMaslovℤ (G : GridDiagram n) (x : GridState n) :
    G.maslovOℤ x = markingMaslovℤ G.O x := by
  rw [GridDiagram.maslovOℤ_def, GridDiagram.OSet_def, markingMaslovℤ]

theorem maslovXℤ_eq_markingMaslovℤ (G : GridDiagram n) (x : GridState n) :
    G.maslovXℤ x = markingMaslovℤ G.X x := by
  rw [GridDiagram.maslovXℤ_def, GridDiagram.XSet_def, markingMaslovℤ]

/-- A grid diagram with prescribed O markings, each X marking lying in the cyclically next row. -/
def markingCarrier (S : GridState n) (hn : 2 ≤ n) : GridDiagram n where
  O := S
  X := S.relabelRows (finRotate n)
  disjoint c := (Grid.finRotate_ne_self hn (S c)).symm

@[simp]
theorem markingCarrier_O (S : GridState n) (hn : 2 ≤ n) : (markingCarrier S hn).O = S := rfl

/-- A column different from its cyclic successor exists only in grids of size at least two. -/
theorem two_le_of_ne_finRotate {a : Fin n} (ha : a ≠ finRotate n a) : 2 ≤ n := by
  rcases n with _ | _ | n
  · exact a.elim0
  · exact absurd (Fin.ext (by have := a.isLt; have := (finRotate _ a).isLt; omega)) ha
  · omega

/-- The Maslov change across an empty rectangle, for an arbitrary marking state. -/
theorem markingMaslovℤ_sub_of_isEmpty (hn : 2 ≤ n) (S : GridState n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    markingMaslovℤ S x - markingMaslovℤ S y =
      1 - 2 * ((S.pointSet ∩ r.toGridRectangle.coveredSquares).card : ℤ) := by
  have h := (markingCarrier S hn).maslovO_sub_maslovO_eq_one_sub_two_mul_card r hr
  rw [GridDiagram.maslovO_eq_intCast, GridDiagram.maslovO_eq_intCast,
    maslovOℤ_eq_markingMaslovℤ, maslovOℤ_eq_markingMaslovℤ, GridDiagram.OSet_def,
    markingCarrier_O] at h
  exact_mod_cast h

/-- Swapping the marking state in two cyclically adjacent columns changes the Maslov grading of
every state by `1` or `-1`. -/
theorem markingMaslovℤ_swapColumns (S : GridState n) {a : Fin n} (ha : a ≠ finRotate n a)
    (x : GridState n) :
    markingMaslovℤ (S.swapColumns a (finRotate n a)) x = markingMaslovℤ S x +
      if x (finRotate n a) ∈ Grid.cIco (finRotate n (S a)) (finRotate n (S (finRotate n a)))
      then 1 else -1 := by
  have h := (markingCarrier S (two_le_of_ne_finRotate ha)).maslovOℤ_swapColumns_finRotate ha x
  rw [maslovOℤ_eq_markingMaslovℤ, maslovOℤ_eq_markingMaslovℤ, GridDiagram.swapColumns_O] at h
  exact h

theorem markingMaslovℤ_swapColumns_sub_le (S : GridState n) {a : Fin n}
    (ha : a ≠ finRotate n a) (x : GridState n) :
    markingMaslovℤ (S.swapColumns a (finRotate n a)) x - markingMaslovℤ S x ≤ 1 ∧
      -1 ≤ markingMaslovℤ (S.swapColumns a (finRotate n a)) x - markingMaslovℤ S x := by
  rw [markingMaslovℤ_swapColumns S ha x]
  split_ifs <;> omega

/-! ### Auxiliary marking pairs -/

/-- An auxiliary marking pair: two marking states, with `O c = X c` allowed. -/
structure AuxiliaryPair (n : ℕ) where
  /-- The O marking state. -/
  O : GridState n
  /-- The X marking state. -/
  X : GridState n

/-- The auxiliary pair of a grid diagram. -/
def toAuxiliaryPair (G : GridDiagram n) : AuxiliaryPair n := ⟨G.O, G.X⟩

@[simp] theorem toAuxiliaryPair_O (G : GridDiagram n) : (toAuxiliaryPair G).O = G.O := rfl

@[simp] theorem toAuxiliaryPair_X (G : GridDiagram n) : (toAuxiliaryPair G).X = G.X := rfl

namespace AuxiliaryPair

/-- The Alexander function `(M_O - M_X)/2 - (n - 1)/2` of an auxiliary pair. -/
def alexander (B : AuxiliaryPair n) (x : GridState n) : ℚ :=
  ((markingMaslovℤ B.O x - markingMaslovℤ B.X x : ℤ) : ℚ) / 2 - (((n : ℤ) - 1 : ℤ) : ℚ) / 2

/-- The valid grid whose native complex is the complex of an auxiliary pair. -/
def carrier (B : AuxiliaryPair n) (hn : 2 ≤ n) : GridDiagram n := markingCarrier B.O hn

@[simp] theorem carrier_O (B : AuxiliaryPair n) (hn : 2 ≤ n) : (B.carrier hn).O = B.O := rfl

/-- The Alexander change across an empty rectangle is the number of covered X markings minus the
number of covered O markings. -/
theorem alexander_sub_alexander (B : AuxiliaryPair n) (hn : 2 ≤ n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    B.alexander x - B.alexander y =
      ((B.X.pointSet ∩ r.toGridRectangle.coveredSquares).card : ℚ) -
        ((B.O.pointSet ∩ r.toGridRectangle.coveredSquares).card : ℚ) := by
  have hO := markingMaslovℤ_sub_of_isEmpty hn B.O r hr
  have hX := markingMaslovℤ_sub_of_isEmpty hn B.X r hr
  have hO' : (markingMaslovℤ B.O x : ℚ) - markingMaslovℤ B.O y =
      1 - 2 * ((B.O.pointSet ∩ r.toGridRectangle.coveredSquares).card : ℚ) := by
    exact_mod_cast hO
  have hX' : (markingMaslovℤ B.X x : ℚ) - markingMaslovℤ B.X y =
      1 - 2 * ((B.X.pointSet ∩ r.toGridRectangle.coveredSquares).card : ℚ) := by
    exact_mod_cast hX
  simp only [alexander]
  push_cast
  linarith

/-- The O markings covered by a rectangle of the carrier are the covered O markings of the pair. -/
theorem card_OColumns_carrier (B : AuxiliaryPair n) (hn : 2 ≤ n) (r : GridRectangle n) :
    ((B.carrier hn).OColumns r).card = (B.O.pointSet ∩ r.coveredSquares).card := by
  rw [GridDiagram.card_OColumns, GridDiagram.OSet_def, carrier_O]

/-- The Alexander function does not increase along the differential of the carrier. -/
theorem alexander_le (B : AuxiliaryPair n) (hn : 2 ≤ n) (x y : GridState n)
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    B.alexander y - ((B.carrier hn).OColumns r.toGridRectangle).card ≤ B.alexander x := by
  have h := B.alexander_sub_alexander hn r hr
  rw [B.card_OColumns_carrier hn]
  have hX := Nat.cast_nonneg (α := ℚ) (B.X.pointSet ∩ r.toGridRectangle.coveredSquares).card
  linarith

end AuxiliaryPair

/-- The Alexander function of the auxiliary pair of a grid is its Alexander grading. -/
theorem alexander_toAuxiliaryPair (G : GridDiagram n) (x : GridState n) :
    (toAuxiliaryPair G).alexander x = G.alexander x := by
  rw [AuxiliaryPair.alexander, GridDiagram.alexander_def, GridDiagram.maslovO_eq_intCast,
    GridDiagram.maslovX_eq_intCast, maslovOℤ_eq_markingMaslovℤ, maslovXℤ_eq_markingMaslovℤ,
    toAuxiliaryPair_O, toAuxiliaryPair_X]
  push_cast
  ring

/-- The Alexander grading of a grid does not increase along its differential. -/
theorem alexander_le_of_isEmpty (G : GridDiagram n) (x y : GridState n)
    (r : GridRectangleBetween x y) (_hr : r.IsEmpty) :
    G.alexander y - (G.OColumns r.toGridRectangle).card ≤ G.alexander x := by
  have h := G.alexander_sub_alexander_eq_card_sub_card r
  rw [← G.card_OColumns r.toGridRectangle] at h
  have hX := Nat.cast_nonneg (α := ℚ) (G.XSet ∩ r.toGridRectangle.coveredSquares).card
  linarith

/-! ### Bifiltrations from an Alexander function -/

section Level

variable (R : Type*) [CommRing R]

/-- Laurent chains satisfying both coordinate bounds for the Alexander function `α`. -/
def alexanderLevel (α : GridState n → ℚ) (a b : ℝ) : Submodule R (LaurentChain R n) where
  carrier := {c | ∀ x k, k ∈ (c x).coeff.support → -(k : ℝ) ≤ a ∧ (α x : ℝ) - k ≤ b}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro c d hc hd x k hk
    have h : k ∈ (c x).coeff.support ∪ (d x).coeff.support :=
      Finsupp.support_add (by simpa only [Finsupp.add_apply, AddMonoidAlgebra.coeff_add] using hk)
    exact (Finset.mem_union.mp h).elim (hc x k) (hd x k)
  smul_mem' := by
    intro a c hc x k hk
    apply hc x k
    exact Finsupp.support_smul (by
      simpa only [Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul] using hk)

theorem mem_alexanderLevel_iff (α : GridState n → ℚ) (a b : ℝ) (c : LaurentChain R n) :
    c ∈ alexanderLevel R α a b ↔
      ∀ x k, k ∈ (c x).coeff.support → -(k : ℝ) ≤ a ∧ (α x : ℝ) - k ≤ b := Iff.rfl

theorem alexanderLevel_mono (α : GridState n → ℚ) {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    alexanderLevel R α a b ≤ alexanderLevel R α a' b' :=
  fun _ hc x k hk => ⟨(hc x k hk).1.trans ha, (hc x k hk).2.trans hb⟩

theorem laurentBifiltrationLevel_eq_alexanderLevel (G : GridDiagram n) (a b : ℝ) :
    laurentBifiltrationLevel G R a b = alexanderLevel R G.alexander a b := rfl

/-- The differential preserves the levels of an Alexander function that does not increase along
it. -/
theorem laurentDifferential_mem_alexanderLevel (G : GridDiagram n) (α : GridState n → ℚ)
    (hα : ∀ x y (r : GridRectangleBetween x y), r.IsEmpty →
      α y - (G.OColumns r.toGridRectangle).card ≤ α x)
    (a b : ℝ) (c : LaurentChain R n) (hc : c ∈ alexanderLevel R α a b) :
    laurentDifferential G R c ∈ alexanderLevel R α a b := by
  intro y k hk
  obtain ⟨x, j, hj, r, hr, rfl⟩ :=
    exists_rectangle_of_mem_support_laurentDifferential G R c hk
  obtain ⟨hb1, hb2⟩ := hc x j hj
  have h := hα x y r ((GridRectangleBetween.mem_emptyRectangles r).mp hr)
  have h' : (α y : ℝ) - ((G.OColumns r.toGridRectangle).card : ℝ) ≤ α x := by exact_mod_cast h
  have hO := Nat.cast_nonneg (α := ℝ) (G.OColumns r.toGridRectangle).card
  push_cast
  constructor <;> linarith

/-- A Laurent map preserves the first coordinate and raises the second coordinate by at most `s`,
from the levels of `α` to the levels of `β`. -/
def LevelShift (α β : GridState n → ℚ)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) (s : ℝ) : Prop :=
  ∀ u v c, c ∈ alexanderLevel R α u v → f c ∈ alexanderLevel R β u (v + s)

variable {R}

theorem LevelShift.comp {α β γ : GridState n → ℚ}
    {f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n} {s t : ℝ}
    (hf : LevelShift R α β f s) (hg : LevelShift R β γ g t) :
    LevelShift R α γ (g ∘ₗ f) (s + t) := by
  intro u v c hc
  rw [← add_assoc]
  exact hg u (v + s) (f c) (hf u v c hc)

/-- The identity raises the second coordinate by `s` when `β ≤ α + s`. -/
theorem levelShift_id {α β : GridState n → ℚ} {s : ℝ} (h : ∀ x, (β x : ℝ) ≤ α x + s) :
    LevelShift R α β LinearMap.id s := by
  intro u v c hc x k hk
  obtain ⟨h1, h2⟩ := hc x k hk
  exact ⟨h1, by linarith [h x]⟩

/-- Coordinate bounds on the matrix of a Laurent map give its level shift. -/
theorem levelShift_of_matrix (α β : GridState n → ℚ)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) (s : ℚ)
    (hf : ∀ x y k, k ∈ (f (single x 1) y).coeff.support →
      (0 : ℚ) ≤ k ∧ β y - k ≤ α x + s) :
    LevelShift R α β f s := by
  intro u v c hc y k hk
  obtain ⟨x, j, hj, d, hd, rfl⟩ := exists_support_laurentMap f c hk
  obtain ⟨hfirst, hsecond⟩ := hf x y d hd
  have hfirst' : (0 : ℝ) ≤ d := by exact_mod_cast hfirst
  have hsecond' : (β y : ℝ) - d ≤ (α x : ℝ) + s := by exact_mod_cast hsecond
  obtain ⟨hx, hy⟩ := hc x j hj
  push_cast
  constructor <;> linarith

end Level

section Bifiltration

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The bifiltration of the native complex of `G` defined by an Alexander function that does not
increase along the differential. -/
def laurentMaslovBifiltrationOf (G : GridDiagram n) (α : GridState n → ℚ)
    (hα : ∀ x y (r : GridRectangleBetween x y), r.IsEmpty →
      α y - (G.OColumns r.toGridRectangle).card ≤ α x) :
    Bifiltration (laurentMaslovComplex G R) where
  level a b m := ((alexanderLevel R α a b).comap (laurentMaslovPiece G R m).subtype).comap
    (laurentMaslovChainEquiv G R m).toLinearMap
  mono _ _ _ _ _ ha hb :=
    Submodule.comap_mono (Submodule.comap_mono (alexanderLevel_mono R α ha hb))
  differential_mem a b i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      change (laurentMaslovChainEquiv G R j ((laurentMaslovComplex G R).d (j + 1) j c) :
        LaurentChain R n) ∈ alexanderLevel R α a b
      rw [laurentMaslovChainEquiv_d]
      exact laurentDifferential_mem_alexanderLevel R G α hα a b _ hc
    · have hrel : ¬ (ComplexShape.down ℤ).Rel i j := by
        simpa only [ComplexShape.down_Rel] using h
      rw [(laurentMaslovComplex G R).shape i j hrel]
      exact Submodule.zero_mem _

/-- The bifiltration of a grid is the bifiltration of its Alexander grading. -/
theorem laurentMaslovBifiltrationOf_alexander (G : GridDiagram n) :
    laurentMaslovBifiltrationOf R G G.alexander (alexander_le_of_isEmpty G) =
      laurentMaslovBifiltration G R := rfl

/-- The bifiltration of an auxiliary marking pair on the native complex of its carrier. -/
def AuxiliaryPair.bifiltration (B : AuxiliaryPair n) (hn : 2 ≤ n) :
    Bifiltration (laurentMaslovComplex (B.carrier hn) R) :=
  laurentMaslovBifiltrationOf R (B.carrier hn) B.alexander (B.alexander_le hn)

variable {R}

/-- Filtration shifts of a native morphism made from a Laurent map with a level shift. -/
theorem laurentMaslovHomOfMap_shiftsOf (G H : GridDiagram n) {α β : GridState n → ℚ}
    (hα : ∀ x y (r : GridRectangleBetween x y), r.IsEmpty →
      α y - (G.OColumns r.toGridRectangle).card ≤ α x)
    (hβ : ∀ x y (r : GridRectangleBetween x y), r.IsEmpty →
      β y - (H.OColumns r.toGridRectangle).card ≤ β x)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) {s : ℝ}
    (hf : LevelShift R α β f s) :
    (laurentMaslovBifiltrationOf R G α hα).Shifts (laurentMaslovBifiltrationOf R H β hβ)
      (laurentMaslovHomOfMap G H f hdeg hcomm) 0 s := by
  intro u v m c hc
  rw [add_zero]
  exact hf u v _ hc

/-- Filtration shifts of the identification of the complexes of two grids with the same O
markings. -/
theorem laurentMaslovMarkingIso_shiftsOf {G H : GridDiagram n} (hO : G.O = H.O)
    {α β : GridState n → ℚ}
    (hα : ∀ x y (r : GridRectangleBetween x y), r.IsEmpty →
      α y - (G.OColumns r.toGridRectangle).card ≤ α x)
    (hβ : ∀ x y (r : GridRectangleBetween x y), r.IsEmpty →
      β y - (H.OColumns r.toGridRectangle).card ≤ β x) {s : ℝ}
    (hf : LevelShift R α β LinearMap.id s) :
    (laurentMaslovBifiltrationOf R G α hα).Shifts (laurentMaslovBifiltrationOf R H β hβ)
      (laurentMaslovMarkingIso R hO).hom 0 s := by
  intro u v m c hc
  rw [add_zero]
  exact hf u v _ hc

end Bifiltration

/-- The canonical class of an auxiliary marking pair, defined through its carrier grid. By
`gridCanonicalClass_markingIso` the identification with any valid grid with the same O markings
carries it to the canonical class of that grid. -/
def AuxiliaryPair.canonicalClass (B : AuxiliaryPair n) (hn : 2 ≤ n) :
    (laurentMaslovComplex (B.carrier hn) (ZMod 2)).homology 0 :=
  gridCanonicalClass (B.carrier hn) hn

/-! ### The derivative at a coincident square and the O switch to an auxiliary pair -/

section Maps

variable {R : Type*} [CommRing R]

/-- At a column whose O and X markings coincide, the derivative map has shifts `(0, 0)` for the
Alexander function of the pair: `A(y) - (n_O(q) - 1) - A(x) = 1 - n_X(q) ≤ 0`. -/
theorem levelShift_oDerivative_of_coincident (B : AuxiliaryPair n) (hn : 2 ≤ n) {h : Fin n}
    (hh : B.O h = B.X h) :
    LevelShift R B.alexander B.alexander (oDerivative R (B.carrier hn) {h}) 0 := by
  have h0 := levelShift_of_matrix (R := R) B.alexander B.alexander
    (oDerivative R (B.carrier hn) {h}) 0 ?_
  · simpa using h0
  intro x y k hk
  obtain ⟨r, hr, hmem, hk1⟩ := exists_rectangle_of_mem_support_oDerivative (B.carrier hn) h hk
  have hr' := (GridRectangleBetween.mem_emptyRectangles r).mp hr
  have hdiff := B.alexander_sub_alexander hn r hr'
  have hcard := B.card_OColumns_carrier hn r.toGridRectangle
  have hcov : (h, B.X h) ∈ B.X.pointSet ∩ r.toGridRectangle.coveredSquares := by
    rw [Finset.mem_inter, GridState.mem_pointSet]
    refine ⟨rfl, ?_⟩
    rw [← hh]
    exact (GridDiagram.mem_OColumns _).mp hmem
  have hX : (1 : ℚ) ≤ ((B.X.pointSet ∩ r.toGridRectangle.coveredSquares).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨_, hcov⟩
  have hpos : (1 : ℚ) ≤ (((B.carrier hn).OColumns r.toGridRectangle).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨h, hmem⟩
  have hkQ : (k : ℚ) + 1 = (((B.carrier hn).OColumns r.toGridRectangle).card : ℚ) := by
    exact_mod_cast hk1
  rw [hcard] at hpos hkQ
  constructor <;> linarith

/-- The Alexander function of an auxiliary pair obtained by an O switch from a grid with the same
X markings. -/
theorem AuxiliaryPair.alexander_oSwitch {K : GridDiagram n} {B : AuxiliaryPair n} {a : Fin n}
    (ha : a ≠ finRotate n a) (hO : B.O = K.O.swapColumns a (finRotate n a)) (hX : B.X = K.X)
    (x : GridState n) :
    B.alexander x = K.alexander x + oSwitchIndicator K a x - 1 / 2 := by
  have hn := two_le_of_ne_finRotate ha
  have hM := maslovOℤ_oSwitch (G := K) (H := B.carrier hn) ha hO x
  rw [maslovOℤ_eq_markingMaslovℤ, AuxiliaryPair.carrier_O] at hM
  rw [← alexander_toAuxiliaryPair, AuxiliaryPair.alexander, AuxiliaryPair.alexander, hM, hX,
    maslovOℤ_eq_markingMaslovℤ, toAuxiliaryPair_O, toAuxiliaryPair_X]
  push_cast
  ring

/-- The O switch from a grid to an auxiliary pair with the same X markings has shifts
`(0, -1/2)`. -/
theorem levelShift_oSwitchMap_auxiliary {K : GridDiagram n} {B : AuxiliaryPair n} {a : Fin n}
    (ha : a ≠ finRotate n a) (hO : B.O = K.O.swapColumns a (finRotate n a)) (hX : B.X = K.X) :
    LevelShift R K.alexander B.alexander (oSwitchMap R K a) (-1 / 2) := by
  have h0 := levelShift_of_matrix (R := R) K.alexander B.alexander (oSwitchMap R K a) (-1 / 2) ?_
  · have hc : ((-1 / 2 : ℚ) : ℝ) = -1 / 2 := by norm_num
    rw [hc] at h0
    exact h0
  intro x y k hk
  rw [oSwitchMap_single] at hk
  by_cases hxy : x = y
  · subst hxy
    rw [Finsupp.single_eq_same] at hk
    have hk' : k = oSwitchIndicator K a x := by
      change k ∈ (Finsupp.single (oSwitchIndicator K a x) (1 : R)).support at hk
      exact Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    subst hk'
    refine ⟨by exact_mod_cast oSwitchIndicator_nonneg K a x, ?_⟩
    rw [AuxiliaryPair.alexander_oSwitch ha hO hX x]
    linarith
  · rw [Finsupp.single_apply, if_neg hxy] at hk
    simp at hk

end Maps

/-! ### The auxiliary insertion and Lemma `aux-death` -/

section Insertion

variable {N : ℕ}

theorem finRotate_castSucc_eq_succ (i : Fin N) : finRotate (N + 1) i.castSucc = i.succ := by
  ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
  simp

/-- The auxiliary pair `B` of Lemma `aux-death`: a column is inserted immediately to the right of
column `c`, a row immediately above the row `r = G.X c`, and an O and an X marking are placed
together in the new square `(c + 1, r + 1)`. -/
def auxiliaryInsertion (G : GridDiagram N) (c : Fin N) : AuxiliaryPair (N + 1) :=
  ⟨G.O.insertPoint c.succ (G.X c).succ, G.X.insertPoint c.succ (G.X c).succ⟩

/-- The X stabilization `A` of Lemma `aux-death`: in the inserted `2 × 2` block it has X markings
at `(c, r + 1)` and `(c + 1, r)`, the O marking at `(c + 1, r + 1)`, and an empty southwest
square. -/
def auxiliaryStabilization (G : GridDiagram N) (c : Fin N) : GridDiagram (N + 1) :=
  G.stabilizeX c.succ (G.X c).succ c

theorem auxiliaryStabilization_O (G : GridDiagram N) (c : Fin N) :
    (auxiliaryStabilization G c).O = (auxiliaryInsertion G c).O := by
  rw [auxiliaryStabilization, GridDiagram.stabilizeX_O]
  rfl

theorem succ_succAbove_self (i : Fin N) : i.succ.succAbove i = i.castSucc :=
  Fin.succAbove_of_castSucc_lt i.succ i Fin.castSucc_lt_succ

/-- The X markings of `A` are those of `B` with the two new columns exchanged. -/
theorem auxiliaryStabilization_X (G : GridDiagram N) (c : Fin N) :
    (auxiliaryStabilization G c).X =
      (auxiliaryInsertion G c).X.swapColumns c.castSucc (finRotate (N + 1) c.castSucc) := by
  rw [finRotate_castSucc_eq_succ, auxiliaryStabilization, GridDiagram.stabilizeX_X]
  ext j : 1
  refine Fin.succAboveCases c.succ ?_ (fun i => ?_) j
  · rw [GridState.splitPoint_apply_newColumn, GridState.swapColumns_apply, Equiv.swap_apply_right]
    change _ = G.X.insertPoint c.succ (G.X c).succ c.castSucc
    rw [← succ_succAbove_self c, GridState.insertPoint_apply_succAbove]
  · rw [GridState.splitPoint_apply_succAbove, GridState.swapColumns_apply]
    split_ifs with hi
    · rw [hi, succ_succAbove_self, Equiv.swap_apply_left]
      change _ = G.X.insertPoint c.succ (G.X c).succ c.succ
      rw [GridState.insertPoint_apply_newColumn]
    · have h1 : c.succ.succAbove i ≠ c.castSucc := by
        rw [← succ_succAbove_self c]
        exact fun h => hi (Fin.succAbove_right_injective h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 (Fin.succAbove_ne _ _)]
      change _ = G.X.insertPoint c.succ (G.X c).succ (c.succ.succAbove i)
      rw [GridState.insertPoint_apply_succAbove]

/-- The new O marking of `B` lies on its new X marking. -/
theorem auxiliaryInsertion_coincident (G : GridDiagram N) (c : Fin N) :
    (auxiliaryInsertion G c).O c.succ = (auxiliaryInsertion G c).X c.succ := by
  change G.O.insertPoint c.succ (G.X c).succ c.succ = G.X.insertPoint c.succ (G.X c).succ c.succ
  rw [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_newColumn]

theorem castSucc_ne_finRotate_castSucc (c : Fin N) :
    c.castSucc ≠ finRotate (N + 1) c.castSucc := by
  rw [finRotate_castSucc_eq_succ]
  exact (Fin.castSucc_lt_succ : c.castSucc < c.succ).ne

/-- The stabilization `A` is an elementary X stabilization of `G`. -/
theorem isXStabilization_auxiliaryStabilization (G : GridDiagram N) (c : Fin N) :
    GridDiagram.IsXStabilization G (auxiliaryStabilization G c) := by
  refine G.isXStabilization_stabilizeX c.succ (G.X c).succ c (Or.inr ?_) (Or.inr ?_)
  · rw [succ_succAbove_self, finRotate_castSucc_eq_succ]
  · rw [succ_succAbove_self, finRotate_castSucc_eq_succ]

theorem auxiliaryStabilization_movesTo (G : GridDiagram N) (c : Fin N) :
    (auxiliaryStabilization G c).MovesTo G :=
  Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
    (GridDiagram.IsMove.stabilization ((GridDiagram.isStabilization_iff _ _).mpr
      (Or.inr (isXStabilization_auxiliaryStabilization G c)))))

/-- The Alexander gradings of `A` and `B` differ by at most `1/2`. -/
theorem alexander_auxiliaryStabilization_le (G : GridDiagram N) (c : Fin N)
    (x : GridState (N + 1)) :
    (auxiliaryStabilization G c).alexander x ≤ (auxiliaryInsertion G c).alexander x + 1 / 2 := by
  obtain ⟨-, h2⟩ := markingMaslovℤ_swapColumns_sub_le (auxiliaryInsertion G c).X
    (castSucc_ne_finRotate_castSucc c) x
  rw [← auxiliaryStabilization_X] at h2
  have h2' : (-1 : ℚ) ≤ (markingMaslovℤ (auxiliaryStabilization G c).X x : ℚ) -
      markingMaslovℤ (auxiliaryInsertion G c).X x := by exact_mod_cast h2
  rw [← alexander_toAuxiliaryPair]
  simp only [AuxiliaryPair.alexander, toAuxiliaryPair_O, toAuxiliaryPair_X,
    auxiliaryStabilization_O]
  push_cast
  linarith

/-- The literal identification `I : C(B) → C(A)` has shifts `(0, 1/2)`. -/
theorem auxiliaryInsertion_identification_shifts (G : GridDiagram N) (c : Fin N)
    (hn : 2 ≤ N + 1) :
    ((auxiliaryInsertion G c).bifiltration (ZMod 2) hn).Shifts
      (laurentMaslovBifiltration (auxiliaryStabilization G c) (ZMod 2))
      (laurentMaslovMarkingIso (ZMod 2)
        (G := (auxiliaryInsertion G c).carrier hn) (H := auxiliaryStabilization G c)
        (auxiliaryStabilization_O G c).symm).hom
      0 (1 / 2) := by
  rw [← laurentMaslovBifiltrationOf_alexander]
  apply laurentMaslovMarkingIso_shiftsOf
  apply levelShift_id
  intro x
  have h := alexander_auxiliaryStabilization_le G c x
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  exact h'

/-- **Lemma `aux-death`** (`nativeAuxiliaryContraction`). For the auxiliary pair `B` obtained by
inserting an O and an X marking together next to the X marking of column `c`, there is a native
map `ρ_B : C(B) → C(G)` of degree zero with shifts `(0, 1/2)` and `ρ_{B*} can(B) = can(G)`. The
map `D_B = ρ_B Φ_i` of the lemma is its composite with the derivative at the coincident square
`i = c + 1`, which is a chain map of degree `+1` (`laurentDifferential_comp_oDerivative_eq`,
`oDerivative_singleton_mem_maslovPiece`) with shifts `(0, 0)`
(`levelShift_oDerivative_of_coincident`, `auxiliaryInsertion_coincident`). -/
theorem nativeAuxiliaryContraction (G : GridDiagram N) (hN : 2 ≤ N) (c : Fin N) :
    ∃ ρ : laurentMaslovComplex ((auxiliaryInsertion G c).carrier (Nat.le_succ_of_le hN))
        (ZMod 2) ⟶ laurentMaslovComplex G (ZMod 2),
      ((auxiliaryInsertion G c).bifiltration (ZMod 2) (Nat.le_succ_of_le hN)).Shifts
        (laurentMaslovBifiltration G (ZMod 2)) ρ 0 (1 / 2) ∧
      homologyMap ρ 0 ((auxiliaryInsertion G c).canonicalClass (Nat.le_succ_of_le hN)) =
        gridCanonicalClass G hN := by
  have hN1 : 2 ≤ N + 1 := Nat.le_succ_of_le hN
  obtain ⟨_, RA, hRs, hRc⟩ := exists_movesTo_canonical_map_of_two_le
    (auxiliaryStabilization G c) G hN1 (auxiliaryStabilization_movesTo G c)
  refine ⟨(laurentMaslovMarkingIso (ZMod 2)
    (G := (auxiliaryInsertion G c).carrier hN1) (H := auxiliaryStabilization G c)
    (auxiliaryStabilization_O G c).symm).hom ≫ RA,
    ?_, ?_⟩
  · have h := (auxiliaryInsertion_identification_shifts G c hN1).comp hRs
    simpa using h
  · rw [homologyMap_comp, CategoryTheory.comp_apply, AuxiliaryPair.canonicalClass,
      gridCanonicalClass_markingIso _ _ hN1 (auxiliaryStabilization_O G c).symm, hRc]

/-- **Corollary `paired-aux-contraction`** (`pairedAuxiliaryContraction`). If a native map
`φ = Φ_i F : C(K) → C(B)` has shifts `(0, -1/2)` and sends `can(K)` to `can(B)`, then
`D_B F = ρ_B φ` has shifts `(0, 0)` and sends `can(K)` to `can(G)`. -/
theorem pairedAuxiliaryContraction (G : GridDiagram N) (hN : 2 ≤ N) (c : Fin N)
    (K : GridDiagram (N + 1))
    (φ : laurentMaslovComplex K (ZMod 2) ⟶
      laurentMaslovComplex ((auxiliaryInsertion G c).carrier (Nat.le_succ_of_le hN)) (ZMod 2))
    (hφ : (laurentMaslovBifiltration K (ZMod 2)).Shifts
      ((auxiliaryInsertion G c).bifiltration (ZMod 2) (Nat.le_succ_of_le hN)) φ 0 (-1 / 2))
    (hcan : homologyMap φ 0 (gridCanonicalClass K (Nat.le_succ_of_le hN)) =
      (auxiliaryInsertion G c).canonicalClass (Nat.le_succ_of_le hN)) :
    ∃ ρ : laurentMaslovComplex ((auxiliaryInsertion G c).carrier (Nat.le_succ_of_le hN))
        (ZMod 2) ⟶ laurentMaslovComplex G (ZMod 2),
      ((auxiliaryInsertion G c).bifiltration (ZMod 2) (Nat.le_succ_of_le hN)).Shifts
        (laurentMaslovBifiltration G (ZMod 2)) ρ 0 (1 / 2) ∧
      homologyMap ρ 0 ((auxiliaryInsertion G c).canonicalClass (Nat.le_succ_of_le hN)) =
        gridCanonicalClass G hN ∧
      (laurentMaslovBifiltration K (ZMod 2)).Shifts (laurentMaslovBifiltration G (ZMod 2))
        (φ ≫ ρ) 0 0 ∧
      homologyMap (φ ≫ ρ) 0 (gridCanonicalClass K (Nat.le_succ_of_le hN)) =
        gridCanonicalClass G hN := by
  obtain ⟨ρ, hρs, hρc⟩ := nativeAuxiliaryContraction G hN c
  refine ⟨ρ, hρs, hρc, ?_, ?_⟩
  · have h := hφ.comp hρs
    norm_num at h
    exact h
  · rw [homologyMap_comp, CategoryTheory.comp_apply, hcan, hρc]

/-- Corollary `paired-aux-contraction` for an actual O switch `F : C(K) → C(B)`, where `K` is a
valid grid with the X markings of `B` and `B.O` is `K.O` with columns `a` and `a + 1` exchanged,
and the coincident O marking of `B` comes from column `cK ≠ c + 1` of `K`. The map `Φ_i F` is
`oDerivativeSwitchHom`. -/
theorem pairedAuxiliaryContraction_oSwitch (G : GridDiagram N) (hN : 2 ≤ N) (c : Fin N)
    (K : GridDiagram (N + 1)) {a : Fin (N + 1)} (ha : a ≠ finRotate (N + 1) a)
    (hO : ((auxiliaryInsertion G c).carrier (Nat.le_succ_of_le hN)).O =
      K.O.swapColumns a (finRotate (N + 1) a))
    (hX : (auxiliaryInsertion G c).X = K.X) {cK : Fin (N + 1)} (hc : c.succ ≠ cK)
    (hrow : (auxiliaryInsertion G c).O c.succ = K.O cK) :
    ∃ ρ : laurentMaslovComplex ((auxiliaryInsertion G c).carrier (Nat.le_succ_of_le hN))
        (ZMod 2) ⟶ laurentMaslovComplex G (ZMod 2),
      ((auxiliaryInsertion G c).bifiltration (ZMod 2) (Nat.le_succ_of_le hN)).Shifts
        (laurentMaslovBifiltration G (ZMod 2)) ρ 0 (1 / 2) ∧
      homologyMap ρ 0 ((auxiliaryInsertion G c).canonicalClass (Nat.le_succ_of_le hN)) =
        gridCanonicalClass G hN ∧
      (laurentMaslovBifiltration K (ZMod 2)).Shifts (laurentMaslovBifiltration G (ZMod 2))
        (oDerivativeSwitchHom (ZMod 2) ha hO c.succ ≫ ρ) 0 0 ∧
      homologyMap (oDerivativeSwitchHom (ZMod 2) ha hO c.succ ≫ ρ) 0
        (gridCanonicalClass K (Nat.le_succ_of_le hN)) = gridCanonicalClass G hN := by
  have hN1 : 2 ≤ N + 1 := Nat.le_succ_of_le hN
  set B := auxiliaryInsertion G c with hB
  have hshift : (laurentMaslovBifiltration K (ZMod 2)).Shifts (B.bifiltration (ZMod 2) hN1)
      (oDerivativeSwitchHom (ZMod 2) ha hO c.succ) 0 (-1 / 2) := by
    have h := laurentMaslovHomOfMap_shiftsOf K (B.carrier hN1) (alexander_le_of_isEmpty K)
      (B.alexander_le hN1)
      (oDerivative (ZMod 2) (B.carrier hN1) {c.succ} ∘ₗ oSwitchMap (ZMod 2) K a)
      (oDerivativeSwitch_mem_maslovPiece ha hO c.succ)
      (laurentDifferential_comp_oDerivativeSwitch ha hO c.succ)
      ((levelShift_oSwitchMap_auxiliary (B := B) ha hO hX).comp
        (levelShift_oDerivative_of_coincident B hN1 (auxiliaryInsertion_coincident G c)))
    rw [laurentMaslovBifiltrationOf_alexander, add_zero] at h
    exact h
  have hcan := homologyMap_labelDerivativeSwitch_gridCanonicalClass_anyX (G := K)
    (H := B.carrier hN1) hN1 ha hO hc hrow
  exact pairedAuxiliaryContraction G hN c K _ hshift hcan

end Insertion

end OnLeConjecture.KnotFloer.GridFull
