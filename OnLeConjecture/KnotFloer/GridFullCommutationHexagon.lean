/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationFilteredInverse
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Commutation.Hexagon

/-!
# Filtration and grading of the full hexagon map

Count empty hexagons of both geometric orientations, allowing X markings. The rectangle
under each hexagon contains exactly one additional O marking and one additional X marking.
Its weighted Maslov degree therefore rises by one, while its two filtration coordinates
decrease by the O and X counts of the hexagon. These statements apply to the concrete full
Laurent hexagon map. Its inverse-homotopy equation is a separate assertion.

The geometric shapes and O-marking removal identities are ported from TauCeti at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`. The Maslov argument adapts its
`Commutation/Grading/Hexagon.lean`, and the X-marking removal identity below generalizes
its X-avoiding special case to arbitrary X counts.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} {G : GridDiagram n}

/-- The two geometric orientations of a commutation hexagon. -/
abbrev FullCommutationHexagon (C : GridDiagram.ColumnCommutationData G) (x y : GridState n) :=
  GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y ⊕
    GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y

namespace FullCommutationHexagon

variable {C : GridDiagram.ColumnCommutationData G} {x y : GridState n}

/-- The underlying oriented rectangle of either hexagon shape. -/
def toRectangle : FullCommutationHexagon C x y → GridRectangleBetween x y
  | .inl P => P.toGridRectangleBetween
  | .inr P => P.toGridRectangleBetween

/-- Emptiness excludes interior state points, with no restriction on markings. -/
def IsEmpty (P : FullCommutationHexagon C x y) : Prop := P.toRectangle.IsEmpty

/-- The marking squares inside either hexagon shape. -/
noncomputable def coveredSquares : FullCommutationHexagon C x y → Finset (Fin n × Fin n)
  | .inl P => P.coveredSquares
  | .inr P => P.coveredSquares

/-- The O-marking count of the hexagon. -/
noncomputable def oCount (P : FullCommutationHexagon C x y) : ℕ :=
  (G.OSet ∩ P.coveredSquares).card

/-- The X-marking count of the hexagon. -/
noncomputable def xCount (P : FullCommutationHexagon C x y) : ℕ :=
  (G.XSet ∩ P.coveredSquares).card

end FullCommutationHexagon

variable (G)

/-- The terminal-side hexagon removes exactly the X marking of the cut-off column. -/
theorem XSet_inter_rectangle_eq_insert_hexagon (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y) :
    G.XSet ∩ P.toGridRectangle.coveredSquares =
      insert (C.column, G.X C.column) (G.XSet ∩ P.coveredSquares) := by
  classical
  ext p
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_inter,
    G.mem_XSet, P.mem_coveredSquares]
  constructor
  · rintro ⟨hp, hr⟩
    by_cases hc : p.1 = C.column
    · exact Or.inl (Prod.ext hc (by rw [← hc, hp]))
    · exact Or.inr ⟨hp, hc, hr⟩
  · rintro (rfl | ⟨hp, _, hr⟩)
    · exact ⟨rfl, G.column_mem_toGridRectangle_coveredSquares P C.X_column_below⟩
    · exact ⟨hp, hr⟩

/-- The initial-side hexagon removes exactly the X marking of the successor column. -/
theorem XSet_inter_rectangle_eq_insert_initialHexagon (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    G.XSet ∩ P.toGridRectangle.coveredSquares =
      insert (finRotate n C.column, G.X (finRotate n C.column))
        (G.XSet ∩ P.coveredSquares) := by
  classical
  ext p
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_inter,
    G.mem_XSet, P.mem_coveredSquares]
  constructor
  · rintro ⟨hp, hr⟩
    by_cases hc : p.1 = finRotate n C.column
    · exact Or.inl (Prod.ext hc (by rw [← hc, hp]))
    · exact Or.inr ⟨hp, hc, hr⟩
  · rintro (rfl | ⟨hp, _, hr⟩)
    · exact ⟨rfl, G.next_mem_toGridRectangle_coveredSquares P C.X_next_above⟩
    · exact ⟨hp, hr⟩

/-- The rectangle underlying either hexagon has one additional marking of each kind. -/
theorem fullCommutationHexagon_rectangle_counts (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : FullCommutationHexagon C x y) :
    (G.OSet ∩ P.toRectangle.toGridRectangle.coveredSquares).card = P.oCount + 1 ∧
      (G.XSet ∩ P.toRectangle.toGridRectangle.coveredSquares).card = P.xCount + 1 := by
  classical
  rcases P with P | P
  · constructor
    · change (G.OSet ∩ P.toGridRectangle.coveredSquares).card =
        (G.OSet ∩ P.coveredSquares).card + 1
      rw [← G.card_OColumns, G.OColumns_toGridRectangle_eq_insert_of_hexagon P,
        Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares]), G.card_OColumnsOfSquares]
    · change (G.XSet ∩ P.toGridRectangle.coveredSquares).card =
        (G.XSet ∩ P.coveredSquares).card + 1
      rw [XSet_inter_rectangle_eq_insert_hexagon G C P,
        Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares])]
  · constructor
    · change (G.OSet ∩ P.toGridRectangle.coveredSquares).card =
        (G.OSet ∩ P.coveredSquares).card + 1
      rw [← G.card_OColumns, G.OColumns_toGridRectangle_eq_insert_of_initialHexagon P,
        Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares]), G.card_OColumnsOfSquares]
    · change (G.XSet ∩ P.toGridRectangle.coveredSquares).card =
        (G.XSet ∩ P.coveredSquares).card + 1
      rw [XSet_inter_rectangle_eq_insert_initialHexagon G C P,
        Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares])]

/-- An empty hexagon raises the unweighted Maslov grading by one plus twice its O count. -/
theorem fullCommutationHexagon_maslov_change (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : FullCommutationHexagon C x y) (hP : P.IsEmpty) :
    G.maslovOℤ y = G.maslovOℤ x + 1 + 2 * (P.oCount : ℤ) := by
  have h := G.maslovO_sub_maslovO_eq_one_sub_two_mul_card P.toRectangle hP
  rw [(fullCommutationHexagon_rectangle_counts G C P).1,
    G.maslovO_eq_intCast, G.maslovO_eq_intCast] at h
  have hq : (G.maslovOℤ y : ℚ) = (G.maslovOℤ x : ℚ) + 1 + 2 * (P.oCount : ℚ) := by
    push_cast at h
    linarith
  exact_mod_cast hq

/-- The weighted Alexander-coordinate drop is the X count, without X-avoidance. -/
theorem fullCommutationHexagon_alexander_change (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : FullCommutationHexagon C x y) :
    G.alexander y - (P.oCount : ℚ) = G.alexander x - (P.xCount : ℚ) := by
  have h := G.alexander_sub_alexander_eq_card_sub_card P.toRectangle
  obtain ⟨hO, hX⟩ := fullCommutationHexagon_rectangle_counts G C P
  rw [hO, hX] at h
  push_cast at h
  linarith

/-- Each Laurent-weighted empty hexagon term raises Maslov degree by exactly one. -/
theorem fullCommutationHexagon_maslovDegree (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : FullCommutationHexagon C x y) (hP : P.IsEmpty) (k : ℤ) :
    laurentMaslovDegree G (k + (P.oCount : ℤ)) y = laurentMaslovDegree G k x + 1 := by
  rw [laurentMaslovDegree, fullCommutationHexagon_maslov_change G C P hP, laurentMaslovDegree]
  ring

/-- Every full hexagon term decreases both filtration coordinates. -/
theorem fullCommutationHexagon_coordinates_le (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : FullCommutationHexagon C x y) (k : ℤ) :
    -((k + (P.oCount : ℤ) : ℤ) : ℝ) ≤ -(k : ℝ) ∧
      (G.alexander y : ℝ) - (k + (P.oCount : ℤ) : ℤ) ≤ (G.alexander x : ℝ) - k := by
  have h := fullCommutationHexagon_alexander_change G C P
  have hreal : (G.alexander y : ℝ) - (P.oCount : ℝ) =
      (G.alexander x : ℝ) - (P.xCount : ℝ) := by exact_mod_cast h
  have hO := Nat.cast_nonneg (α := ℝ) P.oCount
  have hX := Nat.cast_nonneg (α := ℝ) P.xCount
  push_cast
  constructor <;> linarith

/-- All empty hexagons of both orientations, with arbitrary X count. -/
noncomputable def fullCommutationHexagons (C : GridDiagram.ColumnCommutationData G)
    (x y : GridState n) : Finset (FullCommutationHexagon C x y) := by
  classical
  exact Finset.univ.filter FullCommutationHexagon.IsEmpty

@[simp]
theorem mem_fullCommutationHexagons {C : GridDiagram.ColumnCommutationData G} {x y : GridState n}
    (P : FullCommutationHexagon C x y) : P ∈ fullCommutationHexagons G C x y ↔ P.IsEmpty := by
  classical
  simp [fullCommutationHexagons]

variable (R : Type*) [CommSemiring R]

/-- The O-weighted full hexagon coefficient. -/
noncomputable def laurentCommutationHexagonCoefficient (C : GridDiagram.ColumnCommutationData G)
    (x y : GridState n) : LaurentPolynomial R :=
  ∑ P ∈ fullCommutationHexagons G C x y, LaurentPolynomial.T (P.oCount : ℤ)

/-- The full hexagon map evaluated on a grid state. -/
noncomputable def laurentCommutationHexagonOnGenerator (C : GridDiagram.ColumnCommutationData G)
    (x : GridState n) : LaurentChain R n :=
  ∑ y, Finsupp.single y (laurentCommutationHexagonCoefficient G R C x y)

@[simp]
theorem laurentCommutationHexagonOnGenerator_apply (C : GridDiagram.ColumnCommutationData G)
    (x y : GridState n) :
    laurentCommutationHexagonOnGenerator G R C x y =
      laurentCommutationHexagonCoefficient G R C x y := by
  classical
  rw [laurentCommutationHexagonOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The Laurent-linear count of all empty geometric commutation hexagons. -/
noncomputable def laurentCommutationHexagonMap (C : GridDiagram.ColumnCommutationData G) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  Finsupp.lsum (LaurentPolynomial R) fun x : GridState n =>
    (LinearMap.id : LaurentPolynomial R →ₗ[LaurentPolynomial R]
      LaurentPolynomial R).smulRight (laurentCommutationHexagonOnGenerator G R C x)

@[simp]
theorem laurentCommutationHexagonMap_single (C : GridDiagram.ColumnCommutationData G)
    (x : GridState n) :
    laurentCommutationHexagonMap G R C (Finsupp.single x 1) =
      laurentCommutationHexagonOnGenerator G R C x := by
  rw [laurentCommutationHexagonMap, Finsupp.lsum_single]
  simp

theorem laurentCommutationHexagonMap_apply_apply (C : GridDiagram.ColumnCommutationData G)
    (c : LaurentChain R n) (y : GridState n) :
    laurentCommutationHexagonMap G R C c y =
      c.sum fun x a => a * laurentCommutationHexagonCoefficient G R C x y := by
  simp [laurentCommutationHexagonMap, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    LinearMap.smulRight_apply]

/-- Every surviving term is contributed by a genuine empty hexagon and its O count. -/
theorem exists_hexagon_of_mem_support_laurentCommutationHexagonMap
    (C : GridDiagram.ColumnCommutationData G) (c : LaurentChain R n) {y : GridState n} {k : ℤ}
    (hk : k ∈ (laurentCommutationHexagonMap G R C c y).coeff.support) :
    ∃ x : GridState n, ∃ j ∈ (c x).coeff.support,
      ∃ P ∈ fullCommutationHexagons G C x y, k = j + (P.oCount : ℤ) := by
  classical
  rw [laurentCommutationHexagonMap_apply_apply, Finsupp.sum, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  rw [laurentCommutationHexagonCoefficient, AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨P, hP, hdP⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hd)
  change d ∈ (Finsupp.single (P.oCount : ℤ) (1 : R)).support at hdP
  have hd := Finset.mem_singleton.mp (Finsupp.support_single_subset hdP)
  exact ⟨x, j, hj, P, hP, by rw [hd]⟩

/-- The full geometric hexagon map raises Maslov degree by one. -/
theorem laurentCommutationHexagonMap_mem_maslovPiece (C : GridDiagram.ColumnCommutationData G)
    {m : ℤ} {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    laurentCommutationHexagonMap G R C c ∈ laurentMaslovPiece G R (m + 1) := by
  intro y k hk
  obtain ⟨x, j, hj, P, hP, rfl⟩ :=
    exists_hexagon_of_mem_support_laurentCommutationHexagonMap G R C c hk
  rw [fullCommutationHexagon_maslovDegree G C P ((mem_fullCommutationHexagons G P).mp hP)]
  exact congrArg (fun m => m + 1) (hc x j hj)

/-- The full geometric hexagon map preserves both Laurent filtration bounds. -/
theorem laurentCommutationHexagonMap_mem_bifiltrationLevel (S : Type*) [CommRing S]
    (C : GridDiagram.ColumnCommutationData G) {a b : ℝ} {c : LaurentChain S n}
    (hc : c ∈ laurentBifiltrationLevel G S a b) :
    laurentCommutationHexagonMap G S C c ∈ laurentBifiltrationLevel G S a b := by
  intro y k hk
  obtain ⟨x, j, hj, P, _, rfl⟩ :=
    exists_hexagon_of_mem_support_laurentCommutationHexagonMap G S C c hk
  have hb := hc x j hj
  have hp := fullCommutationHexagon_coordinates_le G C P j
  exact ⟨hp.1.trans hb.1, hp.2.trans hb.2⟩

/-- The full geometric hexagon map between its two Maslov homogeneous pieces. -/
noncomputable def laurentCommutationHexagonPieceMap
    (C : GridDiagram.ColumnCommutationData G) (m : ℤ) :
    laurentMaslovPiece G R m →ₗ[R] laurentMaslovPiece G R (m + 1) :=
  LinearMap.codRestrict _
    (((laurentCommutationHexagonMap G R C).restrictScalars R).comp
      (laurentMaslovPiece G R m).subtype)
    (fun c => laurentCommutationHexagonMap_mem_maslovPiece G R C c.property)

@[simp]
theorem coe_laurentCommutationHexagonPieceMap (C : GridDiagram.ColumnCommutationData G)
    (m : ℤ) (c : laurentMaslovPiece G R m) :
    (laurentCommutationHexagonPieceMap G R C m c : LaurentChain R n) =
      laurentCommutationHexagonMap G R C c := rfl

end OnLeConjecture.KnotFloer.GridFull
