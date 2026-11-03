/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov
public import OnLeConjecture.KnotFloer.GridFullLaurentBifiltration
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Commutation.Grading.Basic

/-!
# The full Laurent pentagon map

Both orientations of empty commutation pentagons are counted, including
pentagons containing X markings. Each pentagon is weighted by `T (#O)`.
For validated column commutation data, this map preserves Maslov degree
and both filtration coordinates. The Alexander-coordinate decrease of an
individual term is exactly its number of X markings.

The polygon shapes and state grading formulas are the checked TauCeti
commutation geometry at commit `eb4dd2412a1cd62f73128361bfd3cb422df32e37`.
This file proves grading and filtration statements for the explicit map.
The full chain-map equation and inverse hexagon homotopy remain separate
polygon-composition assertions.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-- The two geometric orientations of a commutation pentagon. -/
abbrev CommutationPentagon (C : GridDiagram.ColumnTurn n) (x y : GridState n) :=
  GridPentagonBetween C.column C.turnRow x y ⊕
    GridInitialPentagonBetween C.column C.turnRow x y

namespace CommutationPentagon

variable {C : GridDiagram.ColumnTurn n} {x y : GridState n}

/-- Emptiness concerns interior state points and imposes no marking avoidance. -/
def IsEmpty : CommutationPentagon C x y → Prop
  | .inl P => P.IsEmpty
  | .inr P => P.IsEmpty

/-- The marking squares inside the pentagon. -/
noncomputable def coveredSquares : CommutationPentagon C x y → Finset (Fin n × Fin n)
  | .inl P => P.coveredSquares
  | .inr P => P.coveredSquares

/-- The number of O markings inside the pentagon. -/
noncomputable def oCount (G : GridDiagram n) (P : CommutationPentagon C x y) : ℕ :=
  (G.OSet ∩ P.coveredSquares).card

/-- The number of X markings inside the pentagon. -/
noncomputable def xCount (G : GridDiagram n) (P : CommutationPentagon C x y) : ℕ :=
  (G.XSet ∩ P.coveredSquares).card

end CommutationPentagon

/-- The finite set of all empty pentagons at the specified turn. -/
noncomputable def fullCommutationPentagons (C : GridDiagram.ColumnTurn n) (x y : GridState n) :
    Finset (CommutationPentagon C x y) := by
  classical
  exact Finset.univ.filter CommutationPentagon.IsEmpty

@[simp]
theorem mem_fullCommutationPentagons {C : GridDiagram.ColumnTurn n} {x y : GridState n}
    (P : CommutationPentagon C x y) :
    P ∈ fullCommutationPentagons C x y ↔ P.IsEmpty := by
  classical
  simp [fullCommutationPentagons]

variable (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The full Laurent pentagon coefficient, with both orientations and every X count. -/
noncomputable def laurentCommutationCoefficient (C : GridDiagram.ColumnTurn n)
    (x y : GridState n) : LaurentPolynomial R :=
  ∑ P ∈ fullCommutationPentagons C x y, LaurentPolynomial.T (P.oCount G : ℤ)

/-- The full pentagon map on a grid state. -/
noncomputable def laurentCommutationOnGenerator (C : GridDiagram.ColumnTurn n)
    (x : GridState n) : LaurentChain R n :=
  ∑ y, Finsupp.single y (laurentCommutationCoefficient G R C x y)

@[simp]
theorem laurentCommutationOnGenerator_apply (C : GridDiagram.ColumnTurn n)
    (x y : GridState n) :
    laurentCommutationOnGenerator G R C x y = laurentCommutationCoefficient G R C x y := by
  classical
  rw [laurentCommutationOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The Laurent-linear map counting every empty commutation pentagon. -/
noncomputable def laurentCommutationMap (C : GridDiagram.ColumnTurn n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  Finsupp.lsum (LaurentPolynomial R) fun x : GridState n =>
    (LinearMap.id : LaurentPolynomial R →ₗ[LaurentPolynomial R]
      LaurentPolynomial R).smulRight (laurentCommutationOnGenerator G R C x)

@[simp]
theorem laurentCommutationMap_single (C : GridDiagram.ColumnTurn n) (x : GridState n) :
    laurentCommutationMap G R C (Finsupp.single x 1) =
      laurentCommutationOnGenerator G R C x := by
  rw [laurentCommutationMap, Finsupp.lsum_single]
  simp

theorem laurentCommutationMap_apply_apply (C : GridDiagram.ColumnTurn n)
    (c : LaurentChain R n) (y : GridState n) :
    laurentCommutationMap G R C c y =
      c.sum fun x a => a * laurentCommutationCoefficient G R C x y := by
  simp [laurentCommutationMap, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    LinearMap.smulRight_apply]

/-- The full pentagon map acts on a Laurent monomial by the geometric polygon sum. -/
theorem laurentCommutationMap_monomialGenerator (C : GridDiagram.ColumnTurn n)
    (k : ℤ) (x : GridState n) :
    laurentCommutationMap G R C (laurentMonomialGenerator R k x) =
      ∑ y, ∑ P ∈ fullCommutationPentagons C x y,
        laurentMonomialGenerator R (k + (P.oCount G : ℤ)) y := by
  classical
  rw [laurentMonomialGenerator, ← Finsupp.smul_single_one, map_smul,
    laurentCommutationMap_single]
  simp only [laurentCommutationOnGenerator, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul,
    laurentCommutationCoefficient, Finsupp.single_finsetSum,
    ← LaurentPolynomial.T_add, laurentMonomialGenerator]

/-- Each nonzero coefficient of the map is contributed by an actual empty pentagon. -/
theorem exists_pentagon_of_mem_support_laurentCommutationMap (C : GridDiagram.ColumnTurn n)
    (c : LaurentChain R n) {y : GridState n} {k : ℤ}
    (hk : k ∈ (laurentCommutationMap G R C c y).coeff.support) :
    ∃ x : GridState n, ∃ j ∈ (c x).coeff.support,
      ∃ P ∈ fullCommutationPentagons C x y, k = j + (P.oCount G : ℤ) := by
  classical
  rw [laurentCommutationMap_apply_apply, Finsupp.sum, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  rw [laurentCommutationCoefficient, AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨P, hP, hdP⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hd)
  change d ∈ (Finsupp.single (P.oCount G : ℤ) (1 : R)).support at hdP
  have hd := Finset.mem_singleton.mp (Finsupp.support_single_subset hdP)
  exact ⟨x, j, hj, P, hP, by rw [hd]⟩

omit R in
/-- The validated turn does not lie inside the reversed arc of its X markings. -/
theorem commutationTurn_notMem_XArc (C : GridDiagram.ColumnCommutationData G) :
    C.turnRow ∉ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) := fun h =>
  Grid.notMem_cIoo_of_mem_insert_cIco C.X_column_below C.X_next_above
    (Grid.mem_cIoo_cyclic_left h)

omit R in
/-- Both Maslov gradings change by twice the corresponding marking count. -/
theorem fullCommutationPentagon_maslov_changes (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : CommutationPentagon C x y) (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovOℤ y =
        G.maslovOℤ x + 2 * (P.oCount G : ℤ) ∧
      (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y =
        G.maslovXℤ x + 2 * (P.xCount G : ℤ) := by
  rcases P with P | P
  · have hO := G.maslovOℤ_swapColumns_of_isEmpty C hP
    have hX := G.maslovXℤ_swapColumns_of_isEmpty C hP
    rw [G.card_pentagonOColumns] at hO
    rw [if_neg (commutationTurn_notMem_XArc G C), mul_zero, sub_zero] at hX
    simp only [GridDiagram.ColumnCommutationData.commutationBidegree_eq_zero,
      Prod.fst_zero, add_zero] at hO
    exact And.intro hO hX
  · have hO := G.maslovOℤ_swapColumns_initialPentagon_of_isEmpty C hP
    have hX := G.maslovXℤ_swapColumns_initialPentagon_of_isEmpty C hP
    rw [G.card_OColumnsOfSquares] at hO
    rw [if_neg (commutationTurn_notMem_XArc G C), mul_zero, sub_zero] at hX
    simp only [GridDiagram.ColumnCommutationData.commutationBidegree_eq_zero,
      Prod.fst_zero, add_zero] at hO
    exact And.intro hO hX

omit R in
/-- Every weighted full pentagon term has the same Maslov degree as its input. -/
theorem fullCommutationPentagon_maslovDegree (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : CommutationPentagon C x y) (hP : P.IsEmpty) (k : ℤ) :
    laurentMaslovDegree (G.swapColumns C.column (finRotate n C.column))
        (k + (P.oCount G : ℤ)) y = laurentMaslovDegree G k x := by
  have hO := (fullCommutationPentagon_maslov_changes G C P hP).1
  simp only [laurentMaslovDegree, hO]
  ring

/-- The full pentagon map preserves the actual homogeneous Maslov pieces. -/
theorem laurentCommutationMap_mem_maslovPiece (C : GridDiagram.ColumnCommutationData G)
    {m : ℤ} {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    laurentCommutationMap G R C c ∈
      laurentMaslovPiece (G.swapColumns C.column (finRotate n C.column)) R m := by
  intro y k hk
  obtain ⟨x, j, hj, P, hP, rfl⟩ :=
    exists_pentagon_of_mem_support_laurentCommutationMap G R C c hk
  rw [fullCommutationPentagon_maslovDegree G C P ((mem_fullCommutationPentagons P).mp hP)]
  exact hc x j hj

omit R in
/-- The Alexander-coordinate drop of a weighted full pentagon is its X count. -/
theorem fullCommutationPentagon_alexander_change (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : CommutationPentagon C x y) (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).alexander y - (P.oCount G : ℚ) =
      G.alexander x - (P.xCount G : ℚ) := by
  obtain ⟨hO, hX⟩ := fullCommutationPentagon_maslov_changes G C P hP
  have hOq : ((G.swapColumns C.column (finRotate n C.column)).maslovOℤ y : ℚ) =
      (G.maslovOℤ x : ℚ) + 2 * (P.oCount G : ℚ) := by exact_mod_cast hO
  have hXq : ((G.swapColumns C.column (finRotate n C.column)).maslovXℤ y : ℚ) =
      (G.maslovXℤ x : ℚ) + 2 * (P.xCount G : ℚ) := by exact_mod_cast hX
  simp only [GridDiagram.alexander_def, GridDiagram.maslovO_eq_intCast,
    GridDiagram.maslovX_eq_intCast]
  linarith

omit R in
/-- Every full pentagon term decreases the two filtration coordinates by its O and X counts. -/
theorem fullCommutationPentagon_coordinates_le (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (P : CommutationPentagon C x y) (hP : P.IsEmpty) (k : ℤ) :
    -((k + (P.oCount G : ℤ) : ℤ) : ℝ) ≤ -(k : ℝ) ∧
      ((G.swapColumns C.column (finRotate n C.column)).alexander y : ℝ) -
          (k + (P.oCount G : ℤ) : ℤ) ≤ (G.alexander x : ℝ) - k := by
  have h := fullCommutationPentagon_alexander_change G C P hP
  have hreal : ((G.swapColumns C.column (finRotate n C.column)).alexander y : ℝ) -
      (P.oCount G : ℝ) = (G.alexander x : ℝ) - (P.xCount G : ℝ) := by exact_mod_cast h
  have hO := Nat.cast_nonneg (α := ℝ) (P.oCount G)
  have hX := Nat.cast_nonneg (α := ℝ) (P.xCount G)
  push_cast
  constructor <;> linarith

/-- The full pentagon map preserves both filtration bounds, including negative Laurent powers. -/
theorem laurentCommutationMap_mem_bifiltrationLevel (S : Type*) [CommRing S]
    (C : GridDiagram.ColumnCommutationData G) {a b : ℝ} {c : LaurentChain S n}
    (hc : c ∈ laurentBifiltrationLevel G S a b) :
    laurentCommutationMap G S C c ∈
      laurentBifiltrationLevel (G.swapColumns C.column (finRotate n C.column)) S a b := by
  intro y k hk
  obtain ⟨x, j, hj, P, hP, rfl⟩ :=
    exists_pentagon_of_mem_support_laurentCommutationMap G S C c hk
  have hb := hc x j hj
  have hp := fullCommutationPentagon_coordinates_le G C P
    ((mem_fullCommutationPentagons P).mp hP) j
  exact ⟨hp.1.trans hb.1, hp.2.trans hb.2⟩

end OnLeConjecture.KnotFloer.GridFull
