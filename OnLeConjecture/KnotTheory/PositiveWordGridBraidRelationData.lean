/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationFinal

/-! # The local window sequences of the braid relation

The data of `docs/route-n/J09-word-grid-moves.tex`, appendix *The local sequences*: for each of the
seven possible sets of degenerate ranks (ranks among `i, i + 1, i + 2` that do not occur outside
the block), the initial window states of `σᵢ σᵢ₊₁ σᵢ` (suffix `A`, rank offsets `[0, 1, 0]`) and of
`σᵢ₊₁ σᵢ σᵢ₊₁` (suffix `B`, rank offsets `[1, 0, 1]`), their move sequences, the final window
states and the identification of the internal labels. The window labels are encoded as natural
numbers: `0, 1, 2` for `α_A, α_B, α_C`, `3, 4, 5` for `β_0, β_1, β_2`, `10, …, 15` for
`α'_A, α'_B, α'_C, β'_1, β'_2, β'_3`, `20 + e` for `ι_e`, `30 + e` for `θ_e`, `40 + e` and `50 + e`
for `ζ_e` and `ζ'_e`, and `100, 101, …` for the labels `ν` created by stabilizations. The flags
list, for `e = 0, 1, 2`, whether the rank `i + e` occurs outside the block.

All checks are proved by `decide` (kernel evaluation of the finite window model); no
`native_decide` is used. All results are unconditional.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.BraidWindow

/-! ### Case: no rank is degenerate -/

/-- The initial window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def init_nA : WState :=
  ⟨[(0, 20), (3, 21), (4, 0), (1, 4), (5, 22), (32, 1), (2, 3), (30, 5), (31, 2)], [30, 20, 3, 0,
    2, 21, 4, 5, 31, 1, 32, 22]⟩

/-- The move sequence of `σᵢ σᵢ₊₁ σᵢ`. -/
def moves_nA : List WMove :=
  [.r 2 21, .c 4, .dO 4 3 1 32, .r 20 3, .c 0, .dX 1 2 0 20, .r 2 4, .r 5 31, .r 21 4,
    .dX 1 2 4 20, .r 5 32, .c 3, .dO 5 4 2 31, .dX 2 3 5 22, .c 1, .sO 3 true true 100, .r 100 32]

/-- The final window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def final_nA : WState :=
  ⟨[(3, 21), (30, 22), (32, 20), (100, 3), (31, 100)], [30, 3, 20, 21, 31, 32, 100, 22]⟩

/-- The initial window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def init_nB : WState :=
  ⟨[(10, 21), (13, 22), (14, 10), (11, 20), (30, 13), (15, 11), (12, 15), (31, 14), (32, 12)], [30,
    20, 11, 21, 13, 15, 31, 10, 12, 32, 14, 22]⟩

/-- The move sequence of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def moves_nB : List WMove :=
  [.r 21 13, .c 3, .dX 4 5 11 20, .r 21 15, .r 13 15, .dX 4 5 15 20, .r 20 13, .c 1, .dO 3 2 13 30,
    .r 10 12, .r 10 32, .dO 1 0 10 14, .c 0, .c 3, .dO 3 2 12 32, .sX 1 false false 101, .r 20 101,
    .c 0, .c 2]

/-- The final window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def final_nB : WState :=
  ⟨[(101, 21), (30, 22), (32, 20), (14, 101), (31, 14)], [30, 101, 20, 21, 31, 32, 14, 22]⟩

/-- The renaming of the internal labels of the final state of `σᵢ₊₁ σᵢ σᵢ₊₁` to those of
`σᵢ σᵢ₊₁ σᵢ`. -/
def ident_n : List (ℕ × ℕ) :=
  [(101, 3), (14, 100)]

theorem initA_n : InitOK init_nA [0, 1, 0] [true, true, true] := by decide

theorem initB_n : InitOK init_nB [1, 0, 1] [true, true, true] := by decide

theorem pair_n : PairOK init_nA [0, 1, 0] init_nB [1, 0, 1] := by decide

theorem runA_n : run init_nA moves_nA = some final_nA := by decide

theorem runB_n : run init_nB moves_nB = some final_nB := by decide

theorem final_n : FinalOK final_nA final_nB ident_n := by decide

/-! ### Case: the rank `i` is degenerate -/

/-- The initial window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def init_d0A : WState :=
  ⟨[(0, 40), (3, 21), (4, 0), (1, 4), (5, 22), (32, 1), (2, 3), (40, 5), (31, 2)], [40, 3, 0, 2,
    21, 4, 5, 31, 1, 32, 22]⟩

/-- The move sequence of `σᵢ σᵢ₊₁ σᵢ`. -/
def moves_d0A : List WMove :=
  [.r 2 21, .c 4, .dO 4 3 1 32, .r 40 3, .c 0, .dX 1 2 0 40, .r 21 2, .r 4 5, .r 4 31,
    .dO 2 1 4 32, .r 2 21, .r 40 21, .c 0, .c 2, .dX 1 2 3 21, .r 5 31, .r 2 31, .r 40 31, .r 2 5,
    .dO 3 2 5 40, .r 2 32, .c 0, .dO 1 2 40 32]

/-- The final window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def final_d0A : WState :=
  ⟨[(2, 21), (32, 22), (31, 2)], [21, 31, 32, 2, 22]⟩

/-- The initial window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def init_d0B : WState :=
  ⟨[(10, 21), (13, 22), (14, 10), (11, 50), (50, 13), (15, 11), (12, 15), (31, 14), (32, 12)], [50,
    11, 21, 13, 15, 31, 10, 12, 32, 14, 22]⟩

/-- The move sequence of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def moves_d0B : List WMove :=
  [.dO 3 4 50 11, .r 15 31, .r 11 21, .dX 3 4 11 13, .r 31 15, .dX 3 4 15 13, .r 13 31, .c 3,
    .dO 5 4 12 32, .c 1, .r 10 32, .dO 1 0 10 14, .c 2, .dO 2 1 13 32]

/-- The final window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def final_d0B : WState :=
  ⟨[(14, 21), (32, 22), (31, 14)], [21, 31, 32, 14, 22]⟩

/-- The renaming of the internal labels of the final state of `σᵢ₊₁ σᵢ σᵢ₊₁` to those of
`σᵢ σᵢ₊₁ σᵢ`. -/
def ident_d0 : List (ℕ × ℕ) :=
  [(14, 2)]

theorem initA_d0 : InitOK init_d0A [0, 1, 0] [false, true, true] := by decide

theorem initB_d0 : InitOK init_d0B [1, 0, 1] [false, true, true] := by decide

theorem pair_d0 : PairOK init_d0A [0, 1, 0] init_d0B [1, 0, 1] := by decide

theorem runA_d0 : run init_d0A moves_d0A = some final_d0A := by decide

theorem runB_d0 : run init_d0B moves_d0B = some final_d0B := by decide

theorem final_d0 : FinalOK final_d0A final_d0B ident_d0 := by decide

/-! ### Case: the rank `i + 1` is degenerate -/

/-- The initial window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def init_d1A : WState :=
  ⟨[(0, 20), (3, 41), (4, 0), (1, 4), (5, 22), (32, 1), (2, 3), (30, 5), (41, 2)], [30, 20, 3, 0,
    2, 41, 4, 5, 1, 32, 22]⟩

/-- The move sequence of `σᵢ σᵢ₊₁ σᵢ`. -/
def moves_d1A : List WMove :=
  [.r 20 3, .c 4, .dO 4 3 1 32, .c 5, .dO 7 6 2 41, .c 4, .r 41 4, .dX 2 3 4 0, .r 5 32,
    .dX 4 3 5 22, .c 0, .dX 1 2 0 20, .c 1, .sX 0 false true 102, .r 102 32, .c 1]

/-- The final window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def final_d1A : WState :=
  ⟨[(102, 41), (30, 22), (3, 102), (32, 20), (41, 3)], [30, 3, 20, 41, 32, 102, 22]⟩

/-- The initial window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def init_d1B : WState :=
  ⟨[(10, 51), (13, 22), (14, 10), (11, 20), (30, 13), (15, 11), (12, 15), (51, 14), (32, 12)], [30,
    20, 11, 51, 13, 15, 10, 12, 32, 14, 22]⟩

/-- The move sequence of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def moves_d1B : List WMove :=
  [.c 6, .dO 8 7 12 32, .c 3, .dX 4 5 11 20, .r 51 13, .r 20 13, .c 2, .dO 2 1 13 30, .c 4,
    .r 51 15, .dX 3 4 15 20, .r 10 32, .c 2, .dX 3 4 14 10, .sO 3 true false 103, .r 20 103, .c 2]

/-- The final window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def final_d1B : WState :=
  ⟨[(10, 51), (30, 22), (103, 10), (32, 20), (51, 103)], [30, 103, 20, 51, 32, 10, 22]⟩

/-- The renaming of the internal labels of the final state of `σᵢ₊₁ σᵢ σᵢ₊₁` to those of
`σᵢ σᵢ₊₁ σᵢ`. -/
def ident_d1 : List (ℕ × ℕ) :=
  [(103, 3), (51, 41), (10, 102)]

theorem initA_d1 : InitOK init_d1A [0, 1, 0] [true, false, true] := by decide

theorem initB_d1 : InitOK init_d1B [1, 0, 1] [true, false, true] := by decide

theorem pair_d1 : PairOK init_d1A [0, 1, 0] init_d1B [1, 0, 1] := by decide

theorem runA_d1 : run init_d1A moves_d1A = some final_d1A := by decide

theorem runB_d1 : run init_d1B moves_d1B = some final_d1B := by decide

theorem final_d1 : FinalOK final_d1A final_d1B ident_d1 := by decide

/-! ### Case: the rank `i + 2` is degenerate -/

/-- The initial window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def init_d2A : WState :=
  ⟨[(0, 20), (3, 21), (4, 0), (1, 4), (5, 42), (42, 1), (2, 3), (30, 5), (31, 2)], [30, 20, 3, 0,
    2, 21, 4, 5, 31, 1, 42]⟩

/-- The move sequence of `σᵢ σᵢ₊₁ σᵢ`. -/
def moves_d2A : List WMove :=
  [.dX 5 4 42 1, .r 20 3, .c 0, .dX 1 2 0 20, .r 20 2, .c 4, .dX 5 6 2 3, .c 3, .r 21 4,
    .dX 1 2 4 20, .c 2, .r 31 1, .dO 2 1 1 5, .r 21 5, .dX 1 2 5 20]

/-- The final window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def final_d2A : WState :=
  ⟨[(3, 21), (30, 20), (31, 3)], [30, 3, 20, 21, 31]⟩

/-- The initial window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def init_d2B : WState :=
  ⟨[(10, 21), (13, 52), (14, 10), (11, 20), (30, 13), (15, 11), (12, 15), (31, 14), (52, 12)], [30,
    20, 11, 21, 13, 15, 31, 10, 12, 52, 14]⟩

/-- The move sequence of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def moves_d2B : List WMove :=
  [.c 3, .dX 4 5 11 20, .r 21 13, .c 6, .dO 6 5 12 52, .r 21 15, .r 13 15, .dX 4 5 15 20, .r 20 13,
    .r 31 10, .c 2, .dO 2 1 13 30, .r 21 10, .r 20 10, .r 31 52, .c 2, .dO 4 3 14 31, .r 21 52,
    .dX 2 1 52 20]

/-- The final window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def final_d2B : WState :=
  ⟨[(10, 21), (30, 20), (31, 10)], [30, 10, 20, 21, 31]⟩

/-- The renaming of the internal labels of the final state of `σᵢ₊₁ σᵢ σᵢ₊₁` to those of
`σᵢ σᵢ₊₁ σᵢ`. -/
def ident_d2 : List (ℕ × ℕ) :=
  [(10, 3)]

theorem initA_d2 : InitOK init_d2A [0, 1, 0] [true, true, false] := by decide

theorem initB_d2 : InitOK init_d2B [1, 0, 1] [true, true, false] := by decide

theorem pair_d2 : PairOK init_d2A [0, 1, 0] init_d2B [1, 0, 1] := by decide

theorem runA_d2 : run init_d2A moves_d2A = some final_d2A := by decide

theorem runB_d2 : run init_d2B moves_d2B = some final_d2B := by decide

theorem final_d2 : FinalOK final_d2A final_d2B ident_d2 := by decide

/-! ### Case: the ranks `i` and `i + 1` are degenerate -/

/-- The initial window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def init_d01A : WState :=
  ⟨[(0, 40), (3, 41), (4, 0), (1, 4), (5, 22), (32, 1), (2, 3), (40, 5), (41, 2)], [40, 3, 0, 2,
    41, 4, 5, 1, 32, 22]⟩

/-- The move sequence of `σᵢ σᵢ₊₁ σᵢ`. -/
def moves_d01A : List WMove :=
  [.c 4, .dO 4 3 1 32, .r 40 3, .r 4 5, .dO 3 2 4 32, .r 40 0, .c 0, .dX 1 2 0 40, .c 2, .c 3,
    .r 5 32, .dX 4 3 5 22, .r 2 41, .r 40 41, .r 2 32, .c 0, .dX 1 2 3 41, .c 0, .dO 1 2 40 32]

/-- The final window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def final_d01A : WState :=
  ⟨[(2, 41), (32, 22), (41, 2)], [41, 32, 2, 22]⟩

/-- The initial window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def init_d01B : WState :=
  ⟨[(10, 51), (13, 22), (14, 10), (11, 50), (50, 13), (15, 11), (12, 15), (51, 14), (32, 12)], [50,
    11, 51, 13, 15, 10, 12, 32, 14, 22]⟩

/-- The move sequence of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def moves_d01B : List WMove :=
  [.dO 3 4 50 11, .c 5, .dO 7 6 12 32, .r 10 32, .r 11 51, .dX 3 4 11 13, .r 13 15, .c 3,
    .dX 2 3 14 10, .dX 3 4 15 13, .r 13 32, .c 2, .dO 2 1 13 32]

/-- The final window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def final_d01B : WState :=
  ⟨[(10, 51), (32, 22), (51, 10)], [51, 32, 10, 22]⟩

/-- The renaming of the internal labels of the final state of `σᵢ₊₁ σᵢ σᵢ₊₁` to those of
`σᵢ σᵢ₊₁ σᵢ`. -/
def ident_d01 : List (ℕ × ℕ) :=
  [(51, 41), (10, 2)]

theorem initA_d01 : InitOK init_d01A [0, 1, 0] [false, false, true] := by decide

theorem initB_d01 : InitOK init_d01B [1, 0, 1] [false, false, true] := by decide

theorem pair_d01 : PairOK init_d01A [0, 1, 0] init_d01B [1, 0, 1] := by decide

theorem runA_d01 : run init_d01A moves_d01A = some final_d01A := by decide

theorem runB_d01 : run init_d01B moves_d01B = some final_d01B := by decide

theorem final_d01 : FinalOK final_d01A final_d01B ident_d01 := by decide

/-! ### Case: the ranks `i + 1` and `i + 2` are degenerate -/

/-- The initial window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def init_d12A : WState :=
  ⟨[(0, 20), (3, 41), (4, 0), (1, 4), (5, 42), (42, 1), (2, 3), (30, 5), (41, 2)], [30, 20, 3, 0,
    2, 41, 4, 5, 1, 42]⟩

/-- The move sequence of `σᵢ σᵢ₊₁ σᵢ`. -/
def moves_d12A : List WMove :=
  [.dX 5 4 42 1, .dO 4 3 1 5, .dO 3 2 4 5, .c 4, .dO 4 3 2 41, .r 20 3, .r 20 0, .c 0,
    .dX 1 2 0 20, .c 2, .r 41 5, .dX 1 2 5 20]

/-- The final window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def final_d12A : WState :=
  ⟨[(3, 41), (30, 20), (41, 3)], [30, 3, 20, 41]⟩

/-- The initial window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def init_d12B : WState :=
  ⟨[(10, 51), (13, 52), (14, 10), (11, 20), (30, 13), (15, 11), (12, 15), (51, 14), (52, 12)], [30,
    20, 11, 51, 13, 15, 10, 12, 52, 14]⟩

/-- The move sequence of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def moves_d12B : List WMove :=
  [.r 20 11, .c 3, .dX 4 5 11 20, .c 6, .dO 6 5 12 52, .r 51 13, .r 20 13, .r 15 10, .dO 5 4 15 52,
    .c 2, .dO 2 1 13 30, .r 51 10, .r 20 10, .r 51 52, .c 3, .dO 3 2 14 51, .c 2, .dX 2 1 52 20]

/-- The final window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def final_d12B : WState :=
  ⟨[(10, 51), (30, 20), (51, 10)], [30, 10, 20, 51]⟩

/-- The renaming of the internal labels of the final state of `σᵢ₊₁ σᵢ σᵢ₊₁` to those of
`σᵢ σᵢ₊₁ σᵢ`. -/
def ident_d12 : List (ℕ × ℕ) :=
  [(10, 3), (51, 41)]

theorem initA_d12 : InitOK init_d12A [0, 1, 0] [true, false, false] := by decide

theorem initB_d12 : InitOK init_d12B [1, 0, 1] [true, false, false] := by decide

theorem pair_d12 : PairOK init_d12A [0, 1, 0] init_d12B [1, 0, 1] := by decide

theorem runA_d12 : run init_d12A moves_d12A = some final_d12A := by decide

theorem runB_d12 : run init_d12B moves_d12B = some final_d12B := by decide

theorem final_d12 : FinalOK final_d12A final_d12B ident_d12 := by decide

/-! ### Case: all three ranks are degenerate -/

/-- The initial window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def init_d012A : WState :=
  ⟨[(0, 40), (3, 41), (4, 0), (1, 4), (5, 42), (42, 1), (2, 3), (40, 5), (41, 2)], [40, 3, 0, 2,
    41, 4, 5, 1, 42]⟩

/-- The move sequence of `σᵢ σᵢ₊₁ σᵢ`. -/
def moves_d012A : List WMove :=
  [.dX 5 4 42 1, .dO 4 3 1 5, .dO 3 2 4 5, .c 4, .dO 4 3 2 41, .c 3, .r 41 5, .dX 2 3 5 0]

/-- The final window state of `σᵢ σᵢ₊₁ σᵢ`. -/
def final_d012A : WState :=
  ⟨[(0, 40), (3, 41), (40, 0), (41, 3)], [40, 3, 0, 41]⟩

/-- The initial window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def init_d012B : WState :=
  ⟨[(10, 51), (13, 52), (14, 10), (11, 50), (50, 13), (15, 11), (12, 15), (51, 14), (52, 12)], [50,
    11, 51, 13, 15, 10, 12, 52, 14]⟩

/-- The move sequence of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def moves_d012B : List WMove :=
  [.dO 3 4 50 11, .r 10 12, .dO 5 4 15 12, .r 12 10, .c 5, .dO 5 4 12 52, .r 51 13, .dX 3 4 11 13,
    .r 13 51, .c 3, .r 52 14, .dX 2 3 14 10]

/-- The final window state of `σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def final_d012B : WState :=
  ⟨[(10, 51), (13, 52), (51, 10), (52, 13)], [51, 13, 10, 52]⟩

/-- The renaming of the internal labels of the final state of `σᵢ₊₁ σᵢ σᵢ₊₁` to those of
`σᵢ σᵢ₊₁ σᵢ`. -/
def ident_d012 : List (ℕ × ℕ) :=
  [(51, 40), (13, 3), (10, 0), (52, 41)]

theorem initA_d012 : InitOK init_d012A [0, 1, 0] [false, false, false] := by decide

theorem initB_d012 : InitOK init_d012B [1, 0, 1] [false, false, false] := by decide

theorem pair_d012 : PairOK init_d012A [0, 1, 0] init_d012B [1, 0, 1] := by decide

theorem runA_d012 : run init_d012A moves_d012A = some final_d012A := by decide

theorem runB_d012 : run init_d012B moves_d012B = some final_d012B := by decide

theorem final_d012 : FinalOK final_d012A final_d012B ident_d012 := by decide

end OnLeConjecture.KnotTheory.BraidWindow
