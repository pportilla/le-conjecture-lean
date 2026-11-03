/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesFinal
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationData

/-! # Signed checks of the braid relation windows

The window sequences of `PositiveWordGridBraidRelationData` (seven cases of degenerate ranks),
checked against the signed conventions: `SignedGrid.InitOKS` for the blocks
`σᵢ σᵢ₊₁ σᵢ` (rank offsets `[0, 1, 0]`) and `σᵢ₊₁ σᵢ σᵢ₊₁` (rank offsets `[1, 0, 1]`) of
positive letters, and `SignedGrid.PairOKS`. All checks are proved by `decide`; no
`native_decide` is used. All results are unconditional.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.SignedGrid

open BraidWindow

theorem sinitA_n : InitOKS 3 init_nA [0, 1, 0] [true, true, true] [true, true, true] := by decide

theorem sinitB_n : InitOKS 3 init_nB [1, 0, 1] [true, true, true] [true, true, true] := by decide

theorem spair_n :
    PairOKS init_nA [0, 1, 0] [true, true, true] init_nB [1, 0, 1] [true, true, true] := by
  decide

theorem sinitA_d0 : InitOKS 3 init_d0A [0, 1, 0] [true, true, true] [false, true, true] := by decide

theorem sinitB_d0 : InitOKS 3 init_d0B [1, 0, 1] [true, true, true] [false, true, true] := by decide

theorem spair_d0 :
    PairOKS init_d0A [0, 1, 0] [true, true, true] init_d0B [1, 0, 1] [true, true, true] := by
  decide

theorem sinitA_d1 : InitOKS 3 init_d1A [0, 1, 0] [true, true, true] [true, false, true] := by decide

theorem sinitB_d1 : InitOKS 3 init_d1B [1, 0, 1] [true, true, true] [true, false, true] := by decide

theorem spair_d1 :
    PairOKS init_d1A [0, 1, 0] [true, true, true] init_d1B [1, 0, 1] [true, true, true] := by
  decide

theorem sinitA_d2 : InitOKS 3 init_d2A [0, 1, 0] [true, true, true] [true, true, false] := by decide

theorem sinitB_d2 : InitOKS 3 init_d2B [1, 0, 1] [true, true, true] [true, true, false] := by decide

theorem spair_d2 :
    PairOKS init_d2A [0, 1, 0] [true, true, true] init_d2B [1, 0, 1] [true, true, true] := by
  decide

theorem sinitA_d01 :
    InitOKS 3 init_d01A [0, 1, 0] [true, true, true] [false, false, true] := by decide

theorem sinitB_d01 :
    InitOKS 3 init_d01B [1, 0, 1] [true, true, true] [false, false, true] := by decide

theorem spair_d01 :
    PairOKS init_d01A [0, 1, 0] [true, true, true] init_d01B [1, 0, 1] [true, true, true] := by
  decide

theorem sinitA_d12 :
    InitOKS 3 init_d12A [0, 1, 0] [true, true, true] [true, false, false] := by decide

theorem sinitB_d12 :
    InitOKS 3 init_d12B [1, 0, 1] [true, true, true] [true, false, false] := by decide

theorem spair_d12 :
    PairOKS init_d12A [0, 1, 0] [true, true, true] init_d12B [1, 0, 1] [true, true, true] := by
  decide

theorem sinitA_d012 :
    InitOKS 3 init_d012A [0, 1, 0] [true, true, true] [false, false, false] := by decide

theorem sinitB_d012 :
    InitOKS 3 init_d012B [1, 0, 1] [true, true, true] [false, false, false] := by decide

theorem spair_d012 :
    PairOKS init_d012A [0, 1, 0] [true, true, true] init_d012B [1, 0, 1] [true, true, true] := by
  decide

end OnLeConjecture.KnotTheory.SignedGrid
