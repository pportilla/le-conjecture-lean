/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesLabeled

/-! # The local window model for the braid relation

`docs/route-n/J09-word-grid-moves.tex`, Definition *window state* and the local moves (c), (r),
(d), (s). A window state (`BraidWindow.WState`) is a list of window columns, each given by its
`O`-label and its `X`-label, and a list of row labels from bottom to top. Labels are natural
numbers; the labels `20, 21, 22` (rows `ι r`, of type in) and `30, 31, 32` (rows `θ r`, of type
out) are connecting, all other labels are internal. The function `BraidWindow.step` performs one
local move and checks its hypotheses; `BraidWindow.run` performs a list of moves. In the segment
tests the outside marking of a connecting row is placed at the position `k` right of the `k`
window columns. Everything in this module is computable, and the move sequences of the appendix
are checked by `decide` in `PositiveWordGridBraidRelationData.lean`.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.BraidWindow

/-- The connecting labels. -/
def isConn (n : ℕ) : Bool := (20 ≤ n && n ≤ 22) || (30 ≤ n && n ≤ 32)

/-- A window state: window columns `(O-label, X-label)` from left to right, and row labels from
bottom to top. -/
structure WState where
  cols : List (ℕ × ℕ)
  rows : List ℕ
deriving DecidableEq, Repr

namespace WState

/-- The window position of the column with `O`-label `z`, or the number of columns. -/
def pO (S : WState) (z : ℕ) : ℕ := S.cols.findIdx fun c => c.1 == z

/-- The window position of the column with `X`-label `z`, or the number of columns. -/
def pX (S : WState) (z : ℕ) : ℕ := S.cols.findIdx fun c => c.2 == z

/-- The position of a row label. -/
def ri (S : WState) (z : ℕ) : ℕ := S.rows.idxOf z

/-- A label is internal in `S` if it is not connecting and it is an `O`-label and an `X`-label of
window columns. -/
def isInt (S : WState) (z : ℕ) : Bool :=
  !isConn z && S.cols.any (fun c => c.1 == z) && S.cols.any (fun c => c.2 == z)

/-- The column at a position, with a default. -/
def col (S : WState) (t : ℕ) : ℕ × ℕ := S.cols.getD t (0, 0)

end WState

/-- Exchange of the entries at the positions `t` and `t + 1`. -/
def swapAt {α : Type*} : List α → ℕ → List α
  | a :: b :: l, 0 => b :: a :: l
  | a :: l, t + 1 => a :: swapAt l t
  | l, _ => l

/-- The local moves. `sO s right above ν` splits the `O`-marking of column `s`, with the new
column right (`right = true`) or left of column `s`, and the new row `ν` above (`above = true`)
or below the split row. -/
inductive WMove
  | c (t : ℕ)
  | r (x y : ℕ)
  | dX (p s x y : ℕ)
  | dO (p s x y : ℕ)
  | sO (s : ℕ) (right above : Bool) (ν : ℕ)
  | sX (s : ℕ) (right above : Bool) (ν : ℕ)
deriving DecidableEq, Repr

/-- Boolean form of `NonintN`. -/
def nonintB (a b c d : ℕ) : Bool := decide (NonintN a b c d)

/-- The number of entries equal to `k`. -/
def countEq (k : ℕ) (l : List ℕ) : ℕ := (l.filter (· == k)).length

/-- Two labels are consecutive rows, the first below the second. -/
def adjRows (S : WState) (x y : ℕ) : Bool := S.rows.contains x && S.rows[S.ri x + 1]? == some y

/-- One local move, with its hypotheses checked. -/
def step (S : WState) : WMove → Option WState
  | .c t =>
    if t + 1 < S.cols.length &&
        nonintB (S.ri (S.col t).1) (S.ri (S.col t).2) (S.ri (S.col (t + 1)).1)
          (S.ri (S.col (t + 1)).2) then
      some ⟨swapAt S.cols t, S.rows⟩
    else none
  | .r x y =>
    if adjRows S x y && (S.isInt x || S.isInt y) &&
        countEq S.cols.length [S.pO x, S.pX x, S.pO y, S.pX y] ≤ 1 &&
        nonintB (S.pO x) (S.pX x) (S.pO y) (S.pX y) then
      some ⟨S.cols, swapAt S.rows (S.ri x)⟩
    else none
  | .dX p s x y =>
    if (p + 1 == s || s + 1 == p) && p < S.cols.length && s < S.cols.length &&
        S.col p == (x, y) && (S.col s).2 == x && (S.col s).1 != y && !isConn x &&
        (adjRows S x y || adjRows S y x) then
      some ⟨(S.cols.set s ((S.col s).1, y)).eraseIdx p, S.rows.erase x⟩
    else none
  | .dO p s x y =>
    if (p + 1 == s || s + 1 == p) && p < S.cols.length && s < S.cols.length &&
        S.col p == (y, x) && (S.col s).1 == x && (S.col s).2 != y && !isConn x &&
        (adjRows S x y || adjRows S y x) then
      some ⟨(S.cols.set s (y, (S.col s).2)).eraseIdx p, S.rows.erase x⟩
    else none
  | .sO s right above ν =>
    if s < S.cols.length && !S.rows.contains ν && !isConn ν then
      some ⟨(S.cols.set s (ν, (S.col s).2)).insertIdx (if right then s + 1 else s) ((S.col s).1, ν),
        S.rows.insertIdx (if above then S.ri (S.col s).1 + 1 else S.ri (S.col s).1) ν⟩
    else none
  | .sX s right above ν =>
    if s < S.cols.length && !S.rows.contains ν && !isConn ν then
      some ⟨(S.cols.set s ((S.col s).1, ν)).insertIdx (if right then s + 1 else s) (ν, (S.col s).2),
        S.rows.insertIdx (if above then S.ri (S.col s).2 + 1 else S.ri (S.col s).2) ν⟩
    else none

/-- A list of local moves. -/
def run (S : WState) : List WMove → Option WState
  | [] => some S
  | m :: ms => (step S m).bind fun S' => run S' ms

end OnLeConjecture.KnotTheory.BraidWindow
