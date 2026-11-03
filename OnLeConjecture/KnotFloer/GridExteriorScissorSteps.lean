/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorReduction
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Commutation.Move

/-!
# The combinatorial route of the scissor and cleanup construction

This file states `ScissorRouteStatement`, the combinatorial part of `ScissorCleanupStatement`
(`GridExteriorReduction`), in the form consumed by the algebraic assembly of Section 12 of the
written proof of Statement E (`statement_E_complete_proof.tex`, "Construction of the complete map
and proof of Statement E"). The statement is not proved here.

For a normalized factorization `F` in which strand `0` lies in every factor cycle and the factor
permutations are transitive, `ScissorRouteStatement` asks for prepared factor grids `D_j`, related
by grid moves to the selected word grids of the local words, and, for every signed word grid `H`
of the padded product, the following data.

* A *scissor phase* `ScissorPhase H K k E` from `H` to a grid `K` of the same size. It is a finite
  sequence of adjacent-row `X` switches, adjacent-row `O` switches, row commutations and cyclic row
  rotations. None of these steps moves a marking to another column. The natural number `k` counts
  the `X` switches, and its integer cast must equal `F.scissorShiftCount`. The list `E` records,
  for every `O` switch, the two columns of the exchanged `O` markings. These are the star
  scissors of Section 9: the
  `X` switches are the scissor `X` identities and the `O` switches are the selected scissor `O`
  maps, each followed by its row commutation.
* The *spanning tree condition* `SpanningTreeEdges K E`: the components of `K`, that is, the
  cycles of the permutation `c ↦ X⁻¹(O(c))` of the columns (`gridComponentPerm`), together with
  the edges `E`, form a tree. This is the incidence forest of Section 9 with its root, and it
  makes the reduced incidence determinant equal to one for every choice of root.
* Grid moves from `K` to a grid `K'`, which comprise the seam preparation, the cyclic exposures,
  the marked inverse cancellations of Section 8, the removal of the trailing simple factors and
  the positioning of the auxiliary blocks.
* A *four-mark tower* `FourMarkTower (iteratedSeamGrid D) E.length K' e`: the grid `K'` is
  obtained from the iterated seam of the `D_j` by inserting `E.length` four-mark unknot blocks.
  Each block is inserted immediately to the south-west of the `X` marking of a column of the
  iterated seam (`IsFourMarkInsertion`). The map `e` records the columns of the iterated seam
  inside `K'`.

The algebraic assembly composes the scissor `X` identities (degree zero, second shift `1/2`), the
selected `O` switch maps (degree `-1`, second shift `-1/2`), the colour-natural grid move maps,
the four-mark collapses of Proposition `fourMarkBlockCollapse` and the auxiliary contractions of
Lemma `nativeAuxiliaryContraction` (degree `+1`, second shift `1/2`). Its total second shift is
`F.scissorShiftCount / 2`, and the determinant formula of Section 4 gives the canonical-class
identity.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

variable {n : ℕ}

/-! ### Components and spanning trees -/

/-- The permutation of the columns whose cycles are the components of a grid diagram: the column
`c` goes to the column of the `X` marking in the row of the `O` marking of column `c`. -/
def gridComponentPerm (G : GridDiagram n) : Equiv.Perm (Fin n) :=
  G.O.toPerm.trans G.X.toPerm.symm

/-- The edges `E` join the components of `G` into a tree: together with the components they
connect all columns, and there is one edge fewer than components. -/
def SpanningTreeEdges (G : GridDiagram n) (E : List (Fin n × Fin n)) : Prop :=
  (∀ a b : Fin n,
      Relation.EqvGen (fun a b => (gridComponentPerm G).SameCycle a b ∨ (a, b) ∈ E) a b) ∧
    E.length + 1 = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (gridComponentPerm G)))

/-! ### The scissor phase -/

/-- The scissor phase on grids of a fixed size. The natural number counts the adjacent-row `X`
switches, and the list records the columns of the two `O` markings exchanged by each adjacent-row
`O` switch. Row commutations and cyclic row rotations are free. -/
inductive ScissorPhase : GridDiagram n → GridDiagram n → ℕ → List (Fin n × Fin n) → Prop
  | refl (G : GridDiagram n) : ScissorPhase G G 0 []
  | xSwitch {G G₁ G₂ : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)}
      (h : ScissorPhase G G₁ k E) (r : Fin n) (hr : r ≠ finRotate n r)
      (hO : G₂.O = G₁.O) (hX : G₂.X = G₁.X.swapRows r (finRotate n r)) :
      ScissorPhase G G₂ (k + 1) E
  | oSwitch {G G₁ G₂ : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)}
      (h : ScissorPhase G G₁ k E) (r : Fin n) (hr : r ≠ finRotate n r)
      (hO : G₂.O = G₁.O.swapRows r (finRotate n r)) (hX : G₂.X = G₁.X) :
      ScissorPhase G G₂ k (E ++ [(G₁.O.transpose r, G₁.O.transpose (finRotate n r))])
  | rowCommutation {G G₁ G₂ : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)}
      (h : ScissorPhase G G₁ k E) (hc : GridDiagram.IsRowCommutation G₁ G₂) :
      ScissorPhase G G₂ k E
  | cyclicRows {G G₁ G₂ : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)}
      (h : ScissorPhase G G₁ k E)
      (hc : G₂ = G₁.relabelRows (finRotate n) ∨ G₁ = G₂.relabelRows (finRotate n)) :
      ScissorPhase G G₂ k E

/-! ### Four-mark blocks -/

/-- `G'` is obtained from `G` by inserting a four-mark unknot block immediately to the south-west
of the `X` marking of column `c`. With `q = X_G(c)`, two columns are inserted before column `c` and
two rows before row `q`. The block occupies the columns `c, c + 1` and the rows `q, q + 1`, with
`O` markings at `(c, q)` and `(c + 1, q + 1)` and `X` markings at `(c, q + 1)` and `(c + 1, q)`. All
other markings are the embedded markings of `G`; in particular the `X` marking of the old column
`c` lies at `(c + 2, q + 2)`, diagonally adjacent to the block. -/
def IsFourMarkInsertion (G : GridDiagram n) (c : Fin n) (G' : GridDiagram (n + 2)) : Prop :=
  G'.O = (G.O.insertPoint c.castSucc (G.X c).castSucc).insertPoint c.castSucc.succ
      (G.X c).castSucc.succ ∧
    G'.X = ((G.X.insertPoint c.castSucc (G.X c).castSucc).insertPoint c.castSucc.succ
      (G.X c).castSucc.succ).swapRows (G.X c).castSucc.castSucc (G.X c).castSucc.succ

/-- A tower of four-mark insertions over a base grid `G₀`. The natural number counts the inserted
blocks, and the map records the columns of `G₀` inside the current grid. Every block is inserted
next to the `X` marking of a column of `G₀`. -/
inductive FourMarkTower {n₀ : ℕ} (G₀ : GridDiagram n₀) :
    ℕ → {m : ℕ} → GridDiagram m → (Fin n₀ → Fin m) → Prop
  | base : FourMarkTower G₀ 0 G₀ id
  | insert {k m : ℕ} {G : GridDiagram m} {e : Fin n₀ → Fin m}
      (h : FourMarkTower G₀ k G e) (b : Fin n₀) {G' : GridDiagram (m + 2)}
      (hG' : IsFourMarkInsertion G (e b) G') :
      FourMarkTower G₀ (k + 1) G' fun b' =>
        (e b).castSucc.succ.succAbove ((e b).castSucc.succAbove (e b'))

/-! ### The combinatorial route -/

/-- **The combinatorial route of the scissor and cleanup construction.** For a normalized
factorization in which strand `0` lies in every factor cycle and the factor permutations are
transitive, there are prepared factor grids related by grid moves to the selected word grids of the
local words, and every signed word grid of the padded product reaches a four-mark tower over their
iterated seam by a scissor phase with `F.scissorShiftCount` adjacent `X` switches whose `O`
switches form a spanning tree of components, followed by grid moves. -/
def ScissorRouteStatement : Prop :=
  ∀ (S N B : ℕ) (hS : 2 ≤ S) (hN : 0 < N) (F : NormalizedFactorization S N B),
    F.StrandZeroInEveryFactor (by omega) → F.Transitive →
    ∃ (sizes : Fin N → ℕ) (D : ∀ j, GridDiagram (sizes j)) (hprep : SeamPrepared D)
      (_ : ∀ j, 2 ≤ sizes j),
      (∀ j, (wordGrid (F.word j)).MovesTo (D j)) ∧
      ∀ H : GridDiagram (F.product.length * 3), IsSignedWordGrid F.product H →
        ∃ (K : GridDiagram (F.product.length * 3))
          (E : List (Fin (F.product.length * 3) × Fin (F.product.length * 3)))
          (k m : ℕ) (K' : GridDiagram m) (e : Fin _ → Fin m),
          (k : ℤ) = F.scissorShiftCount ∧ ScissorPhase H K k E ∧ SpanningTreeEdges K E ∧
            K.MovesTo K' ∧ FourMarkTower (iteratedSeamGrid D hprep) E.length K' e

end OnLeConjecture.KnotFloer.GridFull
