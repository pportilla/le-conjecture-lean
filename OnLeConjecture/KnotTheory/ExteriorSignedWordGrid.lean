/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ExteriorSignedBraid
public import OnLeConjecture.KnotTheory.PositiveWordNormalForms
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Move.Basic

/-!
# Signed word grids and normalized factorizations

This file fixes the combinatorial objects in which the remaining steps of the written proof of
Statement E (`statement_E_complete_proof.tex`, Sections 7 and 9 to 12) are stated.

**Signed word grids.** A signed word of length `L` has `3 L` corners `(h, c)`, the corner `(h, c)`
lying in column `3 h + c`. The letter `σ_r^{±1}` of position `h` has the three-column gadget of the
written proof (Section 2): doubling all heights, its outgoing (O) heights are `(2r+1, 2r, 2r+2)`
for `+σ_r` and `(2r+1, 2r+2, 2r)` for `σ_r⁻¹`, and its incoming (X) heights are
`(2r, 2r+2, 2r+1)` for `+σ_r` and `(2r+2, 2r, 2r+1)` for `σ_r⁻¹`. Every horizontal arc joins an
outgoing corner to the nearest incoming corner of the same height to its right, cyclically. A grid
diagram `G` of size `3 L` is a signed word grid of `w` (`IsSignedWordGrid w G`) when its O rows are
ordered by height and the X marking of each column lies in the row of the arc arriving there. For
positive words this is the convention of `IsAdmissibleWordGrid`.

**Normalized factorizations.** `NormalizedFactorization S N B` records `N` positive local words
`β_j` on `a_j ≤ S` strands and `N + B` conjugators. Its factors are
`q_l = (p γ_l) η_l (p γ_l)⁻¹`, where `p = ρ ρ⁻¹` is the padding word with
`ρ = σ_0 ⋯ σ_{S-2}`, the core `η_l` is `β_l` on the first `a_l` strands for `l < N`, and `η_l = σ_0`
for `l ≥ N`.

**The statement of Section 7.** `SignedWordGridRelationsStatement`: for a positive word `w` and a
signed word `v` that both use every generator, a conjugacy derivation from `w` to `v` gives a
signed word grid of `v` related to `wordGrid w` by grid moves.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory

open TauCeti

variable {m : ℕ}

/-! ### Signed word grids -/

/-- Twice the height of the outgoing (O) corner `c` of a letter. -/
def signedOHeight2 (a : Fin (m - 1) × ℤˣ) (c : Fin 3) : ℕ :=
  if a.2 = 1 then ![2 * a.1.val + 1, 2 * a.1.val, 2 * a.1.val + 2] c
  else ![2 * a.1.val + 1, 2 * a.1.val + 2, 2 * a.1.val] c

/-- Twice the height of the incoming (X) corner `c` of a letter. -/
def signedXHeight2 (a : Fin (m - 1) × ℤˣ) (c : Fin 3) : ℕ :=
  if a.2 = 1 then ![2 * a.1.val, 2 * a.1.val + 2, 2 * a.1.val + 1] c
  else ![2 * a.1.val + 2, 2 * a.1.val, 2 * a.1.val + 1] c

/-- The doubled outgoing height of a corner of a signed word. -/
def SignedAdjacentWord.oHeight2 (w : SignedAdjacentWord m) (p : Fin w.length × Fin 3) : ℕ :=
  signedOHeight2 w[p.1.val] p.2

/-- The doubled incoming height of a corner of a signed word. -/
def SignedAdjacentWord.xHeight2 (w : SignedAdjacentWord m) (p : Fin w.length × Fin 3) : ℕ :=
  signedXHeight2 w[p.1.val] p.2

/-- The cyclic distance from the column of `p` to the column of `q`, among `3 L` columns. -/
def SignedAdjacentWord.cornerGap (w : SignedAdjacentWord m) (p q : Fin w.length × Fin 3) : ℕ :=
  ((finProdFinEquiv q).val + w.length * 3 - (finProdFinEquiv p).val) % (w.length * 3)

/-- A grid diagram is a signed word grid of `w`: its O rows are ordered by height, and the X marking
of every column lies in the row of the nearest outgoing corner of the same height to its left,
cyclically. -/
structure IsSignedWordGrid (w : SignedAdjacentWord m) (G : GridDiagram (w.length * 3)) : Prop where
  O_lt : ∀ p q, w.oHeight2 p < w.oHeight2 q →
    G.O (finProdFinEquiv p) < G.O (finProdFinEquiv q)
  X_eq : ∀ q, ∃ p, w.oHeight2 p = w.xHeight2 q ∧
    (∀ p', w.oHeight2 p' = w.xHeight2 q → w.cornerGap p q ≤ w.cornerGap p' q) ∧
    G.X (finProdFinEquiv q) = G.O (finProdFinEquiv p)

/-- **Signed word-grid relations (Lemma `signedWordGridRelations`).** A conjugacy derivation from
a positive word to a signed word, both using every generator, is realized by grid moves from the
selected positive word grid to a signed word grid. -/
def SignedWordGridRelationsStatement : Prop :=
  ∀ {m : ℕ}, 2 ≤ m → ∀ (w : PositiveAdjacentWord m) (v : SignedAdjacentWord m),
    w.toSigned.generatorIndices = Finset.univ → v.generatorIndices = Finset.univ →
    SignedBraidConj w.toSigned v →
    ∃ H : GridDiagram (v.length * 3), IsSignedWordGrid v H ∧ (wordGrid w).MovesTo H

/-! ### Normalized factorizations -/

/-- The word `ρ = σ_0 σ_1 ⋯ σ_{S-2}`. -/
def coxeterSignedWord (S : ℕ) : SignedAdjacentWord S :=
  (List.finRange (S - 1)).map fun i => (i, 1)

/-- The padding word `ρ ρ⁻¹`. -/
def padWord (S : ℕ) : SignedAdjacentWord S :=
  coxeterSignedWord S ++ SignedAdjacentWord.inv (coxeterSignedWord S)

/-- `N` positive local words and `N + B` conjugators on `S` strands. -/
structure NormalizedFactorization (S N B : ℕ) where
  /-- The number of strands `a_j` of the local word `j`. -/
  strands : Fin N → ℕ
  /-- The positive local word `β_j`. -/
  word : ∀ j, PositiveAdjacentWord (strands j)
  two_le_strands : ∀ j, 2 ≤ strands j
  strands_le : ∀ j, strands j ≤ S
  word_cycleCount : ∀ j, (word j).toSigned.cycleCount = 1
  word_generators : ∀ j, (word j).toSigned.generatorIndices = Finset.univ
  /-- The conjugator `γ_l` of each factor, before padding. -/
  conjugator : Fin (N + B) → SignedAdjacentWord S

namespace NormalizedFactorization

variable {S N B : ℕ}

/-- The generator `σ_0` as a signed word, or the empty word when `S < 2`. -/
def firstLetter (S : ℕ) : SignedAdjacentWord S :=
  if h : 2 ≤ S then [(⟨0, by omega⟩, 1)] else []

/-- The core `η_l` of a factor: `β_l` on the first `a_l` strands for `l < N`, and `σ_0`
otherwise. -/
def core (F : NormalizedFactorization S N B) (l : Fin (N + B)) : SignedAdjacentWord S :=
  if h : l.val < N then liftPositiveWord (F.strands_le ⟨l.val, h⟩) (F.word ⟨l.val, h⟩)
  else firstLetter S

/-- The padded factor `q_l = (p γ_l) η_l (p γ_l)⁻¹`. -/
def factor (F : NormalizedFactorization S N B) (l : Fin (N + B)) : SignedAdjacentWord S :=
  conjugateWord (padWord S ++ F.conjugator l) (F.core l)

/-- The ordered product `q_0 ⋯ q_{N+B-1}`. -/
def product (F : NormalizedFactorization S N B) : SignedAdjacentWord S :=
  (List.ofFn F.factor).flatten

/-- Strand `0` lies in the nontrivial cycle of every factor. -/
def StrandZeroInEveryFactor (F : NormalizedFactorization S N B) (hS : 0 < S) : Prop :=
  ∀ l, (F.factor l).permutation ⟨0, hS⟩ ≠ ⟨0, hS⟩

/-- The factor permutations generate a transitive group. -/
def Transitive (F : NormalizedFactorization S N B) : Prop :=
  ∀ x y : Fin S, ∃ σ ∈ Subgroup.closure (Set.range fun l => (F.factor l).permutation), σ x = y

/-- The count `s - U = Σ_l a_l - r - S + 1` of the scissor construction, with `a_l = 2` for the
simple factors and `r = N + B`. -/
def scissorShiftCount (F : NormalizedFactorization S N B) : ℤ :=
  (∑ j, (F.strands j : ℤ)) + B - N - S + 1

end NormalizedFactorization

end OnLeConjecture.KnotTheory
