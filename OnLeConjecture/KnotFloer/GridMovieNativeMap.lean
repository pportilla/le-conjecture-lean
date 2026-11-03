/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMovesToCanonicalMap
public import OnLeConjecture.KnotFloer.GridXSwitchSequence

/-!
# Grid movies and their native maps

A grid movie from a grid diagram `G` to a grid diagram `H` is a finite composite of sequences of
grid moves (`GridDiagram.MovesTo`) and single switches of `X`-markings in cyclically adjacent
columns. The index `s` of `GridMovie A B s` counts the switches. Grid moves carry index zero,
a single switch carries index one, and composition adds the indices.

If `G` and `H` have sizes at least two and a grid movie from `G` to `H` has index `s`, then some
chain map `laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2)` has filtration
shifts `(0, s / 2)` and sends `gridCanonicalClass G` to `gridCanonicalClass H`
(`GridMovie.exists_native_map`). Each move contributes a map with shifts `(0, 0)` by
`exists_movesTo_canonical_map`, and each switch contributes the marking isomorphism
`XSwitchSequence.chainIso`, with shifts `(0, 1 / 2)` by `XSwitchSequence.chainIso_shifts`.

A single switch is reversible: the same pair of columns switches the `X`-markings back
(`XSwitchSequence.nonempty_reverse_one`). Hence a grid movie can be reversed with the same
index (`GridMovie.symm`). A sequence of `l` switches is a grid movie of index `l`
(`GridMovie.of_xSwitchSequence`).

No grid movie is constructed here from a smooth cobordism.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n k m : ℕ}

/-! ### Single switches -/

/-- A single switch of `X`-markings in cyclically adjacent columns is reversed by switching the
same two columns again. -/
theorem XSwitchSequence.nonempty_reverse_one {n : ℕ} {G H : GridDiagram n} :
    Nonempty (XSwitchSequence G H 1) → Nonempty (XSwitchSequence H G 1) := by
  rintro ⟨s⟩
  cases s with
  | cons a ha hO hX tail =>
      cases tail
      refine ⟨.cons a ha hO.symm ?_ (.nil G)⟩
      rw [hX, GridState.swapColumns_swapColumns]

/-- The marking isomorphism `XSwitchSequence.chainIso` of a sequence of `l` switches of
`X`-markings from `G` to `H` gives `GridCanonicalTransport G H (l / 2)`. -/
theorem gridCanonicalTransport_of_xSwitchSequence {G H : GridDiagram n} {l : ℕ}
    (s : XSwitchSequence G H l) : GridCanonicalTransport G H ((l : ℝ) / 2) :=
  fun hn _ => ⟨(s.chainIso (ZMod 2)).hom, s.chainIso_shifts (ZMod 2), s.gridCanonicalClass_map hn⟩

/-! ### Grid movies -/

/-- A grid movie between grid diagrams of possibly different sizes, built from sequences of grid
moves and single switches of `X`-markings in cyclically adjacent columns. The last index counts
the switches: grid moves have index zero, a single switch has index one, and composition adds
the indices. -/
inductive GridMovie : (Σ n, GridDiagram n) → (Σ n, GridDiagram n) → ℕ → Prop
  | moves {n k : ℕ} {G : GridDiagram n} {H : GridDiagram k} :
      G.MovesTo H → GridMovie ⟨n, G⟩ ⟨k, H⟩ 0
  | xswitch {n : ℕ} {G H : GridDiagram n} :
      Nonempty (XSwitchSequence G H 1) → GridMovie ⟨n, G⟩ ⟨n, H⟩ 1
  | trans {A B C : Σ n, GridDiagram n} {s t : ℕ} :
      GridMovie A B s → GridMovie B C t → GridMovie A C (s + t)

namespace GridMovie

/-- Every grid diagram is related to itself by a grid movie of index zero. -/
theorem refl (A : Σ n, GridDiagram n) : GridMovie A A 0 :=
  .moves (GridDiagram.MovesTo.refl A.2)

/-- A sequence of grid moves is a grid movie of index zero. -/
theorem of_movesTo {G : GridDiagram n} {H : GridDiagram k} (h : G.MovesTo H) :
    GridMovie ⟨n, G⟩ ⟨k, H⟩ 0 :=
  .moves h

/-- A grid movie followed by a sequence of grid moves is a grid movie with the same index. -/
theorem trans_movesTo {A : Σ n, GridDiagram n} {s : ℕ} {H : GridDiagram k} {K : GridDiagram m}
    (M : GridMovie A ⟨k, H⟩ s) (h : H.MovesTo K) : GridMovie A ⟨m, K⟩ s :=
  M.trans (.moves h)

/-- A sequence of grid moves followed by a grid movie is a grid movie with the same index. -/
theorem movesTo_trans {G : GridDiagram n} {H : GridDiagram k} {B : Σ n, GridDiagram n} {s : ℕ}
    (h : G.MovesTo H) (M : GridMovie ⟨k, H⟩ B s) : GridMovie ⟨n, G⟩ B s := by
  simpa only [Nat.zero_add] using (GridMovie.moves h).trans M

/-- A single switch of `X`-markings, read backwards, is a grid movie of index one. -/
theorem xswitch_reverse {G H : GridDiagram n} (h : Nonempty (XSwitchSequence G H 1)) :
    GridMovie ⟨n, H⟩ ⟨n, G⟩ 1 :=
  .xswitch (XSwitchSequence.nonempty_reverse_one h)

/-- A sequence of `l` switches of `X`-markings is a grid movie of index `l`. -/
theorem of_xSwitchSequence {G H : GridDiagram n} {l : ℕ} (s : XSwitchSequence G H l) :
    GridMovie ⟨n, G⟩ ⟨n, H⟩ l := by
  induction s with
  | nil G => exact refl _
  | cons a ha hO hX tail ih =>
      rw [Nat.add_comm]
      exact (GridMovie.xswitch ⟨.cons a ha hO hX (.nil _)⟩).trans ih

/-- A grid movie can be reversed with the same index. -/
theorem symm {A B : Σ n, GridDiagram n} {s : ℕ} (M : GridMovie A B s) : GridMovie B A s := by
  induction M with
  | moves h => exact .moves h.symm
  | xswitch h => exact xswitch_reverse h
  | trans _ _ ih₁ ih₂ =>
      rw [Nat.add_comm]
      exact ih₂.trans ih₁

/-- If a grid movie relates `A` to `B`, then `A` has size at least two exactly when `B` has size
at least two. -/
theorem two_le_iff {A B : Σ n, GridDiagram n} {s : ℕ} (M : GridMovie A B s) :
    2 ≤ A.1 ↔ 2 ≤ B.1 := by
  induction M with
  | moves h => exact grid_size_two_le_iff_of_movesTo h
  | xswitch _ => exact Iff.rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- If a grid movie of index `s` relates `A` to `B`, then
`GridCanonicalTransport A.2 B.2 (s / 2)` holds. -/
theorem gridCanonicalTransport {A B : Σ n, GridDiagram n} {s : ℕ} (M : GridMovie A B s) :
    GridCanonicalTransport A.2 B.2 ((s : ℝ) / 2) := by
  induction M with
  | moves h =>
      exact (gridCanonicalTransport_of_movesTo h).1.of_eq_shift (by simp)
  | xswitch h =>
      obtain ⟨s⟩ := h
      exact gridCanonicalTransport_of_xSwitchSequence s
  | trans M₁ _ ih₁ ih₂ =>
      exact (ih₁.trans ih₂ M₁.two_le_iff.mp).of_eq_shift (by push_cast; ring)

/-- **Native maps along grid movies.** If a grid movie of index `s` relates two grid diagrams of
size at least two, then some chain map between their native `ZMod 2` complexes has filtration
shifts `(0, s / 2)` and sends the normalized class of the first grid to the normalized class of
the second. -/
theorem exists_native_map {n k s : ℕ} {G : GridDiagram n} {H : GridDiagram k}
    (M : GridMovie ⟨n, G⟩ ⟨k, H⟩ s) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    ∃ φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2),
      (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2))
        φ 0 ((s : ℝ) / 2) ∧
      homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk :=
  M.gridCanonicalTransport hn hk

/-- If a grid movie of index `s` relates a grid diagram of size `n` with `2 ≤ n` to a grid diagram
of size `k`, then `2 ≤ k`, and some chain map between their native `ZMod 2` complexes has
filtration shifts `(0, s / 2)` and sends the normalized class of the first grid to the normalized
class of the second. -/
theorem exists_native_map_of_two_le {n k s : ℕ} {G : GridDiagram n} {H : GridDiagram k}
    (M : GridMovie ⟨n, G⟩ ⟨k, H⟩ s) (hn : 2 ≤ n) :
    ∃ hk : 2 ≤ k, ∃ φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2),
      (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2))
        φ 0 ((s : ℝ) / 2) ∧
      homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk :=
  ⟨M.two_le_iff.mp hn, M.exists_native_map hn (M.two_le_iff.mp hn)⟩

end GridMovie

end OnLeConjecture.KnotFloer.GridFull
