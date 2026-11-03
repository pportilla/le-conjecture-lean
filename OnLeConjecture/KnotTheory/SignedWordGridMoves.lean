/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesCancelStep
public import OnLeConjecture.KnotTheory.SignedWordGridMovesBraid
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Signed word-grid relations

`SignedWordGridRelationsStatement` (written proof of Statement E,
`statement_E_complete_proof.tex`, Lemma `signedWordGridRelations`, Section 7): a conjugacy
derivation from a positive word `w` to a signed word `v`, both using every generator, gives a
signed word grid of `v` related to `wordGrid w` by grid moves
(`SignedGrid.signedWordGridRelations`).

The derivation is performed behind the guard `padWord m = ρ ρ⁻¹`, which contains every generator,
so that every rank occurs in every intermediate word and every cancellation is realized by
`SignedGrid.fwd_cancel`. A rotation `x a ↦ a x` of the guarded word `g x a` is realized as
`g x a ↦ a g x ↦ g a g x ↦ g a x`: a rotation, an insertion of the guard and a cancellation of the
inner guard (`SignedGrid.fwd_step_guard`). Far commutations and braid relations are
`SignedGrid.fwd_far` and `SignedGrid.fwd_braid`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

/-! ### Words in which every rank occurs -/

/-- Every rank occurs in the signed word `x`. -/
def AllRanks (x : SignedAdjacentWord m) : Prop := ∀ s < m, RankIn x s

theorem AllRanks.mono {x y : SignedAdjacentWord m} (h : AllRanks x) (hxy : ∀ a ∈ x, a ∈ y) :
    AllRanks y := fun s hs => (h s hs).mono hxy

theorem allRanks_of_letters (hm : 2 ≤ m) {x : SignedAdjacentWord m}
    (hx : ∀ i : Fin (m - 1), ∃ a ∈ x, a.1 = i) : AllRanks x := by
  intro s hs
  by_cases h : s < m - 1
  · obtain ⟨a, ha, hae⟩ := hx ⟨s, h⟩
    exact ⟨a, ha, Or.inl (by rw [hae])⟩
  · obtain ⟨a, ha, hae⟩ := hx ⟨s - 1, by omega⟩
    exact ⟨a, ha, Or.inr (by rw [hae]; simp; omega)⟩

theorem allRanks_of_gen (hm : 2 ≤ m) {x : SignedAdjacentWord m}
    (hx : x.generatorIndices = Finset.univ) : AllRanks x := by
  apply allRanks_of_letters hm
  intro i
  have : i ∈ x.generatorIndices := by rw [hx]; exact Finset.mem_univ _
  simp only [SignedAdjacentWord.generatorIndices, List.mem_toFinset, List.mem_map] at this
  exact this

theorem allRanks_pad (hm : 2 ≤ m) (x : SignedAdjacentWord m) : AllRanks (padWord m ++ x) := by
  apply allRanks_of_letters hm
  intro i
  refine ⟨(i, 1), ?_, rfl⟩
  simp [padWord, coxeterSignedWord]

/-! ### The guard -/

theorem inv_append_single (ρ : SignedAdjacentWord m) (a : Fin (m - 1) × ℤˣ) :
    SignedAdjacentWord.inv (ρ ++ [a]) = (a.1, -a.2) :: SignedAdjacentWord.inv ρ := by
  simp [SignedAdjacentWord.inv]

/-- **Insertion and cancellation of a word followed by its inverse.** -/
theorem fwd_pad (u z ρ : SignedAdjacentWord m) (hz : AllRanks (u ++ z)) :
    Fwd (u ++ z) (u ++ (ρ ++ SignedAdjacentWord.inv ρ) ++ z) ∧
      Fwd (u ++ (ρ ++ SignedAdjacentWord.inv ρ) ++ z) (u ++ z) := by
  induction ρ using List.reverseRecOn with
  | nil => simp only [SignedAdjacentWord.inv_nil, List.append_nil]; exact ⟨Fwd.refl _, Fwd.refl _⟩
  | append_singleton ρ a ih =>
    have hsub : ∀ b ∈ u ++ z, b ∈ (u ++ ρ) ++ (SignedAdjacentWord.inv ρ ++ z) := fun b hb => by
      simp only [List.mem_append] at hb ⊢; tauto
    have hc := fwd_cancel (u ++ ρ) (SignedAdjacentWord.inv ρ ++ z) a.1 a.2
      ((hz _ (by have := a.1.isLt; omega)).mono hsub)
      ((hz _ (by have := a.1.isLt; omega)).mono hsub)
    have e1 : u ++ (ρ ++ [a] ++ SignedAdjacentWord.inv (ρ ++ [a])) ++ z =
        (u ++ ρ) ++ (a.1, a.2) :: (a.1, -a.2) :: (SignedAdjacentWord.inv ρ ++ z) := by
      rw [inv_append_single]; simp
    have e2 : u ++ (ρ ++ SignedAdjacentWord.inv ρ) ++ z =
        (u ++ ρ) ++ (SignedAdjacentWord.inv ρ ++ z) := by simp
    rw [e1]
    rw [e2] at ih
    exact ⟨ih.1.trans hc.2, hc.1.trans ih.2⟩

theorem fwd_guard_in (u z : SignedAdjacentWord m) (hz : AllRanks (u ++ z)) :
    Fwd (u ++ z) (u ++ padWord m ++ z) ∧ Fwd (u ++ padWord m ++ z) (u ++ z) :=
  fwd_pad u z (coxeterSignedWord m) hz

/-- **A guarded step.** Every conjugacy step `x → y` gives grid moves between the signed word
grids of the guarded words `padWord m ++ x` and `padWord m ++ y`, in both directions. -/
theorem fwd_step_guard (hm : 2 ≤ m) {x y : SignedAdjacentWord m} (h : SignedBraidConjStep x y) :
    Fwd (padWord m ++ x) (padWord m ++ y) ∧ Fwd (padWord m ++ y) (padWord m ++ x) := by
  cases h with
  | step h =>
    cases h with
    | cancel u v i e =>
      have hr := allRanks_pad hm (u ++ v)
      have := fwd_cancel (padWord m ++ u) v i e
        (by simpa using hr _ (by have := i.isLt; omega))
        (by simpa using hr _ (by have := i.isLt; omega))
      simpa only [List.append_assoc] using this
    | far u v i j e f hij =>
      have h1 := fwd_far (padWord m ++ u) v (i, e) (j, f) hij
      have h2 := fwd_far (padWord m ++ u) v (j, f) (i, e) hij.symm
      simp only [List.append_assoc] at h1 h2
      exact ⟨h1, h2⟩
    | braid u v i j hij =>
      have := fwd_braid (padWord m ++ u) v i j hij
      simpa only [List.append_assoc] using this
  | rotate w a =>
    set g := padWord m
    have hrank : AllRanks (g ++ [a] ++ w) := by
      have := allRanks_pad hm ([a] ++ w); simpa [g] using this
    have hrank' : AllRanks ([] ++ ([a] ++ g ++ w)) := hrank.mono (fun b hb => by
      simp only [List.mem_append, List.nil_append] at hb ⊢; tauto)
    -- `g w a ↦ a g w`
    have r1 : Fwd (g ++ (w ++ [a])) ([a] ++ g ++ w) := by
      have := fwd_rotate (g ++ w) [a]; simpa only [List.append_assoc] using this
    -- `a g w ↦ g a g w`
    have r2 := fwd_guard_in [] ([a] ++ g ++ w) hrank'
    -- `g a g w ↦ g a w`
    have r3 := fwd_guard_in (g ++ [a]) w hrank
    simp only [List.nil_append, List.append_assoc, List.cons_append] at r1 r2 r3 ⊢
    exact ⟨(r1.trans r2.1).trans r3.2, (r3.1.trans r2.2).trans (by
      have := fwd_rotate [a] (g ++ w)
      simpa only [List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using this)⟩

/-! ### The statement -/

/-- **Signed word-grid relations.** -/
theorem signedWordGridRelations : SignedWordGridRelationsStatement := by
  intro m hm w v hw hv hconj
  let Reach : SignedAdjacentWord m → Prop := fun x =>
    ∃ H : GridDiagram (x.length * 3), IsSignedWordGrid x H ∧ (wordGrid w).MovesTo H
  have hReach : ∀ {x y : SignedAdjacentWord m}, Reach x → Fwd x y → Reach y := by
    rintro x y ⟨H, hH, hm'⟩ hf
    obtain ⟨K, hK, hm''⟩ := hf H hH
    exact ⟨K, hK, hm'.trans hm''⟩
  have h0 : Reach w.toSigned := ⟨KnotFloer.GridFull.gridCast (size_toSigned w) (wordGrid w),
    isSignedWordGrid_wordGrid w, KnotFloer.GridFull.movesTo_gridCast _ _⟩
  have h1 : Reach (padWord m ++ w.toSigned) := by
    have := (fwd_guard_in [] w.toSigned (by simpa using allRanks_of_gen hm hw)).1
    simp only [List.nil_append] at this
    exact hReach h0 this
  have hinv : ∀ x y, SignedBraidConj x y → (Reach (padWord m ++ x) ↔ Reach (padWord m ++ y)) := by
    intro x y h
    induction h with
    | rel x y hs =>
      obtain ⟨f1, f2⟩ := fwd_step_guard hm hs
      exact ⟨fun h => hReach h f1, fun h => hReach h f2⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  have h2 : Reach (padWord m ++ v) := (hinv _ _ hconj).mp h1
  have := (fwd_guard_in [] v (by simpa using allRanks_of_gen hm hv)).2
  simp only [List.nil_append] at this
  exact hReach h2 this

end OnLeConjecture.KnotTheory.SignedGrid
