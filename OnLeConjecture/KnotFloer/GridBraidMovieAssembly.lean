/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridBraidMovieStatement
public import OnLeConjecture.KnotFloer.GridXSwitchSequence
public import OnLeConjecture.KnotTheory.PositiveWordBraidMoviePlan
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Move.Basic

/-!
# Assembly of the braid grid movie from its combinatorial inputs

This module proves `BraidNativeMapStatement` from five combinatorial statements,
each stated here as a proposition with the exact form proposed for its job:

* `MovesToCanonicalMapStatement` (J01): grid moves induce native maps with zero shifts
  carrying the normalized class to the normalized class;
* `XSwitchReverseStatement` (J01): a single adjacent X switch can be reversed;
* `CoxeterConjugacyStatement` (J08): every Coxeter element after a full twist is
  conjugate to the standard Coxeter word after the full twist;
* `WordGridConjugacyMovesStatement` (J09): conjugate words have grids related by moves;
* `WordGridDeleteLetterStatement` (J10): deleting one letter is one X switch followed
  by grid moves;
* `TorusCoxeterPowerStatement` (J11): the reflected torus grid is related by moves to the
  grid of `Δ² c`.

The movie is the one of the manuscript: grid moves from the torus grid to the grid of
`Δ² c`, then to the grid of `Δ² γ₀ η` where `γ₀ ⊆ w` has `S - b` distinct letters and `η`
holds the remaining `b - 1` generators, then `b - 1` deletions and `|w| - (S - b)`
insertions. The theorem `braidNativeMap_of_inputs` is conditional on these five
propositions until each is proved.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex OnLeConjecture.KnotTheory

/-- The statement proposed for job J01: grid moves induce native maps with zero shifts
that carry the normalized class to the normalized class. -/
def MovesToCanonicalMapStatement : Prop :=
  ∀ {n k : ℕ} (G : GridDiagram n) (H : GridDiagram k) (hn : 2 ≤ n) (hk : 2 ≤ k),
    G.MovesTo H →
      ∃ φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2),
        (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2))
          φ 0 0 ∧
        homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk

/-- The statement proposed for job J01: a single adjacent X switch can be reversed. -/
def XSwitchReverseStatement : Prop :=
  ∀ {n : ℕ} {G H : GridDiagram n},
    Nonempty (XSwitchSequence G H 1) → Nonempty (XSwitchSequence H G 1)

/-- The statement of job J08: on at least two strands, after a full twist, every word
containing each generator exactly once is conjugate to the standard Coxeter word. The
hypothesis `2 ≤ m` is necessary, because `PositiveWordConj` relates no empty words. -/
def CoxeterConjugacyStatement : Prop :=
  ∀ {m : ℕ} (γ : PositiveAdjacentWord m), γ.Perm (List.finRange (m - 1)) → 2 ≤ m →
    PositiveWordConj (fullTwistWord m ++ γ) (fullTwistWord m ++ coxeterWord m)

/-- The statement proposed for job J09: conjugate words using every generator have
selected grids related by grid moves. -/
def WordGridConjugacyMovesStatement : Prop :=
  ∀ {m : ℕ}, 2 ≤ m → ∀ {u v : PositiveAdjacentWord m},
    u.toSigned.generatorIndices = Finset.univ → PositiveWordConj u v →
      (wordGrid u).MovesTo (wordGrid v)

/-- The statement proposed for job J10: deleting one letter from a word whose remaining
letters use every generator is one adjacent X switch followed by grid moves. -/
def WordGridDeleteLetterStatement : Prop :=
  ∀ {m : ℕ}, 2 ≤ m → ∀ (u v : PositiveAdjacentWord m) (i : Fin (m - 1)),
    (u ++ v).toSigned.generatorIndices = Finset.univ →
      ∃ H : GridDiagram ((u ++ i :: v).length * 3),
        Nonempty (XSwitchSequence (wordGrid (u ++ i :: v)) H 1) ∧
          H.MovesTo (wordGrid (u ++ v))

/-- The statement proposed for job J11 in the case `a = S`, `q = S + 1`. -/
def TorusCoxeterPowerStatement : Prop :=
  ∀ S : ℕ, 2 ≤ S →
    (reflectedTorusGrid (S - 1)).MovesTo (wordGrid (fullTwistWord S ++ coxeterWord S))

/-- Native maps between selected grids of words with a full-twist prefix, with Alexander
shift `s / 2`, carrying normalized classes to normalized classes. -/
def FullTwistWordMap {S : ℕ} (hS : 2 ≤ S) (x y : PositiveAdjacentWord S) (s : ℕ) : Prop :=
  ∃ φ : laurentMaslovComplex (wordGrid (fullTwistWord S ++ x)) (ZMod 2) ⟶
      laurentMaslovComplex (wordGrid (fullTwistWord S ++ y)) (ZMod 2),
    (laurentMaslovBifiltration (wordGrid (fullTwistWord S ++ x)) (ZMod 2)).Shifts
        (laurentMaslovBifiltration (wordGrid (fullTwistWord S ++ y)) (ZMod 2)) φ 0
        ((s : ℝ) / 2) ∧
      homologyMap φ 0 (gridCanonicalClass (wordGrid (fullTwistWord S ++ x))
          (two_le_wordGrid_size_fullTwist hS x)) =
        gridCanonicalClass (wordGrid (fullTwistWord S ++ y)) (two_le_wordGrid_size_fullTwist hS y)

section FullTwistWordMap

variable {S : ℕ} (hS : 2 ≤ S)

theorem FullTwistWordMap.refl (x : PositiveAdjacentWord S) : FullTwistWordMap hS x x 0 :=
  ⟨𝟙 _, fun a b i z hz => by simp only [Nat.cast_zero, zero_div, add_zero]; exact hz, by simp⟩

theorem FullTwistWordMap.trans {x y z : PositiveAdjacentWord S} {s t : ℕ}
    (h₁ : FullTwistWordMap hS x y s) (h₂ : FullTwistWordMap hS y z t) :
    FullTwistWordMap hS x z (s + t) := by
  obtain ⟨φ, hφ, hφc⟩ := h₁
  obtain ⟨ψ, hψ, hψc⟩ := h₂
  refine ⟨φ ≫ ψ, ?_, ?_⟩
  · have h := hφ.comp hψ
    simpa only [add_zero, Nat.cast_add, add_div] using h
  · rw [homologyMap_comp, CategoryTheory.comp_apply, hφc, hψc]

/-- Grid moves give maps with zero shift. -/
theorem FullTwistWordMap.of_movesTo (h01 : MovesToCanonicalMapStatement)
    {x y : PositiveAdjacentWord S}
    (h : (wordGrid (fullTwistWord S ++ x)).MovesTo (wordGrid (fullTwistWord S ++ y))) :
    FullTwistWordMap hS x y 0 := by
  obtain ⟨φ, hφ, hφc⟩ := h01 _ _ (two_le_wordGrid_size_fullTwist hS x)
    (two_le_wordGrid_size_fullTwist hS y) h
  exact ⟨φ, by simpa using hφ, hφc⟩

/-- An X switch followed by grid moves gives a map with Alexander shift `1/2`. -/
theorem FullTwistWordMap.of_switch_movesTo (h01 : MovesToCanonicalMapStatement)
    {x y : PositiveAdjacentWord S} {H : GridDiagram ((fullTwistWord S ++ x).length * 3)}
    (hs : Nonempty (XSwitchSequence (wordGrid (fullTwistWord S ++ x)) H 1))
    (hm : H.MovesTo (wordGrid (fullTwistWord S ++ y))) :
    FullTwistWordMap hS x y 1 := by
  obtain ⟨s⟩ := hs
  obtain ⟨φ, hφ, hφc⟩ := h01 H _ (two_le_wordGrid_size_fullTwist hS x)
    (two_le_wordGrid_size_fullTwist hS y) hm
  refine ⟨(s.chainIso (ZMod 2)).hom ≫ φ, ?_, ?_⟩
  · have h := (s.chainIso_shifts (ZMod 2)).comp hφ
    simpa only [add_zero, Nat.cast_one] using h
  · rw [homologyMap_comp, CategoryTheory.comp_apply,
      s.gridCanonicalClass_map (two_le_wordGrid_size_fullTwist hS x), hφc]

/-- Grid moves followed by an X switch give a map with Alexander shift `1/2`. -/
theorem FullTwistWordMap.of_movesTo_switch (h01 : MovesToCanonicalMapStatement)
    {x y : PositiveAdjacentWord S} {H : GridDiagram ((fullTwistWord S ++ y).length * 3)}
    (hm : (wordGrid (fullTwistWord S ++ x)).MovesTo H)
    (hs : Nonempty (XSwitchSequence H (wordGrid (fullTwistWord S ++ y)) 1)) :
    FullTwistWordMap hS x y 1 := by
  obtain ⟨s⟩ := hs
  obtain ⟨φ, hφ, hφc⟩ := h01 _ H (two_le_wordGrid_size_fullTwist hS x)
    (two_le_wordGrid_size_fullTwist hS y) hm
  refine ⟨φ ≫ (s.chainIso (ZMod 2)).hom, ?_, ?_⟩
  · have h := hφ.comp (s.chainIso_shifts (ZMod 2))
    simpa only [zero_add, Nat.cast_one] using h
  · rw [homologyMap_comp, CategoryTheory.comp_apply, hφc,
      s.gridCanonicalClass_map (two_le_wordGrid_size_fullTwist hS y)]

/-- The form of `FullTwistWordMap.of_switch_movesTo` for words given up to equality. -/
theorem FullTwistWordMap.of_switch_movesTo' (h01 : MovesToCanonicalMapStatement)
    {x y X Y : PositiveAdjacentWord S} (hX : X = fullTwistWord S ++ x)
    (hY : Y = fullTwistWord S ++ y) {H : GridDiagram (X.length * 3)}
    (hs : Nonempty (XSwitchSequence (wordGrid X) H 1)) (hm : H.MovesTo (wordGrid Y)) :
    FullTwistWordMap hS x y 1 := by
  subst hX hY
  exact FullTwistWordMap.of_switch_movesTo hS h01 hs hm

/-- The form of `FullTwistWordMap.of_movesTo_switch` for words given up to equality. -/
theorem FullTwistWordMap.of_movesTo_switch' (h01 : MovesToCanonicalMapStatement)
    {x y X Y : PositiveAdjacentWord S} (hX : X = fullTwistWord S ++ x)
    (hY : Y = fullTwistWord S ++ y) {H : GridDiagram (Y.length * 3)}
    (hm : (wordGrid X).MovesTo H) (hs : Nonempty (XSwitchSequence H (wordGrid Y) 1)) :
    FullTwistWordMap hS x y 1 := by
  subst hX hY
  exact FullTwistWordMap.of_movesTo_switch hS h01 hm hs

/-- A word with a full-twist prefix uses every generator. -/
theorem generatorIndices_fullTwist_append (u : PositiveAdjacentWord S) :
    (fullTwistWord S ++ u).toSigned.generatorIndices = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  have h := fullTwistWord_generatorIndices S
  rw [PositiveAdjacentWord.generatorIndices_toSigned] at h ⊢
  have hi : i ∈ (fullTwistWord S).toFinset := by rw [h]; exact Finset.mem_univ i
  rw [List.mem_toFinset] at hi ⊢
  exact List.mem_append_left _ hi

/-- Deleting one letter after the full twist is a map with Alexander shift `1/2`. -/
theorem FullTwistWordMap.delete (h01 : MovesToCanonicalMapStatement)
    (h10 : WordGridDeleteLetterStatement) (u v : PositiveAdjacentWord S) (i : Fin (S - 1)) :
    FullTwistWordMap hS (u ++ i :: v) (u ++ v) 1 := by
  obtain ⟨H, hs, hm⟩ := h10 hS (fullTwistWord S ++ u) v i (by
    rw [List.append_assoc]; exact generatorIndices_fullTwist_append (u ++ v))
  exact FullTwistWordMap.of_switch_movesTo' hS h01 (List.append_assoc _ _ _)
    (List.append_assoc _ _ _) hs hm

/-- Inserting one letter after the full twist is a map with Alexander shift `1/2`. -/
theorem FullTwistWordMap.insert (h01 : MovesToCanonicalMapStatement)
    (h01r : XSwitchReverseStatement) (h10 : WordGridDeleteLetterStatement)
    (u v : PositiveAdjacentWord S) (i : Fin (S - 1)) :
    FullTwistWordMap hS (u ++ v) (u ++ i :: v) 1 := by
  obtain ⟨H, hs, hm⟩ := h10 hS (fullTwistWord S ++ u) v i (by
    rw [List.append_assoc]; exact generatorIndices_fullTwist_append (u ++ v))
  exact FullTwistWordMap.of_movesTo_switch' hS h01 (List.append_assoc _ _ _)
    (List.append_assoc _ _ _) hm.symm (h01r hs)

end FullTwistWordMap

/-- **Braid native map, conditional form.** The five combinatorial statements of jobs
J01, J08, J09, J10 and J11 imply the braid native map statement. -/
theorem braidNativeMap_of_inputs (h01 : MovesToCanonicalMapStatement)
    (h01r : XSwitchReverseStatement) (h08 : CoxeterConjugacyStatement)
    (h09 : WordGridConjugacyMovesStatement) (h10 : WordGridDeleteLetterStatement)
    (h11 : TorusCoxeterPowerStatement) : BraidNativeMapStatement := by
  intro S hS w
  obtain ⟨γ₀, η, hsub, hperm, hlen₀, hlenη⟩ := exists_coxeter_split (by omega) w
  set b := w.toSigned.cycleCount with hb
  have hb1 : 1 ≤ b := SignedAdjacentWord.one_le_cycleCount (by omega) w.toSigned
  have hle := hsub.length_le
  -- Grid moves from `Δ² c` to `Δ² γ₀ η`.
  have hconj : (wordGrid (fullTwistWord S ++ coxeterWord S)).MovesTo
      (wordGrid (fullTwistWord S ++ (γ₀ ++ η))) :=
    h09 hS (generatorIndices_fullTwist_append _) (h08 _ hperm hS).symm
  -- Deletions from `Δ² γ₀ η` to `Δ² γ₀`, then insertions from `Δ² γ₀` to `Δ² w`.
  have hdel : FullTwistWordMap hS (γ₀ ++ η) γ₀ η.length :=
    reach_append_delete (FullTwistWordMap hS) γ₀ (FullTwistWordMap.refl hS)
      (fun h₁ h₂ => h₁.trans hS h₂) (fun v i => FullTwistWordMap.delete hS h01 h10 γ₀ v i) η
  have hins : FullTwistWordMap hS γ₀ w (w.length - γ₀.length) := by
    simpa using reach_append_of_sublist (FullTwistWordMap hS) [] (FullTwistWordMap.refl hS)
      (fun h₁ h₂ => h₁.trans hS h₂)
      (fun u v i => by simpa using FullTwistWordMap.insert hS h01 h01r h10 u v i) hsub
  obtain ⟨ψ, hψ, hψc⟩ := (FullTwistWordMap.of_movesTo hS h01 hconj).trans hS (hdel.trans hS hins)
  -- The initial grid moves from the torus grid to `Δ² c`.
  obtain ⟨φ, hφ, hφc⟩ := h01 _ _ (by unfold consecutiveTorusGridSize; omega)
    (two_le_wordGrid_size_fullTwist hS (coxeterWord S)) (h11 S hS)
  refine ⟨φ ≫ ψ, ?_, ?_⟩
  · have h := hφ.comp hψ
    have hcount : ((0 + (η.length + (w.length - γ₀.length)) : ℕ) : ℝ) =
        (w.length : ℝ) - ((S : ℝ) - b) + ((b : ℝ) - 1) := by
      rw [hlenη, hlen₀]
      have h1 : S - b ≤ w.length := hlen₀ ▸ hle
      have h2 : b ≤ S := SignedAdjacentWord.cycleCount_le_strandCount w.toSigned
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hb1]
      ring
    rw [hcount, zero_add, zero_add] at h
    exact h
  · rw [homologyMap_comp, CategoryTheory.comp_apply,
      ← gridCanonicalClass_reflectedTorus, hφc, hψc]

end OnLeConjecture.KnotFloer.GridFull
