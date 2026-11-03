/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridAdmissibleDeletion
public import OnLeConjecture.KnotFloer.GridMovieNativeMap
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Letter deletion as one `X` switch on word grids

Let `w = u σ_i v` and `w' = u v` be positive words on `m` strands, and suppose that every adjacent
generator occurs in `w'`. Let `j = |u|`. In the selected grid of `w`, exchanging the
`X`-markings of the columns `3 j + 1` and `3 j + 2` of the deleted letter is one switch of
adjacent `X`-markings (`XSwitchSequence` of length one). The switched grid `H` is related by grid
moves to the selected grid of `w'` (`wordGrid_delete_letter`, job J10 of the dependency audit).

The proof works for every admissible grid `G` of `w` (`IsAdmissibleWordGrid.exists_switch_movesTo`).
After the switch, the columns of the deleted letter carry the following markings, where `R a` is
the row of the arc leaving the corner `a` and `M` is the matching of `w`:

* column `3 j`: `O` in `R (j, 0)` and `X` in `R (M⁻¹ (j, 0))`;
* column `3 j + 1`: `O` in `R (j, 1)` and `X` in `R (j, 0)`;
* column `3 j + 2`: `O` in `R (j, 2)` and `X` in `R (M⁻¹ (j, 1))`.

Three applications of `GridDiagram.IsMarkingRestriction.exists_movesTo_eraseOCorner_of_ambient`
erase the `O`-markings of these three columns in turn: first the middle arc, then the
continuation column of the lower rank `i`, then the continuation column of the upper rank
`i + 1`. Their non-interleaving hypotheses follow from the fact that arcs with the same
unperturbed row do not interleave (`positiveRectilinearWord_noninterleaving_of_arcRow_eq`). The
resulting grid is admissible for `w'`, because the matching of `w'` continues the arcs entering
the deleted letter along the arcs leaving it (`IsLetterDeletion.corner_matching_symm`). Any two
admissible grids of `w'` are related by row commutations (`IsAdmissibleWordGrid.movesTo`).

The insertion form `wordGrid_insert_letter` follows by reversing the switch
(`XSwitchSequence.nonempty_reverse_one`) and the grid moves.

All results are unconditional. The hypothesis `2 ≤ m` of `wordGrid_delete_letter` is not used.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti OnLeConjecture.KnotFloer.GridFull OnLeConjecture.KnotTheory.GridMoves

/-- A single switch of adjacent `X`-markings is a sequence of one switch. -/
def xSwitchSequence_switchAdjacentX {n : ℕ} (G : GridDiagram n) (b : Fin n)
    (h1 : G.O b ≠ G.X (finRotate n b)) (h2 : G.O (finRotate n b) ≠ G.X b) :
    XSwitchSequence G (G.switchAdjacentX b h1 h2) 1 :=
  .cons (H := G.switchAdjacentX b h1 h2) b (G.column_ne_finRotate b) rfl rfl (.nil _)

section LetterSwitch

variable {m : ℕ} {w w' : PositiveAdjacentWord m} {j : Fin w.length}

/-- The column of the middle corner of letter `j` is followed by the column of its last
corner. -/
theorem finRotate_finProdFinEquiv_one (j : Fin w.length) :
    finRotate (w.length * 3) (finProdFinEquiv (j, 1)) = finProdFinEquiv (j, 2) := by
  have hj := j.isLt
  ext
  rw [finRotate_val_of_lt _ (by rw [finProdFinEquiv_val_three]; simp; omega),
    finProdFinEquiv_val_three, finProdFinEquiv_val_three]
  simp
  omega

/-- The column of the first corner of letter `j` is followed by the column of its middle
corner. -/
theorem finRotate_finProdFinEquiv_zero (j : Fin w.length) :
    finRotate (w.length * 3) (finProdFinEquiv (j, 0)) = finProdFinEquiv (j, 1) := by
  have hj := j.isLt
  ext
  rw [finRotate_val_of_lt _ (by rw [finProdFinEquiv_val_three]; simp; omega),
    finProdFinEquiv_val_three, finProdFinEquiv_val_three]
  simp
  omega

/-- Deleting a letter by one switch of `X`-markings and grid moves, for an arbitrary admissible
grid `G` of the longer word `w`. The switch exchanges the `X`-markings of the last two columns of
the deleted letter, and the switched grid `H` has the `O`-markings of `G`. Three erased corners,
one for the middle arc and one for each integer row of the deleted letter, together with row and
column commutations and cyclic permutations, relate `H` to an admissible grid of `w'`, hence to
every admissible grid of `w'`. -/
theorem IsAdmissibleWordGrid.exists_switch_movesTo (hd : IsLetterDeletion w w' j)
    (hocc : ∃ h : Fin w'.length, w'[h.val] = w[j.val])
    {G : GridDiagram (w.length * 3)} (hG : IsAdmissibleWordGrid w G) :
    ∃ H : GridDiagram (w.length * 3), Nonempty (XSwitchSequence G H 1) ∧ H.O = G.O ∧
      ∀ G' : GridDiagram (w'.length * 3), IsAdmissibleWordGrid w' G' → H.MovesTo G' := by
  classical
  obtain ⟨h', hh'⟩ := hocc
  set M := positiveRectilinearWordMatching w with hM
  have hhj : hd.letter h' ≠ j := hd.letter_ne h'
  have hhw : w[(hd.letter h').val] = w[j.val] := by rw [hd.getElem_letter]; exact hh'
  obtain ⟨F1, F2, F3, F4⟩ := positiveRectilinearWordMatching_letter_facts hhj hhw
  have hM10 : M (j, 1) ≠ (j, 0) := fun he => F1 (by rw [he])
  have hM21 : M (j, 2) ≠ (j, 1) := fun he => F3 (by rw [he])
  have hM0 : M (j, 0) = (j, 2) := positiveRectilinearWordMatching_middle w j
  have hMs2 : M.symm (j, 2) = (j, 0) := by rw [Equiv.symm_apply_eq, hM0]
  have hRinj : ∀ a b : Fin w.length × Fin 3, G.O (finProdFinEquiv a) = G.O (finProdFinEquiv b) →
      a = b := fun a b h => finProdFinEquiv.injective (G.O.toPerm.injective h)
  have hX : ∀ a, G.X (finProdFinEquiv a) = G.O (finProdFinEquiv (M.symm a)) := hG.X_eq
  have hBC := finRotate_finProdFinEquiv_one j
  have hAB := finRotate_finProdFinEquiv_zero j
  have h1 : G.O (finProdFinEquiv (j, 1)) ≠ G.X (finRotate _ (finProdFinEquiv (j, 1))) := by
    rw [hBC, hX, hMs2]
    intro he
    have := congrArg Prod.snd (hRinj _ _ he)
    simp at this
  have h2 : G.O (finRotate _ (finProdFinEquiv (j, 1))) ≠ G.X (finProdFinEquiv (j, 1)) := by
    rw [hBC, hX]
    intro he
    apply hM21
    rw [hRinj _ _ he, Equiv.apply_symm_apply]
  refine ⟨G.switchAdjacentX _ h1 h2, ⟨xSwitchSequence_switchAdjacentX G _ h1 h2⟩, rfl, ?_⟩
  intro G' hG'
  set H := G.switchAdjacentX _ h1 h2 with hH
  -- the three columns of the deleted letter
  set A : Fin (w.length * 3) := finProdFinEquiv (j, 0) with hA
  set B : Fin (w.length * 3) := finProdFinEquiv (j, 1) with hB
  set C : Fin (w.length * 3) := finProdFinEquiv (j, 2) with hC
  have hjl := j.isLt
  have hAv : A.val = 3 * j.val := by rw [hA, finProdFinEquiv_val_three]; simp
  have hBv : B.val = 3 * j.val + 1 := by rw [hB, finProdFinEquiv_val_three]; simp; omega
  have hCv : C.val = 3 * j.val + 2 := by rw [hC, finProdFinEquiv_val_three]; simp; omega
  have hcolv : ∀ a : Fin w.length × Fin 3, a.1 ≠ j →
      (finProdFinEquiv a).val ≠ 3 * j.val ∧ (finProdFinEquiv a).val ≠ 3 * j.val + 1 ∧
        (finProdFinEquiv a).val ≠ 3 * j.val + 2 := by
    intro a ha
    rw [Ne, Fin.ext_iff] at ha
    have := a.2.isLt
    rw [finProdFinEquiv_val_three]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have hBC' : B ≠ C := fun he => by rw [Fin.ext_iff, hBv, hCv] at he; omega
  -- the markings of the switched grid
  have hHO : ∀ K, H.O K = G.O K := fun K => rfl
  have hHX : ∀ K, H.X K = G.X (Equiv.swap B C K) := by
    intro K; rw [hH, GridDiagram.switchAdjacentX_X, GridState.swapColumns_apply, hBC]
  have hHXB : H.X B = G.O A := by
    rw [hHX, Equiv.swap_apply_left, hC, hX, hMs2]
  have hHXC : H.X C = G.O (finProdFinEquiv (M.symm (j, 1))) := by
    rw [hHX, Equiv.swap_apply_right, hB, hX]
  have hHXA : H.X A = G.O (finProdFinEquiv (M.symm (j, 0))) := by
    rw [hHX, Equiv.swap_apply_of_ne_of_ne (fun he => by rw [Fin.ext_iff, hAv, hBv] at he; omega)
      (fun he => by rw [Fin.ext_iff, hAv, hCv] at he; omega), hA, hX]
  have hHXK : ∀ K, K ≠ B → K ≠ C → H.X K = G.X K := fun K h1 h2 => by
    rw [hHX, Equiv.swap_apply_of_ne_of_ne h1 h2]
  -- transport to a size of the form `n + 3`
  have hlen := hd.length_eq
  have hN : w.length * 3 = w'.length * 3 + 3 := by rw [hlen]; ring
  have hmove₀ : H.MovesTo (H.castSize hN) := GridDiagram.movesTo_castSize hN H
  have R₀ := (GridDiagram.isMarkingRestriction_self H).castSize hN
  -- step one: the middle arc
  set c₁ : Fin (w'.length * 3 + 3) := ⟨3 * j.val, by omega⟩ with hc₁
  set d₁ : Fin (w'.length * 3 + 3) := ⟨3 * j.val + 1, by omega⟩ with hd₁
  have hκc₁ : (id ∘ Fin.cast hN.symm) c₁ = A := Fin.ext (by simp [hc₁, hAv])
  have hκd₁ : (id ∘ Fin.cast hN.symm) d₁ = B := Fin.ext (by simp [hd₁, hBv])
  have hp₂ : (j, 1) ≠ M.symm (j, 0) := fun he => hM10 (by rw [he, Equiv.apply_symm_apply])
  obtain ⟨G₁, ρ₁, hmove₁, R₁⟩ := R₀.exists_movesTo_eraseOCorner_of_ambient c₁ d₁ hκc₁ hκd₁
    (by rw [hHXB]; rfl)
    (by rw [hHXA]; exact fun he => hp₂ (hRinj _ _ he))
    (by
      intro K hK
      rw [← hAB, Grid.cIoo_finRotate_eq_empty] at hK
      simp at hK)
    (by
      intro K K' hK hKK'
      have hKA : K ≠ A := by
        rintro rfl
        rcases hK with h | h
        · exact lt_irrefl _ h.2
        · exact lt_irrefl _ h.1
      have hK'B : K' ≠ B := by
        rintro rfl
        rw [hHXB] at hKK'
        exact hKA (G.O.toPerm.injective hKK').symm
      exact Grid.noninterleaving_comm.mp (Grid.noninterleaving_of_eq_finRotate hAB.symm hKA hK'B))
  -- facts about the arcs
  set p₂ := M.symm (j, 0) with hp₂def
  set q₂ := M (j, 1) with hq₂def
  set p₃ := M.symm (j, 1) with hp₃def
  set q₃ := M (j, 2) with hq₃def
  set D₂ : Fin (w.length * 3) := finProdFinEquiv q₂ with hD₂
  set D₃ : Fin (w.length * 3) := finProdFinEquiv q₃ with hD₃
  have hD₂v := hcolv q₂ F1
  have hD₃v := hcolv q₃ F3
  have hD₂B : D₂ ≠ B := fun he => hD₂v.2.1 ((congrArg Fin.val he).trans hBv)
  have hD₂C : D₂ ≠ C := fun he => hD₂v.2.2 ((congrArg Fin.val he).trans hCv)
  have hD₃B : D₃ ≠ B := fun he => hD₃v.2.1 ((congrArg Fin.val he).trans hBv)
  have hD₃C : D₃ ≠ C := fun he => hD₃v.2.2 ((congrArg Fin.val he).trans hCv)
  have hD₃D₂ : D₃ ≠ D₂ := by
    intro he
    have h1 := M.injective (finProdFinEquiv.injective he)
    have := congrArg Prod.snd h1
    simp at this
  have hrow₀ : ∀ c : Fin 3, positiveRectilinearWordArcRow w (j, c) =
      ![(w[j.val].val : ℝ) + 1 / 2, (w[j.val].val : ℝ), (w[j.val].val : ℝ) + 1] c :=
    positiveRectilinearWordArcRow_eq w j
  have hrowp₂ : positiveRectilinearWordArcRow w p₂ = positiveRectilinearWordArcRow w (j, 1) := by
    rw [hp₂def, positiveRectilinearWordArcRow_matching_symm, hrow₀]; simp
  have hrowp₃ : positiveRectilinearWordArcRow w p₃ = positiveRectilinearWordArcRow w (j, 2) := by
    rw [hp₃def, positiveRectilinearWordArcRow_matching_symm, hrow₀]; simp
  have hrow12 :
      positiveRectilinearWordArcRow w (j, 1) ≠ positiveRectilinearWordArcRow w (j, 2) := by
    rw [hrow₀, hrow₀]; simp
  have hMXinv : ∀ (K' : Fin (w.length * 3)) (β : Fin w.length × Fin 3),
      G.X K' = G.O (finProdFinEquiv β) → K' = finProdFinEquiv (M β) := by
    intro K' β hK'
    obtain ⟨γ, rfl⟩ := finProdFinEquiv.surjective K'
    rw [hX] at hK'
    rw [← hRinj _ _ hK', Equiv.apply_symm_apply]
  -- step two: the lower continuation column
  set κ₁ := (id ∘ Fin.cast hN.symm) ∘ c₁.succAbove with hκ₁
  set X₁ := Function.update (⇑H.X) B (H.X A) with hX₁
  set c₂ : Fin (w'.length * 3 + 2) := ⟨3 * j.val, by omega⟩ with hc₂
  have hκc₂ : κ₁ c₂ = B := by
    apply Fin.ext
    simp only [hκ₁, Function.comp_apply, id, Fin.val_cast, Fin.val_succAbove, hc₂, hc₁, hBv]
    simp
  obtain ⟨d₂, hd₂⟩ : ∃ d₂, κ₁ d₂ = D₂ := by
    have hne : Fin.cast hN D₂ ≠ c₁ := by
      intro he
      exact hD₂v.1 (by simpa [hc₁, hD₂] using congrArg Fin.val he)
    obtain ⟨d, hd⟩ := Fin.exists_succAbove_eq hne
    refine ⟨d, ?_⟩
    simp only [hκ₁, Function.comp_apply, id, hd]
    exact Fin.ext rfl
  have hX₁B : X₁ B = G.O (finProdFinEquiv p₂) := by
    rw [hX₁, Function.update_self, hHXA]
  have hX₁K : ∀ K, K ≠ B → X₁ K = H.X K := fun K hK => by
    rw [hX₁, Function.update_of_ne hK]
  obtain ⟨G₂, ρ₂, hmove₂, R₂⟩ := R₁.exists_movesTo_eraseOCorner_of_ambient c₂ d₂ hκc₂ hd₂
    (by
      rw [hX₁K _ hD₂B, hHXK _ hD₂B hD₂C, hD₂, hX, hq₂def, Equiv.symm_apply_apply]
      rfl)
    (by
      rw [hX₁B]
      exact fun he => F2 (hRinj _ _ he).symm)
    (by
      intro K hK he
      rw [hX₁B] at he
      have hK2 := G.O.toPerm.injective he
      rw [hK2] at hK
      exact finProdFinEquiv_matching_symm_notMem_cIoo (j, 1) (j, 0)
        (by rw [finProdFinEquiv_val_three, finProdFinEquiv_val_three]; simp; omega)
        hrowp₂ hM10 hK)
    (by
      intro K K' hK hKK'
      obtain ⟨β, rfl⟩ := finProdFinEquiv.surjective K
      rw [hX₁B] at hK
      have hβ := hG.arcRow_eq_of_between hrowp₂ hK
      have hβp₂ : β ≠ p₂ := by
        rintro rfl
        rcases hK with h | h
        · exact lt_irrefl _ h.1
        · exact lt_irrefl _ h.2
      have hK'B : K' ≠ B := by
        rintro rfl
        rw [hX₁B] at hKK'
        exact hβp₂ (hRinj _ _ hKK').symm
      rw [hX₁K _ hK'B, hHX] at hKK'
      have hγ := hMXinv _ β hKK'
      have hK'C : K' ≠ C := by
        rintro rfl
        rw [Equiv.swap_apply_right, hB] at hγ
        have h1 : M β = (j, 1) := (finProdFinEquiv.injective hγ).symm
        have h2 : β = p₃ := by rw [hp₃def, ← h1, Equiv.symm_apply_apply]
        rw [h2, hrowp₃, hrowp₂] at hβ
        exact hrow12 hβ.symm
      rw [Equiv.swap_apply_of_ne_of_ne hK'B hK'C] at hγ
      rw [hγ, hD₂, hB, hq₂def]
      exact positiveRectilinearWord_noninterleaving_of_arcRow_eq w β (j, 1) (hβ.trans hrowp₂))
  -- step three: the upper continuation column
  set κ₂ := κ₁ ∘ c₂.succAbove with hκ₂
  set X₂ := Function.update X₁ D₂ (X₁ B) with hX₂
  set c₃ : Fin (w'.length * 3 + 1) := ⟨3 * j.val, by omega⟩ with hc₃
  have hκc₃ : κ₂ c₃ = C := by
    apply Fin.ext
    simp only [hκ₂, hκ₁, Function.comp_apply, id, Fin.val_cast, Fin.val_succAbove, hc₃, hc₂,
      hc₁, hCv]
    simp
  obtain ⟨d₃, hd₃⟩ : ∃ d₃, κ₂ d₃ = D₃ := by
    have hne : Fin.cast hN D₃ ≠ c₁ := by
      intro he
      exact hD₃v.1 (by simpa [hc₁, hD₃] using congrArg Fin.val he)
    obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq hne
    have hne' : y ≠ c₂ := by
      intro he
      rw [he] at hy
      exact hD₃v.2.1
        (by simpa [hc₂, hc₁, hD₃, Fin.val_succAbove] using (congrArg Fin.val hy).symm)
    obtain ⟨d, hd⟩ := Fin.exists_succAbove_eq hne'
    refine ⟨d, ?_⟩
    simp only [hκ₂, hκ₁, Function.comp_apply, id, hd, hy]
    exact Fin.ext rfl
  have hX₂C : X₂ C = G.O (finProdFinEquiv p₃) := by
    rw [hX₂, Function.update_of_ne (Ne.symm hD₂C), hX₁K _ (Ne.symm hBC'), hHXC]
  have hX₂K : ∀ K, K ≠ D₂ → K ≠ B → X₂ K = H.X K := fun K h1 h2 => by
    rw [hX₂, Function.update_of_ne h1, hX₁K _ h2]
  have hX₂D₂ : X₂ D₂ = G.O (finProdFinEquiv p₂) := by
    rw [hX₂, Function.update_self, hX₁B]
  have hX₂B : X₂ B = G.O (finProdFinEquiv p₂) := by
    rw [hX₂, Function.update_of_ne (Ne.symm hD₂B), hX₁B]
  have hrowp₂₃ : positiveRectilinearWordArcRow w p₂ ≠ positiveRectilinearWordArcRow w (j, 2) := by
    rw [hrowp₂]; exact hrow12
  obtain ⟨G₃, ρ₃, hmove₃, R₃⟩ := R₂.exists_movesTo_eraseOCorner_of_ambient c₃ d₃ hκc₃ hd₃
    (by
      rw [hX₂K _ hD₃D₂ hD₃B, hHXK _ hD₃B hD₃C, hD₃, hX, hq₃def, Equiv.symm_apply_apply]
      rfl)
    (by
      rw [hX₂C]
      exact fun he => F4 (hRinj _ _ he).symm)
    (by
      intro K hK he
      rw [hX₂C] at he
      have hK2 := G.O.toPerm.injective he
      rw [hK2] at hK
      exact finProdFinEquiv_matching_symm_notMem_cIoo (j, 2) (j, 1)
        (by rw [finProdFinEquiv_val_three, finProdFinEquiv_val_three]; simp; omega)
        hrowp₃ hM21 hK)
    (by
      intro K K' hK hKK'
      obtain ⟨β, rfl⟩ := finProdFinEquiv.surjective K
      rw [hX₂C] at hK
      have hβ := hG.arcRow_eq_of_between hrowp₃ hK
      have hβp₃ : β ≠ p₃ := by
        rintro rfl
        rcases hK with h | h
        · exact lt_irrefl _ h.1
        · exact lt_irrefl _ h.2
      have hβp₂ : β ≠ p₂ := by
        rintro rfl
        exact hrowp₂₃ (hβ.trans hrowp₃)
      have hK'D₂ : K' ≠ D₂ := by
        rintro rfl
        rw [hX₂D₂] at hKK'
        exact hβp₂ (hRinj _ _ hKK').symm
      have hK'B : K' ≠ B := by
        rintro rfl
        rw [hX₂B] at hKK'
        exact hβp₂ (hRinj _ _ hKK').symm
      rw [hX₂K _ hK'D₂ hK'B, hHX] at hKK'
      have hγ := hMXinv _ β hKK'
      have hK'C : K' ≠ C := by
        rintro rfl
        rw [Equiv.swap_apply_right, hB] at hγ
        have h1 : M β = (j, 1) := (finProdFinEquiv.injective hγ).symm
        have h2 : β = p₃ := by rw [hp₃def, ← h1, Equiv.symm_apply_apply]
        exact hβp₃ h2
      rw [Equiv.swap_apply_of_ne_of_ne hK'B hK'C] at hγ
      rw [hγ, hD₃, hC, hq₃def]
      exact positiveRectilinearWord_noninterleaving_of_arcRow_eq w β (j, 2) (hβ.trans hrowp₃))
  -- the final grid is admissible for the shorter word
  have hκ₃v : ∀ a : Fin w'.length × Fin 3, (κ₂ ∘ c₃.succAbove) (finProdFinEquiv a) =
      finProdFinEquiv (hd.corner a) := by
    intro a
    apply Fin.ext
    have ha := a.2.isLt
    have h1 := hd.letter_val a.1
    simp only [hκ₂, hκ₁, Function.comp_apply, id, Fin.val_cast, Fin.val_succAbove, hc₃, hc₂,
      hc₁, finProdFinEquiv_val_three, IsLetterDeletion.corner]
    rw [h1]
    split_ifs <;> omega
  have hG₃ : IsAdmissibleWordGrid w' G₃ := by
    constructor
    · intro a
      apply R₃.row_strictMono.injective
      rw [R₃.X_eq, R₃.O_eq, hκ₃v, hκ₃v, hd.corner_matching_symm]
      set p := M.symm (hd.corner a) with hp
      have hca : hd.corner a = M p := by rw [hp, Equiv.apply_symm_apply]
      by_cases hp1 : p = (j, 1)
      · rw [if_pos hp1]
        have h1 : finProdFinEquiv (hd.corner a) = D₂ := by rw [hca, hp1]
        rw [h1, Function.update_of_ne (Ne.symm hD₃D₂), hX₂D₂]
        rfl
      · rw [if_neg hp1]
        by_cases hp2 : p = (j, 2)
        · rw [if_pos hp2]
          have h1 : finProdFinEquiv (hd.corner a) = D₃ := by rw [hca, hp2]
          rw [h1, Function.update_self, hX₂C]
          rfl
        · rw [if_neg hp2]
          have hv := hcolv _ (hd.corner_fst_ne a)
          have hne3 : finProdFinEquiv (hd.corner a) ≠ D₃ := fun he =>
            hp2 (by rw [hp, finProdFinEquiv.injective he, hq₃def, Equiv.symm_apply_apply])
          have hne2 : finProdFinEquiv (hd.corner a) ≠ D₂ := fun he =>
            hp1 (by rw [hp, finProdFinEquiv.injective he, hq₂def, Equiv.symm_apply_apply])
          have hneB : finProdFinEquiv (hd.corner a) ≠ B := fun he =>
            hv.2.1 ((congrArg Fin.val he).trans hBv)
          have hneC : finProdFinEquiv (hd.corner a) ≠ C := fun he =>
            hv.2.2 ((congrArg Fin.val he).trans hCv)
          rw [Function.update_of_ne hne3, hX₂K _ hne2 hneB, hHXK _ hneB hneC, hX]
          rfl
    · intro a b hab
      rw [← R₃.row_strictMono.lt_iff_lt, R₃.O_eq, R₃.O_eq, hκ₃v, hκ₃v]
      apply hG.O_lt_of_arcRow_lt
      rw [hd.arcRow_corner, hd.arcRow_corner]
      exact hab
  exact hmove₀.trans (hmove₁.trans (hmove₂.trans (hmove₃.trans (hG₃.movesTo hG'))))

end LetterSwitch

set_option linter.unusedVariables false in
/-- Deleting a letter of a positive word, when every generator occurs in the shorter word: one
switch of adjacent `X`-markings in the selected grid of the longer word gives a grid related by
grid moves to the selected grid of the shorter word. The hypothesis `2 ≤ m` is not used. -/
theorem wordGrid_delete_letter {m : ℕ} (hm : 2 ≤ m) (u v : PositiveAdjacentWord m)
    (i : Fin (m - 1)) (huv : (u ++ v).toSigned.generatorIndices = Finset.univ) :
    ∃ H : GridDiagram ((u ++ i :: v).length * 3),
      Nonempty (XSwitchSequence (wordGrid (u ++ i :: v)) H 1) ∧ H.MovesTo (wordGrid (u ++ v)) := by
  have hd := isLetterDeletion_append u v i
  have hocc : ∃ h : Fin (u ++ v).length,
      (u ++ v)[h.val] = (u ++ i :: v)[(⟨u.length, by simp⟩ : Fin (u ++ i :: v).length).val] := by
    have hi : i ∈ (u ++ v).toSigned.generatorIndices := by rw [huv]; exact Finset.mem_univ i
    have hi' : i ∈ u ++ v := by
      simpa [SignedAdjacentWord.generatorIndices, PositiveAdjacentWord.toSigned] using hi
    obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hi'
    exact ⟨⟨k, hk⟩, by simp [hki]⟩
  obtain ⟨H, hs, -, hmv⟩ := (wordGrid_isAdmissible _).exists_switch_movesTo hd hocc
  exact ⟨H, hs, hmv _ (wordGrid_isAdmissible _)⟩

/-- Inserting a letter into a positive word, when every generator occurs in the shorter word: the
selected grid of the shorter word is related by grid moves to a grid from which one switch of
adjacent `X`-markings gives the selected grid of the longer word. -/
theorem wordGrid_insert_letter {m : ℕ} (hm : 2 ≤ m) (u v : PositiveAdjacentWord m)
    (i : Fin (m - 1)) (huv : (u ++ v).toSigned.generatorIndices = Finset.univ) :
    ∃ H : GridDiagram ((u ++ i :: v).length * 3),
      Nonempty (XSwitchSequence H (wordGrid (u ++ i :: v)) 1) ∧
        (wordGrid (u ++ v)).MovesTo H := by
  obtain ⟨H, hs, hmv⟩ := wordGrid_delete_letter hm u v i huv
  exact ⟨H, XSwitchSequence.nonempty_reverse_one hs, hmv.symm⟩

end OnLeConjecture.KnotTheory
