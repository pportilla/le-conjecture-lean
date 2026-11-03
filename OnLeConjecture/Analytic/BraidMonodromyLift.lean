/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyCoxeter

/-!
# A cluster braid together with static far strands

In the local factors of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`, subsection "Local factors, without a generic-Morse
projection") the sheets of a local cluster move in a vertical strip while the remaining sheets
stay to the right of it. This module computes the path word of the simplest such configuration:
a cluster of `d` strands, followed by `k` static strands lying to the right of a vertical line
that the cluster never crosses.

* `liftSigned h w`: a signed word on `d` strands placed on the first `d` of `S ≥ d` strands. It
  respects `SignedBraidEquiv` and `SignedBraidConj`.
* `layeredWord_staticLow`: if the strands at the last `k` positions are lower than the strands at
  the first `d` positions, the layered word is the lifted layered word of the first `d` positions
  followed by a word `staticWord` in the letters `σ_i`, `i ≥ d`, which depends only on the heights
  of the last `k` positions.
* `localWord_block`: for configurations whose first `d` points lie to the left of a vertical line,
  whose last `k` points lie to the right of it and agree, the local word is the lifted local word
  of the first `d` points.
* `IsPathWord.block`: the path word of the cluster followed by static far strands is the lifted
  path word of the cluster. `IsRepresentedByPositiveWord.block_signedBraidConj`: if the cluster is
  represented by the positive word `w`, every path word of the whole family is conjugate to
  `liftPositiveWord w`. `cyclicShiftPath_block_signedBraidConj` specializes this to the Coxeter
  model of an ordinary ramification point.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.KnotTheory

open SignedAdjacentWord

/-! ### Lifted signed words -/

/-- A signed word on `d` strands placed on the first `d` of `S ≥ d` strands. -/
def liftSigned {d S : ℕ} (h : d ≤ S) (w : SignedAdjacentWord d) : SignedAdjacentWord S :=
  w.map fun a => ((Fin.castLE (by omega) a.1 : Fin (S - 1)), a.2)

section Lift

variable {d S : ℕ} (h : d ≤ S)

@[simp] theorem liftSigned_nil : liftSigned h ([] : SignedAdjacentWord d) = [] := rfl

@[simp] theorem liftSigned_append (u v : SignedAdjacentWord d) :
    liftSigned h (u ++ v) = liftSigned h u ++ liftSigned h v := by
  simp [liftSigned]

theorem liftSigned_inv (w : SignedAdjacentWord d) :
    liftSigned h (inv w) = inv (liftSigned h w) := by
  simp [liftSigned, inv, List.map_reverse]

theorem liftSigned_toSigned (w : PositiveAdjacentWord d) :
    liftSigned h w.toSigned = liftPositiveWord h w := by
  simp [liftSigned, liftPositiveWord, PositiveAdjacentWord.toSigned]

theorem liftSigned_self (h' : d ≤ d) (w : SignedAdjacentWord d) : liftSigned h' w = w := by
  simp [liftSigned]

theorem liftWordSucc_liftSigned (w : SignedAdjacentWord d) :
    liftWordSucc S (liftSigned h w) = liftSigned (Nat.le_succ_of_le h) w := by
  simp [liftWordSucc, liftSigned, Function.comp_def]

theorem mem_liftSigned {w : SignedAdjacentWord d} {b : Fin (S - 1) × ℤˣ}
    (hb : b ∈ liftSigned h w) : b.1.val + 2 ≤ d := by
  simp only [liftSigned, List.mem_map] at hb
  obtain ⟨a, -, rfl⟩ := hb
  have := a.1.isLt
  simp only [Fin.val_castLE]
  omega

theorem SignedBraidStep.liftSigned {u v : SignedAdjacentWord d} (hs : SignedBraidStep u v) :
    SignedBraidStep (OnLeConjecture.KnotTheory.liftSigned h u)
      (OnLeConjecture.KnotTheory.liftSigned h v) := by
  cases hs with
  | cancel u v i e =>
    simpa [OnLeConjecture.KnotTheory.liftSigned] using
      SignedBraidStep.cancel (OnLeConjecture.KnotTheory.liftSigned h u)
        (OnLeConjecture.KnotTheory.liftSigned h v)
        (Fin.castLE (by omega) i : Fin (S - 1)) e
  | far u v i j e f hf =>
    simpa [OnLeConjecture.KnotTheory.liftSigned] using
      SignedBraidStep.far (OnLeConjecture.KnotTheory.liftSigned h u)
        (OnLeConjecture.KnotTheory.liftSigned h v) (Fin.castLE (by omega) i : Fin (S - 1))
        (Fin.castLE (by omega) j : Fin (S - 1)) e f (by simpa using hf)
  | braid u v i j hj =>
    simpa [OnLeConjecture.KnotTheory.liftSigned] using
      SignedBraidStep.braid (OnLeConjecture.KnotTheory.liftSigned h u)
        (OnLeConjecture.KnotTheory.liftSigned h v) (Fin.castLE (by omega) i : Fin (S - 1))
        (Fin.castLE (by omega) j : Fin (S - 1)) (by simpa using hj)

theorem SignedBraidEquiv.liftSigned {u v : SignedAdjacentWord d} (he : SignedBraidEquiv u v) :
    SignedBraidEquiv (OnLeConjecture.KnotTheory.liftSigned h u)
      (OnLeConjecture.KnotTheory.liftSigned h v) := by
  induction he with
  | rel _ _ hs => exact SignedBraidEquiv.of_step (hs.liftSigned h)
  | refl => exact SignedBraidEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem SignedBraidConj.liftSigned {u v : SignedAdjacentWord d} (hc : SignedBraidConj u v) :
    SignedBraidConj (OnLeConjecture.KnotTheory.liftSigned h u)
      (OnLeConjecture.KnotTheory.liftSigned h v) := by
  induction hc with
  | rel _ _ hs =>
    cases hs with
    | step hs => exact (SignedBraidEquiv.of_step (hs.liftSigned h)).toConj
    | rotate w a =>
      have := SignedBraidConj.rotate (OnLeConjecture.KnotTheory.liftSigned h w)
        (OnLeConjecture.KnotTheory.liftSigned h [a])
      simpa [OnLeConjecture.KnotTheory.liftSigned] using this
  | refl => exact SignedBraidConj.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Lift

/-- Words whose letters are pairwise far apart commute. -/
theorem SignedBraidEquiv.far_comm {m : ℕ} :
    ∀ (u v : SignedAdjacentWord m),
      (∀ a ∈ u, ∀ b ∈ v, a.1.val + 2 ≤ b.1.val ∨ b.1.val + 2 ≤ a.1.val) →
      SignedBraidEquiv (u ++ v) (v ++ u)
  | [], v, _ => by simpa using SignedBraidEquiv.refl v
  | a :: u, v, h => by
    have ih := far_comm u v fun a' ha' b hb => h a' (List.mem_cons_of_mem _ ha') b hb
    have h1 : SignedBraidEquiv (a :: (u ++ v)) (a :: (v ++ u)) := ih.cons a
    have h2 : SignedBraidEquiv (a :: v) (v ++ [a]) :=
      SignedBraidEquiv.far_past a v fun b hb => h a (List.mem_cons_self ..) b hb
    have h3 := h2.append_right u
    simpa [List.append_assoc] using h1.trans h3

/-! ### Layered words with low static strands -/

section StaticLow

variable {α : Type*} [LinearOrder α]

/-- The word of the last `k` strands in the recursion of the layered word, when they are lower
than the first `d` strands. -/
noncomputable def staticWord (d : ℕ) : (k : ℕ) → (Fin k → α) → SignedAdjacentWord (d + k)
  | 0, _ => []
  | k + 1, cs => liftWordSucc (d + k) (staticWord d k (cs ∘ (lowestPos cs).succAbove)) ++
      descRun (d + k) (d + k) (d + (lowestPos cs).val)

theorem mem_staticWord (d : ℕ) : ∀ (k : ℕ) (cs : Fin k → α) {b : Fin (d + k - 1) × ℤˣ},
    b ∈ staticWord d k cs → d ≤ b.1.val
  | 0, _, b, hb => by simp [staticWord] at hb
  | k + 1, cs, b, hb => by
    rw [staticWord] at hb
    rcases List.mem_append.mp hb with hb | hb
    · simp only [liftWordSucc, List.mem_map] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      have := mem_staticWord d k _ ha
      simpa using this
    · have := (mem_descRun hb).1
      omega

/-- The last `k` positions carry strands lower than the first `d` positions. -/
def StaticLow (d k : ℕ) (c : Fin (d + k) → α) : Prop :=
  ∀ (i : Fin d) (j : Fin k), c (Fin.natAdd d j) < c (Fin.castAdd k i)

theorem succAbove_natAdd_castAdd {d k : ℕ} (p : Fin (k + 1)) (i : Fin d) :
    (Fin.natAdd d p).succAbove (Fin.castAdd k i) = Fin.castAdd (k + 1) i := by
  apply Fin.ext
  rw [val_succAbove]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [if_pos (by omega)]

theorem succAbove_natAdd_natAdd {d k : ℕ} (p : Fin (k + 1)) (j : Fin k) :
    (Fin.natAdd d p).succAbove (Fin.natAdd d j) = Fin.natAdd d (p.succAbove j) := by
  apply Fin.ext
  simp only [val_succAbove, Fin.val_natAdd]
  split_ifs <;> omega

/-- **Layered words with low static strands.** -/
theorem layeredWord_staticLow (d : ℕ) : ∀ (k : ℕ) (c : Fin (d + k) → α), Injective c →
    StaticLow d k c →
    layeredWord (d + k) c = liftSigned (Nat.le_add_right d k) (layeredWord d (c ∘ Fin.castAdd k)) ++
      staticWord d k (c ∘ Fin.natAdd d)
  | 0, c, _, _ => by
    simp only [staticWord, List.append_nil]
    rw [liftSigned_self]
    congr 1
  | k + 1, c, hc, hlow => by
    set cs := c ∘ Fin.natAdd d with hcs
    have hpos : lowestPos c = Fin.natAdd d (lowestPos cs) := by
      apply lowestPos_eq hc
      intro q
      refine Fin.addCases (m := d) (n := k + 1) (fun i => ?_) (fun j => ?_) q
      · exact (hlow i _).le
      · exact lowestPos_le cs j
    have hc' : Injective (c ∘ (lowestPos c).succAbove) := hc.comp Fin.succAbove_right_injective
    have hlow' : StaticLow d k (c ∘ (lowestPos c).succAbove) := by
      intro i j
      simp only [Function.comp_apply, hpos, succAbove_natAdd_castAdd, succAbove_natAdd_natAdd]
      exact hlow i _
    have ih := layeredWord_staticLow d k _ hc' hlow'
    have e1 : (c ∘ (lowestPos c).succAbove) ∘ Fin.castAdd k = c ∘ Fin.castAdd (k + 1) := by
      funext i; simp [hpos, succAbove_natAdd_castAdd]
    have e2 : (c ∘ (lowestPos c).succAbove) ∘ Fin.natAdd d = cs ∘ (lowestPos cs).succAbove := by
      funext j; simp [hpos, hcs, succAbove_natAdd_natAdd]
    rw [e1, e2] at ih
    change layeredWord (d + k + 1) c = _
    rw [layeredWord_succ, ih, liftWordSucc_append, liftWordSucc_liftSigned, hpos]
    simp only [staticWord, List.append_assoc, Fin.val_natAdd]

/-- **Transition words with low static strands.** If two height sequences have low static
strands with the same heights, their transition word is the lifted transition word of their
first `d` positions. -/
theorem layeredTransition_staticLow {d k : ℕ} {c₁ c₂ : Fin (d + k) → α} (h₁ : Injective c₁)
    (h₂ : Injective c₂) (hl₁ : StaticLow d k c₁) (hl₂ : StaticLow d k c₂)
    (hs : c₁ ∘ Fin.natAdd d = c₂ ∘ Fin.natAdd d) :
    SignedBraidEquiv (inv (layeredWord (d + k) c₁) ++ layeredWord (d + k) c₂)
      (liftSigned (Nat.le_add_right d k)
        (inv (layeredWord d (c₁ ∘ Fin.castAdd k)) ++ layeredWord d (c₂ ∘ Fin.castAdd k))) := by
  rw [layeredWord_staticLow d k c₁ h₁ hl₁, layeredWord_staticLow d k c₂ h₂ hl₂, hs, inv_append,
    liftSigned_append, liftSigned_inv]
  set T := staticWord d k (c₂ ∘ Fin.natAdd d)
  set X := inv (liftSigned (Nat.le_add_right d k) (layeredWord d (c₁ ∘ Fin.castAdd k)))
  set Y := liftSigned (Nat.le_add_right d k) (layeredWord d (c₂ ∘ Fin.castAdd k))
  have hX : ∀ b ∈ X, b.1.val + 2 ≤ d := fun b hb => by
    simp only [X, inv, List.mem_reverse, List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have := mem_liftSigned _ ha
    exact this
  have hY : ∀ b ∈ Y, b.1.val + 2 ≤ d := fun b hb => mem_liftSigned _ hb
  have hT : ∀ b ∈ T, d ≤ b.1.val := fun b hb => mem_staticWord d k _ hb
  have hTi : ∀ b ∈ inv T, d ≤ b.1.val := fun b hb => by
    simp only [inv, List.mem_reverse, List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact hT a ha
  have hcomm : SignedBraidEquiv (inv T ++ (X ++ Y)) ((X ++ Y) ++ inv T) :=
    SignedBraidEquiv.far_comm _ _ fun a ha b hb => by
      have := hTi a ha
      rcases List.mem_append.mp hb with hb | hb
      · have := hX b hb; omega
      · have := hY b hb; omega
  have h1 := hcomm.append_right T
  have h2 : SignedBraidEquiv ((X ++ Y) ++ inv T ++ T) (X ++ Y) := by
    simpa using SignedBraidEquiv.cancel_inv_mid' (X ++ Y) T []
  have h3 := h1.trans h2
  simp only [List.append_assoc] at h3 ⊢
  exact h3

end StaticLow

end OnLeConjecture.KnotTheory

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

/-! ### Block configurations -/

/-- The permutation of `Fin (d + k)` acting by `σc` on the first `d` and by `σs` on the last
`k` elements. -/
def blockPerm {d k : ℕ} (σc : Equiv.Perm (Fin d)) (σs : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (d + k)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr σc σs)).trans finSumFinEquiv

@[simp] theorem blockPerm_castAdd {d k : ℕ} (σc : Equiv.Perm (Fin d)) (σs : Equiv.Perm (Fin k))
    (i : Fin d) : blockPerm σc σs (Fin.castAdd k i) = Fin.castAdd k (σc i) := by
  simp [blockPerm]

@[simp] theorem blockPerm_natAdd {d k : ℕ} (σc : Equiv.Perm (Fin d)) (σs : Equiv.Perm (Fin k))
    (j : Fin k) : blockPerm σc σs (Fin.natAdd d j) = Fin.natAdd d (σs j) := by
  simp [blockPerm]

@[simp] theorem blockPerm_symm_castAdd {d k : ℕ} (σc : Equiv.Perm (Fin d))
    (σs : Equiv.Perm (Fin k)) (i : Fin d) :
    (blockPerm σc σs).symm (Fin.castAdd k i) = Fin.castAdd k (σc.symm i) := by
  rw [Equiv.symm_apply_eq]; simp

@[simp] theorem blockPerm_symm_natAdd {d k : ℕ} (σc : Equiv.Perm (Fin d))
    (σs : Equiv.Perm (Fin k)) (j : Fin k) :
    (blockPerm σc σs).symm (Fin.natAdd d j) = Fin.natAdd d (σs.symm j) := by
  rw [Equiv.symm_apply_eq]; simp

/-- A configuration whose first `d` points lie to the left of the line `Re = x₀` and whose last
`k` points lie to the right of it. -/
def IsBlockConfig (d k : ℕ) (x₀ : ℝ) (x : Fin (d + k) → ℂ) : Prop :=
  (∀ i : Fin d, (x (Fin.castAdd k i)).re < x₀) ∧ ∀ j : Fin k, x₀ < (x (Fin.natAdd d j)).re

/-- The lexicographic order of a block configuration lists the first `d` points first. -/
theorem configSort_block {d k : ℕ} {x₀ : ℝ} {x : Fin (d + k) → ℂ} (hx : Injective x)
    (hb : IsBlockConfig d k x₀ x) :
    configSort x = blockPerm (configSort (x ∘ Fin.castAdd k)) (configSort (x ∘ Fin.natAdd d)) := by
  symm
  apply eq_configSort hx
  have hc := configSort_strictMono (hx.comp (Fin.castAdd_injective d k))
  have hs := configSort_strictMono (hx.comp (Fin.natAdd_injective k d))
  intro p q hpq
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left i' =>
      simp only [blockPerm_castAdd]
      refine hc ?_
      rw [Fin.lt_def] at hpq ⊢
      simpa using hpq
    | right j' =>
      simp only [blockPerm_castAdd, blockPerm_natAdd]
      rw [lexKey_lt_iff]
      left
      exact (hb.1 _).trans (hb.2 _)
  | right j =>
    induction q using Fin.addCases with
    | left i' =>
      exfalso
      rw [Fin.lt_def] at hpq
      simp at hpq
      omega
    | right j' =>
      simp only [blockPerm_natAdd]
      refine hs ?_
      rw [Fin.lt_def] at hpq ⊢
      simpa using hpq

/-- Any heights on `Fin m`: the transition congruence of layered words. -/
theorem layeredTransition_congr_any {α : Type*} [LinearOrder α] {m : ℕ} {c c' : Fin m → α}
    (hc : Injective c) (hc' : Injective c') (π ρ : Equiv.Perm (Fin m))
    (hagree : ∀ k l, π.symm k < π.symm l → ρ.symm l < ρ.symm k → (c k < c l ↔ c' k < c' l)) :
    SignedBraidEquiv (inv (layeredWord m (c ∘ ⇑π)) ++ layeredWord m (c ∘ ⇑ρ))
      (inv (layeredWord m (c' ∘ ⇑π)) ++ layeredWord m (c' ∘ ⇑ρ)) := by
  cases m with
  | zero => simp only [layeredWord]; exact SignedBraidEquiv.refl _
  | succ n => exact layeredTransition_congr hc hc' π ρ hagree

/-- **Local words of block configurations.** If `x` and `y` are block configurations for the same
line with the same last `k` points, and `z` is injective, the local word from `x` to `y` with
center `z` is the lifted local word of the first `d` points. -/
theorem localWord_block {d k : ℕ} {x₀ : ℝ} {z x y : Fin (d + k) → ℂ} (hz : Injective z)
    (hx : Injective x) (hy : Injective y) (hbx : IsBlockConfig d k x₀ x)
    (hby : IsBlockConfig d k x₀ y) (hs : x ∘ Fin.natAdd d = y ∘ Fin.natAdd d) :
    SignedBraidEquiv (localWord z x y)
      (liftSigned (Nat.le_add_right d k)
        (localWord (z ∘ Fin.castAdd k) (x ∘ Fin.castAdd k) (y ∘ Fin.castAdd k))) := by
  classical
  -- New heights: the static strands below all the cluster strands.
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, ∀ i : Fin d, m₀ ≤ (z (Fin.castAdd k i)).im := by
    rcases isEmpty_or_nonempty (Fin d) with hd | hd
    · exact ⟨0, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i : Fin d => (z (Fin.castAdd k i)).im
      exact ⟨_, hi₀⟩
  let c' : Fin (d + k) → Lex (ℝ × ℝ) := Fin.addCases (fun i => heightKey (z (Fin.castAdd k i)))
    fun j => toLex (m₀ - 1 - j.val, 0)
  have hc'L : ∀ i, c' (Fin.castAdd k i) = heightKey (z (Fin.castAdd k i)) := fun i => by
    simp [c']
  have hc'R : ∀ j, c' (Fin.natAdd d j) = toLex (m₀ - 1 - j.val, 0) := fun j => by simp [c']
  have hlowc : ∀ i j, c' (Fin.natAdd d j) < c' (Fin.castAdd k i) := fun i j => by
    rw [hc'L, hc'R, heightKey, Prod.Lex.toLex_lt_toLex]
    left
    have := hm₀ i
    have : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    linarith
  have hc'inj : Injective c' := by
    intro p q hpq
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left i' =>
        rw [hc'L, hc'L] at hpq
        exact congrArg _ ((Fin.castAdd_injective d k) (hz (heightKey_injective hpq)))
      | right j' => exact absurd hpq (hlowc i j').ne'
    | right j =>
      induction q using Fin.addCases with
      | left i' => exact absurd hpq (hlowc i' j).ne
      | right j' =>
        rw [hc'R, hc'R] at hpq
        have := congrArg (fun p => (ofLex p).1) hpq
        simp only [ofLex_toLex, sub_right_inj] at this
        exact congrArg _ (Fin.ext (by exact_mod_cast this))
  have hπ := configSort_block hx hbx
  have hρ := configSort_block hy hby
  have hsρ : configSort (x ∘ Fin.natAdd d) = configSort (y ∘ Fin.natAdd d) := by rw [hs]
  -- Static labels keep their positions; the inverted pairs are cluster pairs.
  have hagree : ∀ p q, (configSort x).symm p < (configSort x).symm q →
      (configSort y).symm q < (configSort y).symm p →
      ((heightKey ∘ z) p < (heightKey ∘ z) q ↔ c' p < c' q) := by
    intro p q h1 h2
    rw [hπ] at h1
    rw [hρ] at h2
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left i' => simp [hc'L]
      | right j' =>
        exfalso
        simp only [blockPerm_symm_castAdd, blockPerm_symm_natAdd, Fin.lt_def, Fin.val_natAdd,
          Fin.val_castAdd] at h2
        have := ((configSort (y ∘ Fin.castAdd k)).symm i).isLt
        omega
    | right j =>
      exfalso
      induction q using Fin.addCases with
      | left i' =>
        simp only [blockPerm_symm_castAdd, blockPerm_symm_natAdd, Fin.lt_def, Fin.val_natAdd,
          Fin.val_castAdd] at h1
        have := ((configSort (x ∘ Fin.castAdd k)).symm i').isLt
        omega
      | right j' =>
        rw [← hsρ] at h2
        simp only [blockPerm_symm_natAdd, Fin.lt_def, Fin.val_natAdd] at h1 h2
        omega
  have h1 := layeredTransition_congr_any (heightKey_injective.comp hz) hc'inj (configSort x)
    (configSort y) hagree
  -- The new heights have low static strands, with equal static parts.
  have hl₁ : StaticLow d k (c' ∘ ⇑(configSort x)) := fun i j => by
    simp only [Function.comp_apply, hπ, blockPerm_castAdd, blockPerm_natAdd]
    exact hlowc _ _
  have hl₂ : StaticLow d k (c' ∘ ⇑(configSort y)) := fun i j => by
    simp only [Function.comp_apply, hρ, blockPerm_castAdd, blockPerm_natAdd]
    exact hlowc _ _
  have hst : (c' ∘ ⇑(configSort x)) ∘ Fin.natAdd d = (c' ∘ ⇑(configSort y)) ∘ Fin.natAdd d := by
    funext j
    simp only [Function.comp_apply, hπ, hρ, blockPerm_natAdd, hsρ]
  have h2 := layeredTransition_staticLow (hc'inj.comp (configSort x).injective)
    (hc'inj.comp (configSort y).injective) hl₁ hl₂ hst
  have e1 : (c' ∘ ⇑(configSort x)) ∘ Fin.castAdd k = heightKey ∘ (z ∘ Fin.castAdd k) ∘
      ⇑(configSort (x ∘ Fin.castAdd k)) := by
    funext i
    simp only [Function.comp_apply, hπ, blockPerm_castAdd, hc'L]
  have e2 : (c' ∘ ⇑(configSort y)) ∘ Fin.castAdd k = heightKey ∘ (z ∘ Fin.castAdd k) ∘
      ⇑(configSort (y ∘ Fin.castAdd k)) := by
    funext i
    simp only [Function.comp_apply, hρ, blockPerm_castAdd, hc'L]
  rw [e1, e2] at h2
  unfold localWord
  exact h1.trans h2

/-! ### Path words of a cluster with static far strands -/

/-- The family of a cluster `Kc` of `d` strands followed by `k` static strands at the points
`s j`. -/
def blockFamily {d k : ℕ} (Kc : Fin d → ℝ → ℂ) (s : Fin k → ℂ) : Fin (d + k) → ℝ → ℂ :=
  Fin.addCases (fun i t => Kc i t) fun j _ => s j

@[simp] theorem blockFamily_castAdd {d k : ℕ} (Kc : Fin d → ℝ → ℂ) (s : Fin k → ℂ) (i : Fin d)
    (t : ℝ) : blockFamily Kc s (Fin.castAdd k i) t = Kc i t := by
  simp [blockFamily]

@[simp] theorem blockFamily_natAdd {d k : ℕ} (Kc : Fin d → ℝ → ℂ) (s : Fin k → ℂ) (j : Fin k)
    (t : ℝ) : blockFamily Kc s (Fin.natAdd d j) t = s j := by
  simp [blockFamily]

theorem blockFamily_injective {d k : ℕ} {Kc : Fin d → ℝ → ℂ} {s : Fin k → ℂ} {x₀ t : ℝ}
    (hc : Injective fun i => Kc i t) (hs : Injective s) (hleft : ∀ i, (Kc i t).re < x₀)
    (hright : ∀ j, x₀ < (s j).re) : Injective fun p => blockFamily Kc s p t := by
  intro p q hpq
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left i' =>
      simp only [blockFamily_castAdd] at hpq
      exact congrArg _ (hc hpq)
    | right j' =>
      simp only [blockFamily_castAdd, blockFamily_natAdd] at hpq
      have := hleft i; have := hright j'; rw [hpq] at *; linarith
  | right j =>
    induction q using Fin.addCases with
    | left i' =>
      simp only [blockFamily_castAdd, blockFamily_natAdd] at hpq
      have := hleft i'; have := hright j; rw [← hpq] at *; linarith
    | right j' =>
      simp only [blockFamily_natAdd] at hpq
      exact congrArg _ (hs hpq)

/-- **The path word of a cluster with static far strands.** Let the cluster `Kc` of `d` strands
stay to the left of the line `Re = x₀` during `[u, v]`, and let the `k` static points `s j` lie to
the right of it. If `W` is a path word of the cluster, the lifted word is a path word of the whole
family. -/
theorem IsPathWord.block {d k : ℕ} {Kc : Fin d → ℝ → ℂ} {s : Fin k → ℂ} {x₀ u v : ℝ}
    (hinj : ∀ t ∈ Icc u v, Injective fun i => Kc i t) (hs : Injective s)
    (hleft : ∀ i, ∀ t ∈ Icc u v, (Kc i t).re < x₀) (hright : ∀ j, x₀ < (s j).re)
    {W : SignedAdjacentWord d} (hW : IsPathWord Kc u v W) :
    IsPathWord (blockFamily Kc s) u v (liftSigned (Nat.le_add_right d k) W) := by
  obtain ⟨δ, hδ, hW⟩ := hW
  refine ⟨δ, hδ, fun t N P => ?_⟩
  have hblock : ∀ a ≤ N, IsBlockConfig d k x₀ fun p => blockFamily Kc s p (t a) := fun a ha =>
    ⟨fun i => by simpa using hleft i _ (P.mem_Icc ha), fun j => by simpa using hright j⟩
  have hinjK : ∀ a ≤ N, Injective fun p => blockFamily Kc s p (t a) := fun a ha =>
    blockFamily_injective (hinj _ (P.mem_Icc ha)) hs (fun i => hleft i _ (P.mem_Icc ha)) hright
  have key : ∀ M ≤ N, SignedBraidEquiv (chainWord (fun a p => blockFamily Kc s p (t a)) M)
      (liftSigned (Nat.le_add_right d k) (chainWord (fun a i => Kc i (t a)) M)) := by
    intro M
    induction M with
    | zero => intro _; exact SignedBraidEquiv.refl _
    | succ M ih =>
      intro hM
      rw [chainWord_succ, chainWord_succ, liftSigned_append]
      refine (ih (by omega)).append ?_
      have := localWord_block (hinjK M (by omega)) (hinjK M (by omega)) (hinjK (M + 1) hM)
        (hblock M (by omega)) (hblock (M + 1) hM) (by funext j; simp)
      simpa [Function.comp_def] using this
  exact (key N le_rfl).trans ((hW t N P).liftSigned _)

/-- **A represented cluster with static far strands.** If the cluster `Kc` of `d` strands,
staying to the left of the line `Re = x₀`, is represented through closed braids by the positive
word `w`, then every path word of the cluster followed by `k` static points to the right of the
line is conjugate to `w` placed on the first `d` strands. -/
theorem IsRepresentedByPositiveWord.block_signedBraidConj {d k : ℕ} {Kc : Fin d → ℝ → ℂ}
    {s : Fin k → ℂ} {x₀ u v : ℝ} {w : PositiveAdjacentWord d}
    (hrep : IsRepresentedByPositiveWord Kc u v w) (hs : Injective s)
    (hleft : ∀ i, ∀ t ∈ Icc u v, (Kc i t).re < x₀) (hright : ∀ j, x₀ < (s j).re)
    {W : SignedAdjacentWord (d + k)} (hW : IsPathWord (blockFamily Kc s) u v W) :
    SignedBraidConj W (liftPositiveWord (Nat.le_add_right d k) w) := by
  obtain ⟨Wc, hWc, hconj⟩ := hrep.exists_isPathWord_signedBraidConj
  have hinj : ∀ t ∈ Icc u v, Injective fun i => Kc i t := by
    obtain ⟨π, hiso⟩ := hrep
    intro t ht a b hab
    have := hiso.left.injective t ht
      (show Kc (π (π.symm a)) t = Kc (π (π.symm b)) t by simpa using hab)
    simpa using congrArg π this
  have hlt : u < v := by
    obtain ⟨π, hiso⟩ := hrep
    exact hiso.left.lt
  have h1 := hWc.block hinj hs hleft hright
  have h2 := hW.unique hlt h1
  rw [← liftSigned_toSigned]
  exact h2.toConj.trans (hconj.liftSigned _)

/-- **The Coxeter model with static far strands.** The cyclic shift of `d ≥ 2` points on the unit
circle, followed by `k` static points to the right of the line `Re = 3 / 2`, has every path word
on `[0, 1]` conjugate to the Coxeter word placed on the first `d` strands. -/
theorem cyclicShiftPath_block_signedBraidConj {d k : ℕ} (hd : 2 ≤ d) {s : Fin k → ℂ}
    (hs : Injective s) (hright : ∀ j, 3 / 2 < (s j).re) {W : SignedAdjacentWord (d + k)}
    (hW : IsPathWord (blockFamily (cyclicShiftPath d) s) 0 1 W) :
    SignedBraidConj W (liftPositiveWord (Nat.le_add_right d k) (coxeterWord d)) := by
  refine (isRepresented_cyclicShiftPath hd).block_signedBraidConj hs (x₀ := 3 / 2)
    (fun i t _ => ?_) hright hW
  have : (cyclicShiftPath d i t).re ≤ 1 := by
    unfold cyclicShiftPath
    rw [Complex.exp_ofReal_mul_I_re]
    exact Real.cos_le_one _
  linarith

end OnLeConjecture.Analytic
