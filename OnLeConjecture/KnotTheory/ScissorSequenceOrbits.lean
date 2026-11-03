/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridComponents

/-!
# Orbits of matchings through strand labels

This file contains two pieces of permutation combinatorics used to count the components of the
scissor endpoint of Section 9 of the written proof of Statement E
(`statement_E_complete_proof.tex`, subsection "The explicit forest for O-switch selection").

**Orbits through labels** (`sameCycle_iff_of_wrapLabels`). Let `μ` be a permutation of a finite
type, `lab` a labelling of its points by the points of a type with a permutation `Ψ`, and `wrap` a
set of *wrap points*. Suppose that one step of `μ` from a point which is not a wrap point keeps
the label and increases a numerical key, that one step from a wrap point applies `Ψ` to the
label, and that a wrap point is determined by its label. Then two points lie in one orbit of `μ`
exactly when their labels lie in one orbit of `Ψ`. This abstracts the argument of
`positiveRectilinearWordMatching_sameCycle_iff` (`PositiveWordGridComponents`).

**The merged permutation** (`mergePerm`). For permutations `π l` of a type `β`, indexed by
`l : Fin r`, and a point `o`, the permutation `mergePerm π o` of `Fin r × β` sends `(l, y)` to
`(l, (π l)⁻¹ y)`, except that `(l, π l o)` goes to `(l + 1, o)`. It describes the strands of `r`
braid closures in which the strands through `o` are reconnected in a cycle. If every `π l` moves
`o` and has no other nontrivial cycle, the orbits of `mergePerm π o` are one orbit consisting of
the moved points and the singletons of the fixed points (`sameCycle_mergePerm_iff`), so its
number of orbits is one more than the number of fixed points (`orbitCount_mergePerm`). All
results are unconditional.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory

open Equiv Equiv.Perm TauCeti

/-! ### Orbits through labels -/

section Labels

variable {α β : Type*} [Finite α] [Finite β] (μ : Perm α) (Ψ : Perm β)
  (lab : α → β) (wrap : α → Prop)
  (key : α → ℕ)

omit [Finite β] in
/-- Following `μ` from any point reaches a wrap point with the same label. -/
theorem exists_pow_wrap_of_labels
    (hstep : ∀ a, ¬ wrap a → lab (μ a) = lab a ∧ key a < key (μ a)) (a : α) :
    ∃ k : ℕ, wrap ((μ ^ k) a) ∧ lab ((μ ^ k) a) = lab a := by
  by_contra hcon
  push Not at hcon
  -- no iterate is a wrap point, so the key increases along the whole orbit
  have hall : ∀ k : ℕ, ¬ wrap ((μ ^ k) a) ∧
      lab ((μ ^ k) a) = lab a ∧ key a + k ≤ key ((μ ^ k) a) := by
    intro k
    induction k with
    | zero => exact ⟨fun h => hcon 0 h rfl, rfl, by simp⟩
    | succ k ih =>
      obtain ⟨hw, hl, hkey⟩ := ih
      obtain ⟨hl', hk'⟩ := hstep _ hw
      have e : (μ ^ (k + 1)) a = μ ((μ ^ k) a) := by rw [pow_succ', Perm.mul_apply]
      refine ⟨fun h => hcon (k + 1) h (by rw [e, hl', hl]), by rw [e, hl', hl], ?_⟩
      rw [e]; omega
  obtain ⟨k, hk, hka⟩ := (isOfFinOrder_of_finite μ).exists_pow_eq_one
  have := (hall k).2.2
  rw [hka, Perm.one_apply] at this
  omega

/-- **Orbits through labels.** -/
theorem sameCycle_iff_of_wrapLabels
    (hstep : ∀ a, ¬ wrap a → lab (μ a) = lab a ∧ key a < key (μ a))
    (hwrap : ∀ a, wrap a → lab (μ a) = Ψ (lab a))
    (hinj : ∀ a b, wrap a → wrap b → lab a = lab b → a = b) (a b : α) :
    μ.SameCycle a b ↔ Ψ.SameCycle (lab a) (lab b) := by
  -- one step of `μ` keeps the label in one orbit of `Ψ`
  have hone : ∀ c, Ψ.SameCycle (lab c) (lab (μ c)) := by
    intro c
    by_cases hc : wrap c
    · rw [hwrap c hc]; exact sameCycle_apply_right.mpr (SameCycle.refl _ _)
    · rw [(hstep c hc).1]
  -- equal labels give one orbit
  have heq : ∀ x y, lab x = lab y → μ.SameCycle x y := by
    intro x y hxy
    obtain ⟨k, hk, hl⟩ := exists_pow_wrap_of_labels μ lab wrap key hstep x
    obtain ⟨k', hk', hl'⟩ := exists_pow_wrap_of_labels μ lab wrap key hstep y
    have hz := hinj _ _ hk hk' (by rw [hl, hl', hxy])
    have h1 : μ.SameCycle x ((μ ^ k) x) := sameCycle_pow_right.mpr (SameCycle.refl _ _)
    have h2 : μ.SameCycle y ((μ ^ k') y) := sameCycle_pow_right.mpr (SameCycle.refl _ _)
    rw [hz] at h1
    exact h1.trans h2.symm
  -- the orbit of `x` contains points with every forward iterate of its label
  have hfwd : ∀ x (k : ℕ), ∃ x', μ.SameCycle x x' ∧ lab x' = (Ψ ^ k) (lab x) := by
    intro x k
    induction k with
    | zero => exact ⟨x, SameCycle.refl _ _, by simp⟩
    | succ k ih =>
      obtain ⟨x', hx', hl⟩ := ih
      obtain ⟨j, hj, hlj⟩ := exists_pow_wrap_of_labels μ lab wrap key hstep x'
      refine ⟨μ ((μ ^ j) x'), hx'.trans (sameCycle_apply_right.mpr
        (sameCycle_pow_right.mpr (SameCycle.refl _ _))), ?_⟩
      rw [hwrap _ hj, hlj, hl, pow_succ', Perm.mul_apply]
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction k with
    | zero => exact SameCycle.refl _ _
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hone _)
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    obtain ⟨x', hx', hl⟩ := hfwd a k
    exact hx'.trans (heq x' b (by rw [hl, hk]))

end Labels

/-! ### The merged permutation -/

section Merge

variable {r : ℕ} {β : Type*} [DecidableEq β] [Finite β] (π : Fin r → Perm β) (o : β)

/-- The merged permutation: `(l, y) ↦ (l, (π l)⁻¹ y)`, except that `(l, π l o)` goes to
`(l + 1, o)`, cyclically in `l`. -/
def mergePerm : Perm (Fin r × β) where
  toFun a := if (π a.1).symm a.2 = o then (finRotate r a.1, o) else (a.1, (π a.1).symm a.2)
  invFun a := if a.2 = o then ((finRotate r).symm a.1, π ((finRotate r).symm a.1) o)
    else (a.1, π a.1 a.2)
  left_inv a := by
    rcases a with ⟨l, y⟩
    by_cases h : (π l).symm y = o
    · simp only [h, if_true, Equiv.symm_apply_apply]
      rw [← h, Equiv.apply_symm_apply]
    · simp only [h, if_false, Equiv.apply_symm_apply]
  right_inv a := by
    rcases a with ⟨l, y⟩
    by_cases h : y = o
    · simp only [h, if_true, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · simp only [h, if_false, Equiv.symm_apply_apply]

omit [Finite β] in
theorem mergePerm_apply_of_ne {l : Fin r} {y : β} (h : (π l).symm y ≠ o) :
    mergePerm π o (l, y) = (l, (π l).symm y) := by
  simp [mergePerm, h]

omit [Finite β] in
theorem mergePerm_apply_of_eq {l : Fin r} {y : β} (h : (π l).symm y = o) :
    mergePerm π o (l, y) = (finRotate r l, o) := by
  simp [mergePerm, h]

omit [Finite β] in
theorem mergePerm_apply_apply (l : Fin r) (x : β) :
    mergePerm π o (l, π l x) = if x = o then (finRotate r l, o) else (l, x) := by
  by_cases h : x = o
  · rw [if_pos h, mergePerm_apply_of_eq]; simp [h]
  · rw [if_neg h, mergePerm_apply_of_ne]; · simp
    simpa using h

/-- A point of `Fin r × β` is moved when `π l` moves its second coordinate. -/
def MergeMoved (a : Fin r × β) : Prop := π a.1 a.2 ≠ a.2

variable {π o}

omit [Finite β] in
theorem mergePerm_fixed (hmo : ∀ l, π l o ≠ o) {a : Fin r × β} (ha : ¬ MergeMoved π a) :
    mergePerm π o a = a := by
  rcases a with ⟨l, y⟩
  simp only [MergeMoved, ne_eq, not_not] at ha
  have hy : (π l).symm y = y := by rw [Equiv.symm_apply_eq, ha]
  have hyo : y ≠ o := fun h => hmo l (by rw [← h, ha])
  rw [mergePerm_apply_of_ne _ _ (by rw [hy]; exact hyo), hy]

/-- A moved point lies in the orbit of `(l + 1, o)`. -/
theorem sameCycle_mergePerm_succ (hcyc : ∀ l y, π l y ≠ y → (π l).SameCycle y o)
    {l : Fin r} {y : β} (hy : π l y ≠ y) :
    (mergePerm π o).SameCycle (l, y) (finRotate r l, o) := by
  classical
  have hy' : (π l)⁻¹.SameCycle y (π l o) := by
    have h1 := hcyc l y hy
    have h2 : (π l).SameCycle o (π l o) := sameCycle_apply_right.mpr (SameCycle.refl _ _)
    exact sameCycle_inv.mpr (h1.trans h2)
  have hex : ∃ k : ℕ, ((π l)⁻¹ ^ k) y = π l o := hy'.exists_nat_pow_eq
  set k := Nat.find hex with hk
  have hkspec : ((π l)⁻¹ ^ k) y = π l o := Nat.find_spec hex
  have hlt : ∀ i < k, ((π l)⁻¹ ^ i) y ≠ π l o := fun i hi => Nat.find_min hex hi
  have hiter : ∀ i ≤ k, (mergePerm π o ^ i) (l, y) = (l, ((π l)⁻¹ ^ i) y) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [pow_succ', Perm.mul_apply, ih (by omega), mergePerm_apply_of_ne]
      · rw [pow_succ', Perm.mul_apply]; rfl
      · intro he
        apply hlt i (by omega)
        rw [← he]
        simp
  have h1 : (mergePerm π o).SameCycle (l, y) (l, π l o) := ⟨k, by
    rw [← hkspec, zpow_natCast, hiter k le_rfl]⟩
  have h2 : mergePerm π o (l, π l o) = (finRotate r l, o) :=
    mergePerm_apply_of_eq _ _ (by simp)
  exact h1.trans ⟨1, by simp [h2]⟩

omit [DecidableEq β] [Finite β] in
/-- Every point of `Fin r` is reached from every other one by a power of `finRotate r`. -/
theorem exists_finRotate_pow_eq (l l' : Fin r) : ∃ k : ℕ, (finRotate r ^ k) l = l' := by
  rcases r with _ | _ | r
  · exact l.elim0
  · exact ⟨0, Fin.ext (by have := l.isLt; have := l'.isLt; simp)⟩
  · exact isCycle_finRotate.exists_pow_eq (Grid.finRotate_ne_self (by omega) l)
      (Grid.finRotate_ne_self (by omega) l')

/-- The points `(l, o)` lie in one orbit. -/
theorem sameCycle_mergePerm_base (hmo : ∀ l, π l o ≠ o)
    (hcyc : ∀ l y, π l y ≠ y → (π l).SameCycle y o) (l l' : Fin r) :
    (mergePerm π o).SameCycle (l, o) (l', o) := by
  have hstep : ∀ l : Fin r, (mergePerm π o).SameCycle (l, o) (finRotate r l, o) :=
    fun l => sameCycle_mergePerm_succ hcyc (hmo l)
  have hpow : ∀ k : ℕ, (mergePerm π o).SameCycle (l, o) ((finRotate r ^ k) l, o) := by
    intro k
    induction k with
    | zero => exact SameCycle.refl _ _
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hstep _)
  obtain ⟨k, hk⟩ := exists_finRotate_pow_eq l l'
  rw [← hk]
  exact hpow k

/-- **Orbits of the merged permutation.** If every `π l` moves `o` and has no nontrivial cycle
other than the cycle of `o`, two points lie in one orbit exactly when they are equal or both
moved. -/
theorem sameCycle_mergePerm_iff (hmo : ∀ l, π l o ≠ o)
    (hcyc : ∀ l y, π l y ≠ y → (π l).SameCycle y o) (a b : Fin r × β) :
    (mergePerm π o).SameCycle a b ↔ a = b ∨ (MergeMoved π a ∧ MergeMoved π b) := by
  -- an unmoved point is fixed, so its orbit is a singleton
  have hsing : ∀ a b, ¬ MergeMoved π a → (mergePerm π o).SameCycle a b → a = b := by
    intro a b ha h
    obtain ⟨k, rfl⟩ := h
    have hfix : ∀ k : ℤ, (mergePerm π o ^ k) a = a := fun k =>
      (zpow_apply_eq_self_of_apply_eq_self (mergePerm_fixed hmo ha) k)
    exact (hfix k).symm
  constructor
  · intro h
    by_cases ha : MergeMoved π a
    · by_cases hb : MergeMoved π b
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inl (hsing b a hb h.symm).symm
    · exact Or.inl (hsing a b ha h)
  · rintro (rfl | ⟨ha, hb⟩)
    · exact SameCycle.refl _ _
    · rcases a with ⟨l, y⟩
      rcases b with ⟨l', y'⟩
      exact ((sameCycle_mergePerm_succ hcyc ha).trans
        (sameCycle_mergePerm_base hmo hcyc _ _)).trans (sameCycle_mergePerm_succ hcyc hb).symm

/-- **Number of orbits of the merged permutation.** -/
theorem orbitCount_mergePerm (hr : 0 < r) (hmo : ∀ l, π l o ≠ o)
    (hcyc : ∀ l y, π l y ≠ y → (π l).SameCycle y o) :
    orbitCount (mergePerm π o) = Nat.card {a : Fin r × β // ¬ MergeMoved π a} + 1 := by
  classical
  let F : Fin r × β → Option {a : Fin r × β // ¬ MergeMoved π a} := fun a =>
    if h : MergeMoved π a then none else some ⟨a, h⟩
  have hF : Function.Surjective F := by
    intro x
    rcases x with _ | ⟨a, ha⟩
    · exact ⟨(⟨0, hr⟩, o), by simp [F, MergeMoved, hmo]⟩
    · exact ⟨a, by simp [F, ha]⟩
  have hiff : ∀ a b, (mergePerm π o).SameCycle a b ↔
      (1 : Perm (Option {a : Fin r × β // ¬ MergeMoved π a})).SameCycle (F a) (F b) := by
    intro a b
    rw [sameCycle_mergePerm_iff hmo hcyc, sameCycle_one]
    by_cases ha : MergeMoved π a <;> by_cases hb : MergeMoved π b <;>
      simp [F, ha, hb, Subtype.ext_iff] <;> aesop
  rw [orbitCount_eq_of_sameCycle_iff F hF hiff, orbitCount_one, Finite.card_option]

end Merge

end OnLeConjecture.KnotTheory
