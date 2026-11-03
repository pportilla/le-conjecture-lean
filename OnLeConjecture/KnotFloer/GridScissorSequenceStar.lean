/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridScissorSequenceRows

/-!
# Evaluation of the star rule

This file evaluates the component permutation produced by the star rule `ScissorPhase.star` of
`GridScissorSequenceRows` (Section 9 of the written proof of Statement E,
`statement_E_complete_proof.tex`): after the center `c` has exchanged its `X` marking with the
leaves `z_1, …, z_k` in turn, the leaf `z_i` ends where `z_{i-1}` ended before (with `z_0 = c`),
and the center ends where the last leaf ended (`starPerm_getElem`, `starPerm_center`). Every other
column keeps its arc (`starPerm_of_not_mem`). The star rule is restated with hypotheses indexed by
the position of the leaf (`ScissorPhase.star_index`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

variable {n : ℕ}

/-! ### Values of the star permutation -/

theorem starPerm_of_not_mem (μ : Equiv.Perm (Fin n)) (c : Fin n) :
    ∀ (L : List (Fin n)) (d : Fin n), d ≠ c → d ∉ L → starPerm μ c L d = μ d := by
  intro L
  induction L generalizing μ with
  | nil => intro d _ _; simp [starPerm]
  | cons z L ih =>
    intro d hdc hdL
    rw [starPerm_cons, ih _ d hdc (fun h => hdL (List.mem_cons_of_mem _ h)),
      Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        (fun h => hdL (by rw [h]; exact List.mem_cons_self)) hdc]

theorem starPerm_center (μ : Equiv.Perm (Fin n)) (c : Fin n) :
    ∀ (L : List (Fin n)), L.Nodup → c ∉ L →
      starPerm μ c L c = μ ((c :: L).getLast (List.cons_ne_nil _ _)) := by
  intro L
  induction L generalizing μ with
  | nil => intro _ _; simp [starPerm]
  | cons z L ih =>
    intro hnd hc
    have hzL : z ∉ L := (List.nodup_cons.mp hnd).1
    have hcL : c ∉ L := fun h => hc (List.mem_cons_of_mem _ h)
    have hcz : c ≠ z := fun h => hc (h ▸ List.mem_cons_self)
    rw [starPerm_cons, ih _ (List.nodup_cons.mp hnd).2 hcL]
    by_cases hne : L = []
    · subst hne; simp [Equiv.swap_apply_right]
    · have hy : L.getLast hne ∈ L := List.getLast_mem hne
      have hyz : L.getLast hne ≠ z := fun h => hzL (by rw [← h]; exact hy)
      have hyc : L.getLast hne ≠ c := fun h => hcL (by rw [← h]; exact hy)
      rw [List.getLast_cons hne, List.getLast_cons (List.cons_ne_nil _ _), List.getLast_cons hne,
        Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hyz hyc]

theorem starPerm_getElem (μ : Equiv.Perm (Fin n)) (c : Fin n) :
    ∀ (L : List (Fin n)), L.Nodup → c ∉ L → ∀ (i : ℕ) (hi : i < L.length),
      starPerm μ c L L[i] = μ ((c :: L)[i]'(by simp; omega)) := by
  intro L
  induction L generalizing μ with
  | nil => intro _ _ i hi; simp at hi
  | cons z L ih =>
    intro hnd hc i hi
    have hzL : z ∉ L := (List.nodup_cons.mp hnd).1
    have hcL : c ∉ L := fun h => hc (List.mem_cons_of_mem _ h)
    have hcz : c ≠ z := fun h => hc (h ▸ List.mem_cons_self)
    rw [starPerm_cons]
    rcases i with _ | i
    · simp only [List.getElem_cons_zero]
      rw [starPerm_of_not_mem _ _ L z (Ne.symm hcz) hzL, Equiv.Perm.mul_apply,
        Equiv.swap_apply_left]
    · simp only [List.getElem_cons_succ]
      rw [ih _ (List.nodup_cons.mp hnd).2 hcL i (by simp at hi; omega)]
      rcases i with _ | i
      · simp [Equiv.swap_apply_right]
      · simp only [List.getElem_cons_succ, Equiv.Perm.mul_apply]
        have hm : L[i]'(by simp at hi; omega) ∈ L := List.getElem_mem _
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => hzL (by rw [← h]; exact hm))
          (fun h => hcL (by rw [← h]; exact hm))]

/-! ### The star rule with indexed hypotheses -/

/-- **The star rule**, with the hypotheses at the `i`-th leaf stated through the original
component permutation `μ`. -/
theorem ScissorPhase.star_index (c : Fin n) (sel : Fin n → Bool) (L : List (Fin n))
    (hLnd : L.Nodup) (hcL : c ∉ L) (μ : Equiv.Perm (Fin n)) (hμ : ∀ d, μ d ≠ d)
    (hfp : ∀ i ≤ L.length, ∀ d, starPerm μ c (L.take i) d ≠ d)
    (hni : ∀ (i : ℕ) (hi : i < L.length),
      NonintN c.val (μ L[i]).val (L[i]).val (μ ((c :: L)[i]'(by simp; omega))).val)
    {G : GridDiagram n} {k : ℕ} {E : List (Fin n × Fin n)} (m₁ m₂ : List (Fin n))
    (hnd : (m₁ ++ L.reverse ++ c :: m₂).Nodup) (hl : (m₁ ++ L.reverse ++ c :: m₂).length = n)
    (hnd' : (m₁ ++ c :: (L.reverse ++ m₂)).Nodup)
    (hl' : (m₁ ++ c :: (L.reverse ++ m₂)).length = n)
    (h : ScissorPhase G (phaseGrid (listPerm _ hnd hl) μ hμ) k E) :
    ScissorPhase G (phaseGrid (listPerm _ hnd' hl') (starPerm μ c L)
        (by have := hfp L.length le_rfl; rwa [List.take_length] at this))
      (k + starXCount sel L) (E ++ starEdges c sel L) := by
  refine ScissorPhase.star c sel L μ hμ ?_ ?_ m₁ m₂ hnd hl hnd' hl' _ h
  · intro L₁ L₂ z hL d
    have := hfp (L₁.length + 1) (by rw [hL]; simp) d
    have e : List.take (L₁.length + 1) (L₁ ++ z :: L₂) = L₁ ++ [z] := by
      rw [List.take_length_add_append]; rfl
    rwa [hL, e] at this
  · intro L₁ L₂ z hL
    have hi : L₁.length < L.length := by rw [hL]; simp
    have hz : L[L₁.length] = z := by simp [hL]
    have hnd₁ : L₁.Nodup := by rw [hL] at hLnd; exact (List.nodup_append.mp hLnd).1
    have hc₁ : c ∉ L₁ := fun h => hcL (by rw [hL]; exact List.mem_append_left _ h)
    have hz₁ : z ∉ L₁ := by
      rw [hL] at hLnd
      intro h
      exact (List.nodup_append.mp hLnd).2.2 z h z List.mem_cons_self rfl
    have hzc : z ≠ c := fun h => hcL (by rw [hL, h]; simp)
    rw [starPerm_of_not_mem μ c L₁ z hzc hz₁, starPerm_center μ c L₁ hnd₁ hc₁]
    have := hni L₁.length hi
    rw [hz] at this
    convert this using 3
    rw [List.getLast_eq_getElem]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [List.getElem_of_eq (show c :: L = (c :: L₁) ++ z :: L₂ by rw [hL]; rfl)]
    rw [List.getElem_append_left (by simp)]

end OnLeConjecture.KnotFloer.GridFull
