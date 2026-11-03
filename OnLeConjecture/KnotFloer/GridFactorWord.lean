/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFactorArcPairs
public import OnLeConjecture.KnotTheory.PositiveWordGridAdmissibleDeletion
public import OnLeConjecture.KnotTheory.PositiveWordBraidMoviePlan

/-!
# The corner grading of admissible word grids

Let `w` be a positive word of length `ℓ` on `m` strands, and let `G` be an admissible grid of `w`
(`IsAdmissibleWordGrid w G`), for instance the selected grid `wordGrid w`. The arcs of `G` are
indexed by their starting corners `a = (j, c)`, in the native column `3 j + c`. The arc leaving
`a` ends at the corner `M a` of the matching `positiveRectilinearWordMatching w`, it has the
unperturbed height `h a`, and its grid row is `R a = G.O (3 j + c)`.

By the arc pair formula (`alexanderTwoℤ_cornerShift_add_eq_sum_arcPairWeight`), with the rows
reindexed by corners,

`2 A(x₀) + (3ℓ - 1) = ∑_{R a < R b} Ψ(a, b)`,
`Ψ(a, b) = 2 [col (M a) ≤ col b] - [col a < col b] - [col (M a) < col (M b)]`.

Admissibility gives `R a < R b` whenever `h a < h b`, so the sum splits into the pairs of
different heights and the pairs of equal heights.

* **Different heights.** The heights arriving at the corners of a letter are the heights leaving
  them, rotated by one corner. Hence the contributions of two different letters cancel, and each
  letter contributes `2` on its own (`sum_heightPart`). The total is `2ℓ`.
* **Equal heights.** Two arcs of the same height do not interleave, so `Ψ(a, b) = Ψ(b, a)`
  (`cornerPairWeight_symm`). The order of rows inside a height class therefore does not matter,
  and the pairs may be ordered by their starting columns (`sum_tiePart_eq_column`). Pairs of
  half-integer arcs contribute `0`. At an integer height with `k` occurrences the contribution is
  `k - 1`. When every generator occurs, every strand rank occurs, and the total is `2ℓ - m`.

Consequently `2 A(x₀) = ℓ - m + 1`. Every integer height has exactly one wrapping arc, so
`wrapNumber G = m`. The corner lower bound then gives Theorem 5.8 of the factor lower bound proof:
`ν_G(t) ≥ (t/2) (ℓ - m + 1)/2` for `0 ≤ t ≤ 2/m`.

The written proof uses the preferred tie order of Definition 5.1 and its move equivalence
(Lemma 5.2) with the selected grid. The symmetry of `Ψ` makes the argument valid for every
admissible grid, so no move sequence is used.

## Main results

* `alexanderTwoℤ_cornerShift_admissible`: `2 A(x₀) = ℓ - m + 1`.
* `wrapNumber_admissible`: `wrapNumber G = m`.
* `admissible_spectralThreshold_lower`: Theorem 5.8 for every admissible grid.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

variable {m : ℕ} (w : PositiveAdjacentWord m)

/-- The weight `Ψ(a, b)` of an ordered pair of arcs of a word, indexed by their starting
corners. -/
def cornerPairWeight (a b : Fin w.length × Fin 3) : ℤ :=
  2 * (if finProdFinEquiv (positiveRectilinearWordMatching w a) ≤ finProdFinEquiv b then 1
    else 0) -
    (if finProdFinEquiv a < finProdFinEquiv b then 1 else 0) -
      (if finProdFinEquiv (positiveRectilinearWordMatching w a) <
          finProdFinEquiv (positiveRectilinearWordMatching w b) then 1 else 0)

/-! ### Heights at the corners of a letter -/

private theorem finRotate_three_zero : finRotate 3 0 = 1 := by decide
private theorem finRotate_three_one : finRotate 3 1 = 2 := by decide
private theorem finRotate_three_two : finRotate 3 2 = 0 := by decide

/-- The height arriving at a corner is the height leaving the next corner of its letter. -/
theorem arcRow_matching_symm_eq_rotate (a : Fin w.length × Fin 3) :
    positiveRectilinearWordArcRow w ((positiveRectilinearWordMatching w).symm a) =
      positiveRectilinearWordArcRow w (a.1, finRotate 3 a.2) := by
  obtain ⟨j, c⟩ := a
  rw [positiveRectilinearWordArcRow_matching_symm, positiveRectilinearWordArcRow_eq]
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue, finRotate_three_zero]
    rfl
  · simp only [Fin.mk_one, Fin.isValue, finRotate_three_one]
    rfl
  · simp only [Fin.reduceFinMk, Fin.isValue, finRotate_three_two]
    rfl

/-- At no corner do the arriving and the leaving arc have the same height. -/
theorem arcRow_matching_symm_ne (a : Fin w.length × Fin 3) :
    positiveRectilinearWordArcRow w ((positiveRectilinearWordMatching w).symm a) ≠
      positiveRectilinearWordArcRow w a := by
  obtain ⟨j, c⟩ := a
  rw [positiveRectilinearWordArcRow_matching_symm, positiveRectilinearWordArcRow_eq]
  fin_cases c <;> norm_num

/-! ### Rows indexed by corners -/

section Admissible

variable {w} {G : GridDiagram (w.length * 3)} (hG : IsAdmissibleWordGrid w G)
include hG

theorem admissible_X_symm (a : Fin w.length × Fin 3) :
    G.X.toPerm.symm (G.O (finProdFinEquiv a)) =
      finProdFinEquiv (positiveRectilinearWordMatching w a) := by
  rw [Equiv.symm_apply_eq]
  exact (hG.X_finProdFinEquiv_matching a).symm

/-- The arc pair sum with rows indexed by the starting corners of their arcs. -/
theorem sum_arcPairWeight_admissible :
    ∑ α : Fin (w.length * 3), ∑ β : Fin (w.length * 3),
        (if α < β then arcPairWeight G α β else 0) =
      ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
        if G.O (finProdFinEquiv a) < G.O (finProdFinEquiv b) then cornerPairWeight w a b
          else 0 := by
  symm
  refine Fintype.sum_equiv (finProdFinEquiv.trans G.O.toPerm) _ _ fun a => ?_
  refine Fintype.sum_equiv (finProdFinEquiv.trans G.O.toPerm) _ _ fun b => ?_
  change _ = if G.O (finProdFinEquiv a) < G.O (finProdFinEquiv b) then
    arcPairWeight G (G.O (finProdFinEquiv a)) (G.O (finProdFinEquiv b)) else 0
  unfold arcPairWeight cornerPairWeight
  rw [admissible_X_symm hG, admissible_X_symm hG]
  simp only [Equiv.symm_apply_apply]

/-- Admissibility splits the row order into the height order and the order inside a height
class. -/
theorem ite_rowOrder_split (a b : Fin w.length × Fin 3) (x : ℤ) :
    (if G.O (finProdFinEquiv a) < G.O (finProdFinEquiv b) then x else 0) =
      (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b then x else 0) +
        (if positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b ∧
            G.O (finProdFinEquiv a) < G.O (finProdFinEquiv b) then x else 0) := by
  rcases lt_trichotomy (positiveRectilinearWordArcRow w a) (positiveRectilinearWordArcRow w b)
    with h | h | h
  · rw [if_pos (hG.O_lt_of_arcRow_lt a b h), if_pos h, if_neg (fun h' => (ne_of_lt h) h'.1),
      add_zero]
  · have hn : ¬ positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b := by
      rw [h]
      exact lt_irrefl _
    rw [if_neg hn, zero_add]
    exact if_congr (and_iff_right h).symm rfl rfl
  · have h' := hG.O_lt_of_arcRow_lt b a h
    rw [if_neg (not_lt.mpr h'.le), if_neg (not_lt.mpr h.le),
      if_neg (fun h'' => (ne_of_gt h) h''.1), add_zero]

end Admissible

/-! ### Pairs of arcs of different heights -/

/-- The integrand of the height part after the arriving corners have been reindexed. -/
def heightIntegrand (a b : Fin w.length × Fin 3) : ℤ :=
  2 * (if positiveRectilinearWordArcRow w (a.1, finRotate 3 a.2) <
        positiveRectilinearWordArcRow w b ∧ finProdFinEquiv a ≤ finProdFinEquiv b then 1 else 0) -
    (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b ∧
        finProdFinEquiv a < finProdFinEquiv b then 1 else 0) -
    (if positiveRectilinearWordArcRow w (a.1, finRotate 3 a.2) <
        positiveRectilinearWordArcRow w (b.1, finRotate 3 b.2) ∧
        finProdFinEquiv a < finProdFinEquiv b then 1 else 0)

/-- The contribution of an ordered pair of letters to the height part. -/
def heightBlock (j j' : Fin w.length) : ℤ :=
  ∑ u : Fin 3, ∑ v : Fin 3, heightIntegrand w (j, u) (j', v)

private theorem col_le_iff (j j' : Fin w.length) (u v : Fin 3) :
    finProdFinEquiv (j, u) ≤ finProdFinEquiv (j', v) ↔ u.val + 3 * j.val ≤ v.val + 3 * j'.val := by
  rw [Fin.le_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]

private theorem col_lt_iff (j j' : Fin w.length) (u v : Fin 3) :
    finProdFinEquiv (j, u) < finProdFinEquiv (j', v) ↔ u.val + 3 * j.val < v.val + 3 * j'.val := by
  rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]

/-- **One letter.** The pairs of corners of one letter contribute `2`. -/
theorem heightBlock_self (j : Fin w.length) : heightBlock w j j = 2 := by
  unfold heightBlock heightIntegrand
  simp only [col_le_iff, col_lt_iff, Fin.sum_univ_three, finRotate_three_zero,
    finRotate_three_one, finRotate_three_two, positiveRectilinearWordArcRow_eq]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **Two letters.** The pairs formed by an earlier and a later letter cancel. -/
theorem heightBlock_of_lt {j j' : Fin w.length} (h : j < j') : heightBlock w j j' = 0 := by
  have hjj : j.val < j'.val := h
  have c1 : ∀ u v : Fin 3, u.val + 3 * j.val ≤ v.val + 3 * j'.val := fun u v => by
    have := u.isLt; omega
  have c2 : ∀ u v : Fin 3, u.val + 3 * j.val < v.val + 3 * j'.val := fun u v => by
    have := u.isLt; omega
  unfold heightBlock heightIntegrand
  simp only [col_le_iff, col_lt_iff, c1, c2, and_true]
  set f : Fin 3 → Fin 3 → ℤ := fun u v =>
    if positiveRectilinearWordArcRow w (j, u) < positiveRectilinearWordArcRow w (j', v) then 1
      else 0 with hf
  have e1 : ∑ u : Fin 3, ∑ v : Fin 3, (if positiveRectilinearWordArcRow w (j, finRotate 3 u) <
      positiveRectilinearWordArcRow w (j', v) then (1 : ℤ) else 0) = ∑ u, ∑ v, f u v :=
    Equiv.sum_comp (finRotate 3) (fun u => ∑ v, f u v)
  have e3 : ∑ u : Fin 3, ∑ v : Fin 3, (if positiveRectilinearWordArcRow w (j, finRotate 3 u) <
      positiveRectilinearWordArcRow w (j', finRotate 3 v) then (1 : ℤ) else 0) =
        ∑ u, ∑ v, f u v := by
    rw [← Equiv.sum_comp (finRotate 3) (fun u => ∑ v, f u v)]
    exact Finset.sum_congr rfl fun u _ => Equiv.sum_comp (finRotate 3) (fun v => f _ v)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e1, e3]
  ring

/-- Pairs formed by a later and an earlier letter do not occur. -/
theorem heightBlock_of_gt {j j' : Fin w.length} (h : j' < j) : heightBlock w j j' = 0 := by
  have hjj : j'.val < j.val := h
  have c1 : ∀ u v : Fin 3, ¬ u.val + 3 * j.val ≤ v.val + 3 * j'.val := fun u v => by
    have := v.isLt; omega
  have c2 : ∀ u v : Fin 3, ¬ u.val + 3 * j.val < v.val + 3 * j'.val := fun u v => by
    have := v.isLt; omega
  unfold heightBlock heightIntegrand
  simp [col_le_iff, col_lt_iff, c1, c2]

theorem heightBlock_eq (j j' : Fin w.length) :
    heightBlock w j j' = if j = j' then 2 else 0 := by
  rcases lt_trichotomy j j' with h | rfl | h
  · rw [heightBlock_of_lt w h, if_neg (ne_of_lt h)]
  · rw [heightBlock_self, if_pos rfl]
  · rw [heightBlock_of_gt w h, if_neg (ne_of_gt h)]

/-- The height part of the corner grading. -/
theorem sum_heightIntegrand :
    ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3, heightIntegrand w a b =
      2 * w.length := by
  have h : ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3, heightIntegrand w a b =
      ∑ j : Fin w.length, ∑ j' : Fin w.length, heightBlock w j j' := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rfl
  rw [h]
  simp only [heightBlock_eq, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The height part.** The pairs of arcs of different heights contribute `2ℓ`. -/
theorem sum_heightPart :
    ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
        (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b then
          cornerPairWeight w a b else 0) = 2 * w.length := by
  set M := positiveRectilinearWordMatching w with hM
  have hsplit : ∀ a b : Fin w.length × Fin 3,
      (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b then
        cornerPairWeight w a b else 0) =
      2 * (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b ∧
          finProdFinEquiv (M a) ≤ finProdFinEquiv b then 1 else 0) -
        (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b ∧
          finProdFinEquiv a < finProdFinEquiv b then 1 else 0) -
        (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b ∧
          finProdFinEquiv (M a) < finProdFinEquiv (M b) then 1 else 0) := by
    intro a b
    by_cases hab : positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b
    · simp only [hab, true_and, if_true, cornerPairWeight, hM]
    · simp [hab]
  have hT1 : ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
      (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b ∧
        finProdFinEquiv (M a) ≤ finProdFinEquiv b then (1 : ℤ) else 0) =
      ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
        (if positiveRectilinearWordArcRow w (a.1, finRotate 3 a.2) <
          positiveRectilinearWordArcRow w b ∧ finProdFinEquiv a ≤ finProdFinEquiv b then 1
            else 0) := by
    refine Fintype.sum_equiv M _ _ fun a => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← arcRow_matching_symm_eq_rotate, hM, Equiv.symm_apply_apply]
  have hT3 : ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
      (if positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b ∧
        finProdFinEquiv (M a) < finProdFinEquiv (M b) then (1 : ℤ) else 0) =
      ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
        (if positiveRectilinearWordArcRow w (a.1, finRotate 3 a.2) <
          positiveRectilinearWordArcRow w (b.1, finRotate 3 b.2) ∧
            finProdFinEquiv a < finProdFinEquiv b then 1 else 0) := by
    refine Fintype.sum_equiv M _ _ fun a => ?_
    refine Fintype.sum_equiv M _ _ fun b => ?_
    rw [← arcRow_matching_symm_eq_rotate, ← arcRow_matching_symm_eq_rotate, hM,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hT1, hT3, ← sum_heightIntegrand w]
  unfold heightIntegrand
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-! ### Pairs of arcs of equal heights -/

/-- **Symmetry on height classes.** Two different arcs of the same height do not interleave, and
their four endpoints are distinct, so their weight does not depend on their order. -/
theorem cornerPairWeight_symm {a b : Fin w.length × Fin 3}
    (hab : positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b) (hne : a ≠ b) :
    cornerPairWeight w a b = cornerPairWeight w b a := by
  have hN := positiveRectilinearWord_noninterleaving_of_arcRow_eq w a b hab
  set M := positiveRectilinearWordMatching w with hM
  have hMab : M a ≠ b := by
    intro he
    have h1 : M.symm b = a := by rw [← he, Equiv.symm_apply_apply]
    exact arcRow_matching_symm_ne w b (by rw [← hM, h1, hab])
  have hMba : M b ≠ a := by
    intro he
    have h1 : M.symm a = b := by rw [← he, Equiv.symm_apply_apply]
    exact arcRow_matching_symm_ne w a (by rw [← hM, h1, hab])
  have hMaa : M a ≠ a := by
    intro he
    have h1 : M.symm a = a := by
      conv_lhs => rw [← he]
      exact Equiv.symm_apply_apply _ _
    exact arcRow_matching_symm_ne w a (by rw [← hM, h1])
  have hMbb : M b ≠ b := by
    intro he
    have h1 : M.symm b = b := by
      conv_lhs => rw [← he]
      exact Equiv.symm_apply_apply _ _
    exact arcRow_matching_symm_ne w b (by rw [← hM, h1])
  have hinj := (finProdFinEquiv : Fin w.length × Fin 3 ≃ Fin (w.length * 3)).injective
  have d1 : (finProdFinEquiv a).val ≠ (finProdFinEquiv b).val := fun h => hne (hinj (Fin.ext h))
  have d2 : (finProdFinEquiv (M a)).val ≠ (finProdFinEquiv (M b)).val := fun h =>
    hne (M.injective (hinj (Fin.ext h)))
  have d3 : (finProdFinEquiv (M a)).val ≠ (finProdFinEquiv b).val := fun h =>
    hMab (hinj (Fin.ext h))
  have d4 : (finProdFinEquiv (M b)).val ≠ (finProdFinEquiv a).val := fun h =>
    hMba (hinj (Fin.ext h))
  have d5 : (finProdFinEquiv (M a)).val ≠ (finProdFinEquiv a).val := fun h =>
    hMaa (hinj (Fin.ext h))
  have d6 : (finProdFinEquiv (M b)).val ≠ (finProdFinEquiv b).val := fun h =>
    hMbb (hinj (Fin.ext h))
  unfold cornerPairWeight
  rw [← hM]
  unfold Grid.Noninterleaving at hN
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hN
  simp only [Fin.lt_def, Fin.le_def]
  generalize (finProdFinEquiv a).val = pa at *
  generalize (finProdFinEquiv b).val = pb at *
  generalize (finProdFinEquiv (M a)).val = qa at *
  generalize (finProdFinEquiv (M b)).val = qb at *
  split_ifs at hN ⊢ <;> omega

/-- **Changing the order inside the classes of a symmetric relation.** If `f` is symmetric on
the pairs of different points related by `E`, then summing `f` over the related pairs ordered by
one strict total order gives the same result as ordering them by another. -/
theorem sum_ite_and_order_eq {ι : Type*} [Fintype ι] (E : ι → ι → Prop) [DecidableRel E]
    (f : ι → ι → ℤ) (hE : ∀ a b, E a b → E b a)
    (hf : ∀ a b, E a b → a ≠ b → f a b = f b a)
    (r s : ι → ι → Prop) [DecidableRel r] [DecidableRel s]
    (hr : ∀ a b, a ≠ b → (r a b ↔ ¬ r b a)) (hr0 : ∀ a, ¬ r a a)
    (hs : ∀ a b, a ≠ b → (s a b ↔ ¬ s b a)) (hs0 : ∀ a, ¬ s a a) :
    ∑ a, ∑ b, (if E a b ∧ r a b then f a b else 0) =
      ∑ a, ∑ b, (if E a b ∧ s a b then f a b else 0) := by
  classical
  have key : ∀ (t : ι → ι → Prop) [DecidableRel t], (∀ a b, a ≠ b → (t a b ↔ ¬ t b a)) →
      (∀ a, ¬ t a a) →
      2 * ∑ a, ∑ b, (if E a b ∧ t a b then f a b else 0) =
        ∑ a, ∑ b, (if E a b ∧ a ≠ b then f a b else 0) := by
    intro t _ ht ht0
    have hswap : ∑ a, ∑ b, (if E a b ∧ t a b then f a b else 0) =
        ∑ a, ∑ b, (if E a b ∧ t b a then f a b else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h : E b a ∧ t b a
      · have hba : b ≠ a := fun e => ht0 a (by rw [← e] at h ⊢; exact h.2)
        rw [if_pos h, if_pos ⟨hE b a h.1, h.2⟩, hf b a h.1 hba]
      · rw [if_neg h, if_neg (fun h' => h ⟨hE a b h'.1, h'.2⟩)]
    rw [two_mul]
    nth_rewrite 2 [hswap]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      simp [ht0]
    · have h1 := ht a b hab
      by_cases hE' : E a b
      · by_cases htab : t a b
        · have htba : ¬ t b a := h1.mp htab
          simp [hE', htab, htba, hab]
        · have htba : t b a := by
            by_contra hc
            exact htab (h1.mpr hc)
          simp [hE', htab, htba, hab]
      · simp [hE']
  have h1 := key r hr hr0
  have h2 := key s hs hs0
  linarith

section Admissible

variable {w} {G : GridDiagram (w.length * 3)} (hG : IsAdmissibleWordGrid w G)
include hG

omit hG in
/-- **The order of rows inside a height class is irrelevant.** -/
theorem sum_tiePart_eq_column :
    ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
        (if positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b ∧
          G.O (finProdFinEquiv a) < G.O (finProdFinEquiv b) then cornerPairWeight w a b else 0) =
      ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
        (if positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b ∧
          finProdFinEquiv a < finProdFinEquiv b then cornerPairWeight w a b else 0) := by
  have hOinj : ∀ a b : Fin w.length × Fin 3, a ≠ b →
      G.O (finProdFinEquiv a) ≠ G.O (finProdFinEquiv b) := fun a b hab h =>
    hab (finProdFinEquiv.injective (G.O.toPerm.injective h))
  have hcinj : ∀ a b : Fin w.length × Fin 3, a ≠ b →
      (finProdFinEquiv a : Fin (w.length * 3)) ≠ finProdFinEquiv b := fun a b hab h =>
    hab (finProdFinEquiv.injective h)
  apply sum_ite_and_order_eq
  · exact fun a b h => h.symm
  · exact fun a b h hab => cornerPairWeight_symm w h hab
  · intro a b hab
    rcases lt_or_gt_of_ne (hOinj a b hab) with h | h
    · exact ⟨fun _ => not_lt.mpr h.le, fun _ => h⟩
    · exact ⟨fun h' => absurd h' (not_lt.mpr h.le), fun h' => absurd h h'⟩
  · exact fun a => lt_irrefl _
  · intro a b hab
    rcases lt_or_gt_of_ne (hcinj a b hab) with h | h
    · exact ⟨fun _ => not_lt.mpr h.le, fun _ => h⟩
    · exact ⟨fun h' => absurd h' (not_lt.mpr h.le), fun h' => absurd h h'⟩
  · exact fun a => lt_irrefl _

end Admissible

/-! ### Occurrences of a strand rank -/

section Occurrences

variable (r : Fin m)

/-- The local offset of the corners of an occurrence of the rank `r`: `0` when `r` is the lower
rank of the letter and `1` when it is the upper rank. -/
def occOffset (q : PositiveRectilinearRowOccurrences w r) : ℕ :=
  if r = adjacentLower w[q.val.val] then 0 else 1

theorem occOffset_le (q : PositiveRectilinearRowOccurrences w r) : occOffset w r q ≤ 1 := by
  unfold occOffset
  split_ifs <;> omega

theorem col_outgoing_val (q : PositiveRectilinearRowOccurrences w r) :
    (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩))).val =
      3 * q.val.val + 1 + occOffset w r q := by
  rw [positiveRectilinearOutgoingArc_symm_inr, finProdFinEquiv_apply_val]
  unfold occOffset
  split_ifs <;> simp <;> omega

theorem col_incoming_val (q : PositiveRectilinearRowOccurrences w r) :
    (finProdFinEquiv ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩))).val =
      3 * q.val.val + occOffset w r q := by
  rw [positiveRectilinearIncomingArc_symm_inr, finProdFinEquiv_apply_val]
  unfold occOffset
  split_ifs
  · simp
  · simp only [Fin.isValue, Fin.val_one]
    omega

theorem arcRow_outgoing_inr (q : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearWordArcRow w ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) =
      (r.val : ℝ) := by
  rw [positiveRectilinearOutgoingArc_symm_inr, positiveRectilinearWordArcRow_eq]
  rcases q.prop with h | h
  · rw [if_pos h]
    have hv : r.val = (w[q.val.val]).val := congrArg Fin.val h
    simp [hv]
  · have hne : r ≠ adjacentLower w[q.val.val] := by
      intro h'
      have := congrArg Fin.val (h.symm.trans h')
      simp at this
    rw [if_neg hne]
    have hv : r.val = (w[q.val.val]).val + 1 := congrArg Fin.val h
    simp [hv, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The matching on an integer-row arc, in the form used below. -/
theorem matching_outgoing_inr (q : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearWordMatching w ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) =
      (positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r,
        positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) q⟩) :=
  positiveRectilinearWordMatching_outgoingArc_symm_inr w r q

private theorem occ_lt_iff (q q' : PositiveRectilinearRowOccurrences w r) :
    q < q' ↔ q.val.val < q'.val.val :=
  Iff.rfl

private theorem occ_le_iff (q q' : PositiveRectilinearRowOccurrences w r) :
    q ≤ q' ↔ q.val.val ≤ q'.val.val :=
  Iff.rfl

private theorem occ_eq_of_val (q q' : PositiveRectilinearRowOccurrences w r)
    (h : q.val.val = q'.val.val) : q = q' :=
  Subtype.ext (Fin.ext h)

/-- An occurrence is the last one exactly when its sorted successor wraps. -/
theorem isMax_iff_succ_le (q : PositiveRectilinearRowOccurrences w r) :
    (∀ b, b ≤ q) ↔
      positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) q ≤ q := by
  rcases positiveRectilinearSortedSuccessor_next (PositiveRectilinearRowOccurrences w r) q with
    ⟨h1, _⟩ | ⟨h1, h2⟩
  · constructor
    · intro hmax
      exact absurd (hmax _) (not_le.mpr h1)
    · intro hle
      exact absurd hle (not_le.mpr h1)
  · exact ⟨fun _ => h1, fun _ b => (h2 b).2⟩

theorem col_outgoing_lt_iff (q q' : PositiveRectilinearRowOccurrences w r) :
    finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) <
        finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q'⟩)) ↔
      q < q' := by
  rw [Fin.lt_def, col_outgoing_val, col_outgoing_val, occ_lt_iff]
  have h1 := occOffset_le w r q
  have h2 := occOffset_le w r q'
  constructor
  · intro h
    rcases Nat.lt_trichotomy q.val.val q'.val.val with h' | h' | h'
    · exact h'
    · have he := occ_eq_of_val w r q q' h'
      subst he
      omega
    · omega
  · intro h
    omega

/-- **Weights of two occurrences.** For two occurrences `q < q'` of the rank `r`, the weight of
their arcs is `1` when `q'` is the last occurrence and `0` otherwise. -/
theorem cornerPairWeight_occurrence (q q' : PositiveRectilinearRowOccurrences w r)
    (hqq : q < q') :
    cornerPairWeight w ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩))
        ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q'⟩)) =
      if ∀ b, b ≤ q' then 1 else 0 := by
  set S := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) q with hS
  set S' := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) q' with hS'
  obtain ⟨hqS, hSq'⟩ : q < S ∧ S ≤ q' := by
    rcases positiveRectilinearSortedSuccessor_next (PositiveRectilinearRowOccurrences w r) q with
      ⟨h1, h2⟩ | ⟨_, h2⟩
    · exact ⟨h1, h2 q' hqq⟩
    · exact absurd (h2 q').2 (not_le.mpr hqq)
  unfold cornerPairWeight
  rw [matching_outgoing_inr, matching_outgoing_inr, ← hS, ← hS']
  simp only [Fin.le_def, Fin.lt_def, col_incoming_val, col_outgoing_val]
  rw [occ_lt_iff] at hqq hqS
  rw [occ_le_iff] at hSq'
  have e1 := occOffset_le w r q
  have e2 := occOffset_le w r q'
  have e3 := occOffset_le w r S
  have e4 := occOffset_le w r S'
  rcases positiveRectilinearSortedSuccessor_next (PositiveRectilinearRowOccurrences w r) q' with
    ⟨h1, _⟩ | ⟨h1, h2⟩
  · rw [← hS'] at h1
    rw [occ_lt_iff] at h1
    have hnot : ¬ ∀ b, b ≤ q' := fun h => absurd (h S') (by rw [occ_le_iff]; omega)
    rw [if_neg hnot]
    rcases Nat.lt_or_ge S.val.val q'.val.val with h3 | h3
    · split_ifs <;> omega
    · have he := occ_eq_of_val w r S q' (by omega)
      rw [he] at e3 ⊢
      split_ifs <;> omega
  · rw [← hS'] at h1 h2
    have hmax : ∀ b, b ≤ q' := fun b => (h2 b).2
    rw [if_pos hmax]
    have h4 := (h2 q).1
    rw [occ_le_iff] at h4
    rcases Nat.lt_or_ge S.val.val q'.val.val with h3 | h3
    · split_ifs <;> omega
    · have he := occ_eq_of_val w r S q' (by omega)
      rw [he] at e3 ⊢
      split_ifs <;> omega

/-- The integer-height pairs of one rank contribute the number of its occurrences minus one. -/
theorem sum_occurrence_pairs (hne : Nonempty (PositiveRectilinearRowOccurrences w r)) :
    ∑ q : PositiveRectilinearRowOccurrences w r, ∑ q' : PositiveRectilinearRowOccurrences w r,
        (if finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) <
            finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q'⟩)) then
          cornerPairWeight w ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩))
            ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q'⟩)) else 0) =
      (Fintype.card (PositiveRectilinearRowOccurrences w r) : ℤ) - 1 := by
  classical
  set qm := (Finset.univ : Finset (PositiveRectilinearRowOccurrences w r)).max'
    Finset.univ_nonempty with hqm
  have hmax : ∀ q', (∀ b, b ≤ q') ↔ q' = qm := by
    intro q'
    constructor
    · intro h
      exact le_antisymm (Finset.le_max' _ q' (Finset.mem_univ _)) (h qm)
    · intro h b
      rw [h]
      exact Finset.le_max' _ b (Finset.mem_univ _)
  have hterm : ∀ q q' : PositiveRectilinearRowOccurrences w r,
      (if finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) <
          finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q'⟩)) then
        cornerPairWeight w ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩))
          ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q'⟩)) else 0) =
      if q' = qm then (if q < q' then 1 else 0) else 0 := by
    intro q q'
    by_cases h : q < q'
    · rw [if_pos ((col_outgoing_lt_iff w r q q').mpr h), cornerPairWeight_occurrence w r q q' h,
        if_pos h]
      by_cases h' : q' = qm
      · rw [if_pos ((hmax q').mpr h'), if_pos h']
      · rw [if_neg (fun h'' => h' ((hmax q').mp h'')), if_neg h']
    · rw [if_neg (fun h' => h ((col_outgoing_lt_iff w r q q').mp h')), if_neg h]
      split_ifs <;> rfl
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_boole]
  have hf : (Finset.univ.filter fun q : PositiveRectilinearRowOccurrences w r => q < qm) =
      Finset.univ.erase qm := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ⟨ne_of_lt, fun h => lt_of_le_of_ne ((hmax qm).mpr rfl q) h⟩
  rw [hf, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpos : 0 < Fintype.card (PositiveRectilinearRowOccurrences w r) := Fintype.card_pos
  push_cast [Nat.cast_sub hpos]
  ring

/-- The wrapping test on the arc of an occurrence. -/
theorem col_incoming_succ_lt_iff (q : PositiveRectilinearRowOccurrences w r) :
    finProdFinEquiv ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r,
        positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) q⟩)) <
      finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) ↔
      ∀ b, b ≤ q := by
  set S := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) q with hS
  rw [isMax_iff_succ_le, ← hS, Fin.lt_def, col_incoming_val, col_outgoing_val, occ_le_iff]
  have e1 := occOffset_le w r q
  have e3 := occOffset_le w r S
  constructor
  · intro h
    omega
  · intro h
    rcases Nat.lt_or_ge S.val.val q.val.val with h3 | h3
    · omega
    · have he := occ_eq_of_val w r S q (by omega)
      rw [he]
      omega

end Occurrences

/-- Every strand rank occurs when every generator occurs. -/
theorem occurrences_nonempty (hm : 2 ≤ m) (hg : w.toSigned.generatorIndices = Finset.univ)
    (r : Fin m) : Nonempty (PositiveRectilinearRowOccurrences w r) := by
  have hmem : ∀ i : Fin (m - 1), i ∈ w := fun i => by
    have h : i ∈ w.toSigned.generatorIndices := by rw [hg]; exact Finset.mem_univ i
    rw [PositiveAdjacentWord.generatorIndices_toSigned] at h
    exact List.mem_toFinset.mp h
  by_cases hr : r.val < m - 1
  · obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp (hmem ⟨r.val, hr⟩)
    exact ⟨⟨⟨k, hk⟩, Or.inl (Fin.ext (by simp [hki]))⟩⟩
  · obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp (hmem ⟨m - 2, by omega⟩)
    refine ⟨⟨⟨k, hk⟩, Or.inr (Fin.ext ?_)⟩⟩
    simp only [hki]
    have := r.isLt
    omega

/-- The number of occurrences of all ranks is twice the length of the word. -/
theorem card_sigma_occurrences :
    Fintype.card (Σ r : Fin m, PositiveRectilinearRowOccurrences w r) = 2 * w.length := by
  have h := Fintype.card_congr (positiveRectilinearOutgoingArc w)
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  omega

/-- **The tie part.** With the pairs of equal heights ordered by their starting columns, the
total weight is `2ℓ - m` when every strand rank occurs. -/
theorem sum_tiePart_column (hocc : ∀ r : Fin m, Nonempty (PositiveRectilinearRowOccurrences w r)) :
    ∑ a : Fin w.length × Fin 3, ∑ b : Fin w.length × Fin 3,
        (if positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b ∧
          finProdFinEquiv a < finProdFinEquiv b then cornerPairWeight w a b else 0) =
      2 * w.length - m := by
  classical
  set out := positiveRectilinearOutgoingArc w with hout
  set F : Fin w.length × Fin 3 → Fin w.length × Fin 3 → ℤ := fun a b =>
    if positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b ∧
      finProdFinEquiv a < finProdFinEquiv b then cornerPairWeight w a b else 0 with hF
  have hinl : ∀ j : Fin w.length, out.symm (Sum.inl j) = (j, 0) := fun _ => rfl
  have hmid : ∀ j : Fin w.length, positiveRectilinearWordArcRow w (j, 0) =
      ((w[j.val]).val : ℝ) + 1 / 2 := fun j => by
    rw [positiveRectilinearWordArcRow_eq]
    rfl
  have hreindex : ∑ a, ∑ b, F a b = ∑ x, ∑ y, F (out.symm x) (out.symm y) := by
    rw [← Equiv.sum_comp out.symm]
    exact Finset.sum_congr rfl fun x _ => (Equiv.sum_comp out.symm _).symm
  change ∑ a, ∑ b, F a b = _
  rw [hreindex]
  simp only [Fintype.sum_sum_type, hinl]
  -- two middle arcs
  have hmm : ∀ j j' : Fin w.length, F (j, 0) (j', 0) = 0 := by
    intro j j'
    simp only [hF]
    split_ifs with h
    · unfold cornerPairWeight
      rw [positiveRectilinearWordMatching_middle, positiveRectilinearWordMatching_middle]
      have h2 := h.2
      rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val] at h2
      simp only [Fin.le_def, Fin.lt_def, finProdFinEquiv_apply_val] at h2 ⊢
      simp only [Fin.isValue, Fin.val_zero, Fin.val_two] at h2 ⊢
      split_ifs <;> omega
    · rfl
  -- a middle arc and an integer arc
  have hmi : ∀ (j : Fin w.length) (p : Σ r : Fin m, PositiveRectilinearRowOccurrences w r),
      F (j, 0) (out.symm (Sum.inr p)) = 0 := by
    intro j ⟨r, q⟩
    simp only [hF]
    rw [if_neg]
    rintro ⟨h, _⟩
    rw [hmid, arcRow_outgoing_inr] at h
    exact positiveWordGrid_natCast_add_half_ne _ _ h
  have him : ∀ (j : Fin w.length) (p : Σ r : Fin m, PositiveRectilinearRowOccurrences w r),
      F (out.symm (Sum.inr p)) (j, 0) = 0 := by
    intro j ⟨r, q⟩
    simp only [hF]
    rw [if_neg]
    rintro ⟨h, _⟩
    rw [hmid, arcRow_outgoing_inr] at h
    exact positiveWordGrid_natCast_add_half_ne _ _ h.symm
  simp only [hmm, hmi, him, Finset.sum_const_zero, add_zero, zero_add]
  -- two integer arcs
  rw [Fintype.sum_sigma]
  have hrank : ∀ (r : Fin m) (q : PositiveRectilinearRowOccurrences w r),
      ∑ p' : (Σ r : Fin m, PositiveRectilinearRowOccurrences w r),
          F (out.symm (Sum.inr ⟨r, q⟩)) (out.symm (Sum.inr p')) =
        ∑ q' : PositiveRectilinearRowOccurrences w r,
          (if finProdFinEquiv (out.symm (Sum.inr ⟨r, q⟩)) <
              finProdFinEquiv (out.symm (Sum.inr ⟨r, q'⟩)) then
            cornerPairWeight w (out.symm (Sum.inr ⟨r, q⟩)) (out.symm (Sum.inr ⟨r, q'⟩))
              else 0) := by
    intro r q
    rw [Fintype.sum_sigma, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl fun q' _ => ?_
      simp only [hF, hout, arcRow_outgoing_inr, true_and]
    · intro r' _ hr'
      refine Finset.sum_eq_zero fun q' _ => ?_
      simp only [hF]
      rw [if_neg]
      rintro ⟨h, _⟩
      rw [arcRow_outgoing_inr, arcRow_outgoing_inr] at h
      exact hr' (Fin.ext (by exact_mod_cast h.symm))
    · intro h
      exact absurd (Finset.mem_univ r) h
  simp only [hrank]
  rw [Finset.sum_congr rfl fun r _ => sum_occurrence_pairs w r (hocc r)]
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Fintype.card_sigma, card_sigma_occurrences]
  simp

section Admissible

variable {w} {G : GridDiagram (w.length * 3)} (hG : IsAdmissibleWordGrid w G)
include hG

/-- **The wrap number of an admissible word grid.** Each strand rank has exactly one wrapping
arc. -/
theorem wrapNumber_admissible
    (hocc : ∀ r : Fin m, Nonempty (PositiveRectilinearRowOccurrences w r)) :
    wrapNumber G = m := by
  classical
  have h1 : (wrapNumber G : ℤ) = ∑ ρ : Fin (w.length * 3),
      if G.X.toPerm.symm ρ < G.O.toPerm.symm ρ then 1 else 0 := by
    unfold wrapNumber
    rw [Finset.card_filter]
    push_cast
    rfl
  have h2 : ∑ ρ : Fin (w.length * 3),
      (if G.X.toPerm.symm ρ < G.O.toPerm.symm ρ then (1 : ℤ) else 0) =
      ∑ a : Fin w.length × Fin 3,
        if finProdFinEquiv (positiveRectilinearWordMatching w a) < finProdFinEquiv a then 1
          else 0 := by
    symm
    refine Fintype.sum_equiv (finProdFinEquiv.trans G.O.toPerm) _ _ fun a => ?_
    change _ = if G.X.toPerm.symm (G.O (finProdFinEquiv a)) <
      G.O.toPerm.symm (G.O.toPerm (finProdFinEquiv a)) then 1 else 0
    rw [admissible_X_symm hG, Equiv.symm_apply_apply]
  have h3 : ∑ a : Fin w.length × Fin 3,
      (if finProdFinEquiv (positiveRectilinearWordMatching w a) < finProdFinEquiv a then
        (1 : ℤ) else 0) = m := by
    rw [← Equiv.sum_comp (positiveRectilinearOutgoingArc w).symm, Fintype.sum_sum_type,
      Fintype.sum_sigma]
    have hz : ∀ j : Fin w.length,
        (if finProdFinEquiv (positiveRectilinearWordMatching w
            ((positiveRectilinearOutgoingArc w).symm (Sum.inl j))) <
          finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inl j)) then
            (1 : ℤ) else 0) = 0 := by
      intro j
      change (if finProdFinEquiv (positiveRectilinearWordMatching w (j, 0)) <
        finProdFinEquiv (j, 0) then (1 : ℤ) else 0) = 0
      rw [positiveRectilinearWordMatching_middle, if_neg]
      rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
      simp
    simp only [hz, Finset.sum_const_zero, zero_add]
    have hrank : ∀ r : Fin m, ∑ q : PositiveRectilinearRowOccurrences w r,
        (if finProdFinEquiv (positiveRectilinearWordMatching w
            ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩))) <
          finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) then
            (1 : ℤ) else 0) = 1 := by
      intro r
      have := hocc r
      set qm := (Finset.univ : Finset (PositiveRectilinearRowOccurrences w r)).max'
        Finset.univ_nonempty with hqm
      have hmax : ∀ q', (∀ b, b ≤ q') ↔ q' = qm := by
        intro q'
        constructor
        · intro h
          exact le_antisymm (Finset.le_max' _ q' (Finset.mem_univ _)) (h qm)
        · intro h b
          rw [h]
          exact Finset.le_max' _ b (Finset.mem_univ _)
      simp only [matching_outgoing_inr, col_incoming_succ_lt_iff, hmax]
      simp
    simp only [hrank, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  have h := h1.trans (h2.trans h3)
  exact_mod_cast h

/-- **The corner grading of an admissible word grid.** `2 A(x₀) = ℓ - m + 1`. -/
theorem alexanderTwoℤ_cornerShift_admissible (hL : 1 ≤ w.length)
    (hocc : ∀ r : Fin m, Nonempty (PositiveRectilinearRowOccurrences w r)) :
    G.alexanderTwoℤ (cornerShift G.O) = (w.length : ℤ) - m + 1 := by
  have h := alexanderTwoℤ_cornerShift_add_eq_sum_arcPairWeight G (by omega)
  rw [sum_arcPairWeight_admissible hG] at h
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    ite_rowOrder_split hG a b (cornerPairWeight w a b)] at h
  simp only [Finset.sum_add_distrib] at h
  rw [sum_heightPart, sum_tiePart_eq_column, sum_tiePart_column w hocc] at h
  push_cast at h
  linarith

/-- **Theorem 5.8 for admissible grids.** For every admissible grid of a word of length `ℓ` on
`m ≥ 2` strands in which every strand rank occurs, and every `0 ≤ t ≤ 2/m`, the canonical class
has weighted spectral threshold at least `(t/2) (ℓ - m + 1)/2`. -/
theorem admissible_spectralThreshold_lower (hm : 2 ≤ m) (hn : 2 ≤ w.length * 3)
    (hocc : ∀ r : Fin m, Nonempty (PositiveRectilinearRowOccurrences w r))
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 2 / (m : ℝ)) :
    ((t / 2 * ((((w.length : ℤ) - m + 1 : ℤ) : ℝ) / 2) : ℝ) : EReal) ≤
      ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
        (gridCanonicalClass G hn) := by
  have hL : 1 ≤ w.length := by omega
  have h := alexander_spectralThreshold_corner G hn m (by omega)
    (wrapNumber_admissible hG hocc).le t ht0 ht
  have hA : (G.alexander (cornerShift G.O) : ℝ) = (((w.length : ℤ) - m + 1 : ℤ) : ℝ) / 2 := by
    have e := G.two_mul_alexander_eq_intCast (cornerShift G.O)
    rw [alexanderTwoℤ_cornerShift_admissible hG hL hocc] at e
    have e' : (G.alexander (cornerShift G.O) : ℚ) = (((w.length : ℤ) - m + 1 : ℤ) : ℚ) / 2 := by
      linarith
    rw [e']
    push_cast
    ring
  rwa [hA] at h

end Admissible

end OnLeConjecture.KnotFloer.GridFull
