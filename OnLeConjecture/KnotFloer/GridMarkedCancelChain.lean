/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelUnused

/-!
# Chains of marked word grids

`MRelF v p v' p'` says that, for every protected grid, every marked word grid of `v` with the
marked arc leaving the corner with the values `p` is related by grid moves to a marked word grid
of `v'` with the marked arc leaving `p'`. `MRel v p v' p' j` allows the protected grid `H` to grow
by a frame tower with `j` blocks, for triply prepared `H`. The corners are given by their values,
so that equalities of words can be used directly. Both relations are transitive.

The elementary steps are the slides of the marked arc (`mrelF_slide_pow`), the cyclic rotations
(`mrelF_rotate`), the cancellation and the insertion of an inverse pair whose strands are used by
the rest of the word (`mrelF_cancel_front`, `mrelF_insert_front`, `mrelF_insert_mid`), and the
cancellation of an inverse pair whose upper strand is not used by the rest of the word, which
adds one block (`mrel_cancel_unused`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid
  OnLeConjecture.KnotFloer.GridFull

variable {m : ℕ}

/-! ### Keys and marked word grids -/

/-- An admissible key: the outgoing height, refined by the position of the corner. -/
def admKey (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) : ℕ :=
  v.oHeight2 p * (v.length * 3) + (finProdFinEquiv p).val

theorem admKey_mono (v : SignedAdjacentWord m) :
    ∀ a b, v.oHeight2 a < v.oHeight2 b → admKey v a < admKey v b := by
  intro a b h
  have h1 := (finProdFinEquiv a).isLt
  have h2 : (v.oHeight2 a + 1) * (v.length * 3) ≤ v.oHeight2 b * (v.length * 3) :=
    Nat.mul_le_mul_right _ h
  simp only [admKey]
  rw [Nat.add_one_mul] at h2
  omega

theorem isMarkedGrid_markedGrid {k : ℕ} (v : SignedAdjacentWord m) (hv : 0 < v.length)
    (p : Fin v.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
    (hO : H.O (Fin.last k) = 0) :
    IsMarkedGrid v hv p H hX hO (markedGrid v (admKey v) hv p H hX hO).toGrid :=
  ⟨admKey v, admKey_mono v, rfl⟩

/-- Two marked word grids with the same data are related by grid moves. -/
theorem IsMarkedGrid.movesTo {k : ℕ} {v : SignedAdjacentWord m} {hv : 0 < v.length}
    {p : Fin v.length × Fin 3} {H : GridDiagram (k + 1)} {hX : H.X 0 = 0}
    {hO : H.O (Fin.last k) = 0} {M M' : GridDiagram (v.length * 3 + k + 1)}
    (hM : IsMarkedGrid v hv p H hX hO M) (hM' : IsMarkedGrid v hv p H hX hO M') :
    M.MovesTo M' := by
  obtain ⟨κ', hκ', rfl⟩ := hM'
  exact MFwd.of_key hM hκ'

/-! ### The relations -/

/-- Marked word grids of `v` at the corner with values `p` are related to marked word grids of
`v'` at the corner with values `p'`, for every protected grid. -/
def MRelF (v : SignedAdjacentWord m) (p : ℕ × Fin 3) (v' : SignedAdjacentWord m)
    (p' : ℕ × Fin 3) : Prop :=
  ∃ (hp : p.1 < v.length) (hp' : p'.1 < v'.length),
    MFwd v (Nat.zero_lt_of_lt hp) (⟨p.1, hp⟩, p.2) v' (Nat.zero_lt_of_lt hp') (⟨p'.1, hp'⟩, p'.2)

/-- Marked word grids of `v` at `p` with a triply prepared protected grid `H` are related to
marked word grids of `v'` at `p'` with a frame tower of `j` blocks over `H`. -/
def MRel (v : SignedAdjacentWord m) (p : ℕ × Fin 3) (v' : SignedAdjacentWord m)
    (p' : ℕ × Fin 3) (j : ℕ) : Prop :=
  ∃ (hp : p.1 < v.length) (hp' : p'.1 < v'.length),
    ∀ {k : ℕ} (H : GridDiagram (k + 1)) (hH : TriplyPrepared H)
      (M : GridDiagram (v.length * 3 + k + 1)),
      IsMarkedGrid v (Nat.zero_lt_of_lt hp) (⟨p.1, hp⟩, p.2) H hH.1 hH.2.1 M →
      ∃ (k' : ℕ) (H' : GridDiagram (k' + 1)) (hH' : TriplyPrepared H')
        (M' : GridDiagram (v'.length * 3 + k' + 1)), FrameTower H j H' ∧
        IsMarkedGrid v' (Nat.zero_lt_of_lt hp') (⟨p'.1, hp'⟩, p'.2) H' hH'.1 hH'.2.1 M' ∧
        M.MovesTo M'

variable {v v' v'' : SignedAdjacentWord m} {p p' p'' : ℕ × Fin 3}

theorem MRelF.refl (hp : p.1 < v.length) : MRelF v p v p :=
  ⟨hp, hp, MFwd.refl _ _ _⟩

theorem MRelF.trans (h₁ : MRelF v p v' p') (h₂ : MRelF v' p' v'' p'') : MRelF v p v'' p'' := by
  obtain ⟨hp, hp', h₁⟩ := h₁
  obtain ⟨hq', hq'', h₂⟩ := h₂
  exact ⟨hp, hq'', MFwd.trans h₁ h₂⟩

theorem MRelF.cast {w w' : SignedAdjacentWord m} {q q' : ℕ × Fin 3} (h : MRelF v p v' p')
    (hv : v = w) (hp : p = q) (hv' : v' = w') (hp' : p' = q') : MRelF w q w' q' := by
  subst hv hp hv' hp'; exact h

theorem MRelF.toMRel (h : MRelF v p v' p') : MRel v p v' p' 0 := by
  obtain ⟨hp, hp', h⟩ := h
  refine ⟨hp, hp', fun H hH M hM => ?_⟩
  obtain ⟨M', hM', hm⟩ := h H hH.1 hH.2.1 M hM
  exact ⟨_, H, hH, M', FrameTower.base, hM', hm⟩

theorem MRel.trans {j j' : ℕ} (h₁ : MRel v p v' p' j) (h₂ : MRel v' p' v'' p'' j') :
    MRel v p v'' p'' (j + j') := by
  obtain ⟨hp, hp', h₁⟩ := h₁
  obtain ⟨hq', hq'', h₂⟩ := h₂
  refine ⟨hp, hq'', fun H hH M hM => ?_⟩
  obtain ⟨k', H', hH', M', ht, hM', hm⟩ := h₁ H hH M hM
  obtain ⟨k'', H'', hH'', M'', ht', hM'', hm'⟩ := h₂ H' hH' M' hM'
  exact ⟨k'', H'', hH'', M'', ht.trans ht', hM'', hm.trans hm'⟩

theorem MRel.cast {w w' : SignedAdjacentWord m} {q q' : ℕ × Fin 3} {j j' : ℕ}
    (h : MRel v p v' p' j) (hv : v = w) (hp : p = q) (hv' : v' = w') (hp' : p' = q')
    (hj : j = j') : MRel w q w' q' j' := by
  subst hv hp hv' hp' hj; exact h

/-! ### Elementary steps -/

theorem mrelF_slide (v : SignedAdjacentWord m) (q : Fin v.length × Fin 3) :
    MRelF v (q.1.val, q.2) v ((sM v q).1.val, (sM v q).2) :=
  ⟨q.1.isLt, (sM v q).1.isLt, mfwd_slide v (Nat.zero_lt_of_lt q.1.isLt) q⟩

theorem mrelF_slide_pow (v : SignedAdjacentWord m) (q : Fin v.length × Fin 3) :
    ∀ j : ℕ, MRelF v (q.1.val, q.2) v ((((sM v) ^ j) q).1.val, (((sM v) ^ j) q).2)
  | 0 => MRelF.refl q.1.isLt
  | j + 1 => by
    have h := mrelF_slide v (((sM v) ^ j) q)
    rw [← Equiv.Perm.mul_apply, ← pow_succ'] at h
    exact (mrelF_slide_pow v q j).trans h

theorem mrelF_rotate (x y : SignedAdjacentWord m) {h : ℕ} (hh : h < (x ++ y).length)
    (c : Fin 3) :
    MRelF (x ++ y) (h, c) (y ++ x)
      (if h < x.length then h + y.length else h - x.length, c) :=
  ⟨hh, (rotL x y ⟨h, hh⟩).isLt, mfwd_rotate x y _ _ (⟨h, hh⟩, c)⟩

theorem mrelF_rotate_left (x y : SignedAdjacentWord m) {h : ℕ} (hh : h < x.length) (c : Fin 3) :
    MRelF (x ++ y) (h, c) (y ++ x) (h + y.length, c) :=
  (mrelF_rotate x y (by simp only [List.length_append]; omega) c).cast rfl rfl rfl
    (by rw [if_pos hh])

theorem mrelF_rotate_right (x y : SignedAdjacentWord m) {h : ℕ} (hh : x.length ≤ h)
    (hh' : h < (x ++ y).length) (c : Fin 3) :
    MRelF (x ++ y) (h, c) (y ++ x) (h - x.length, c) :=
  (mrelF_rotate x y hh' c).cast rfl rfl rfl (by rw [if_neg (by omega)])

theorem mrelF_cancel_front (r : Fin (m - 1)) (e : ℤˣ) (t : SignedAdjacentWord m)
    (h0 : RankIn t r.val) (h1 : RankIn t (r.val + 1)) {i : ℕ} (hi : i < t.length) (c : Fin 3) :
    MRelF ([(r, e), (r, -e)] ++ t) (i + 2, c) t (i, c) :=
  ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, hi,
    mfwd_cancel_front r e t h0 h1 (⟨i, hi⟩, c)⟩

theorem mrelF_insert_front (r : Fin (m - 1)) (e : ℤˣ) (t : SignedAdjacentWord m)
    (h0 : RankIn t r.val) (h1 : RankIn t (r.val + 1)) {i : ℕ} (hi : i < t.length) (c : Fin 3) :
    MRelF t (i, c) ([(r, e), (r, -e)] ++ t) (i + 2, c) := by
  have hi2 : i + 2 < ([(r, e), (r, -e)] ++ t).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  refine ⟨hi, hi2, fun H hX hO M hM => ?_⟩
  have hM₁ := isMarkedGrid_markedGrid ([(r, e), (r, -e)] ++ t) (Nat.zero_lt_of_lt hi2)
    (⟨i + 2, hi2⟩, c) H hX hO
  obtain ⟨M₂, hM₂, hm₂⟩ := mfwd_cancel_front r e t h0 h1 (⟨i, hi⟩, c) H hX hO _ hM₁
  exact ⟨_, hM₁, (IsMarkedGrid.movesTo hM hM₂).trans hm₂.symm⟩

theorem RankIn.of_append_comm {u w : SignedAdjacentWord m} {s : ℕ} (h : RankIn (u ++ w) s) :
    RankIn (w ++ u) s :=
  h.mono fun a ha => by simp only [List.mem_append] at ha ⊢; tauto

/-- **Insertion of an inverse pair** between two words, the marked arc leaving a corner of the
first word. -/
theorem mrelF_insert_mid (u w : SignedAdjacentWord m) (r : Fin (m - 1)) (e : ℤˣ)
    (h0 : RankIn (u ++ w) r.val) (h1 : RankIn (u ++ w) (r.val + 1)) {i : ℕ} (hi : i < u.length)
    (c : Fin 3) :
    MRelF (u ++ w) (i, c) (u ++ [(r, e), (r, -e)] ++ w) (i, c) := by
  have s1 := mrelF_rotate_left u w hi c
  have s2 := mrelF_insert_front r e (w ++ u) (RankIn.of_append_comm h0) (RankIn.of_append_comm h1)
    (i := i + w.length) (by simp only [List.length_append]; omega) c
  have s3 := mrelF_rotate_right ([(r, e), (r, -e)] ++ w) u (h := i + w.length + 2)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) c
  refine s1.trans (s2.trans (s3.cast (by simp) rfl (by simp) ?_))
  simp only [List.length_append, List.length_cons, List.length_nil]
  congr 1; omega

/-! ### Cancellation with an unused upper strand -/

theorem block_unused_S (r : Fin (m - 1)) (t : SignedAdjacentWord m)
    (h0 : RankIn t r.val) (h1 : ¬ RankIn t (r.val + 1)) :
    BlockS 2 1 r.val [0, 0] [true, false] [(r, 1), (r, -1)] t (flagOf [true, false]) where
  kpos := by norm_num
  len := rfl
  val k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp
  sgn k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [posB]
  offs_le k hk := by interval_cases k <;> simp
  fl_iff e' he' := by
    interval_cases e'
    · simp only [flagOf, List.getD_cons_zero, true_iff, Nat.add_zero]
      exact (rankIn_iff t _).mp h0
    · simp only [flagOf, List.getD_cons_succ, List.getD_cons_zero, Bool.false_eq_true,
        false_iff]
      exact fun h => h1 ((rankIn_iff t _).mpr h)

/-- The initial window state of `σ_r σ_r⁻¹` with the upper strand unused: the arc `5` of the
upper strand closes up. -/
def cancU : WState := ⟨[(0, 20), (1, 5), (2, 0), (3, 2), (5, 1), (30, 3)], [20, 1, 30, 0, 3, 2, 5]⟩

/-- The move sequence of `σ_r σ_r⁻¹` with the upper strand unused. -/
def cancUMoves : List WMove := [.c 4, .dX 3 4 3 2, .dX 2 3 2 0, .c 1, .dO 1 0 0 30]

theorem cancU_init : InitOKS 2 cancU [0, 0] [true, false] [true, false] := by decide

theorem cancU_run : run cancU cancUMoves = some Funk := by decide

theorem cancU_ok : UnusedOK cancU [true, false] := by decide

theorem cancU_ol : 30 ∈ Ol cancU := by decide

theorem cancU_xl : ∀ x ∈ Xl cancU, x ∉ Ol cancU → isConn x = true := by decide

/-- **Cancellation of an inverse pair with an unused upper strand.** The protected grid grows by
one block. -/
theorem mrel_cancel_unused (r : Fin (m - 1)) (t : SignedAdjacentWord m)
    (h0 : RankIn t r.val) (h1 : ¬ RankIn t (r.val + 1)) {i : ℕ} (hi : i < t.length)
    (c : Fin 3) :
    MRel ([(r, 1), (r, -1)] ++ t) (i + 2, c) t (i, c) 1 := by
  have hi2 : i + 2 < ([(r, 1), (r, -1)] ++ t).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  refine ⟨hi2, hi, fun H hH M hM => ?_⟩
  have hB := block_unused_S r t h0 h1
  have hm1 := MFwd.of_key hM (skappa_mono (K := 2) cancU _ cancU_init.2.2.2.2.1)
  have hm2 := markedGrid_movesTo_winGrid cancU hB cancU_init (upCorner hB (⟨i, hi⟩, c)) H
    hH.1 hH.2.1
  obtain ⟨M', hM', hm3⟩ := marked_cancel_unused hB cancU cancU_init cancU_run cancU_ok cancU_ol
    cancU_xl (⟨i, hi⟩, c) H hH
  exact ⟨_, unkH H, unkH_tp H hH, M', unkH_tower H hH, hM', hm1.trans (hm2.trans hm3)⟩

end OnLeConjecture.KnotTheory.MarkedCancel
