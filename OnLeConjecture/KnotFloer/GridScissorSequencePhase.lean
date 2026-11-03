/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridScissorSequenceStar
public import OnLeConjecture.KnotTheory.ScissorSequenceComponents
public import OnLeConjecture.KnotTheory.ScissorSequenceCount

/-!
# The star scissors on the signed word grid of a padded product

This file performs the star scissors of Section 9 of the written proof of Statement E
(`statement_E_complete_proof.tex`, subsection "Signed word grids and the scissor switches") on an
arbitrary signed word grid `H` of the product `(factorProduct F.factor)` of a normalized
factorization.

The columns of `H` are the corners of the product. Write `Z l x` for the column of the last
outgoing corner of the rank `x` in the factor `l`, and `Fc l x` for the column of the first
incoming corner (`lastCorner`, `firstCorner`). The arc of `Z l x` ends at `Fc (l + 1) x`,
cyclically. For each rank `x = 1, …, S - 1` in turn the phase

* reorders the rows of the rank `x` by row commutations, so that the rows of `Z (r - 1) x`, …,
  `Z 1 x`, `Z 0 x` are the last ones, from bottom to top (`reflTransGen_rowCommutation_perm`,
  using `nonintN_sameHeight`);
* applies the star rule with center `Z 0 x` and leaves `Z 1 x, …, Z (r - 1) x`
  (`ScissorPhase.star_index`). The leaf `Z l x` uses an `O` switch exactly when it is selected
  (`Selected`): when the strand `x` is fixed by the factor `l`, or when the factor `0` fixes it
  and `l` is the chosen moving factor `lstar x`.

The result (`exists_scissorEndpoint`) is a scissor phase from `H` to a grid `K` whose component
permutation sends `Z l x` to `Fc l x` for every rank `x ≥ 1` and agrees with that of `H`
elsewhere; its rows are still ordered by height; the recorded edges are the pairs
`(Z l x, Z 0 x)` of the selected leaves, and the numbers of `X` switches and of edges add up to
`(S - 1)(r - 1)`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization

/-! ### Sorted lists -/

theorem pairwise_split {α : Type*} (f : α → ℕ) (v : ℕ) :
    ∀ l : List α, l.Pairwise (fun a b => f a ≤ f b) →
      l = l.filter (fun a => f a < v) ++ l.filter (fun a => f a = v) ++
        l.filter (fun a => v < f a) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro hs
    rw [List.pairwise_cons] at hs
    have ih' := ih hs.2
    rcases Nat.lt_trichotomy (f a) v with h | h | h
    · simp only [List.filter_cons, h, decide_true, if_true, h.ne, decide_false,
        Bool.false_eq_true, if_false, show ¬ v < f a by omega, List.cons_append]
      exact congrArg _ ih'
    · have h1 : l.filter (fun b => f b < v) = [] := List.filter_eq_nil_iff.mpr
        (fun b hb => by have := hs.1 b hb; simp; omega)
      rw [h1, List.nil_append] at ih'
      simp only [List.filter_cons, decide_false, Bool.false_eq_true,
        if_false, h, decide_true, if_true, lt_irrefl, h1, List.nil_append, List.cons_append]
      exact congrArg _ ih'
    · have h1 : l.filter (fun b => f b < v) = [] := List.filter_eq_nil_iff.mpr
        (fun b hb => by have := hs.1 b hb; simp; omega)
      have h2 : l.filter (fun b => f b = v) = [] := List.filter_eq_nil_iff.mpr
        (fun b hb => by have := hs.1 b hb; simp; omega)
      rw [h1, h2, List.nil_append, List.nil_append] at ih'
      simp only [List.filter_cons, show ¬ f a < v by omega, decide_false, Bool.false_eq_true,
        if_false, h.ne', h, decide_true, if_true, h1, h2, List.nil_append]
      exact congrArg _ ih'

/-! ### Columns of the product -/

section Columns

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S)

theorem factorProduct_factor : factorProduct F.factor = F.product := rfl

/-- The number of columns of the signed word grids of the product. -/
abbrev prodSize : ℕ := (factorProduct F.factor).length * 3

/-- The column of a corner. -/
abbrev col (p : Fin (factorProduct F.factor).length × Fin 3) : Fin (prodSize F) := finProdFinEquiv p

/-- The outgoing height of the corner of a column. -/
def colHeight (c : Fin (prodSize F)) : ℕ :=
  (factorProduct F.factor).oHeight2 (finProdFinEquiv.symm c)

/-- The column of the last corner of the rank `x` in the factor `l`. -/
def colZ (l : Fin (N + B)) (x : Fin S) : Fin (prodSize F) :=
  col F (lastCorner F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l x)

/-- The column of the first corner of the rank `x` in the factor `l`. -/
def colF (l : Fin (N + B)) (x : Fin S) : Fin (prodSize F) :=
  col F (firstCorner F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l x)

/-- The component permutation of every signed word grid of the product. -/
def prodPerm : Equiv.Perm (Fin (prodSize F)) :=
  finProdFinEquiv.permCongr (sM (factorProduct F.factor))

theorem prodPerm_apply (p : Fin (factorProduct F.factor).length × Fin 3) :
    prodPerm F (col F p) = col F (sM (factorProduct F.factor) p) := by
  simp [prodPerm, Equiv.permCongr_apply]

theorem prodPerm_ne (c : Fin (prodSize F)) : prodPerm F c ≠ c := by
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective c
  rw [prodPerm_apply]
  intro h
  have e := finProdFinEquiv.injective h
  have := sM_height (factorProduct F.factor) p
  rw [e] at this
  exact oHeight2_ne_xHeight2 (factorProduct F.factor) p this.symm

/-- The component permutation of a signed word grid of the product. -/
theorem gridComponentPerm_eq_prodPerm {H : GridDiagram (prodSize F)}
    (hH : IsSignedWordGrid (factorProduct F.factor) H) : gridComponentPerm H = prodPerm F := by
  rw [isSignedWordGrid_iff] at hH
  refine Equiv.ext fun c => ?_
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective c
  rw [prodPerm_apply]
  change H.X.toPerm.symm (H.O.toPerm (col F p)) = col F (sM (factorProduct F.factor) p)
  rw [Equiv.symm_apply_eq]
  have := hH.2 (sM (factorProduct F.factor) p)
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

theorem prodPerm_colZ (l : Fin (N + B)) (x : Fin S) :
    prodPerm F (colZ F hS l x) = colF F hS (finRotate (N + B) l) x := by
  rw [colZ, prodPerm_apply, sM_lastCorner]; rfl

theorem colHeight_col (p : Fin (factorProduct F.factor).length × Fin 3) :
    colHeight F (col F p) = (factorProduct F.factor).oHeight2 p := by simp [colHeight]

theorem colHeight_colZ (l : Fin (N + B)) (x : Fin S) : colHeight F (colZ F hS l x) = 2 * x.val := by
  rw [colZ, colHeight_col]; exact oHeight2_lastCorner _ _ hS l x

theorem colZ_injective {l l' : Fin (N + B)} {x x' : Fin S} (h : colZ F hS l x = colZ F hS l' x') :
    l = l' ∧ x = x' :=
  lastCorner_injective F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS
    (finProdFinEquiv.injective h)

theorem colF_lt_colZ (l : Fin (N + B)) (x : Fin S) : (colF F hS l x).val < (colZ F hS l x).val :=
  firstCorner_lt_lastCorner F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l x

theorem colZ_lt_colF {l l' : Fin (N + B)} (h : l.val < l'.val) (x x' : Fin S) :
    (colZ F hS l x).val < (colF F hS l' x').val :=
  lastCorner_lt_firstCorner_succ F.factor
    (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l l' h x x'

/-- A first corner is never a last corner. -/
theorem firstCorner_ne_lastCorner (l l' : Fin (N + B)) (x x' : Fin S) :
    firstCorner F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l x ≠
      lastCorner F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l' x' := by
  intro h
  have hl : l = l' := by
    have := congrArg (fun p => segOf F.factor p.1) h
    simpa only [segOf_firstCorner, segOf_lastCorner] using this
  subst hl
  have e := congrArg (fun p => p.1.val) h
  simp only [firstCorner, lastCorner] at e
  have := (SignedGrid.NormalizedFactorization.factor_isPadded F l).length_ge
  have := x.isLt
  have := x'.isLt
  omega

/-- A first column is never a last column. -/
theorem colF_ne_colZ (l l' : Fin (N + B)) (x x' : Fin S) : colF F hS l x ≠ colZ F hS l' x' :=
  fun h => firstCorner_ne_lastCorner F hS l l' x x' (finProdFinEquiv.injective h)

end Columns


/-! ### Two noninterleaving configurations -/

theorem nonintN_of_chain {a b c d : ℕ} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    NonintN a d c b := by
  unfold NonintN CIooN
  constructor <;> constructor <;> intro _ <;> split_ifs <;> omega

theorem nonintN_of_wrap {f a b c : ℕ} (h1 : f < a) (h2 : a < b) (h3 : b < c) :
    NonintN a f c b := by
  unfold NonintN CIooN
  constructor <;> constructor <;> intro _ <;> split_ifs <;> omega

/-! ### The leaves of the star at one rank -/

/-- The factor `0`. -/
def fac0 {N B : ℕ} (hN : 0 < N) : Fin (N + B) := ⟨0, Nat.lt_of_lt_of_le hN (Nat.le_add_right N B)⟩

theorem succ_lt_of_lt_pred {r i : ℕ} (h : i < r - 1) : i + 1 < r := by omega

section Leaves

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S) (hN : 0 < N)

/-- The column of the center of the star at the rank `x`. -/
def center (x : Fin S) : Fin (prodSize F) := colZ F hS (fac0 hN) x

/-- The leaves of the star at the rank `x`: the last columns of the rank in the factors
`1, …, r - 1`, in this order. -/
def leaves (x : Fin S) : List (Fin (prodSize F)) :=
  (List.finRange (N + B - 1)).map fun i => colZ F hS ⟨i.val + 1, succ_lt_of_lt_pred i.isLt⟩ x

theorem leaves_length (x : Fin S) : (leaves F hS x).length = N + B - 1 := by simp [leaves]

theorem leaves_getElem (x : Fin S) (i : ℕ) (hi : i < (leaves F hS x).length) :
    (leaves F hS x)[i] = colZ F hS ⟨i + 1, by rw [leaves_length] at hi; omega⟩ x := by
  simp [leaves]

theorem mem_leaves (x : Fin S) (d : Fin (prodSize F)) :
    d ∈ leaves F hS x ↔ ∃ l : Fin (N + B), l.val ≠ 0 ∧ d = colZ F hS l x := by
  simp only [leaves, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, by simp, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l.val - 1, by omega⟩, by congr 1; exact Fin.ext (by simp; omega)⟩

theorem leaves_nodup (x : Fin S) : (leaves F hS x).Nodup := by
  refine (List.nodup_finRange _).map fun i j h => ?_
  have := (colZ_injective F hS h).1
  ext; have := congrArg Fin.val this; simp at this; omega

theorem center_not_mem_leaves (x : Fin S) : center F hS hN x ∉ leaves F hS x := by
  rw [mem_leaves]
  rintro ⟨l, hl, h⟩
  have := (colZ_injective F hS h).1
  exact hl (by rw [← this]; rfl)

theorem center_cons_getElem (x : Fin S) (i : ℕ)
    (hi : i < (center F hS hN x :: leaves F hS x).length) :
    (center F hS hN x :: leaves F hS x)[i] =
      colZ F hS ⟨i, by simp [leaves_length] at hi; omega⟩ x := by
  rcases i with _ | i
  · rfl
  · simp only [List.getElem_cons_succ, leaves_getElem]

theorem center_cons_getLast (x : Fin S) :
    (center F hS hN x :: leaves F hS x).getLast (List.cons_ne_nil _ _) =
      colZ F hS ⟨N + B - 1, by omega⟩ x := by
  rw [List.getLast_eq_getElem, center_cons_getElem]
  simp [leaves_length]

/-- Every column of the center and the leaves is a last column. -/
theorem mem_center_cons (x : Fin S) (d : Fin (prodSize F)) :
    d ∈ center F hS hN x :: leaves F hS x ↔ ∃ l : Fin (N + B), d = colZ F hS l x := by
  rw [List.mem_cons, mem_leaves]
  constructor
  · rintro (rfl | ⟨l, -, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨l, rfl⟩
  · rintro ⟨l, rfl⟩
    by_cases hl : l.val = 0
    · left; congr 1; exact Fin.ext hl
    · right; exact ⟨l, hl, rfl⟩

end Leaves

/-! ### Selection of the `O` switches -/

section Selection

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S) (hN : 0 < N)

open Classical in
/-- The chosen moving factor at the rank `x`. -/
def lstar (x : Fin S) : Fin (N + B) :=
  if h : ∃ l, F.factorPerm l x ≠ x then Classical.choose h else fac0 hN

theorem lstar_spec {x : Fin S} (h : ∃ l, F.factorPerm l x ≠ x) :
    F.factorPerm (lstar F hN x) x ≠ x := by
  rw [lstar, dif_pos h]; exact Classical.choose_spec h

/-- The leaf of the factor `l` uses an `O` switch at the rank `x`. -/
def Selected (x : Fin S) (l : Fin (N + B)) : Prop :=
  F.factorPerm l x = x ∨ (F.factorPerm (fac0 hN) x = x ∧ l = lstar F hN x)

instance (x : Fin S) (l : Fin (N + B)) : Decidable (Selected F hN x l) := by
  unfold Selected; infer_instance

/-- The selection of the `O` switches as a function of the columns. -/
def sel (x : Fin S) (d : Fin (prodSize F)) : Bool :=
  decide (∃ l : Fin (N + B), l.val ≠ 0 ∧ d = colZ F hS l x ∧ Selected F hN x l)

theorem sel_colZ (x : Fin S) (l : Fin (N + B)) (hl : l.val ≠ 0) :
    sel F hS hN x (colZ F hS l x) = decide (Selected F hN x l) := by
  simp only [sel]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨l', -, h, hs⟩
    rwa [(colZ_injective F hS h).1]
  · intro hs; exact ⟨l, hl, rfl, hs⟩

include hS in
/-- The number of selected leaves at a rank is the number of factors fixing it. -/
theorem card_selected (htrans : F.Transitive) (x : Fin S) :
    (Finset.univ.filter fun l : Fin (N + B) => l.val ≠ 0 ∧ Selected F hN x l).card =
      (Finset.univ.filter fun l : Fin (N + B) => F.factorPerm l x = x).card := by
  by_cases h0 : F.factorPerm (fac0 hN) x = x
  · have hmove := F.exists_factor_moves hS htrans x
    have hst := lstar_spec F hN hmove
    have hst0 : (lstar F hN x).val ≠ 0 := fun e => hst (by
      rw [show lstar F hN x = fac0 hN from Fin.ext e]; exact h0)
    have e : (Finset.univ.filter fun l : Fin (N + B) => l.val ≠ 0 ∧ Selected F hN x l) =
        insert (lstar F hN x) ((Finset.univ.filter fun l : Fin (N + B) =>
          F.factorPerm l x = x).erase (fac0 hN)) := by
      ext l
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      unfold Selected
      constructor
      · rintro ⟨hl, h | ⟨-, rfl⟩⟩
        · right; exact ⟨fun e => hl (by rw [e]; rfl), h⟩
        · left; rfl
      · rintro (rfl | ⟨hl, h⟩)
        · exact ⟨hst0, Or.inr ⟨h0, rfl⟩⟩
        · exact ⟨fun e => hl (Fin.ext e), Or.inl h⟩
    rw [e, Finset.card_insert_of_notMem (by simp [hst]),
      Finset.card_erase_of_mem (by simp [h0])]
    have : 0 < (Finset.univ.filter fun l : Fin (N + B) => F.factorPerm l x = x).card :=
      Finset.card_pos.mpr ⟨fac0 hN, by simp [h0]⟩
    omega
  · congr 1
    ext l
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    unfold Selected
    constructor
    · rintro ⟨-, h | ⟨h, -⟩⟩
      · exact h
      · exact absurd h h0
    · intro h
      refine ⟨fun e => h0 ?_, Or.inl h⟩
      rwa [show l = fac0 hN from Fin.ext e] at h

/-- The number of `O` switches of the star at the rank `x`. -/
theorem length_starEdges (htrans : F.Transitive) (x : Fin S) :
    (starEdges (center F hS hN x) (sel F hS hN x) (leaves F hS x)).length =
      (Finset.univ.filter fun l : Fin (N + B) => F.factorPerm l x = x).card := by
  rw [← card_selected F hS hN htrans x, starEdges, List.length_map, leaves, List.filter_map,
    List.length_map]
  have e : ∀ i : Fin (N + B - 1), ((sel F hS hN x) ∘ fun i : Fin (N + B - 1) =>
      colZ F hS ⟨i.val + 1, succ_lt_of_lt_pred i.isLt⟩ x) i =
        decide (Selected F hN x ⟨i.val + 1, succ_lt_of_lt_pred i.isLt⟩) :=
    fun i => sel_colZ F hS hN x _ (by simp)
  rw [List.filter_congr (fun i _ => e i)]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  refine Finset.card_bij (fun i _ => ⟨i.val + 1, succ_lt_of_lt_pred i.isLt⟩) ?_ ?_ ?_
  · intro i hi
    have hi' := List.mem_filter.mp (List.mem_toFinset.mp hi)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp, ?_⟩
    simpa using hi'.2
  · intro i _ j _ h
    exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
  · intro l hl
    obtain ⟨-, hl0, hls⟩ := Finset.mem_filter.mp hl
    refine ⟨⟨l.val - 1, by omega⟩, ?_, ?_⟩
    · refine List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩)
      rw [decide_eq_true_eq]
      convert hls
      change l.val - 1 + 1 = l.val
      omega
    · exact Fin.ext (show l.val - 1 + 1 = l.val by omega)

theorem starXCount_add_length (x : Fin S) :
    starXCount (sel F hS hN x) (leaves F hS x) +
      (starEdges (center F hS hN x) (sel F hS hN x) (leaves F hS x)).length = N + B - 1 := by
  rw [starXCount, starEdges, List.length_map, ← leaves_length F hS x]
  have := List.length_eq_length_filter_add (sel F hS hN x) (l := leaves F hS x)
  omega

theorem mem_starEdges (x : Fin S) (e : Fin (prodSize F) × Fin (prodSize F)) :
    e ∈ starEdges (center F hS hN x) (sel F hS hN x) (leaves F hS x) ↔
      ∃ l : Fin (N + B), l.val ≠ 0 ∧ Selected F hN x l ∧ e = (colZ F hS l x, center F hS hN x) := by
  simp only [starEdges, List.mem_map, List.mem_filter, mem_leaves]
  constructor
  · rintro ⟨z, ⟨⟨l, hl, rfl⟩, hs⟩, rfl⟩
    rw [sel_colZ F hS hN x l hl, decide_eq_true_eq] at hs
    exact ⟨l, hl, hs, rfl⟩
  · rintro ⟨l, hl, hs, rfl⟩
    exact ⟨colZ F hS l x, ⟨⟨l, hl, rfl⟩, by
      rw [sel_colZ F hS hN x l hl, decide_eq_true_eq]
      exact hs⟩, rfl⟩

end Selection


/-! ### One rank of the star scissors -/

theorem finRotate_of_succ_lt {r : ℕ} (l : Fin r) (h : l.val + 1 < r) :
    finRotate r l = ⟨l.val + 1, h⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact GridMoves.finRotate_eq_of_val_eq_succ rfl

theorem finRotate_of_succ_eq {r : ℕ} (l : Fin r) (h : l.val + 1 = r) :
    finRotate r l = ⟨0, by omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain rfl : l = Fin.last k := Fin.ext (by simp; omega)
  rw [finRotate_last]; rfl

theorem starPerm_mem {n : ℕ} (μ : Equiv.Perm (Fin n)) (c : Fin n) (L : List (Fin n))
    (hnd : L.Nodup) (hc : c ∉ L) (d : Fin n) (hd : d ∈ c :: L) :
    ∃ e ∈ c :: L, starPerm μ c L d = μ e := by
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨_, List.getLast_mem _, starPerm_center μ d L hnd hc⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    exact ⟨_, List.getElem_mem _, starPerm_getElem μ c L hnd hc i hi⟩

section RankStep

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S) (hN : 0 < N)

/-- The last columns of a rank. -/
def IsZAt (x : Fin S) (d : Fin (prodSize F)) : Prop := ∃ l, d = colZ F hS l x

instance (x : Fin S) : DecidablePred (IsZAt F hS x) := fun _ => by
  unfold IsZAt; infer_instance

/-- The star permutation sends every last column of the rank to the first column of the same
factor. -/
theorem starPerm_colZ (x : Fin S) (μ : Equiv.Perm (Fin (prodSize F)))
    (hZ : ∀ l, μ (colZ F hS l x) = colF F hS (finRotate (N + B) l) x) (l : Fin (N + B)) :
    starPerm μ (center F hS hN x) (leaves F hS x) (colZ F hS l x) = colF F hS l x := by
  by_cases hl : l.val = 0
  · have e : colZ F hS l x = center F hS hN x := by
      rw [center]; congr 1; exact Fin.ext hl
    rw [e, starPerm_center _ _ _ (leaves_nodup F hS x) (center_not_mem_leaves F hS hN x),
      center_cons_getLast, hZ, finRotate_of_succ_eq _ (by simp; omega)]
    congr 1; exact Fin.ext (by simp; omega)
  · have hi : l.val - 1 < (leaves F hS x).length := by
      rw [leaves_length]; have := l.isLt; omega
    have e : colZ F hS l x = (leaves F hS x)[l.val - 1] := by
      rw [leaves_getElem]; congr 1; exact Fin.ext (by simp; omega)
    rw [e, starPerm_getElem _ _ _ (leaves_nodup F hS x) (center_not_mem_leaves F hS hN x) _ hi,
      center_cons_getElem, hZ, finRotate_of_succ_lt _ (by simp; omega)]
    congr 1; exact Fin.ext (by simp; omega)

/-- **One rank of the star scissors.** -/
theorem rank_step (x : Fin S) {H : GridDiagram (prodSize F)} {k : ℕ}
    {E : List (Fin (prodSize F) × Fin (prodSize F))}
    (ℓ : List (Fin (prodSize F))) (hnd : ℓ.Nodup) (hl : ℓ.length = prodSize F)
    (hsort : ℓ.Pairwise fun a b => colHeight F a ≤ colHeight F b)
    (μ : Equiv.Perm (Fin (prodSize F))) (hμ : ∀ d, μ d ≠ d)
    (hμx : ∀ d, colHeight F d = 2 * x.val → μ d = prodPerm F d)
    (h : ScissorPhase H (phaseGrid (listPerm ℓ hnd hl) μ hμ) k E) :
    ∃ (ℓ' : List (Fin (prodSize F))) (hnd' : ℓ'.Nodup) (hl' : ℓ'.length = prodSize F)
      (hμ' : ∀ d, starPerm μ (center F hS hN x) (leaves F hS x) d ≠ d),
      ℓ'.Pairwise (fun a b => colHeight F a ≤ colHeight F b) ∧
      ScissorPhase H (phaseGrid (listPerm ℓ' hnd' hl')
          (starPerm μ (center F hS hN x) (leaves F hS x)) hμ')
        (k + starXCount (sel F hS hN x) (leaves F hS x))
        (E ++ starEdges (center F hS hN x) (sel F hS hN x) (leaves F hS x)) := by
  set c := center F hS hN x with hc
  set L := leaves F hS x with hL
  have hLnd : L.Nodup := leaves_nodup F hS x
  have hcL : c ∉ L := center_not_mem_leaves F hS hN x
  have hZ : ∀ l, μ (colZ F hS l x) = colF F hS (finRotate (N + B) l) x := fun l => by
    rw [hμx _ (colHeight_colZ F hS l x), prodPerm_colZ]
  -- the rows of the rank `x`
  set m₁ := ℓ.filter (fun d => colHeight F d < 2 * x.val) with hm₁
  set M := ℓ.filter (fun d => colHeight F d = 2 * x.val) with hM
  set m₂ := ℓ.filter (fun d => 2 * x.val < colHeight F d) with hm₂
  have hsplit : ℓ = m₁ ++ M ++ m₂ := pairwise_split _ _ ℓ hsort
  set Oth := M.filter (fun d => ¬ IsZAt F hS x d) with hOth
  set M' := Oth ++ L.reverse ++ [c] with hM'
  have hall : ∀ d, d ∈ ℓ := fun d => mem_of_listPerm ℓ hnd hl d
  have hmemM : ∀ d, d ∈ M ↔ colHeight F d = 2 * x.val := by
    intro d; simp [hM, List.mem_filter, hall d]
  have hZmem : ∀ d, IsZAt F hS x d ↔ d ∈ c :: L := by
    intro d; rw [hc, hL, mem_center_cons]; rfl
  have hmemM' : ∀ d, d ∈ M' ↔ colHeight F d = 2 * x.val := by
    intro d
    simp only [hM', List.mem_append, List.mem_reverse, List.mem_singleton, hOth, List.mem_filter,
      decide_eq_true_eq, hmemM]
    by_cases hz : IsZAt F hS x d
    · obtain ⟨l, rfl⟩ := hz
      have := (hZmem (colZ F hS l x)).mp ⟨l, rfl⟩
      simp only [List.mem_cons] at this
      simp only [colHeight_colZ, true_and]
      tauto
    · have h1 : d ∉ L := fun h => hz ((hZmem d).mpr (List.mem_cons_of_mem _ h))
      have h2 : d ≠ c := fun h => hz ((hZmem d).mpr (h ▸ List.mem_cons_self))
      simp only [hz, not_false_eq_true, and_true, h1, h2, or_false]
  have hndM : M.Nodup := hnd.filter _
  have hndM' : M'.Nodup := by
    rw [hM', List.append_assoc, List.nodup_append]
    refine ⟨hndM.filter _, ?_, ?_⟩
    · rw [List.nodup_append]
      exact ⟨List.nodup_reverse.mpr hLnd, List.nodup_singleton _, by
        intro a ha b hb; rw [List.mem_singleton] at hb; subst hb
        exact fun h => hcL (h ▸ List.mem_reverse.mp ha)⟩
    · intro a ha b hb hab
      subst hab
      rw [hOth, List.mem_filter] at ha
      apply (decide_eq_true_eq.mp ha.2)
      rw [hZmem]
      simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hb
      rcases hb with hb | hb
      · exact List.mem_cons_of_mem _ hb
      · rw [hb]; exact List.mem_cons_self
  have hperm : M.Perm M' := (List.perm_ext_iff_of_nodup hndM hndM').mpr
    (fun d => by rw [hmemM, hmemM'])
  have hpermℓ : (m₁ ++ M ++ m₂).Perm (m₁ ++ M' ++ m₂) :=
    List.Perm.append_right _ (List.Perm.append_left _ hperm)
  have hnd₀ : (m₁ ++ M ++ m₂).Nodup := by rw [← hsplit]; exact hnd
  have hl₀ : (m₁ ++ M ++ m₂).length = prodSize F := by rw [← hsplit]; exact hl
  have hnd₁ : (m₁ ++ M' ++ m₂).Nodup := hpermℓ.nodup_iff.mp hnd₀
  have hl₁ : (m₁ ++ M' ++ m₂).length = prodSize F := by rw [← hpermℓ.length_eq, hl₀]
  -- the rows of the rank are pairwise noninterleaving
  have hniM : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → NonintN a.val (μ a).val b.val (μ b).val := by
    intro a ha b hb hab
    rw [hmemM] at ha hb
    rw [hμx a ha, hμx b hb]
    obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨p', rfl⟩ := finProdFinEquiv.surjective b
    rw [colHeight_col] at ha hb
    rw [prodPerm_apply, prodPerm_apply]
    have hp : p.2 ≠ 0 := fun h0 => by
      have := (oHeight2_odd_iff _ p).mpr h0; omega
    have hp' : p'.2 ≠ 0 := fun h0 => by
      have := (oHeight2_odd_iff _ p').mpr h0; omega
    exact nonintN_sameHeight _ hp hp' (by rw [ha, hb]) (fun e => hab (by rw [e]))
  have h₁ : ScissorPhase H (phaseGrid (listPerm _ hnd₁ hl₁) μ hμ) k E := by
    apply ScissorPhase.of_rowCommutations (by rwa [listPerm_congr hsplit hnd hl hnd₀ hl₀] at h)
    exact reflTransGen_rowCommutation_perm μ hμ hperm hniM m₁ m₂ hnd₀ hl₀ hnd₁ hl₁
  -- the star
  have eM : m₁ ++ M' ++ m₂ = (m₁ ++ Oth) ++ L.reverse ++ c :: m₂ := by simp [hM']
  have hnd₂ : ((m₁ ++ Oth) ++ L.reverse ++ c :: m₂).Nodup := by rw [← eM]; exact hnd₁
  have hl₂ : ((m₁ ++ Oth) ++ L.reverse ++ c :: m₂).length = prodSize F := by rw [← eM]; exact hl₁
  have hperm₃ : ((m₁ ++ Oth) ++ L.reverse ++ c :: m₂).Perm
      ((m₁ ++ Oth) ++ c :: (L.reverse ++ m₂)) := by
    rw [List.append_assoc (m₁ ++ Oth)]
    exact List.Perm.append_left _ (List.perm_middle.trans (List.Perm.cons _ (List.Perm.refl _)))
  have hnd₃ : ((m₁ ++ Oth) ++ c :: (L.reverse ++ m₂)).Nodup := hperm₃.nodup_iff.mp hnd₂
  have hl₃ : ((m₁ ++ Oth) ++ c :: (L.reverse ++ m₂)).length = prodSize F := by
    rw [← hperm₃.length_eq, hl₂]
  have hfp : ∀ i ≤ L.length, ∀ d, starPerm μ c (L.take i) d ≠ d := by
    intro i _ d hd
    have hndi : (L.take i).Nodup := hLnd.sublist (List.take_sublist _ _)
    have hci : c ∉ L.take i := fun h => hcL ((List.take_sublist _ _).subset h)
    by_cases hdm : d ∈ c :: L.take i
    · obtain ⟨e, he, hval⟩ := starPerm_mem μ c _ hndi hci d hdm
      have he' : e ∈ c :: L := by
        rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((List.take_sublist _ _).subset he)
      have hd' : d ∈ c :: L := by
        rcases List.mem_cons.mp hdm with rfl | hdm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((List.take_sublist _ _).subset hdm)
      obtain ⟨le, rfl⟩ := (hZmem e).mpr he'
      obtain ⟨ld, rfl⟩ := (hZmem d).mpr hd'
      rw [hval, hZ] at hd
      exact colF_ne_colZ F hS _ _ _ _ hd
    · rw [starPerm_of_not_mem μ c _ d (fun h => hdm (h ▸ List.mem_cons_self))
        (fun h => hdm (List.mem_cons_of_mem _ h))] at hd
      exact hμ d hd
  have hni : ∀ (i : ℕ) (hi : i < L.length),
      NonintN c.val (μ L[i]).val (L[i]).val (μ ((c :: L)[i]'(by simp; omega))).val := by
    intro i hi
    have hi' : i < N + B - 1 := by rw [hL, leaves_length] at hi; exact hi
    have e1 : L[i] = colZ F hS ⟨i + 1, by omega⟩ x := leaves_getElem F hS x i hi
    have e2 : (c :: L)[i]'(by simp; omega) = colZ F hS ⟨i, by omega⟩ x :=
      center_cons_getElem F hS hN x i (Nat.lt_succ_of_lt hi)
    rw [e1, e2, hZ, hZ, finRotate_of_succ_lt (⟨i, by omega⟩ : Fin (N + B)) (by simp; omega)]
    have hc0 : c = colZ F hS ⟨0, by omega⟩ x := rfl
    rw [hc0]
    by_cases h2 : i + 2 < N + B
    · rw [finRotate_of_succ_lt (⟨i + 1, by omega⟩ : Fin (N + B)) (by simp; omega)]
      exact nonintN_of_chain (colZ_lt_colF F hS (by simp) x x) (colF_lt_colZ F hS _ x)
        (colZ_lt_colF F hS (by simp) x x)
    · rw [finRotate_of_succ_eq (⟨i + 1, by omega⟩ : Fin (N + B)) (by simp; omega)]
      exact nonintN_of_wrap (colF_lt_colZ F hS _ x) (colZ_lt_colF F hS (by simp) x x)
        (colF_lt_colZ F hS _ x)
  have h₂ : ScissorPhase H (phaseGrid (listPerm _ hnd₂ hl₂) μ hμ) k E := by
    rwa [← listPerm_congr eM hnd₁ hl₁ hnd₂ hl₂]
  have hstar := ScissorPhase.star_index c (sel F hS hN x) L hLnd hcL μ hμ hfp hni (m₁ ++ Oth) m₂
    hnd₂ hl₂ hnd₃ hl₃ h₂
  refine ⟨_, hnd₃, hl₃, _, ?_, hstar⟩
  -- the rows remain ordered by height
  have hblock : ∀ d ∈ Oth ++ c :: L.reverse, colHeight F d = 2 * x.val := by
    intro d hd
    rw [← hmemM', hM']
    simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hd ⊢
    tauto
  have e3 : (m₁ ++ Oth) ++ c :: (L.reverse ++ m₂) = m₁ ++ (Oth ++ c :: L.reverse) ++ m₂ := by simp
  rw [e3]
  have hs₁ : m₁.Pairwise fun a b => colHeight F a ≤ colHeight F b := hsort.filter _
  have hs₂ : m₂.Pairwise fun a b => colHeight F a ≤ colHeight F b := hsort.filter _
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨hs₁, List.pairwise_of_forall_mem_list fun a ha b hb => by
      rw [hblock a ha, hblock b hb], fun a ha b hb => ?_⟩, hs₂, fun a ha b hb => ?_⟩
  · have := (List.mem_filter.mp ha).2; simp at this; rw [hblock b hb]; omega
  · have := (List.mem_filter.mp hb).2
    simp only [decide_eq_true_eq] at this
    rcases List.mem_append.mp ha with ha | ha
    · have := (List.mem_filter.mp ha).2; simp at this; omega
    · rw [hblock a ha]; omega

end RankStep


/-! ### All ranks -/

section AllRanks

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S) (hN : 0 < N)

/-- The rows of a signed word grid of the product are ordered by height. -/
theorem rowList_sorted {H : GridDiagram (prodSize F)}
    (hH : IsSignedWordGrid (factorProduct F.factor) H) :
    (rowList H).Pairwise fun a b => colHeight F a ≤ colHeight F b := by
  rw [rowList, List.pairwise_map]
  refine (List.pairwise_lt_finRange _).imp fun {i j} hij => ?_
  by_contra hlt
  push Not at hlt
  have := hH.O_lt (finProdFinEquiv.symm (H.O.toPerm.symm j))
    (finProdFinEquiv.symm (H.O.toPerm.symm i)) hlt
  simp only [Equiv.apply_symm_apply] at this
  exact absurd hij (not_lt.mpr this.le)

theorem phaseGrid_rowList {H : GridDiagram (prodSize F)}
    (hH : IsSignedWordGrid (factorProduct F.factor) H) :
    phaseGrid (listPerm (rowList H) (rowList_nodup H) (rowList_length H)) (prodPerm F)
      (prodPerm_ne F) = H := by
  conv_rhs => rw [eq_phaseGrid H]
  exact phaseGrid_congr (listPerm_rowList H) (gridComponentPerm_eq_prodPerm F hH).symm _ _

/-- **The star scissors at the ranks `1, …, t`.** -/
theorem exists_phase_upto (htrans : F.Transitive) {H : GridDiagram (prodSize F)}
    (hH : IsSignedWordGrid (factorProduct F.factor) H) :
    ∀ t, t ≤ S - 1 → ∃ (ℓ : List (Fin (prodSize F))) (hnd : ℓ.Nodup)
      (hl : ℓ.length = prodSize F) (μ : Equiv.Perm (Fin (prodSize F))) (hμ : ∀ d, μ d ≠ d)
      (k : ℕ) (E : List (Fin (prodSize F) × Fin (prodSize F))),
      ℓ.Pairwise (fun a b => colHeight F a ≤ colHeight F b) ∧
      (∀ l (x : Fin S), 1 ≤ x.val → x.val ≤ t → μ (colZ F hS l x) = colF F hS l x) ∧
      (∀ d, (∀ l (x : Fin S), 1 ≤ x.val → x.val ≤ t → d ≠ colZ F hS l x) →
        μ d = prodPerm F d) ∧
      ScissorPhase H (phaseGrid (listPerm ℓ hnd hl) μ hμ) k E ∧
      k + E.length = t * (N + B - 1) ∧
      (∀ e, e ∈ E ↔ ∃ (x : Fin S) (l : Fin (N + B)), 1 ≤ x.val ∧ x.val ≤ t ∧ l.val ≠ 0 ∧
        Selected F hN x l ∧ e = (colZ F hS l x, center F hS hN x)) ∧
      E.length = ∑ x ∈ Finset.univ.filter (fun x : Fin S => 1 ≤ x.val ∧ x.val ≤ t),
        (Finset.univ.filter fun l : Fin (N + B) => F.factorPerm l x = x).card := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rowList H, rowList_nodup H, rowList_length H, prodPerm F, prodPerm_ne F, 0, [],
      rowList_sorted F hH, fun l x h1 h2 => by omega, fun d _ => rfl, ?_, by simp,
      fun e => by
        simp only [List.not_mem_nil, nonpos_iff_eq_zero, ne_eq, exists_and_left, false_iff,
          not_exists, not_and]
        intro x _ _ _
        omega, ?_⟩
    · rw [phaseGrid_rowList F hH]; exact .refl H
    · simp only [List.length_nil]
      symm
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter] at hx
      omega
  | succ t ih =>
    intro ht
    obtain ⟨ℓ, hnd, hl, μ, hμ, k, E, hsort, hZ, hrest, hph, hk, hmem, hlen⟩ := ih (by omega)
    set x : Fin S := ⟨t + 1, by omega⟩ with hx
    have hμx : ∀ d, colHeight F d = 2 * x.val → μ d = prodPerm F d := by
      intro d hd
      apply hrest
      intro l x' h1 h2 he
      rw [he, colHeight_colZ] at hd
      simp [hx] at hd; omega
    obtain ⟨ℓ', hnd', hl', hμ', hsort', hph'⟩ := rank_step F hS hN x ℓ hnd hl hsort μ hμ hμx hph
    have hZx : ∀ l, μ (colZ F hS l x) = colF F hS (finRotate (N + B) l) x := fun l => by
      rw [hμx _ (colHeight_colZ F hS l x), prodPerm_colZ]
    -- columns of the other ranks are not moved by the star
    have hnot : ∀ d, (∀ l, d ≠ colZ F hS l x) →
        starPerm μ (center F hS hN x) (leaves F hS x) d = μ d := by
      intro d hd
      apply starPerm_of_not_mem
      · exact fun h => hd _ h
      · intro h
        obtain ⟨l, -, rfl⟩ := (mem_leaves F hS x d).mp h
        exact hd l rfl
    refine ⟨ℓ', hnd', hl', _, hμ', _, _, hsort', ?_, ?_, hph', ?_, ?_, ?_⟩
    · intro l x' h1 h2
      by_cases hxx : x'.val = t + 1
      · have : x' = x := Fin.ext hxx
        subst this
        exact starPerm_colZ F hS hN x μ hZx l
      · rw [hnot _ (fun l' he => by
          have := congrArg (colHeight F) he
          rw [colHeight_colZ, colHeight_colZ] at this
          simp [hx] at this; omega)]
        exact hZ l x' h1 (by omega)
    · intro d hd
      rw [hnot d (fun l he => hd l x (by simp [hx]) (by simp [hx]) he)]
      exact hrest d (fun l x' h1 h2 => hd l x' h1 (by omega))
    · have := starXCount_add_length F hS hN x
      rw [List.length_append]
      rw [Nat.add_mul, one_mul]
      omega
    · intro e
      rw [List.mem_append, hmem, mem_starEdges]
      constructor
      · rintro (⟨x', l, h1, h2, h3, h4, rfl⟩ | ⟨l, h3, h4, rfl⟩)
        · exact ⟨x', l, h1, by omega, h3, h4, rfl⟩
        · exact ⟨x, l, by simp [hx], by simp [hx], h3, h4, rfl⟩
      · rintro ⟨x', l, h1, h2, h3, h4, rfl⟩
        by_cases hxx : x'.val = t + 1
        · have : x' = x := Fin.ext hxx
          subst this
          exact Or.inr ⟨l, h3, h4, rfl⟩
        · exact Or.inl ⟨x', l, h1, by omega, h3, h4, rfl⟩
    · rw [List.length_append, hlen, length_starEdges F hS hN htrans x]
      have e : (Finset.univ.filter fun x' : Fin S => 1 ≤ x'.val ∧ x'.val ≤ t + 1) =
          insert x (Finset.univ.filter fun x' : Fin S => 1 ≤ x'.val ∧ x'.val ≤ t) := by
        ext x'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hx,
          Fin.ext_iff]
        omega
      rw [e, Finset.sum_insert (by simp [hx]), add_comm]

end AllRanks

end OnLeConjecture.KnotFloer.GridFull
