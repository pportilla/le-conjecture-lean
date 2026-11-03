/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnweightedPaths
public import Mathlib.Data.Finset.Sort

/-!
# Deleting fixed points from a seam correction path

Let `U` be a set of columns of the seam grid of parameters `n, m`. Assume that every state
visited by a correction path agrees with the initial retained state `w` on `U`, and that each
column of `U` is west or carries a high row of `w`. Deleting the columns of `U` and the rows of
`w(U)`, and relabeling the remaining columns and rows increasingly, produces a correction path of
the same length for the seam parameters `n', m'`, where `n - n'` and `m - m'` are the numbers of
west and east columns of `U`.

The relabelings are recorded in `SeamCompressionData`. Its relation `Rel` between a state and
its compression is the reusable form of the construction: compressed rectangles, matching
partners, and matching sources are characterized through it.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-! ### Increasing relabelings -/

/-- An increasing relabeling preserves membership in clockwise open intervals. -/
theorem orderEmbedding_mem_cIoo_iff {a b : ℕ} (f : Fin a ↪o Fin b) (x y z : Fin a) :
    f z ∈ Grid.cIoo (f x) (f y) ↔ z ∈ Grid.cIoo x y := by
  have hlt (u v : Fin a) : (f u).val < (f v).val ↔ u.val < v.val := by
    rw [← Fin.lt_def, ← Fin.lt_def, f.lt_iff_lt]
  simp only [Grid.mem_cIoo, ne_eq, f.injective.eq_iff, hlt]

/-- An increasing map sends exactly an initial segment of indices below a fixed bound. -/
theorem orderEmbedding_val_lt_iff {a b : ℕ} (g : Fin a ↪o Fin b) (t : ℕ) (i : Fin a) :
    (g i).val < t ↔ i.val < (Finset.univ.filter fun j : Fin a => (g j).val < t).card := by
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter fun j : Fin a => (g j).val < t := by
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ j, lt_of_le_of_lt ?_ hi⟩
      exact Fin.le_iff_val_le_val.mp (g.monotone (Finset.mem_Iic.mp hj))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hge
    have hsub : (Finset.univ.filter fun j : Fin a => (g j).val < t) ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      have hle := Fin.le_iff_val_le_val.mp (g.monotone (not_lt.mp hji))
      omega
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

/-- Counting indices of an embedding is counting its range. -/
theorem orderEmbedding_card_filter {a b : ℕ} (g : Fin a ↪o Fin b) (K : Finset (Fin b))
    (hK : Set.range g = K) (P : Fin b → Prop) [DecidablePred P] :
    (Finset.univ.filter fun j : Fin a => P (g j)).card = (K.filter P).card := by
  rw [← Finset.card_map g.toEmbedding]
  congr 1
  ext c
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hr : g j ∈ Set.range g := ⟨j, rfl⟩
    rw [hK] at hr
    exact ⟨hr, hj⟩
  · rintro ⟨hc, hP⟩
    have hr : c ∈ Set.range g := by
      rw [hK]
      exact hc
    obtain ⟨j, rfl⟩ := hr
    exact ⟨j, hP, rfl⟩

/-- A pair-sector state sends every west column to a low row. -/
theorem seamPairSector_val_le (w : GridState (n + m + 1))
    (hw : SeamPairSector (n := n) (m := m) w) (c : Fin (n + m + 1)) (hc : c.val < n) :
    (w c).val ≤ n := by
  have h := hw ⟨c.val, hc⟩
  rwa [show seamLeft n m (⟨c.val, hc⟩ : Fin n).castSucc = c from Fin.ext rfl] at h

/-! ### Compression data -/

/-- Increasing enumerations of the kept columns and kept rows of a seam grid. A column outside
the range of `col` is deleted, and the rows outside the range of `row` are the rows of the
reference state `w` in deleted columns. -/
structure SeamCompressionData (n m n' m' : ℕ) (w : GridState (n + m + 1)) where
  /-- The increasing enumeration of the kept columns. -/
  col : Fin (n' + m' + 1) ↪o Fin (n + m + 1)
  /-- The increasing enumeration of the kept rows. -/
  row : Fin (n' + m' + 1) ↪o Fin (n + m + 1)
  /-- The reference state lies in the image of all pairs of factor states. -/
  sector : SeamPairSector (n := n) (m := m) w
  /-- The kept west columns are exactly the first `n'` kept columns. -/
  col_lt_iff : ∀ i, (col i).val < n ↔ i.val < n'
  /-- The kept low rows are exactly the first `n' + 1` kept rows. -/
  row_le_iff : ∀ j, (row j).val ≤ n ↔ j.val ≤ n'
  /-- A deleted column is west or carries a high reference row. -/
  deleted_type : ∀ c, c ∉ Set.range col → c.val < n ∨ n < (w c).val
  /-- Every deleted row is the reference row of a deleted column. -/
  deleted_row : ∀ r, r ∉ Set.range row → ∃ c, c ∉ Set.range col ∧ w c = r

namespace SeamCompressionData

variable {n' m' : ℕ} {w : GridState (n + m + 1)} (D : SeamCompressionData n m n' m' w)

/-- A state agrees with the reference state on every deleted column. -/
def Fixes (v : GridState (n + m + 1)) : Prop :=
  ∀ c, c ∉ Set.range D.col → v c = w c

/-- The state `v'` is the compression of `v`: the relabelings carry the points of `v'` to the
points of `v` in kept columns. -/
def Rel (v : GridState (n + m + 1)) (v' : GridState (n' + m' + 1)) : Prop :=
  ∀ i, D.row (v' i) = v (D.col i)

theorem fixes_ref : D.Fixes w := fun _ _ => rfl

/-- A state fixing the deleted columns sends kept columns to kept rows. -/
theorem mem_range_row {v : GridState (n + m + 1)} (hv : D.Fixes v) (i : Fin (n' + m' + 1)) :
    v (D.col i) ∈ Set.range D.row := by
  by_contra h
  obtain ⟨c, hc, hwc⟩ := D.deleted_row _ h
  have he : v c = v (D.col i) := (hv c hc).trans hwc
  exact hc ⟨i, (v.toPerm.injective he).symm⟩

/-- The column-to-row function of the compressed state. -/
def stateFun {v : GridState (n + m + 1)} (hv : D.Fixes v) (i : Fin (n' + m' + 1)) :
    Fin (n' + m' + 1) :=
  (D.mem_range_row hv i).choose

theorem row_stateFun {v : GridState (n + m + 1)} (hv : D.Fixes v) (i : Fin (n' + m' + 1)) :
    D.row (D.stateFun hv i) = v (D.col i) :=
  (D.mem_range_row hv i).choose_spec

theorem stateFun_injective {v : GridState (n + m + 1)} (hv : D.Fixes v) :
    Function.Injective (D.stateFun hv) := by
  intro i j hij
  apply D.col.injective
  apply v.toPerm.injective
  change v (D.col i) = v (D.col j)
  rw [← D.row_stateFun hv i, ← D.row_stateFun hv j, hij]

/-- The compressed state of a state fixing the deleted columns. -/
def state (v : GridState (n + m + 1)) (hv : D.Fixes v) : GridState (n' + m' + 1) :=
  ⟨Equiv.ofBijective (D.stateFun hv)
    ⟨D.stateFun_injective hv, Finite.surjective_of_injective (D.stateFun_injective hv)⟩⟩

theorem rel_state {v : GridState (n + m + 1)} (hv : D.Fixes v) : D.Rel v (D.state v hv) :=
  fun i => D.row_stateFun hv i

/-- The compression of a state is unique. -/
theorem eq_of_rel_of_rel {v : GridState (n + m + 1)} {v' v'' : GridState (n' + m' + 1)}
    (h' : D.Rel v v') (h'' : D.Rel v v'') : v' = v'' :=
  GridState.ext fun i => D.row.injective ((h' i).trans (h'' i).symm)

/-- States fixing the deleted columns with equal compressions are equal. -/
theorem eq_of_rel {u v : GridState (n + m + 1)} {u' v' : GridState (n' + m' + 1)}
    (hu : D.Fixes u) (hv : D.Fixes v) (hu' : D.Rel u u') (hv' : D.Rel v v') (h : u' = v') :
    u = v := by
  subst h
  apply GridState.ext
  intro c
  by_cases hc : c ∈ Set.range D.col
  · obtain ⟨i, rfl⟩ := hc
    rw [← hu' i, ← hv' i]
  · rw [hu c hc, hv c hc]

/-! ### Seam sectors -/

/-- Compression preserves the image of all pairs of factor states. -/
theorem pairSector_of_rel {v : GridState (n + m + 1)} {v' : GridState (n' + m' + 1)}
    (hv : SeamPairSector (n := n) (m := m) v) (h : D.Rel v v') :
    SeamPairSector (n := n') (m := m') v' := by
  intro c
  have hi : (seamLeft n' m' c.castSucc).val < n' := c.isLt
  have hle := seamPairSector_val_le v hv _ ((D.col_lt_iff _).mpr hi)
  rw [← h] at hle
  exact (D.row_le_iff _).mp hle

/-- Compression preserves the complement of the image of all pairs of factor states. -/
theorem not_pairSector_of_rel {v : GridState (n + m + 1)} {v' : GridState (n' + m' + 1)}
    (hfix : D.Fixes v) (hv : ¬ SeamPairSector (n := n) (m := m) v) (h : D.Rel v v') :
    ¬ SeamPairSector (n := n') (m := m') v' := by
  rw [not_seamPairSector_iff] at hv ⊢
  obtain ⟨c, hc⟩ := hv
  have hd : (seamLeft n m c.castSucc).val < n := c.isLt
  have hmem : seamLeft n m c.castSucc ∈ Set.range D.col := by
    by_contra hnot
    rw [hfix _ hnot] at hc
    have hle := seamPairSector_val_le w D.sector _ hd
    omega
  obtain ⟨i, hi⟩ := hmem
  have hin : i.val < n' := (D.col_lt_iff i).mp (by rw [hi]; exact hd)
  refine ⟨⟨i.val, hin⟩, ?_⟩
  rw [show seamLeft n' m' (⟨i.val, hin⟩ : Fin n').castSucc = i from Fin.ext rfl]
  rw [← hi, ← h i] at hc
  by_contra hle
  have hrow := (D.row_le_iff (v' i)).mpr (by omega)
  omega

/-! ### Southwest columns and matching partners -/

/-- Compression preserves southwest columns. -/
theorem mem_southwest_iff {v : GridState (n + m + 1)} {v' : GridState (n' + m' + 1)}
    (h : D.Rel v v') (i : Fin (n' + m' + 1)) :
    i ∈ seamSouthwestColumns (n := n') (m := m') v' ↔
      D.col i ∈ seamSouthwestColumns (n := n) (m := m) v := by
  have hc : n' ≤ i.val ↔ n ≤ (D.col i).val := by
    rw [← not_lt, ← not_lt, D.col_lt_iff]
  rw [mem_seamSouthwestColumns, mem_seamSouthwestColumns, ← h i, D.row_le_iff, hc]

/-- A deleted column is never southwest for a state fixing the deleted columns. -/
theorem southwest_mem_range {v : GridState (n + m + 1)} (hv : D.Fixes v)
    {c : Fin (n + m + 1)} (hc : c ∈ seamSouthwestColumns (n := n) (m := m) v) :
    c ∈ Set.range D.col := by
  by_contra hnot
  rw [mem_seamSouthwestColumns, hv c hnot] at hc
  rcases D.deleted_type c hnot with h | h <;> omega

/-- The compressed complementary state. -/
def complement (x : SeamComplement n m) (hx : D.Fixes x.val) : SeamComplement n' m' :=
  ⟨D.state x.val hx, D.not_pairSector_of_rel hx x.property (D.rel_state hx)⟩

theorem rel_complement (x : SeamComplement n m) (hx : D.Fixes x.val) :
    D.Rel x.val (D.complement x hx).val :=
  D.rel_state hx

/-- Compression preserves the first southwest column. -/
theorem col_complementFirst (x : SeamComplement n m) (hx : D.Fixes x.val) :
    D.col (seamComplementFirst (D.complement x hx)) = seamComplementFirst x := by
  have hrel := D.rel_complement x hx
  have h1 : D.col (seamComplementFirst (D.complement x hx)) ∈ seamSouthwestColumns x.val :=
    (D.mem_southwest_iff hrel _).mp (seamComplementFirst_mem _)
  obtain ⟨j, hj⟩ := D.southwest_mem_range hx (seamComplementFirst_mem x)
  have hjm : j ∈ seamSouthwestColumns (D.complement x hx).val :=
    (D.mem_southwest_iff hrel j).mpr (by rw [hj]; exact seamComplementFirst_mem x)
  apply le_antisymm
  · rw [← hj]
    exact D.col.monotone (Finset.min'_le _ _ hjm)
  · exact Finset.min'_le _ _ h1

/-- Compression preserves the second southwest column. -/
theorem col_complementSecond (x : SeamComplement n m) (hx : D.Fixes x.val) :
    D.col (seamComplementSecond (D.complement x hx)) = seamComplementSecond x := by
  have hrel := D.rel_complement x hx
  have hf := D.col_complementFirst x hx
  have hmem := seamComplementSecond_mem_erase (D.complement x hx)
  rw [Finset.mem_erase] at hmem
  have h1 : D.col (seamComplementSecond (D.complement x hx)) ∈
      (seamSouthwestColumns x.val).erase (seamComplementFirst x) := by
    rw [Finset.mem_erase]
    refine ⟨?_, (D.mem_southwest_iff hrel _).mp hmem.2⟩
    rw [← hf]
    exact fun he => hmem.1 (D.col.injective he)
  have hmem2 := seamComplementSecond_mem_erase x
  rw [Finset.mem_erase] at hmem2
  obtain ⟨j, hj⟩ := D.southwest_mem_range hx hmem2.2
  have hjm : j ∈ (seamSouthwestColumns (D.complement x hx).val).erase
      (seamComplementFirst (D.complement x hx)) := by
    rw [Finset.mem_erase]
    refine ⟨fun he => hmem2.1 ?_, (D.mem_southwest_iff hrel j).mpr (by rw [hj]; exact hmem2.2)⟩
    rw [← hj, he, hf]
  apply le_antisymm
  · rw [← hj]
    exact D.col.monotone (Finset.min'_le _ _ hjm)
  · exact Finset.min'_le _ _ h1

/-- The matching partner of a state fixing the deleted columns fixes them as well. -/
theorem fixes_partner (x : SeamComplement n m) (hx : D.Fixes x.val) :
    D.Fixes (seamComplementPartner x).val := by
  intro c hc
  change x.val.swapColumns _ _ c = w c
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne, hx c hc]
  · intro he
    rw [he] at hc
    exact hc (D.southwest_mem_range hx (seamComplementFirst_mem x))
  · intro he
    rw [he] at hc
    exact hc (D.southwest_mem_range hx (seamComplementSecond_mem x))

/-- Compression commutes with the matching partner. -/
theorem rel_partner (x : SeamComplement n m) (hx : D.Fixes x.val) :
    D.Rel (seamComplementPartner x).val (seamComplementPartner (D.complement x hx)).val := by
  intro i
  change D.row ((D.complement x hx).val.swapColumns _ _ i) = x.val.swapColumns _ _ (D.col i)
  rw [GridState.swapColumns_apply, GridState.swapColumns_apply, D.rel_complement x hx,
    ← D.col_complementFirst x hx, ← D.col_complementSecond x hx, D.col.injective.swap_apply]

/-- Compression preserves the increasing orientation of a matching source. -/
theorem complementSource (x : SeamComplement n m) (hx : D.Fixes x.val)
    (hs : SeamComplementSource x) : SeamComplementSource (D.complement x hx) := by
  unfold SeamComplementSource at hs ⊢
  rw [← D.col_complementFirst x hx, ← D.col_complementSecond x hx,
    ← D.rel_complement x hx, ← D.rel_complement x hx] at hs
  exact Fin.lt_def.mp (D.row.lt_iff_lt.mp (Fin.lt_def.mpr hs))

/-- The compressed matching source. -/
def source (x : SeamMatchingSource n m) (hx : D.Fixes x.val.val) : SeamMatchingSource n' m' :=
  ⟨D.complement x.val hx, D.complementSource x.val hx x.property⟩

theorem source_injective {x y : SeamMatchingSource n m} (hx : D.Fixes x.val.val)
    (hy : D.Fixes y.val.val) (h : D.source x hx = D.source y hy) : x = y := by
  have h' : D.state x.val.val hx = D.state y.val.val hy := congrArg (fun z => z.val.val) h
  exact Subtype.ext (Subtype.ext (D.eq_of_rel hx hy (D.rel_state hx) (D.rel_state hy) h'))

theorem source_congr {x y : SeamMatchingSource n m} (h : x = y) (hx : D.Fixes x.val.val)
    (hy : D.Fixes y.val.val) : D.source x hx = D.source y hy := by
  subst h
  rfl

/-! ### Rectangles -/

/-- A rectangle between states fixing the deleted columns has a kept initial side. -/
theorem left_mem_range {a b : GridState (n + m + 1)} (r : GridRectangleBetween a b)
    (ha : D.Fixes a) (hb : D.Fixes b) : r.left ∈ Set.range D.col := by
  by_contra h
  have h1 := r.map_left
  rw [hb _ h, ← ha _ h] at h1
  exact r.left_ne_right (a.toPerm.injective h1)

/-- A rectangle between states fixing the deleted columns has a kept terminal side. -/
theorem right_mem_range {a b : GridState (n + m + 1)} (r : GridRectangleBetween a b)
    (ha : D.Fixes a) (hb : D.Fixes b) : r.right ∈ Set.range D.col := by
  by_contra h
  have h1 := r.map_right
  rw [hb _ h, ← ha _ h] at h1
  exact r.left_ne_right (a.toPerm.injective h1).symm

/-- The compressed initial side. -/
def rectLeft {a b : GridState (n + m + 1)} (r : GridRectangleBetween a b)
    (ha : D.Fixes a) (hb : D.Fixes b) : Fin (n' + m' + 1) :=
  (D.left_mem_range r ha hb).choose

/-- The compressed terminal side. -/
def rectRight {a b : GridState (n + m + 1)} (r : GridRectangleBetween a b)
    (ha : D.Fixes a) (hb : D.Fixes b) : Fin (n' + m' + 1) :=
  (D.right_mem_range r ha hb).choose

theorem col_rectLeft {a b : GridState (n + m + 1)} (r : GridRectangleBetween a b)
    (ha : D.Fixes a) (hb : D.Fixes b) : D.col (D.rectLeft r ha hb) = r.left :=
  (D.left_mem_range r ha hb).choose_spec

theorem col_rectRight {a b : GridState (n + m + 1)} (r : GridRectangleBetween a b)
    (ha : D.Fixes a) (hb : D.Fixes b) : D.col (D.rectRight r ha hb) = r.right :=
  (D.right_mem_range r ha hb).choose_spec

/-- The compressed rectangle between compressed states, with the relabeled sides. -/
def rect {a b : GridState (n + m + 1)} {a' b' : GridState (n' + m' + 1)}
    (r : GridRectangleBetween a b) (ha : D.Fixes a) (hb : D.Fixes b)
    (ha' : D.Rel a a') (hb' : D.Rel b b') : GridRectangleBetween a' b' where
  left := D.rectLeft r ha hb
  right := D.rectRight r ha hb
  left_ne_right := fun h => r.left_ne_right (by
    rw [← D.col_rectLeft r ha hb, ← D.col_rectRight r ha hb, h])
  map_left := D.row.injective (by
    rw [hb', ha', D.col_rectLeft, D.col_rectRight, r.map_left])
  map_right := D.row.injective (by
    rw [hb', ha', D.col_rectLeft, D.col_rectRight, r.map_right])
  map_of_ne := fun i hl hr => D.row.injective (by
    rw [hb', ha']
    apply r.map_of_ne
    · rw [← D.col_rectLeft r ha hb]
      exact fun he => hl (D.col.injective he)
    · rw [← D.col_rectRight r ha hb]
      exact fun he => hr (D.col.injective he))

@[simp] theorem rect_left {a b : GridState (n + m + 1)} {a' b' : GridState (n' + m' + 1)}
    (r : GridRectangleBetween a b) (ha : D.Fixes a) (hb : D.Fixes b)
    (ha' : D.Rel a a') (hb' : D.Rel b b') :
    D.col (D.rect r ha hb ha' hb').left = r.left :=
  D.col_rectLeft r ha hb

@[simp] theorem rect_right {a b : GridState (n + m + 1)} {a' b' : GridState (n' + m' + 1)}
    (r : GridRectangleBetween a b) (ha : D.Fixes a) (hb : D.Fixes b)
    (ha' : D.Rel a a') (hb' : D.Rel b b') :
    D.col (D.rect r ha hb ha' hb').right = r.right :=
  D.col_rectRight r ha hb

/-- Compression preserves emptiness of rectangles. -/
theorem rect_isEmpty {a b : GridState (n + m + 1)} {a' b' : GridState (n' + m' + 1)}
    (r : GridRectangleBetween a b) (ha : D.Fixes a) (hb : D.Fixes b)
    (ha' : D.Rel a a') (hb' : D.Rel b b') (hr : r.IsEmpty) :
    (D.rect r ha hb ha' hb').IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo] at hr ⊢
  intro i hi
  have hi' : D.col i ∈ Grid.cIoo r.left r.right := by
    rw [← D.rect_left r ha hb ha' hb', ← D.rect_right r ha hb ha' hb',
      orderEmbedding_mem_cIoo_iff]
    exact hi
  have h := hr (D.col i) hi'
  rw [bottom_def, top_def, ← D.rect_left r ha hb ha' hb', ← D.rect_right r ha hb ha' hb',
    ← ha', ← ha', ← ha', orderEmbedding_mem_cIoo_iff] at h
  rw [bottom_def, top_def]
  exact h

end SeamCompressionData

/-! ### Internal paths -/

/-- The matching sources visited by an internal path, in order. -/
def SeamInternalPath.sources : {k : ℕ} → {x y : SeamMatchingSource n m} →
    SeamInternalPath k x y → List (SeamMatchingSource n m)
  | 0, x, _, _ => [x]
  | _ + 1, x, _, π => x :: SeamInternalPath.sources π.2.2

theorem SeamInternalPath.left_mem_sources {k : ℕ} {x y : SeamMatchingSource n m}
    (π : SeamInternalPath k x y) : x ∈ π.sources := by
  cases k with
  | zero => exact List.mem_singleton_self x
  | succ k => exact List.mem_cons_self

theorem SeamInternalPath.right_mem_sources : {k : ℕ} → {x y : SeamMatchingSource n m} →
    (π : SeamInternalPath k x y) → y ∈ π.sources
  | 0, x, y, π => by
    have h : x = y := π.property
    subst h
    exact List.mem_singleton_self x
  | _ + 1, _, _, π => List.mem_cons_of_mem _ (SeamInternalPath.right_mem_sources π.2.2)

/-- The path keeps column `c` at its initial value: every visited matching source and the final
retained state agree with the initial retained state at `c`. -/
def SeamCorrectionPath.FixesColumn {k : ℕ} {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (c : Fin (n + m + 1)) : Prop :=
  (∀ s ∈ π.2.2.2.1.sources, s.val.val c = seamState p.1 p.2 c) ∧
    seamState q.1 q.2 c = seamState p.1 p.2 c

namespace SeamCompressionData

variable {n' m' : ℕ} {w : GridState (n + m + 1)} (D : SeamCompressionData n m n' m' w)

/-- The compressed internal path, with the same number of transitions. -/
def internalPath : {k : ℕ} → {x y : SeamMatchingSource n m} → (π : SeamInternalPath k x y) →
    (∀ s ∈ π.sources, D.Fixes s.val.val) → (hx : D.Fixes x.val.val) →
    (hy : D.Fixes y.val.val) → SeamInternalPath k (D.source x hx) (D.source y hy)
  | 0, _, _, π, _, hx, hy => ⟨(), D.source_congr π.property hx hy⟩
  | _ + 1, x, _, π, hπ, hx, hy =>
    have hz : D.Fixes π.1.val.val := hπ π.1 (List.mem_cons_of_mem _ π.2.2.left_mem_sources)
    ⟨D.source π.1 hz,
      ⟨D.rect π.2.1.val hx (D.fixes_partner π.1.val hz) (D.rel_complement x.val hx)
          (D.rel_partner π.1.val hz),
        fun h => π.2.1.property.1 (D.source_injective hx hz h),
        D.rect_isEmpty _ _ _ _ _ π.2.1.property.2⟩,
      internalPath π.2.2 (fun s hs => hπ s (List.mem_cons_of_mem _ hs)) hz hy⟩

/-! ### Deleting a set of columns -/

section ofDeleted

variable (w) (U : Finset (Fin (n + m + 1)))

theorem card_low_rows :
    (Finset.univ.filter fun r : Fin (n + m + 1) => r.val < n + 1).card = n + 1 := by
  have he : (Finset.univ.filter fun r : Fin (n + m + 1) => r.val < n + 1) =
      Finset.Iic (seamLeft n m (Fin.last n)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
      Fin.le_iff_val_le_val, seamLeft_val, Fin.val_last]
    omega
  rw [he, Fin.card_Iic, seamLeft_val, Fin.val_last]

theorem card_west_le :
    (U.filter fun c => c.val < n).card ≤ n := by
  have h := Finset.card_le_card (Finset.filter_subset_filter (fun c : Fin (n + m + 1) => c.val < n)
    (Finset.subset_univ U))
  rwa [seam_first_columns_card] at h

theorem card_east_le (hU : ∀ c ∈ U, c.val < n ∨ n < (w c).val) :
    (U.filter fun c => n ≤ c.val).card ≤ m := by
  have hsub : (U.filter fun c => n ≤ c.val).image w ⊆
      Finset.univ.filter fun r : Fin (n + m + 1) => ¬ r.val < n + 1 := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hU c hc.1 with h | h <;> omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ w.toPerm.injective] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun r : Fin (n + m + 1) => r.val < n + 1)
  rw [card_low_rows, Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem card_west_add_east :
    (U.filter fun c => c.val < n).card + (U.filter fun c => n ≤ c.val).card = U.card := by
  have h := Finset.card_filter_add_card_filter_not (s := U) (fun c : Fin (n + m + 1) => c.val < n)
  have he : (U.filter fun c => ¬ c.val < n) = U.filter fun c => n ≤ c.val := by
    ext c
    simp only [Finset.mem_filter, not_lt]
  rwa [he] at h

theorem card_compl_eq (hU : ∀ c ∈ U, c.val < n ∨ n < (w c).val) :
    Uᶜ.card = n - (U.filter fun c => c.val < n).card +
      (m - (U.filter fun c => n ≤ c.val).card) + 1 := by
  rw [Finset.card_compl, Fintype.card_fin, ← card_west_add_east U]
  have h1 := card_west_le U
  have h2 := card_east_le w U hU
  omega

theorem card_compl_image_eq (hU : ∀ c ∈ U, c.val < n ∨ n < (w c).val) :
    (U.image w)ᶜ.card = n - (U.filter fun c => c.val < n).card +
      (m - (U.filter fun c => n ≤ c.val).card) + 1 := by
  rw [Finset.card_compl, Finset.card_image_of_injective _ w.toPerm.injective]
  rw [← card_compl_eq w U hU, Finset.card_compl]

theorem card_compl_filter_west :
    (Uᶜ.filter fun c => c.val < n).card = n - (U.filter fun c => c.val < n).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun c : Fin (n + m + 1) => c.val < n) (fun c => c ∈ U)
  rw [seam_first_columns_card] at h
  have e1 : ((Finset.univ.filter fun c : Fin (n + m + 1) => c.val < n).filter fun c => c ∈ U) =
      U.filter fun c => c.val < n := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  have e2 : ((Finset.univ.filter fun c : Fin (n + m + 1) => c.val < n).filter
      fun c => c ∉ U) = Uᶜ.filter fun c => c.val < n := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, and_comm]
  rw [e1, e2] at h
  omega

theorem card_compl_image_filter_low (hw : SeamPairSector (n := n) (m := m) w)
    (hU : ∀ c ∈ U, c.val < n ∨ n < (w c).val) :
    ((U.image w)ᶜ.filter fun r => r.val < n + 1).card =
      n - (U.filter fun c => c.val < n).card + 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun r : Fin (n + m + 1) => r.val < n + 1) (fun r => r ∈ U.image w)
  rw [card_low_rows] at h
  have e1 : ((Finset.univ.filter fun r : Fin (n + m + 1) => r.val < n + 1).filter
      fun r => r ∈ U.image w) = (U.filter fun c => c.val < n).image w := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hr, c, hc, rfl⟩
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      rcases hU c hc with h | h <;> omega
    · rintro ⟨c, ⟨hc, hcn⟩, rfl⟩
      exact ⟨by have := seamPairSector_val_le w hw c hcn; omega, c, hc, rfl⟩
  have e2 : ((Finset.univ.filter fun r : Fin (n + m + 1) => r.val < n + 1).filter
      fun r => r ∉ U.image w) = (U.image w)ᶜ.filter fun r => r.val < n + 1 := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, and_comm]
  rw [e1, e2, Finset.card_image_of_injective _ w.toPerm.injective] at h
  have h1 := card_west_le U
  omega

/-- The compression data deleting the columns of `U` and the reference rows of `U`. -/
def ofDeleted (hw : SeamPairSector (n := n) (m := m) w)
    (hU : ∀ c ∈ U, c.val < n ∨ n < (w c).val) :
    SeamCompressionData n m (n - (U.filter fun c => c.val < n).card)
      (m - (U.filter fun c => n ≤ c.val).card) w where
  col := Uᶜ.orderEmbOfFin (card_compl_eq w U hU)
  row := (U.image w)ᶜ.orderEmbOfFin (card_compl_image_eq w U hU)
  sector := hw
  col_lt_iff := fun i => by
    rw [orderEmbedding_val_lt_iff _ n i, orderEmbedding_card_filter _ Uᶜ
      (Finset.range_orderEmbOfFin _ _) (fun c => c.val < n), card_compl_filter_west]
  row_le_iff := fun j => by
    rw [← Nat.lt_succ_iff, ← Nat.lt_succ_iff, orderEmbedding_val_lt_iff _ (n + 1) j,
      orderEmbedding_card_filter _ (U.image w)ᶜ (Finset.range_orderEmbOfFin _ _)
        (fun r => r.val < n + 1), card_compl_image_filter_low w U hw hU]
  deleted_type := fun c hc => by
    rw [Finset.range_orderEmbOfFin, Finset.coe_compl, Set.mem_compl_iff, not_not,
      Finset.mem_coe] at hc
    exact hU c hc
  deleted_row := fun r hr => by
    rw [Finset.range_orderEmbOfFin, Finset.coe_compl, Set.mem_compl_iff, not_not,
      Finset.mem_coe, Finset.mem_image] at hr
    obtain ⟨c, hc, hcr⟩ := hr
    refine ⟨c, ?_, hcr⟩
    rw [Finset.range_orderEmbOfFin, Finset.coe_compl, Set.mem_compl_iff, not_not,
      Finset.mem_coe]
    exact hc

theorem mem_range_ofDeleted_col (hw : SeamPairSector (n := n) (m := m) w)
    (hU : ∀ c ∈ U, c.val < n ∨ n < (w c).val) (c : Fin (n + m + 1)) :
    c ∈ Set.range (ofDeleted w U hw hU).col ↔ c ∉ U := by
  change c ∈ Set.range (Uᶜ.orderEmbOfFin _) ↔ _
  rw [Finset.range_orderEmbOfFin, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]

end ofDeleted

end SeamCompressionData

/-! ### Compression of correction paths -/

/-- Deleting columns kept fixed by a correction path, together with their rows, gives a
correction path of the same length for smaller seam parameters. -/
theorem SeamCorrectionPath.compress {k : ℕ} {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q)
    (U : Finset (Fin (n + m + 1))) (hfix : ∀ c ∈ U, π.FixesColumn c)
    (htype : ∀ c ∈ U, c.val < n ∨ n < (seamState p.1 p.2 c).val) :
    ∃ (n' m' : ℕ) (p' q' : SeamRetainedIndex n' m'),
      n' + (U.filter fun c => c.val < n).card = n ∧
      m' + (U.filter fun c => n ≤ c.val).card = m ∧
      Nonempty (SeamCorrectionPath (n := n') (m := m') k p' q') := by
  obtain ⟨x, y, e, ι, f⟩ := π
  have hw := seamState_mem_pairSector p.1 p.2
  let D := SeamCompressionData.ofDeleted (seamState p.1 p.2) U hw htype
  have hmem (c : Fin (n + m + 1)) (hc : c ∉ Set.range D.col) : c ∈ U := by
    by_contra h
    exact hc ((SeamCompressionData.mem_range_ofDeleted_col _ U hw htype c).mpr h)
  have hsrc : ∀ s ∈ ι.sources, D.Fixes s.val.val :=
    fun s hs c hc => (hfix c (hmem c hc)).1 s hs
  have hq : D.Fixes (seamState q.1 q.2) := fun c hc => (hfix c (hmem c hc)).2
  have hx := hsrc x ι.left_mem_sources
  have hy := hsrc y ι.right_mem_sources
  obtain ⟨p1, p2, hp⟩ := exists_seamState_of_pairSector (D.state _ D.fixes_ref)
    (D.pairSector_of_rel hw (D.rel_state _))
  obtain ⟨q1, q2, hq'⟩ := exists_seamState_of_pairSector (D.state _ hq)
    (D.pairSector_of_rel (seamState_mem_pairSector q.1 q.2) (D.rel_state hq))
  have hrp : D.Rel (seamState p.1 p.2) (seamState p1 p2) := by
    rw [hp]
    exact D.rel_state _
  have hrq : D.Rel (seamState q.1 q.2) (seamState q1 q2) := by
    rw [hq']
    exact D.rel_state _
  refine ⟨_, _, (p1, p2), (q1, q2),
    Nat.sub_add_cancel (SeamCompressionData.card_west_le U),
    Nat.sub_add_cancel (SeamCompressionData.card_east_le _ U htype), ⟨?_⟩⟩
  exact ⟨D.source x hx, D.source y hy,
    ⟨D.rect e.val D.fixes_ref (D.fixes_partner x.val hx) hrp (D.rel_partner x.val hx),
      D.rect_isEmpty _ _ _ _ _ e.property⟩,
    D.internalPath ι hsrc hx hy,
    ⟨D.rect f.val hy hq (D.rel_complement y.val hy) hrq, D.rect_isEmpty _ _ _ _ _ f.property⟩⟩

end OnLeConjecture.KnotFloer.GridFull
