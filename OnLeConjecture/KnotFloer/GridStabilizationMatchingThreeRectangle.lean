/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingShortRectangle
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingHeight

/-!
# The rectangle determined by an entry, one advance and an exit

The two inverse row-matching moves cancel outside the outer side columns. The
three full rectangles therefore determine a rectangle between the original centers.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

private theorem ordered_middle_mem {n : ℕ} {a p q k : Fin n}
    (h1 : a ∈ Grid.cIco q p) (h2 : a ∈ Grid.cIco k q) : q ∈ Grid.cIoo p k := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem split_row_interval {n : ℕ} (q : Fin n) {u v w : Fin (n + 1)}
    (hu : u ∈ Grid.cIoo q.succ v) (hw : w ∈ Grid.cIoo v u)
    (h0 : w ≠ q.castSucc) (h1 : w ≠ q.succ) :
    w ∈ Grid.cIoo v q.castSucc ∨ w ∈ Grid.cIoo q.succ u := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

/-- Away from the outer columns and the new column, the final node agrees with the first center. -/
theorem stabilizationMatchingThree_node_apply_of_ne (x : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc)
    (c : Fin (n + 1)) (hcb : c ≠ s.succ)
    (hcp : c ≠ a.val.transpose (G.X s).castSucc)
    (hck : c ≠ b.val.transpose (G.X s).succ) :
    b.val c = x.insertPoint s.succ (G.X s).succ c := by
  have es := stabilizationMatchingEntry_shape G s x a e he
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  have hv := m.map_of_ne c (by simpa only [ms.2.1] using hck)
    (by simpa only [ms.1] using hcp)
  change Equiv.swap (G.X s).castSucc (G.X s).succ (b.val c) = a.val c at hv
  rw [Equiv.swap_apply_eq_iff] at hv
  have ev := e.map_of_ne c (by simpa only [es.1] using hcb)
    (by simpa only [es.2.2.1] using hcp)
  exact hv.trans ev

/-- The value left behind on the old lower-row column is the advancing rectangle's bottom. -/
theorem stabilizationMatchingThree_previous_lowerColumn
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc) :
    b.val (a.val.transpose (G.X s).castSucc) = m.bottom := by
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  have h0 : m.bottom ≠ (G.X s).castSucc := fun h => m.bottom_ne_top (h.trans hmt.symm)
  have h1 : m.bottom ≠ (G.X s).succ := fun h =>
    stabilizationMatchingTransition_not_both_rows G s a b hab m (Or.inr hmt) (Or.inl h)
  have hv := m.map_right
  change Equiv.swap (G.X s).castSucc (G.X s).succ (b.val m.right) = m.bottom at hv
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne h0 h1, ms.1] at hv
  exact hv

/-- The first center carries the advancing bottom row on the final upper-row column. -/
theorem stabilizationMatchingThree_center_upperColumn (x : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc) :
    x.insertPoint s.succ (G.X s).succ (b.val.transpose (G.X s).succ) = m.bottom := by
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  have hkp : b.val.transpose (G.X s).succ ≠ a.val.transpose (G.X s).castSucc := by
    simpa only [ms.1, ms.2.1] using m.left_ne_right
  have hkq : b.val.transpose (G.X s).succ ≠ a.val.transpose (G.X s).succ := by
    rw [← ms.2.2]
    exact fun h => Fin.castSucc_lt_succ.ne (b.val.transpose.toPerm.injective h).symm
  rw [stabilizationMatchingEntry_center_apply_of_ne G s x a e he _
    (stabilizationMatchingNode_row_columns_ne_newColumn G s b).2 hkp hkq, ← ms.2.1]
  rfl

/-- The center rectangle reconstructed from one advancing internal transition. -/
noncomputable def stabilizationMatchingThreeCenterRectangle (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ) := by
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  have fs := stabilizationMatchingExit_shape G s b y f hf
  have hkp : b.val.transpose (G.X s).succ ≠ a.val.transpose (G.X s).castSucc := by
    simpa only [ms.1, ms.2.1] using m.left_ne_right
  refine { left := b.val.transpose (G.X s).succ
           right := a.val.transpose (G.X s).castSucc
           left_ne_right := hkp
           map_left := ?_
           map_right := ?_
           map_of_ne := ?_ }
  · rw [stabilizationMatchingEntry_center_lowerColumn G s x a e he]
    have h := f.map_left
    simpa only [fs.2.2.1, fs.1, ← stabilizationMatchingTransition_newColumn G s a b m] using h
  · rw [stabilizationMatchingThree_center_upperColumn G s x a b hab e he m hmt]
    have h := f.map_of_ne (a.val.transpose (G.X s).castSucc)
      (by simpa only [fs.2.2.1] using Ne.symm hkp)
      (by simpa only [fs.1] using (stabilizationMatchingNode_row_columns_ne_newColumn G s a).1)
    exact h.trans (stabilizationMatchingThree_previous_lowerColumn G s a b hab m hmt)
  · intro c hck hcp
    by_cases hcb : c = s.succ
    · subst c
      simp only [GridState.insertPoint_apply_newColumn]
    · have h := f.map_of_ne c (by simpa only [fs.2.2.1] using hck)
        (by simpa only [fs.1] using hcb)
      exact h.trans (stabilizationMatchingThree_node_apply_of_ne
        G s x a b hab e he m hmt c hcb hcp hck)

@[simp]
theorem stabilizationMatchingThreeCenterRectangle_left (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf).left =
      b.val.transpose (G.X s).succ := rfl

@[simp]
theorem stabilizationMatchingThreeCenterRectangle_right (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf).right =
      a.val.transpose (G.X s).castSucc := rfl

@[simp]
theorem stabilizationMatchingThreeCenterRectangle_bottom (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf).bottom =
      m.bottom :=
  stabilizationMatchingThree_center_upperColumn G s x a b hab e he m hmt

@[simp]
theorem stabilizationMatchingThreeCenterRectangle_top (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf).top =
      a.val s.succ :=
  stabilizationMatchingEntry_center_lowerColumn G s x a e he

/-- The three-rectangle reconstruction contains the inserted center in its interior. -/
theorem stabilizationMatchingThreeCenterRectangle_center_mem (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hm : m.IsEmpty) (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (s.succ, (G.X s).succ) ∈ (stabilizationMatchingThreeCenterRectangle
      G s x y a b hab e he m hmt f hf).toGridRectangle.interior := by
  rw [GridRectangleBetween.mem_toGridRectangle_interior,
    stabilizationMatchingThreeCenterRectangle_left, stabilizationMatchingThreeCenterRectangle_right]
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  constructor
  · simpa only [ms.1, ms.2.1] using
      stabilizationMatchingTransition_newColumn_mem_interior G s a b hab m hm
  · rw [stabilizationMatchingThree_center_upperColumn G s x a b hab e he m hmt,
      stabilizationMatchingEntry_center_lowerColumn G s x a e he]
    exact Grid.mem_cIoo_cyclic_right
      (stabilizationMatchingTransition_advancing_height G s a b hab m hm hmt)

/-- The three-rectangle reconstruction has only the inserted center as a possible interior point. -/
theorem stabilizationMatchingThreeCenterRectangle_admissible (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hm : m.IsEmpty) (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    StabilizationAdmissibleRectangle G s
      (stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf) := by
  intro c hc hr
  by_contra hcb
  change c ∈ Grid.cIoo (b.val.transpose (G.X s).succ)
    (a.val.transpose (G.X s).castSucc) at hc
  have hck := Grid.ne_left_of_mem_cIoo hc
  have hcp := Grid.ne_right_of_mem_cIoo hc
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  have has := a.property.1
  have hbs := b.property.1
  change s.castSucc ∈ Grid.cIco (a.val.transpose (G.X s).succ)
    (a.val.transpose (G.X s).castSucc) at has
  change s.castSucc ∈ Grid.cIco (b.val.transpose (G.X s).succ)
    (b.val.transpose (G.X s).castSucc) at hbs
  rw [ms.2.2] at hbs
  have hq := ordered_middle_mem has hbs
  have hcq : c ≠ a.val.transpose (G.X s).succ := by
    intro h
    exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hq (h ▸ hc)
  have hxc := stabilizationMatchingEntry_center_apply_of_ne G s x a e he c hcb hcp hcq
  have h0 : x.insertPoint s.succ (G.X s).succ c ≠ (G.X s).castSucc := by
    intro h
    exact hcq ((x.insertPoint s.succ (G.X s).succ).toPerm.injective
      (h.trans (stabilizationMatchingEntry_center_upperColumn G s x a e he).symm))
  have h1 : x.insertPoint s.succ (G.X s).succ c ≠ (G.X s).succ := by
    intro h
    exact hcb ((x.insertPoint s.succ (G.X s).succ).toPerm.injective
      (h.trans (GridState.insertPoint_apply_newColumn x s.succ (G.X s).succ).symm))
  change x.insertPoint s.succ (G.X s).succ c ∈ Grid.cIoo
    (x.insertPoint s.succ (G.X s).succ (b.val.transpose (G.X s).succ))
    (x.insertPoint s.succ (G.X s).succ (a.val.transpose (G.X s).castSucc)) at hr
  rw [stabilizationMatchingThree_center_upperColumn G s x a b hab e he m hmt,
    stabilizationMatchingEntry_center_lowerColumn G s x a e he] at hr
  have hheight := stabilizationMatchingTransition_advancing_height G s a b hab m hm hmt
  rcases split_row_interval (G.X s) hheight hr h0 h1 with hhigh | hlow
  · have hc' : c ∈ Grid.cIoo m.left m.right := by simpa only [ms.1, ms.2.1] using hc
    have h := (m.isEmpty_iff_forall_notMem_cIoo.mp hm) c hc'
    apply h
    rw [← hxc, hmt]
    exact hhigh
  · have hbcol : s.succ ∈ Grid.cIoo (b.val.transpose (G.X s).succ)
        (a.val.transpose (G.X s).castSucc) := by
      simpa only [ms.1, ms.2.1] using
        stabilizationMatchingTransition_newColumn_mem_interior G s a b hab m hm
    rw [← Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hbcol] at hc
    rcases Finset.mem_union.mp hc with hout | hin
    · apply stabilizationMatchingExit_empty_region G s b y f hf c hout
      rw [stabilizationMatchingThree_node_apply_of_ne G s x a b hab e he m hmt c hcb hcp hck,
        ← stabilizationMatchingTransition_newColumn G s a b m]
      exact hlow
    · rcases Finset.mem_insert.mp hin with h | hin
      · exact hcb h
      · exact stabilizationMatchingEntry_empty_region G s x a e he c hin (hxc ▸ hlow)

/-- Every entry-advance-exit path reconstructs a genuine old empty rectangle. -/
theorem exists_old_rectangle_of_matching_entry_advance_exit (x y : GridState n)
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hm : m.IsEmpty) (hmt : m.top = (G.X s).castSucc)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    ∃ r : GridRectangleBetween x y, r.IsEmpty ∧
      r.insertPoint s.succ (G.X s).succ =
        stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf := by
  obtain ⟨r, hr⟩ := GridRectangleBetween.exists_insertPoint_eq
    (stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf)
  refine ⟨r, ?_, hr⟩
  apply (stabilizationAdmissibleRectangle_insertPoint_iff G s r).mp
  rw [hr]
  exact stabilizationMatchingThreeCenterRectangle_admissible G s x y a b hab e he m hm hmt f hf

/-- From a fixed node, the new upper-row column determines the node reached by an advance. -/
theorem stabilizationMatchingAdvance_node_eq_of_upperColumn_eq
    (a b c : StabilizationMatchingNode G s) (hab : a ≠ b) (hac : a ≠ c)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hmt : m.top = (G.X s).castSucc)
    (t : GridRectangleBetween a.val (stabilizationMatchingTargetState G s c))
    (htt : t.top = (G.X s).castSucc)
    (hc : b.val.transpose (G.X s).succ = c.val.transpose (G.X s).succ) : b = c := by
  apply stabilizationMatchingTargetState_injective G s
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  have ts := stabilizationMatchingTransition_advancing_columns G s a c hac t htt
  rw [m.target_eq_swapColumns, t.target_eq_swapColumns, ms.1, ts.1, ms.2.1, ts.2.1, hc]

end OnLeConjecture.KnotFloer.GridFull
