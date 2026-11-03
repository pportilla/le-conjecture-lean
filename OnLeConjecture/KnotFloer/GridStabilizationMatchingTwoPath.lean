/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingShortRectangle
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingEntryFromRectangle

/-!
# Recovering an entry-exit path from an admissible rectangle

When the bottom of an admissible center rectangle is the lower matching row,
its matching entry is followed by a single empty exit rectangle. The forward
reconstruction recovers the original rectangle.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)
variable {x y : GridState n}

theorem stabilizationMatchingEntry_upperColumn_of_bottom
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (hb : r.bottom = (G.X s).castSucc)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty) :
    z.val.transpose (G.X s).succ = r.left := by
  apply (x.insertPoint s.succ (G.X s).succ).toPerm.injective
  exact (stabilizationMatchingEntry_center_upperColumn G s x z e he).trans hb.symm

/-- The exit rectangle after the matching entry at a lower-row bottom. -/
noncomputable def stabilizationMatchingTwoExit
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (hb : r.bottom = (G.X s).castSucc)
    (hi : s.succ ∈ Grid.cIoo r.left r.right)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (hp : z.val.transpose (G.X s).castSucc = r.right) :
    GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ) := by
  have hq := stabilizationMatchingEntry_upperColumn_of_bottom G s r hb z e he
  have hL : z.val r.left = (G.X s).succ := by
    rw [← hq, GridState.apply_transpose_apply]
  have hR : z.val r.right = (G.X s).castSucc := by
    rw [← hp, GridState.apply_transpose_apply]
  have ht : x.insertPoint s.succ (G.X s).succ r.right = z.val s.succ := by
    rw [← hp]
    exact stabilizationMatchingEntry_center_lowerColumn G s x z e he
  refine { left := r.left
           right := s.succ
           left_ne_right := (Grid.ne_left_of_mem_cIoo hi).symm
           map_left := r.map_left.trans ht
           map_right := ?_
           map_of_ne := ?_ }
  · rw [GridState.insertPoint_apply_newColumn, hL]
  · intro c hcL hcb
    by_cases hcR : c = r.right
    · subst c
      exact r.map_right.trans (hb.trans hR.symm)
    · exact (r.map_of_ne c hcL hcR).trans
        (stabilizationMatchingEntry_center_apply_of_ne G s x z e he c hcb
          (hp ▸ hcR) (hq ▸ hcL))

/-- The exit contains no interior state point, by admissibility of the old lift. -/
theorem stabilizationMatchingTwoExit_isEmpty
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (ha : StabilizationAdmissibleRectangle G s r)
    (hb : r.bottom = (G.X s).castSucc)
    (hi : (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (hp : z.val.transpose (G.X s).castSucc = r.right) :
    (stabilizationMatchingTwoExit G s r hb
      ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1 z e he hp).IsEmpty := by
  have hcenter := (GridRectangleBetween.mem_toGridRectangle_interior r).mp hi
  have hq := stabilizationMatchingEntry_upperColumn_of_bottom G s r hb z e he
  have hL : z.val r.left = (G.X s).succ := by
    rw [← hq, GridState.apply_transpose_apply]
  have ht : x.insertPoint s.succ (G.X s).succ r.right = z.val s.succ := by
    rw [← hp]
    exact stabilizationMatchingEntry_center_lowerColumn G s x z e he
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
  intro c hc hr
  change c ∈ Grid.cIoo r.left s.succ at hc
  change z.val c ∈ Grid.cIoo (z.val r.left) (z.val s.succ) at hr
  have hcR : c ∈ Grid.cIoo r.left r.right :=
    Grid.cIoo_subset_cIoo_right_of_mem_cIoo hcenter.1 hc
  have hcb := Grid.ne_right_of_mem_cIoo hc
  have hcl := Grid.ne_left_of_mem_cIoo hc
  have hcr := Grid.ne_right_of_mem_cIoo hcR
  have hcval := stabilizationMatchingEntry_center_apply_of_ne G s x z e he c hcb
    (hp ▸ hcr) (hq ▸ hcl)
  rw [hL, ← ht, ← hcval] at hr
  have hrowcenter : (G.X s).succ ∈ Grid.cIoo
      (x.insertPoint s.succ (G.X s).succ r.left)
      (x.insertPoint s.succ (G.X s).succ r.right) := by
    simpa only [GridState.insertPoint_apply_newColumn] using hcenter.2
  have hrow := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hrowcenter hr
  exact hcb (ha c hcR hrow)

/-- Forward reconstruction of this entry and exit returns the initial rectangle. -/
theorem stabilizationMatchingTwoExit_reconstruct
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (ha : StabilizationAdmissibleRectangle G s r)
    (hb : r.bottom = (G.X s).castSucc)
    (hi : (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (hp : z.val.transpose (G.X s).castSucc = r.right) :
    stabilizationMatchingTwoCenterRectangle G s x y z e he
      (stabilizationMatchingTwoExit G s r hb
        ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1 z e he hp)
      (stabilizationMatchingTwoExit_isEmpty G s r ha hb hi z e he hp) = r := by
  apply GridRectangleBetween.ext
  · exact stabilizationMatchingEntry_upperColumn_of_bottom G s r hb z e he
  · exact hp

/-- An entry and an exit at one internal matching node, with their actual rectangles. -/
abbrev StabilizationMatchingTwoPath (x y : GridState n) :=
  Σ z : StabilizationMatchingNode G s,
    { e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
        (stabilizationMatchingTargetState G s z) // e.IsEmpty } ×
      { f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ) // f.IsEmpty }

instance (x y : GridState n) : Finite (StabilizationMatchingTwoPath G s x y) := by
  unfold StabilizationMatchingTwoPath
  infer_instance

/-- The admissible center rectangle reconstructed from an entry-exit path. -/
noncomputable def stabilizationMatchingTwoPathRectangle
    (p : StabilizationMatchingTwoPath G s x y) :
    GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ) :=
  stabilizationMatchingTwoCenterRectangle G s x y p.1 p.2.1.val p.2.1.property
    p.2.2.val p.2.2.property

/-- Reconstruction does not identify different entry-exit paths. -/
theorem stabilizationMatchingTwoPathRectangle_injective :
    Function.Injective (stabilizationMatchingTwoPathRectangle G s (x := x) (y := y)) := by
  intro p q hpq
  obtain ⟨z, ⟨e, he⟩, ⟨f, hf⟩⟩ := p
  obtain ⟨w, ⟨e', he'⟩, ⟨f', hf'⟩⟩ := q
  have hcol : z.val.transpose (G.X s).castSucc = w.val.transpose (G.X s).castSucc :=
    congrArg GridRectangleBetween.right hpq
  have hzw := stabilizationMatchingEntry_node_eq_of_lowerColumn_eq G s x z w e he e' he' hcol
  subst w
  have heq : e = e' := by
    have es := stabilizationMatchingEntry_shape G s x z e he
    have es' := stabilizationMatchingEntry_shape G s x z e' he'
    exact GridRectangleBetween.ext (es.1.trans es'.1.symm)
      (es.2.2.1.trans es'.2.2.1.symm)
  have hfq : f = f' := by
    have fs := stabilizationMatchingExit_shape G s z y f hf
    have fs' := stabilizationMatchingExit_shape G s z y f' hf'
    exact GridRectangleBetween.ext (fs.2.2.1.trans fs'.2.2.1.symm)
      (fs.1.trans fs'.1.symm)
  subst e'
  subst f'
  rfl

/-- Every entry-exit path gives precisely the lower-bottom part of the old rectangle count. -/
theorem stabilizationMatchingTwoPathRectangle_properties
    (p : StabilizationMatchingTwoPath G s x y) :
    StabilizationAdmissibleRectangle G s (stabilizationMatchingTwoPathRectangle G s p) ∧
      (s.succ, (G.X s).succ) ∈
        (stabilizationMatchingTwoPathRectangle G s p).toGridRectangle.interior ∧
      (stabilizationMatchingTwoPathRectangle G s p).bottom = (G.X s).castSucc :=
  ⟨stabilizationMatchingTwoCenterRectangle_admissible G s x y p.1 p.2.1.val p.2.1.property
      p.2.2.val p.2.2.property,
    stabilizationMatchingTwoCenterRectangle_center_mem G s x y p.1 p.2.1.val p.2.1.property
      p.2.2.val p.2.2.property,
    stabilizationMatchingTwoCenterRectangle_bottom G s x y p.1 p.2.1.val p.2.1.property
      p.2.2.val p.2.2.property⟩

/-- Every admissible rectangle with this bottom row comes from an actual entry-exit path. -/
theorem exists_matchingTwoPath_of_bottom
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (ha : StabilizationAdmissibleRectangle G s r)
    (hi : (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior)
    (hb : r.bottom = (G.X s).castSucc) :
    ∃ p : StabilizationMatchingTwoPath G s x y,
      stabilizationMatchingTwoPathRectangle G s p = r := by
  let z := stabilizationRectangleEntryNode G s r ha hi
  let e := stabilizationRectangleEntry G s r ha hi
  have he : e.IsEmpty := stabilizationRectangleEntry_isEmpty G s r ha hi
  have hp : z.val.transpose (G.X s).castSucc = r.right :=
    stabilizationRectangleEntryNode_lowerColumn G s r ha hi
  let f := stabilizationMatchingTwoExit G s r hb
    ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1 z e he hp
  have hf : f.IsEmpty := stabilizationMatchingTwoExit_isEmpty G s r ha hb hi z e he hp
  refine ⟨⟨z, ⟨e, he⟩, ⟨f, hf⟩⟩, ?_⟩
  exact stabilizationMatchingTwoExit_reconstruct G s r ha hb hi z e he hp

/-- Entry-exit paths are in bijection with the lower-bottom admissible rectangles. -/
noncomputable def stabilizationMatchingTwoPathEquiv :
    StabilizationMatchingTwoPath G s x y ≃
      { r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
          (y.insertPoint s.succ (G.X s).succ) //
        StabilizationAdmissibleRectangle G s r ∧
          (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧
          r.bottom = (G.X s).castSucc } :=
  Equiv.ofBijective
    (fun p => ⟨stabilizationMatchingTwoPathRectangle G s p,
      stabilizationMatchingTwoPathRectangle_properties G s p⟩) (by
    constructor
    · intro p q h
      exact stabilizationMatchingTwoPathRectangle_injective G s (congrArg Subtype.val h)
    · rintro ⟨r, ha, hi, hb⟩
      obtain ⟨p, hp⟩ := exists_matchingTwoPath_of_bottom G s r ha hi hb
      exact ⟨p, Subtype.ext hp⟩)

end OnLeConjecture.KnotFloer.GridFull
