/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingThreePath
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingCenterPath

/-!
# Entry-advance-exit paths and admissible rectangles

The path type retains the two distinct internal nodes and each of its three
empty rectangles. Its advancing condition selects the internal transitions
that can have an empty exit.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)
variable {x y : GridState n}

/-- An internal empty rectangle with an empty exit must advance. -/
theorem stabilizationMatching_middle_advancing_of_empty_exit
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hm : m.IsEmpty)
    (f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ))
    (hf : f.IsEmpty) : m.top = (G.X s).castSucc := by
  rcases stabilizationMatchingTransition_oriented_row_edge G s a b hab m hm with h | h
  · exact h
  · exact False.elim (stabilizationMatchingRetreating_not_exit G s a b hab y m f hm hf h)

/-- An entry, one advancing transition between distinct nodes, and an exit. -/
abbrev StabilizationMatchingThreePath (x y : GridState n) :=
  Σ a : StabilizationMatchingNode G s,
    Σ b : { b : StabilizationMatchingNode G s // a ≠ b },
      { e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
          (stabilizationMatchingTargetState G s a) // e.IsEmpty } ×
        { m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b.val) //
          m.IsEmpty ∧ m.top = (G.X s).castSucc } ×
        { f : GridRectangleBetween b.val.val (y.insertPoint s.succ (G.X s).succ) // f.IsEmpty }

instance (x y : GridState n) : Finite (StabilizationMatchingThreePath G s x y) := by
  unfold StabilizationMatchingThreePath
  infer_instance

/-- The center rectangle determined by the three full rectangles. -/
noncomputable def stabilizationMatchingThreePathRectangle
    (p : StabilizationMatchingThreePath G s x y) :
    GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ) :=
  stabilizationMatchingThreeCenterRectangle G s x y p.1 p.2.1.val p.2.1.property
    p.2.2.1.val p.2.2.1.property p.2.2.2.1.val p.2.2.2.1.property.2
    p.2.2.2.2.val p.2.2.2.2.property

/-- The reconstructed rectangle is admissible, contains the center, and has a different bottom. -/
theorem stabilizationMatchingThreePathRectangle_properties
    (p : StabilizationMatchingThreePath G s x y) :
    StabilizationAdmissibleRectangle G s (stabilizationMatchingThreePathRectangle G s p) ∧
      (s.succ, (G.X s).succ) ∈
        (stabilizationMatchingThreePathRectangle G s p).toGridRectangle.interior ∧
      (stabilizationMatchingThreePathRectangle G s p).bottom ≠ (G.X s).castSucc := by
  obtain ⟨a, ⟨b, hab⟩, ⟨e, he⟩, ⟨m, hm, hmt⟩, ⟨f, hf⟩⟩ := p
  refine ⟨stabilizationMatchingThreeCenterRectangle_admissible
    G s x y a b hab e he m hm hmt f hf,
    stabilizationMatchingThreeCenterRectangle_center_mem
      G s x y a b hab e he m hm hmt f hf, ?_⟩
  change (stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf).bottom ≠ _
  rw [stabilizationMatchingThreeCenterRectangle_bottom]
  exact fun h => m.bottom_ne_top (h.trans hmt.symm)

/-- The outer side columns determine both internal nodes and all three rectangles. -/
theorem stabilizationMatchingThreePathRectangle_injective :
    Function.Injective (stabilizationMatchingThreePathRectangle G s (x := x) (y := y)) := by
  intro p q hpq
  obtain ⟨a, ⟨b, hab⟩, ⟨e, he⟩, ⟨m, hm, hmt⟩, ⟨f, hf⟩⟩ := p
  obtain ⟨a', ⟨b', hab'⟩, ⟨e', he'⟩, ⟨m', hm', hmt'⟩, ⟨f', hf'⟩⟩ := q
  have hcol : a.val.transpose (G.X s).castSucc = a'.val.transpose (G.X s).castSucc :=
    congrArg GridRectangleBetween.right hpq
  have haa := stabilizationMatchingEntry_node_eq_of_lowerColumn_eq
    G s x a a' e he e' he' hcol
  subst a'
  have hcol' : b.val.transpose (G.X s).succ = b'.val.transpose (G.X s).succ :=
    congrArg GridRectangleBetween.left hpq
  have hbb := stabilizationMatchingAdvance_node_eq_of_upperColumn_eq
    G s a b b' hab hab' m hmt m' hmt' hcol'
  subst b'
  have heq : e = e' := by
    have es := stabilizationMatchingEntry_shape G s x a e he
    have es' := stabilizationMatchingEntry_shape G s x a e' he'
    exact GridRectangleBetween.ext (es.1.trans es'.1.symm)
      (es.2.2.1.trans es'.2.2.1.symm)
  have hmq : m = m' := by
    have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
    have ms' := stabilizationMatchingTransition_advancing_columns G s a b hab m' hmt'
    exact GridRectangleBetween.ext (ms.2.1.trans ms'.2.1.symm) (ms.1.trans ms'.1.symm)
  have hfq : f = f' := by
    have fs := stabilizationMatchingExit_shape G s b y f hf
    have fs' := stabilizationMatchingExit_shape G s b y f' hf'
    exact GridRectangleBetween.ext (fs.2.2.1.trans fs'.2.2.1.symm) (fs.1.trans fs'.1.symm)
  subst e'
  subst m'
  subst f'
  rfl

/-- Every admissible rectangle containing the center and with a different bottom
has a three-rectangle path. -/
theorem exists_matchingThreePath_of_bottom_ne
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ))
    (ha : StabilizationAdmissibleRectangle G s r)
    (hi : (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior)
    (hb : r.bottom ≠ (G.X s).castSucc) :
    ∃ p : StabilizationMatchingThreePath G s x y,
      stabilizationMatchingThreePathRectangle G s p = r := by
  let a := stabilizationRectangleEntryNode G s r ha hi
  let b := stabilizationRectangleExitNode G s r ha hi hb
  have hab : a ≠ b := stabilizationRectangleEntryNode_ne_exitNode G s r ha hi hb
  let e := stabilizationRectangleEntry G s r ha hi
  have he : e.IsEmpty := stabilizationRectangleEntry_isEmpty G s r ha hi
  let m := stabilizationRectangleMiddle G s r ha hi hb
  have hm : m.IsEmpty := stabilizationRectangleMiddle_isEmpty G s r ha hi hb
  have hmt : m.top = (G.X s).castSucc := stabilizationRectangleMiddle_top G s r ha hi hb
  let f := stabilizationRectangleThreeExit G s r ha hi hb
  have hf : f.IsEmpty := stabilizationRectangleThreeExit_isEmpty G s r ha hi hb
  refine ⟨⟨a, ⟨b, hab⟩, ⟨e, he⟩, ⟨m, hm, hmt⟩, ⟨f, hf⟩⟩, ?_⟩
  apply GridRectangleBetween.ext
  · exact stabilizationRectangleExitNode_upperColumn G s r ha hi hb
  · exact stabilizationRectangleEntryNode_lowerColumn G s r ha hi

/-- Three-rectangle paths are in bijection with the remaining nonempty admissible rectangles. -/
noncomputable def stabilizationMatchingThreePathEquiv :
    StabilizationMatchingThreePath G s x y ≃
      { r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
          (y.insertPoint s.succ (G.X s).succ) //
        StabilizationAdmissibleRectangle G s r ∧
          (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧
          r.bottom ≠ (G.X s).castSucc } :=
  Equiv.ofBijective
    (fun p => ⟨stabilizationMatchingThreePathRectangle G s p,
      stabilizationMatchingThreePathRectangle_properties G s p⟩) (by
    constructor
    · intro p q h
      exact stabilizationMatchingThreePathRectangle_injective G s (congrArg Subtype.val h)
    · rintro ⟨r, ha, hi, hb⟩
      obtain ⟨p, hp⟩ := exists_matchingThreePath_of_bottom_ne G s r ha hi hb
      exact ⟨p, Subtype.ext hp⟩)

end OnLeConjecture.KnotFloer.GridFull
