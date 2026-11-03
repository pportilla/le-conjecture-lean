/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamImmediateFirstLeftProjection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorShortLift
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamImmediateSecondProjection

/-!
# Finite first-factor immediate corrections

The two equal-orientation cases map to empty first-factor rectangles
incident to the last column and absent from the direct projection.
The projection is injective because emptiness forces each auxiliary
pivot to the appropriate boundary column.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

abbrev SeamImmediateFirstRightData (p q : SeamRetainedIndex n m) :=
  Σ s : SeamMatchingSource n m,
    {e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s.val).val //
      e.IsEmpty ∧ e.left.val < n} ×
    {f : GridRectangleBetween s.val.val (seamState q.1 q.2) // f.IsEmpty ∧ f.left.val < n}

abbrev SeamImmediateFirstLeftData (p q : SeamRetainedIndex n m) :=
  Σ s : SeamMatchingSource n m,
    {e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s.val).val //
      e.IsEmpty ∧ e.right.val < n} ×
    {f : GridRectangleBetween s.val.val (seamState q.1 q.2) // f.IsEmpty ∧ f.right.val < n}

instance seamImmediateFirstRightDataFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamImmediateFirstRightData p q) := inferInstance

instance seamImmediateFirstLeftDataFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamImmediateFirstLeftData p q) := inferInstance

def seamImmediateFirstRightProjection (p q : SeamRetainedIndex n m)
    (d : SeamImmediateFirstRightData p q) : GridRectangleBetween p.1 q.1 :=
  seamImmediateFirstRightRectangle p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 d.2.1.property.2 d.2.2.property.2

def seamImmediateFirstLeftProjection (p q : SeamRetainedIndex n m)
    (d : SeamImmediateFirstLeftData p q) : GridRectangleBetween p.1 q.1 :=
  seamImmediateFirstLeftRectangle p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 d.2.1.property.2 d.2.2.property.2

theorem seamImmediateFirstRightProjection_injective (p q : SeamRetainedIndex n m) :
    Function.Injective (seamImmediateFirstRightProjection p q) := by
  rintro ⟨x, e, f⟩ ⟨y, g, h⟩ hh
  have haI := congrArg (fun r => r.left) hh
  change seamFirstFactorIndex e.val.left = seamFirstFactorIndex g.val.left at haI
  have ha : e.val.left = g.val.left := by
    apply Fin.ext
    have hv := congrArg Fin.val haI
    simpa only [seamFirstFactorIndex, dif_pos e.property.2, dif_pos g.property.2] using hv
  have hp : seamComplementFirst x.val = seamComplementFirst y.val := by
    apply Fin.ext
    exact (seamImmediateFirstRight_pivot_eq_cut p q x e.val f.val
      e.property.1 f.property.1 e.property.2 f.property.2).trans
      (seamImmediateFirstRight_pivot_eq_cut p q y g.val h.val
        g.property.1 h.property.1 g.property.2 h.property.2).symm
  obtain ⟨heP, hfP⟩ := seamImmediateFirstRight_sides p q x e.val f.val
    e.property.1 f.property.1 e.property.2 f.property.2
  obtain ⟨hgP, hhP⟩ := seamImmediateFirstRight_sides p q y g.val h.val
    g.property.1 h.property.1 g.property.2 h.property.2
  have hfA := seamImmediate_left_column_eq p q x e.val f.val e.property.2 f.property.2
  have hhA := seamImmediate_left_column_eq p q y g.val h.val g.property.2 h.property.2
  have hxy : x.val.val = y.val.val := by
    rw [f.val.source_eq_swapColumns, h.val.source_eq_swapColumns,
      ← hfA, ← hhA, hfP, hhP, ha, hp]
  have hxy : x = y := Subtype.ext (Subtype.ext hxy)
  subst y
  have heg : e = g := Subtype.ext (GridRectangleBetween.ext ha (heP.trans hgP.symm))
  have hfh : f = h := Subtype.ext (GridRectangleBetween.ext
    (hfA.symm.trans (ha.trans hhA)) (hfP.trans hhP.symm))
  subst g
  subst h
  rfl

theorem seamImmediateFirstLeftProjection_injective (p q : SeamRetainedIndex n m) :
    Function.Injective (seamImmediateFirstLeftProjection p q) := by
  rintro ⟨x, e, f⟩ ⟨y, g, h⟩ hh
  have haI := congrArg (fun r => r.right) hh
  change seamFirstFactorIndex e.val.right = seamFirstFactorIndex g.val.right at haI
  have ha : e.val.right = g.val.right := by
    apply Fin.ext
    have hv := congrArg Fin.val haI
    simpa only [seamFirstFactorIndex, dif_pos e.property.2, dif_pos g.property.2] using hv
  have hq : seamComplementSecond x.val = seamComplementSecond y.val := by
    apply Fin.ext
    exact (seamImmediateFirstLeft_pivot_eq_last p q x e.val f.val
      e.property.1 f.property.1 e.property.2 f.property.2).trans
      (seamImmediateFirstLeft_pivot_eq_last p q y g.val h.val
        g.property.1 h.property.1 g.property.2 h.property.2).symm
  obtain ⟨heQ, hfQ⟩ := seamImmediateFirstLeft_sides p q x e.val f.val
    e.property.1 f.property.1 e.property.2 f.property.2
  obtain ⟨hgQ, hhQ⟩ := seamImmediateFirstLeft_sides p q y g.val h.val
    g.property.1 h.property.1 g.property.2 h.property.2
  have hfA := seamImmediate_right_column_eq p q x e.val f.val e.property.2 f.property.2
  have hhA := seamImmediate_right_column_eq p q y g.val h.val g.property.2 h.property.2
  have hxy : x.val.val = y.val.val := by
    rw [f.val.source_eq_swapColumns, h.val.source_eq_swapColumns,
      ← hfA, ← hhA, hfQ, hhQ, ha, hq]
  have hxy : x = y := Subtype.ext (Subtype.ext hxy)
  subst y
  have heg : e = g := Subtype.ext (GridRectangleBetween.ext (heQ.trans hgQ.symm) ha)
  have hfh : f = h := Subtype.ext (GridRectangleBetween.ext
    (hfQ.trans hhQ.symm) (hfA.symm.trans (ha.trans hhA)))
  subst g
  subst h
  rfl

/-- The missing direct first-factor rectangles with a last-column endpoint. -/
abbrev SeamObstructedFirstLastRectangle (p q : SeamRetainedIndex n m) :=
  {r : GridRectangleBetween p.1 q.1 // r.IsEmpty ∧
    ¬ (seamFirstFactorRectangle r p.2).IsEmpty ∧
    (r.left = Fin.last n ∨ r.right = Fin.last n)}

abbrev SeamImmediateFirstData (p q : SeamRetainedIndex n m) :=
  SeamImmediateFirstRightData p q ⊕ SeamImmediateFirstLeftData p q

instance seamObstructedFirstLastRectangleFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamObstructedFirstLastRectangle p q) := inferInstance

instance seamImmediateFirstDataFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamImmediateFirstData p q) := inferInstance

def seamImmediateFirstProjection (p q : SeamRetainedIndex n m) :
    SeamImmediateFirstData p q → SeamObstructedFirstLastRectangle p q
  | Sum.inl ⟨s, e, f⟩ => ⟨seamImmediateFirstRightProjection p q ⟨s, e, f⟩,
      seamImmediateFirstRightRectangle_isEmpty p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2,
      seamImmediateFirstRightRectangle_lift_not_isEmpty p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2,
      Or.inr (seamImmediateFirstRightRectangle_right p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2)⟩
  | Sum.inr ⟨s, e, f⟩ => ⟨seamImmediateFirstLeftProjection p q ⟨s, e, f⟩,
      seamImmediateFirstLeftRectangle_isEmpty p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2,
      seamImmediateFirstLeftRectangle_lift_not_isEmpty p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2,
      Or.inl (seamImmediateFirstLeftRectangle_left p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2)⟩

theorem seamImmediateFirstProjection_injective (p q : SeamRetainedIndex n m) :
    Function.Injective (seamImmediateFirstProjection p q) := by
  intro a b hh
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (seamImmediateFirstRightProjection_injective p q
      (congrArg Subtype.val hh))
  · have hr := congrArg Subtype.val hh
    have hright : (seamImmediateFirstRightProjection p q a).right = Fin.last n :=
      seamImmediateFirstRightRectangle_right p q a.1 a.2.1.val a.2.2.val
        a.2.1.property.1 a.2.2.property.1 a.2.1.property.2 a.2.2.property.2
    have hleft : (seamImmediateFirstLeftProjection p q b).left = Fin.last n :=
      seamImmediateFirstLeftRectangle_left p q b.1 b.2.1.val b.2.2.val
        b.2.1.property.1 b.2.2.property.1 b.2.1.property.2 b.2.2.property.2
    have heq : (seamImmediateFirstRightProjection p q a).left =
        (seamImmediateFirstLeftProjection p q b).left := congrArg (fun r => r.left) hr
    exact False.elim ((seamImmediateFirstRightProjection p q a).left_ne_right
      ((heq.trans hleft).trans hright.symm))
  · exact False.elim (by
      have hr := congrArg Subtype.val hh
      have hleft := seamImmediateFirstLeftRectangle_left p q a.1 a.2.1.val a.2.2.val
        a.2.1.property.1 a.2.2.property.1 a.2.1.property.2 a.2.2.property.2
      have hright := seamImmediateFirstRightRectangle_right p q b.1 b.2.1.val b.2.2.val
        b.2.1.property.1 b.2.2.property.1 b.2.1.property.2 b.2.2.property.2
      have heq := congrArg (fun r => r.right) hr
      exact (seamImmediateFirstLeftProjection p q a).left_ne_right
        (hleft.trans (hright.symm.trans heq.symm)))
  · exact congrArg Sum.inr (seamImmediateFirstLeftProjection_injective p q
      (congrArg Subtype.val hh))

/-- Recover the equal-source representation of a zero-transition correction. -/
def seamImmediateFirstRightDataOfZero (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.left.val < n) (hf : c.2.2.2.2.val.left.val < n) :
    SeamImmediateFirstRightData p q := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  exact ⟨s, ⟨e.val, e.property, he⟩, ⟨f.val, f.property, hf⟩⟩

def seamImmediateFirstLeftDataOfZero (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.right.val < n) (hf : c.2.2.2.2.val.right.val < n) :
    SeamImmediateFirstLeftData p q := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  exact ⟨s, ⟨e.val, e.property, he⟩, ⟨f.val, f.property, hf⟩⟩

@[simp] theorem seamImmediateFirstRightDataOfZero_entry_left (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.left.val < n) (hf : c.2.2.2.2.val.left.val < n) :
    (seamImmediateFirstRightDataOfZero p q c he hf).2.1.val.left = c.2.2.1.val.left := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  rfl

@[simp] theorem seamImmediateFirstLeftDataOfZero_entry_right (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.right.val < n) (hf : c.2.2.2.2.val.right.val < n) :
    (seamImmediateFirstLeftDataOfZero p q c he hf).2.1.val.right = c.2.2.1.val.right := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  rfl

/-- Every missing direct rectangle incident to the last column has this unique immediate lift. -/
theorem seamImmediateFirstProjection_surjective (x y : GridState (n + 1))
    (z : GridState (m + 1)) :
    Function.Surjective (seamImmediateFirstProjection (x, z) (y, z)) := by
  rintro ⟨r, he, hb, hl | hr⟩
  · let c := seamFirstFactorShortLift_left_last r z he hb hl
    have hs := seamFirstFactorShortLift_left_last_small_sides r z he hb hl
    let d := seamImmediateFirstLeftDataOfZero (x, z) (y, z) c hs.1 hs.2
    refine ⟨Sum.inr d, Subtype.ext ?_⟩
    apply GridRectangleBetween.ext
    · exact (seamImmediateFirstLeftRectangle_left (x, z) (y, z) d.1 d.2.1.val d.2.2.val
        d.2.1.property.1 d.2.2.property.1 d.2.1.property.2 d.2.2.property.2).trans hl.symm
    · change seamFirstFactorIndex d.2.1.val.right = r.right
      rw [seamImmediateFirstLeftDataOfZero_entry_right]
      exact seamFirstFactorShortLift_left_last_index r z he hb hl
  · let c := seamFirstFactorShortLift_right_last r z he hb hr
    have hs := seamFirstFactorShortLift_right_last_small_sides r z he hb hr
    let d := seamImmediateFirstRightDataOfZero (x, z) (y, z) c hs.1 hs.2
    refine ⟨Sum.inl d, Subtype.ext ?_⟩
    apply GridRectangleBetween.ext
    · change seamFirstFactorIndex d.2.1.val.left = r.left
      rw [seamImmediateFirstRightDataOfZero_entry_left]
      exact seamFirstFactorShortLift_right_last_index r z he hb hr
    · exact (seamImmediateFirstRightRectangle_right (x, z) (y, z) d.1 d.2.1.val d.2.2.val
        d.2.1.property.1 d.2.2.property.1 d.2.1.property.2 d.2.2.property.2).trans hr.symm

/-- A genuine finite bijection, retaining the actual entry and exit rectangles. -/
def seamImmediateFirstEquiv (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    SeamImmediateFirstData (x, z) (y, z) ≃ SeamObstructedFirstLastRectangle (x, z) (y, z) :=
  Equiv.ofBijective (seamImmediateFirstProjection (x, z) (y, z))
    ⟨seamImmediateFirstProjection_injective _ _, seamImmediateFirstProjection_surjective x y z⟩

theorem seamImmediateFirst_card (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    Fintype.card (SeamImmediateFirstData (x, z) (y, z)) =
      Fintype.card (SeamObstructedFirstLastRectangle (x, z) (y, z)) :=
  Fintype.card_congr (seamImmediateFirstEquiv x y z)

/-- With the second factor fixed, a mixed immediate correction would give a rectangle z→z. -/
theorem seamImmediate_same_second_orientations (x y : GridState (n + 1))
    (z : GridState (m + 1)) (s : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState x z) (seamComplementPartner s.val).val)
    (f : GridRectangleBetween s.val.val (seamState y z)) (he : e.IsEmpty) (hf : f.IsEmpty) :
    (e.left.val < n ∧ f.left.val < n) ∨ (e.right.val < n ∧ f.right.val < n) := by
  have heR := seamEnteringRectangle_ranges (seamState_mem_pairSector x z)
    (seamComplementPartner s.val).property e
  have hfR := seamLeavingRectangle_ranges (seamState_mem_pairSector y z) s.val.property f
  rcases heR with heR | heR <;> rcases hfR with hfR | hfR
  · exact Or.inl ⟨heR.1, hfR.1⟩
  · exact False.elim ((seamImmediateMixedSecondRectangle (x, z) (y, z) s e f he hf
      (Or.inl ⟨heR.1, hfR.1⟩)).source_ne_target rfl)
  · exact False.elim ((seamImmediateMixedSecondRectangle (x, z) (y, z) s e f he hf
      (Or.inr ⟨heR.1, hfR.1⟩)).source_ne_target rfl)
  · exact Or.inr ⟨heR.1, hfR.1⟩

theorem seamImmediate_entry_left_not_small (p : SeamRetainedIndex n m)
    (s : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s.val).val)
    (h : e.right.val < n) : ¬ e.left.val < n := by
  rcases seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
      (seamComplementPartner s.val).property e with hh | hh <;> omega

def seamImmediateFirstDataToZero (p q : SeamRetainedIndex n m) :
    SeamImmediateFirstData p q → SeamCorrectionPath 0 p q
  | Sum.inl ⟨s, e, f⟩ => ⟨s, s, ⟨e.val, e.property.1⟩, ⟨(), rfl⟩, ⟨f.val, f.property.1⟩⟩
  | Sum.inr ⟨s, e, f⟩ => ⟨s, s, ⟨e.val, e.property.1⟩, ⟨(), rfl⟩, ⟨f.val, f.property.1⟩⟩

/-- Every actual zero-transition path with fixed second factor has one of the two orientations. -/
def seamZeroToImmediateFirstData (x y : GridState (n + 1)) (z : GridState (m + 1))
    (c : SeamCorrectionPath 0 (x, z) (y, z)) : SeamImmediateFirstData (x, z) (y, z) := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  have hor := seamImmediate_same_second_orientations x y z s e.val f.val e.property f.property
  by_cases he : e.val.left.val < n
  · have hf : f.val.left.val < n := by
      rcases hor with h | h
      · exact h.2
      · exact False.elim ((seamImmediate_entry_left_not_small (x, z) s e.val h.1) he)
    exact Sum.inl ⟨s, ⟨e.val, e.property, he⟩, ⟨f.val, f.property, hf⟩⟩
  · have hr := hor.resolve_left (fun h => he h.1)
    exact Sum.inr ⟨s, ⟨e.val, e.property, hr.1⟩, ⟨f.val, f.property, hr.2⟩⟩

theorem seamZeroToImmediateFirstData_left_inv (x y : GridState (n + 1))
    (z : GridState (m + 1)) :
    Function.LeftInverse (seamZeroToImmediateFirstData x y z)
      (seamImmediateFirstDataToZero (x, z) (y, z)) := by
  rintro (⟨s, e, f⟩ | ⟨s, e, f⟩)
  · simp only [seamImmediateFirstDataToZero, seamZeroToImmediateFirstData]
    split_ifs with he
    · simp [he]
    · exact False.elim (he e.property.2)
  · have he := seamImmediate_entry_left_not_small (x, z) s e.val e.property.2
    simp only [seamImmediateFirstDataToZero, seamZeroToImmediateFirstData]
    split_ifs with he'
    · exact False.elim (he he')
    · simp [he]

theorem seamZeroToImmediateFirstData_right_inv (x y : GridState (n + 1))
    (z : GridState (m + 1)) :
    Function.RightInverse (seamZeroToImmediateFirstData x y z)
      (seamImmediateFirstDataToZero (x, z) (y, z)) := by
  rintro ⟨s, t, e, ⟨u, hst⟩, f⟩
  subst t
  cases u
  by_cases he : e.val.left.val < n
  · simp only [seamZeroToImmediateFirstData, dif_pos he, seamImmediateFirstDataToZero]
  · simp only [seamZeroToImmediateFirstData, dif_neg he, seamImmediateFirstDataToZero]

/-- The whole actual zero-transition path type, rather than a selected orientation subset. -/
def seamCorrectionZeroFirstEquiv (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    SeamCorrectionPath 0 (x, z) (y, z) ≃ SeamObstructedFirstLastRectangle (x, z) (y, z) :=
  (Equiv.ofBijective (seamZeroToImmediateFirstData x y z)
    ⟨(seamZeroToImmediateFirstData_right_inv x y z).injective,
      (seamZeroToImmediateFirstData_left_inv x y z).surjective⟩).trans
    (seamImmediateFirstEquiv x y z)

theorem seamCorrectionZeroFirst_card (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    Fintype.card (SeamCorrectionPath 0 (x, z) (y, z)) =
      Fintype.card (SeamObstructedFirstLastRectangle (x, z) (y, z)) :=
  Fintype.card_congr (seamCorrectionZeroFirstEquiv x y z)

end OnLeConjecture.KnotFloer.GridFull
