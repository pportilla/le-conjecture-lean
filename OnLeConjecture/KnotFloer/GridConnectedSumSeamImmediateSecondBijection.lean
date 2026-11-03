/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamImmediateSecondExtrema

/-!
# The second-factor immediate-correction bijection

With the first factor fixed, every zero-transition correction is mixed.
Its projected second-factor rectangle wraps in columns, has a zero row
endpoint, and has a nonempty retained lift. Conversely each such empty
factor rectangle has a unique correction, including its entry and exit.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

abbrev SeamImmediateSecondBottomData (p q : SeamRetainedIndex n m) :=
  Σ s : SeamMatchingSource n m,
    {e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s.val).val //
      e.IsEmpty ∧ e.left.val < n} ×
    {f : GridRectangleBetween s.val.val (seamState q.1 q.2) // f.IsEmpty ∧ f.right.val < n}

abbrev SeamImmediateSecondTopData (p q : SeamRetainedIndex n m) :=
  Σ s : SeamMatchingSource n m,
    {e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s.val).val //
      e.IsEmpty ∧ e.right.val < n} ×
    {f : GridRectangleBetween s.val.val (seamState q.1 q.2) // f.IsEmpty ∧ f.left.val < n}

instance seamImmediateSecondBottomDataFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamImmediateSecondBottomData p q) := inferInstance

instance seamImmediateSecondTopDataFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamImmediateSecondTopData p q) := inferInstance

def seamImmediateSecondBottomProjection (p q : SeamRetainedIndex n m)
    (d : SeamImmediateSecondBottomData p q) : GridRectangleBetween p.2 q.2 :=
  seamImmediateMixedSecondRectangle p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 (Or.inl ⟨d.2.1.property.2, d.2.2.property.2⟩)

def seamImmediateSecondTopProjection (p q : SeamRetainedIndex n m)
    (d : SeamImmediateSecondTopData p q) : GridRectangleBetween p.2 q.2 :=
  seamImmediateMixedSecondRectangle p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 (Or.inr ⟨d.2.1.property.2, d.2.2.property.2⟩)

theorem seamImmediateSecondBottomProjection_sides (p q : SeamRetainedIndex n m)
    (d : SeamImmediateSecondBottomData p q) :
    seamRight n m (seamImmediateSecondBottomProjection p q d).left = d.2.2.val.left ∧
      seamRight n m (seamImmediateSecondBottomProjection p q d).right = d.2.1.val.right := by
  have hs := seamImmediateMixedSecondRectangle_sides p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 (Or.inl ⟨d.2.1.property.2, d.2.2.property.2⟩)
  have hr := seamImmediateSecond_bottom_sides p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 d.2.1.property.2 d.2.2.property.2
  exact ⟨hs.1.trans hr.2.2.symm, hs.2.trans hr.2.1.symm⟩

theorem seamImmediateSecondTopProjection_sides (p q : SeamRetainedIndex n m)
    (d : SeamImmediateSecondTopData p q) :
    seamRight n m (seamImmediateSecondTopProjection p q d).left = d.2.1.val.left ∧
      seamRight n m (seamImmediateSecondTopProjection p q d).right = d.2.2.val.right := by
  have hs := seamImmediateMixedSecondRectangle_sides p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 (Or.inr ⟨d.2.1.property.2, d.2.2.property.2⟩)
  have hr := seamImmediateSecond_top_sides p q d.1 d.2.1.val d.2.2.val
    d.2.1.property.1 d.2.2.property.1 d.2.1.property.2 d.2.2.property.2
  exact ⟨hs.1.trans hr.2.1.symm, hs.2.trans hr.2.2.symm⟩

theorem seamImmediateSecondBottomProjection_injective (p q : SeamRetainedIndex n m) :
    Function.Injective (seamImmediateSecondBottomProjection p q) := by
  rintro ⟨x, e, f⟩ ⟨y, g, h⟩ hh
  have hs₁ := seamImmediateSecondBottomProjection_sides p q ⟨x, e, f⟩
  have hs₂ := seamImmediateSecondBottomProjection_sides p q ⟨y, g, h⟩
  have hQ : f.val.left = h.val.left := hs₁.1.symm.trans
    ((congrArg (fun r => seamRight n m r.left) hh).trans hs₂.1)
  have hP : e.val.right = g.val.right := hs₁.2.symm.trans
    ((congrArg (fun r => seamRight n m r.right) hh).trans hs₂.2)
  have hA : e.val.left = g.val.left :=
    (seamImmediateSecond_bottom_pivot p q x e.val f.val
      e.property.1 f.property.1 e.property.2 f.property.2).trans
    (seamImmediateSecond_bottom_pivot p q y g.val h.val
      g.property.1 h.property.1 g.property.2 h.property.2).symm
  have hfA := (seamImmediateSecond_bottom_sides p q x e.val f.val
    e.property.1 f.property.1 e.property.2 f.property.2).1
  have hhA := (seamImmediateSecond_bottom_sides p q y g.val h.val
    g.property.1 h.property.1 g.property.2 h.property.2).1
  have hxy : x.val.val = y.val.val := by
    rw [f.val.source_eq_swapColumns, h.val.source_eq_swapColumns, ← hfA, ← hhA, hA, hQ]
  have hxy : x = y := Subtype.ext (Subtype.ext hxy)
  subst y
  have heg : e = g := Subtype.ext (GridRectangleBetween.ext hA hP)
  have hfh : f = h := Subtype.ext
    (GridRectangleBetween.ext hQ (hfA.symm.trans (hA.trans hhA)))
  subst g
  subst h
  rfl

theorem seamImmediateSecondTopProjection_injective (p q : SeamRetainedIndex n m) :
    Function.Injective (seamImmediateSecondTopProjection p q) := by
  rintro ⟨x, e, f⟩ ⟨y, g, h⟩ hh
  have hs₁ := seamImmediateSecondTopProjection_sides p q ⟨x, e, f⟩
  have hs₂ := seamImmediateSecondTopProjection_sides p q ⟨y, g, h⟩
  have hQ : e.val.left = g.val.left := hs₁.1.symm.trans
    ((congrArg (fun r => seamRight n m r.left) hh).trans hs₂.1)
  have hP : f.val.right = h.val.right := hs₁.2.symm.trans
    ((congrArg (fun r => seamRight n m r.right) hh).trans hs₂.2)
  have hA : e.val.right = g.val.right :=
    (seamImmediateSecond_top_pivot p q x e.val f.val
      e.property.1 f.property.1 e.property.2 f.property.2).trans
    (seamImmediateSecond_top_pivot p q y g.val h.val
      g.property.1 h.property.1 g.property.2 h.property.2).symm
  have hfA := (seamImmediateSecond_top_sides p q x e.val f.val
    e.property.1 f.property.1 e.property.2 f.property.2).1
  have hhA := (seamImmediateSecond_top_sides p q y g.val h.val
    g.property.1 h.property.1 g.property.2 h.property.2).1
  have hxy : x.val.val = y.val.val := by
    rw [f.val.source_eq_swapColumns, h.val.source_eq_swapColumns, ← hfA, ← hhA, hA, hP]
  have hxy : x = y := Subtype.ext (Subtype.ext hxy)
  subst y
  have heg : e = g := Subtype.ext (GridRectangleBetween.ext hQ hA)
  have hfh : f = h := Subtype.ext
    (GridRectangleBetween.ext (hfA.symm.trans (hA.trans hhA)) hP)
  subst g
  subst h
  rfl

/-- The wrapping empty second-factor rectangles incident to zero and missing from direct lifts. -/
abbrev SeamObstructedSecondZeroRectangle (p q : SeamRetainedIndex n m) :=
  {r : GridRectangleBetween p.2 q.2 // r.IsEmpty ∧
    ¬ (seamSecondFactorRectangle p.1 r).IsEmpty ∧ r.right < r.left ∧
    (r.bottom = 0 ∨ r.top = 0)}

abbrev SeamImmediateSecondData (p q : SeamRetainedIndex n m) :=
  SeamImmediateSecondBottomData p q ⊕ SeamImmediateSecondTopData p q

instance seamObstructedSecondZeroRectangleFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamObstructedSecondZeroRectangle p q) := inferInstance

instance seamImmediateSecondDataFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamImmediateSecondData p q) := inferInstance

def seamImmediateSecondProjection (p q : SeamRetainedIndex n m) :
    SeamImmediateSecondData p q → SeamObstructedSecondZeroRectangle p q
  | Sum.inl ⟨s, e, f⟩ => ⟨seamImmediateSecondBottomProjection p q ⟨s, e, f⟩,
      seamImmediateMixedSecondRectangle_isEmpty p q s e.val f.val
        e.property.1 f.property.1 (Or.inl ⟨e.property.2, f.property.2⟩),
      seamImmediateSecond_bottom_lift_not_isEmpty p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2,
      seamImmediateMixedSecondRectangle_wraps p q s e.val f.val
        e.property.1 f.property.1 (Or.inl ⟨e.property.2, f.property.2⟩),
      Or.inl (seamImmediateSecond_bottom_zero p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2)⟩
  | Sum.inr ⟨s, e, f⟩ => ⟨seamImmediateSecondTopProjection p q ⟨s, e, f⟩,
      seamImmediateMixedSecondRectangle_isEmpty p q s e.val f.val
        e.property.1 f.property.1 (Or.inr ⟨e.property.2, f.property.2⟩),
      seamImmediateSecond_top_lift_not_isEmpty p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2,
      seamImmediateMixedSecondRectangle_wraps p q s e.val f.val
        e.property.1 f.property.1 (Or.inr ⟨e.property.2, f.property.2⟩),
      Or.inr (seamImmediateSecond_top_zero p q s e.val f.val
        e.property.1 f.property.1 e.property.2 f.property.2)⟩

theorem seamImmediateSecondProjection_injective (p q : SeamRetainedIndex n m) :
    Function.Injective (seamImmediateSecondProjection p q) := by
  intro a b hh
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (seamImmediateSecondBottomProjection_injective p q
      (congrArg Subtype.val hh))
  · have hr := congrArg Subtype.val hh
    have hbottom := seamImmediateSecond_bottom_zero p q a.1 a.2.1.val a.2.2.val
      a.2.1.property.1 a.2.2.property.1 a.2.1.property.2 a.2.2.property.2
    have htop := seamImmediateSecond_top_zero p q b.1 b.2.1.val b.2.2.val
      b.2.1.property.1 b.2.2.property.1 b.2.1.property.2 b.2.2.property.2
    have ht := congrArg (fun r => r.top) hr
    exact False.elim ((seamImmediateSecondBottomProjection p q a).bottom_ne_top
      (hbottom.trans ((ht.trans htop).symm)))
  · have hr := congrArg Subtype.val hh
    have htop := seamImmediateSecond_top_zero p q a.1 a.2.1.val a.2.2.val
      a.2.1.property.1 a.2.2.property.1 a.2.1.property.2 a.2.2.property.2
    have hbottom := seamImmediateSecond_bottom_zero p q b.1 b.2.1.val b.2.2.val
      b.2.1.property.1 b.2.2.property.1 b.2.1.property.2 b.2.2.property.2
    have hb := congrArg (fun r => r.bottom) hr
    exact False.elim ((seamImmediateSecondTopProjection p q a).bottom_ne_top
      ((hb.trans hbottom).trans htop.symm))
  · exact congrArg Sum.inr (seamImmediateSecondTopProjection_injective p q
      (congrArg Subtype.val hh))

/-- Recover the equal-node presentation of a zero-transition bottom-oriented correction. -/
def seamImmediateSecondBottomDataOfZero (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.left.val < n) (hf : c.2.2.2.2.val.right.val < n) :
    SeamImmediateSecondBottomData p q := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  exact ⟨s, ⟨e.val, e.property, he⟩, ⟨f.val, f.property, hf⟩⟩

def seamImmediateSecondTopDataOfZero (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.right.val < n) (hf : c.2.2.2.2.val.left.val < n) :
    SeamImmediateSecondTopData p q := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  exact ⟨s, ⟨e.val, e.property, he⟩, ⟨f.val, f.property, hf⟩⟩

@[simp] theorem seamImmediateSecondBottomDataOfZero_sides (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.left.val < n) (hf : c.2.2.2.2.val.right.val < n) :
    (seamImmediateSecondBottomDataOfZero p q c he hf).2.1.val.right = c.2.2.1.val.right ∧
      (seamImmediateSecondBottomDataOfZero p q c he hf).2.2.val.left = c.2.2.2.2.val.left := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  exact ⟨rfl, rfl⟩

@[simp] theorem seamImmediateSecondTopDataOfZero_sides (p q : SeamRetainedIndex n m)
    (c : SeamCorrectionPath 0 p q)
    (he : c.2.2.1.val.right.val < n) (hf : c.2.2.2.2.val.left.val < n) :
    (seamImmediateSecondTopDataOfZero p q c he hf).2.1.val.left = c.2.2.1.val.left ∧
      (seamImmediateSecondTopDataOfZero p q c he hf).2.2.val.right = c.2.2.2.2.val.right := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  exact ⟨rfl, rfl⟩

/-- Every obstructed wrapping rectangle incident to row zero has an immediate lift. -/
theorem seamImmediateSecondProjection_surjective (x : GridState (n + 1))
    (z w : GridState (m + 1)) :
    Function.Surjective (seamImmediateSecondProjection (x, z) (x, w)) := by
  rintro ⟨r, he, hb, hc, hbottom | htop⟩
  · let c := seamSecondFactorShortLift_bottom_zero x r he hb hc hbottom
    have hs := seamSecondFactorShortLift_bottom_zero_small_sides x r he hb hc hbottom
    let d := seamImmediateSecondBottomDataOfZero (x, z) (x, w) c hs.1 hs.2
    have hd := seamImmediateSecondBottomDataOfZero_sides (x, z) (x, w) c hs.1 hs.2
    have hlift := seamSecondFactorShortLift_bottom_zero_sides x r he hb hc hbottom
    refine ⟨Sum.inl d, Subtype.ext ?_⟩
    apply GridRectangleBetween.ext
    · apply seamRight_injective (m := m)
      exact (seamImmediateSecondBottomProjection_sides (x, z) (x, w) d).1.trans
        (hd.2.trans hlift.2.2.2.1)
    · apply seamRight_injective (m := m)
      exact (seamImmediateSecondBottomProjection_sides (x, z) (x, w) d).2.trans
        (hd.1.trans hlift.2.2.1)
  · let c := seamSecondFactorShortLift_top_zero x r he hb hc htop
    have hs := seamSecondFactorShortLift_top_zero_small_sides x r he hb hc htop
    let d := seamImmediateSecondTopDataOfZero (x, z) (x, w) c hs.1 hs.2
    have hd := seamImmediateSecondTopDataOfZero_sides (x, z) (x, w) c hs.1 hs.2
    have hlift := seamSecondFactorShortLift_top_zero_sides x r he hb hc htop
    refine ⟨Sum.inr d, Subtype.ext ?_⟩
    apply GridRectangleBetween.ext
    · apply seamRight_injective (m := m)
      exact (seamImmediateSecondTopProjection_sides (x, z) (x, w) d).1.trans
        (hd.1.trans hlift.2.1)
    · apply seamRight_injective (m := m)
      exact (seamImmediateSecondTopProjection_sides (x, z) (x, w) d).2.trans
        (hd.2.trans hlift.2.2.2.2)

/-- The mixed finite-data bijection retains both actual correction rectangles. -/
def seamImmediateSecondEquiv (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    SeamImmediateSecondData (x, z) (x, w) ≃ SeamObstructedSecondZeroRectangle (x, z) (x, w) :=
  Equiv.ofBijective (seamImmediateSecondProjection (x, z) (x, w))
    ⟨seamImmediateSecondProjection_injective _ _, seamImmediateSecondProjection_surjective x z w⟩

theorem seamImmediateSecond_card (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    Fintype.card (SeamImmediateSecondData (x, z) (x, w)) =
      Fintype.card (SeamObstructedSecondZeroRectangle (x, z) (x, w)) :=
  Fintype.card_congr (seamImmediateSecondEquiv x z w)

/-- Equal first factors exclude both equal-orientation corrections. -/
theorem seamImmediate_same_first_orientations (x : GridState (n + 1))
    (z w : GridState (m + 1)) (s : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState x z) (seamComplementPartner s.val).val)
    (f : GridRectangleBetween s.val.val (seamState x w)) (he : e.IsEmpty) (hf : f.IsEmpty) :
    (e.left.val < n ∧ f.right.val < n) ∨ (e.right.val < n ∧ f.left.val < n) := by
  have heR := seamEnteringRectangle_ranges (seamState_mem_pairSector x z)
    (seamComplementPartner s.val).property e
  have hfR := seamLeavingRectangle_ranges (seamState_mem_pairSector x w) s.val.property f
  rcases heR with heR | heR <;> rcases hfR with hfR | hfR
  · exact False.elim ((seamImmediateFirstRightRectangle (x, z) (x, w) s e f he hf
      heR.1 hfR.1).source_ne_target rfl)
  · exact Or.inl ⟨heR.1, hfR.1⟩
  · exact Or.inr ⟨heR.1, hfR.1⟩
  · exact False.elim ((seamImmediateFirstLeftRectangle (x, z) (x, w) s e f he hf
      heR.1 hfR.1).source_ne_target rfl)

def seamImmediateSecondDataToZero (p q : SeamRetainedIndex n m) :
    SeamImmediateSecondData p q → SeamCorrectionPath 0 p q
  | Sum.inl ⟨s, e, f⟩ => ⟨s, s, ⟨e.val, e.property.1⟩, ⟨(), rfl⟩, ⟨f.val, f.property.1⟩⟩
  | Sum.inr ⟨s, e, f⟩ => ⟨s, s, ⟨e.val, e.property.1⟩, ⟨(), rfl⟩, ⟨f.val, f.property.1⟩⟩

/-- All zero-transition corrections with fixed first factor have mixed orientations. -/
def seamZeroToImmediateSecondData (x : GridState (n + 1)) (z w : GridState (m + 1))
    (c : SeamCorrectionPath 0 (x, z) (x, w)) : SeamImmediateSecondData (x, z) (x, w) := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  have hor := seamImmediate_same_first_orientations x z w s e.val f.val e.property f.property
  by_cases he : e.val.left.val < n
  · have hf : f.val.right.val < n := by
      rcases hor with h | h
      · exact h.2
      · exact False.elim ((seamImmediate_entry_left_not_small (x, z) s e.val h.1) he)
    exact Sum.inl ⟨s, ⟨e.val, e.property, he⟩, ⟨f.val, f.property, hf⟩⟩
  · have hr := hor.resolve_left (fun h => he h.1)
    exact Sum.inr ⟨s, ⟨e.val, e.property, hr.1⟩, ⟨f.val, f.property, hr.2⟩⟩

theorem seamZeroToImmediateSecondData_left_inv (x : GridState (n + 1))
    (z w : GridState (m + 1)) :
    Function.LeftInverse (seamZeroToImmediateSecondData x z w)
      (seamImmediateSecondDataToZero (x, z) (x, w)) := by
  rintro (⟨s, e, f⟩ | ⟨s, e, f⟩)
  · simp only [seamImmediateSecondDataToZero, seamZeroToImmediateSecondData]
    split_ifs with he
    · simp [he]
    · exact False.elim (he e.property.2)
  · have he := seamImmediate_entry_left_not_small (x, z) s e.val e.property.2
    simp only [seamImmediateSecondDataToZero, seamZeroToImmediateSecondData]
    split_ifs with he'
    · exact False.elim (he he')
    · simp [he]

theorem seamZeroToImmediateSecondData_right_inv (x : GridState (n + 1))
    (z w : GridState (m + 1)) :
    Function.RightInverse (seamZeroToImmediateSecondData x z w)
      (seamImmediateSecondDataToZero (x, z) (x, w)) := by
  rintro ⟨s, t, e, ⟨u, hst⟩, f⟩
  subst t
  cases u
  by_cases he : e.val.left.val < n
  · simp only [seamZeroToImmediateSecondData, dif_pos he, seamImmediateSecondDataToZero]
  · simp only [seamZeroToImmediateSecondData, dif_neg he, seamImmediateSecondDataToZero]

/-- All actual zero-transition corrections with fixed first factor have this finite bijection. -/
def seamCorrectionZeroSecondEquiv (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    SeamCorrectionPath 0 (x, z) (x, w) ≃ SeamObstructedSecondZeroRectangle (x, z) (x, w) :=
  (Equiv.ofBijective (seamZeroToImmediateSecondData x z w)
    ⟨(seamZeroToImmediateSecondData_right_inv x z w).injective,
      (seamZeroToImmediateSecondData_left_inv x z w).surjective⟩).trans
    (seamImmediateSecondEquiv x z w)

theorem seamCorrectionZeroSecond_card (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    Fintype.card (SeamCorrectionPath 0 (x, z) (x, w)) =
      Fintype.card (SeamObstructedSecondZeroRectangle (x, z) (x, w)) :=
  Fintype.card_congr (seamCorrectionZeroSecondEquiv x z w)

end OnLeConjecture.KnotFloer.GridFull
