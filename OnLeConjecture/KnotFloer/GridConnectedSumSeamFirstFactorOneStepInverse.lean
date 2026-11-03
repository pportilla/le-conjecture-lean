/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepMetadata

/-! # One-step correction paths and their first-factor rectangles -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

/-- The three rectangles of a one-step correction, with its zero-length tail removed. -/
abbrev SeamOneStepData (p q : SeamRetainedIndex n m) :=
  Σ x : SeamMatchingSource n m, Σ y : SeamMatchingSource n m,
    {e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val //
      e.IsEmpty} × SeamInternalRectangle x y ×
    {f : GridRectangleBetween y.val.val (seamState q.1 q.2) // f.IsEmpty}

/-- Removing the final equality witness changes no path choices. -/
def seamCorrectionOneDataEquiv (p q : SeamRetainedIndex n m) :
    SeamCorrectionPath 1 p q ≃ SeamOneStepData p q where
  toFun := by
    rintro ⟨x, y, e, ⟨w, r, tail⟩, f⟩
    have hwy : w = y := tail.property
    subst w
    exact ⟨x, y, e, r, f⟩
  invFun := fun ⟨x, y, e, r, f⟩ => ⟨x, y, e, ⟨y, r, ⟨(), rfl⟩⟩, f⟩
  left_inv := by
    rintro ⟨x, y, e, ⟨w, r, tail⟩, f⟩
    have hwy : w = y := tail.property
    subst w
    rfl
  right_inv := by rintro ⟨x, y, e, r, f⟩; rfl

/-- Rectangles remaining after the direct and immediate first-factor cases. -/
abbrev SeamObstructedFirstNonlastBoundaryRectangle
    (u v : GridState (n + 1)) (z : GridState (m + 1)) :=
  {r : GridRectangleBetween u v // r.IsEmpty ∧ ¬ (seamFirstFactorRectangle r z).IsEmpty ∧
    r.left ≠ Fin.last n ∧ r.right ≠ Fin.last n ∧ (z 0 = 0 ∨ z (Fin.last m) = 0)}

section Projection
variable (u v : GridState (n + 1)) (z : GridState (m + 1))

theorem seamOneStepData_first (d : SeamOneStepData (u, z) (v, z))
    (h : d.2.2.1.val.right.val < n) :
    d.2.2.2.1.val.left.val < n ∧ (d.1.val.val d.2.2.2.1.val.left).val ≤ n ∧
      d.2.2.2.1.val.right = seamComplementFirst d.1.val := by
  rcases d with ⟨x, y, e, r, f⟩
  obtain ⟨C, hCn, hCv, ho | ho⟩ := seamFirstFactorOneStep_orientations
    u v z x y e.val r.val f.val r.property.1 e.property r.property.2 f.property
  · simpa only [ho.1] using And.intro hCn (And.intro hCv ho.2.1)
  · have heP := seamMatchingEntry_right_eq_first_of_left_lt (u, z) x e.val e.property ho.2.2.1
    have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
    change e.val.right.val < n at h
    rw [heP] at h
    omega

theorem seamOneStepData_second (d : SeamOneStepData (u, z) (v, z))
    (h : ¬ d.2.2.1.val.right.val < n) :
    d.2.2.2.1.val.right.val < n ∧ (d.1.val.val d.2.2.2.1.val.right).val ≤ n ∧
      d.2.2.2.1.val.left = seamComplementSecond d.1.val := by
  rcases d with ⟨x, y, e, r, f⟩
  obtain ⟨C, hCn, hCv, ho | ho⟩ := seamFirstFactorOneStep_orientations
    u v z x y e.val r.val f.val r.property.1 e.property r.property.2 f.property
  · exact False.elim (h ho.2.2.1)
  · simpa only [ho.2.1] using And.intro hCn (And.intro hCv ho.1)

/-- Every actual one-step correction projects to a missing first-factor rectangle. -/
def seamOneStepProjection (d : SeamOneStepData (u, z) (v, z)) :
    SeamObstructedFirstNonlastBoundaryRectangle u v z := by
  let x := d.1
  let y := d.2.1
  let e := d.2.2.1
  let r := d.2.2.2.1
  let f := d.2.2.2.2
  by_cases h : e.val.right.val < n
  · have hd := seamOneStepData_first u v z d h
    have hCn := hd.1
    have hCv := hd.2.1
    have hP := hd.2.2
    have hs : (r.val.left = seamComplementFirst x.val ∧ r.val.right = r.val.left) ∨
        (r.val.right = seamComplementFirst x.val ∧ r.val.left = r.val.left) := Or.inr ⟨hP, rfl⟩
    refine ⟨seamOneStepFirstRectangle u v z x y e.val r.val f.val
      e.property r.property.2 f.property r.val.left hCn hCv hs,
      seamOneStepFirstRectangle_isEmpty u v z x y e.val r.val f.val
        e.property r.property.2 f.property r.val.left hCn hCv hs,
      seamOneStepFirstRectangle_blocked u v z x y e.val r.val f.val
        e.property r.property.2 f.property r.val.left hCn hCv hs, ?_⟩
    obtain ⟨_, _, hl, hr⟩ := seamOneStepFirstRectangle_columns u v z x y e.val r.val f.val
      e.property r.property.2 f.property r.val.left hCn hCv hs
    exact ⟨hl, hr, Or.inl (seamOneStep_same_second_low_first_zero u v z x y e.val r.val f.val
      e.property r.property.2 f.property r.val.left hCn hCv hs)⟩
  · have hd := seamOneStepData_second u v z d h
    have hCn := hd.1
    have hCv := hd.2.1
    have hQ := hd.2.2
    have hs : (r.val.left = seamComplementSecond x.val ∧ r.val.right = r.val.right) ∨
        (r.val.right = seamComplementSecond x.val ∧ r.val.left = r.val.right) := Or.inl ⟨hQ, rfl⟩
    refine ⟨seamOneStepSecondRectangle u v z x y e.val r.val f.val
      e.property r.property.2 f.property r.val.right hCn hCv hs,
      seamOneStepSecondRectangle_isEmpty u v z x y e.val r.val f.val
        e.property r.property.2 f.property r.val.right hCn hCv hs,
      seamOneStepSecondRectangle_blocked u v z x y e.val r.val f.val
        e.property r.property.2 f.property r.val.right hCn hCv hs, ?_⟩
    obtain ⟨_, _, hl, hr⟩ := seamOneStepSecondRectangle_columns u v z x y e.val r.val f.val
      e.property r.property.2 f.property r.val.right hCn hCv hs
    exact ⟨hl, hr, Or.inr (seamOneStep_same_second_low_second_zero u v z x y e.val r.val f.val
      e.property r.property.2 f.property r.val.right hCn hCv hs)⟩

private theorem oneStepProjection_first_columns (d : SeamOneStepData (u, z) (v, z))
    (h : d.2.2.1.val.right.val < n) :
    (seamOneStepProjection u v z d).val.left.val = d.2.2.2.1.val.left.val ∧
      (seamOneStepProjection u v z d).val.right.val = d.2.2.1.val.right.val := by
  obtain ⟨hCn, hCv, hP⟩ := seamOneStepData_first u v z d h
  simpa only [seamOneStepProjection, dif_pos h] using
    (seamOneStepFirstRectangle_columns u v z d.1 d.2.1 d.2.2.1.val d.2.2.2.1.val d.2.2.2.2.val
      d.2.2.1.property d.2.2.2.1.property.2 d.2.2.2.2.property _ hCn hCv
      (Or.inr ⟨hP, rfl⟩)).imp_right (fun h => h.1)

private theorem oneStepProjection_second_columns (d : SeamOneStepData (u, z) (v, z))
    (h : ¬ d.2.2.1.val.right.val < n) :
    (seamOneStepProjection u v z d).val.left.val = d.2.2.1.val.left.val ∧
      (seamOneStepProjection u v z d).val.right.val = d.2.2.2.1.val.right.val := by
  obtain ⟨hCn, hCv, hQ⟩ := seamOneStepData_second u v z d h
  simpa only [seamOneStepProjection, dif_neg h] using
    (seamOneStepSecondRectangle_columns u v z d.1 d.2.1 d.2.2.1.val d.2.2.2.1.val d.2.2.2.2.val
      d.2.2.1.property d.2.2.2.1.property.2 d.2.2.2.2.property _ hCn hCv
      (Or.inl ⟨hQ, rfl⟩)).imp_right (fun h => h.1)


/-- Rectangle sides determine the matching nodes and hence the full one-step data. -/
theorem seamOneStepData_ext {p q : SeamRetainedIndex n m} (a b : SeamOneStepData p q)
    (heL : a.2.2.1.val.left = b.2.2.1.val.left)
    (heR : a.2.2.1.val.right = b.2.2.1.val.right)
    (hrL : a.2.2.2.1.val.left = b.2.2.2.1.val.left)
    (hrR : a.2.2.2.1.val.right = b.2.2.2.1.val.right)
    (hfL : a.2.2.2.2.val.left = b.2.2.2.2.val.left)
    (hfR : a.2.2.2.2.val.right = b.2.2.2.2.val.right) : a = b := by
  rcases a with ⟨x, y, e, r, f⟩
  rcases b with ⟨x', y', e', r', f'⟩
  have hx : x = x' := by
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    apply Subtype.ext
    rw [e.val.target_eq_swapColumns, e'.val.target_eq_swapColumns, heL, heR]
  have hy : y = y' := by
    apply Subtype.ext
    apply Subtype.ext
    rw [f.val.source_eq_swapColumns, f'.val.source_eq_swapColumns, hfL, hfR]
  subst x'
  subst y'
  have he : e = e' := Subtype.ext (GridRectangleBetween.ext heL heR)
  have hr : r = r' := Subtype.ext (GridRectangleBetween.ext hrL hrR)
  have hf : f = f' := Subtype.ext (GridRectangleBetween.ext hfL hfR)
  subst e'
  subst r'
  subst f'
  rfl

/-- In the zero-column case, all six path sides are recovered from the projected rectangle. -/
theorem seamOneStepProjection_first_sides (d : SeamOneStepData (u, z) (v, z))
    (h : d.2.2.1.val.right.val < n) :
    let R := (seamOneStepProjection u v z d).val
    d.2.2.1.val.left = Fin.last (n + m) ∧ d.2.2.1.val.right = seamLeft n m R.right ∧
      d.2.2.2.1.val.left = seamLeft n m R.left ∧ d.2.2.2.1.val.right = seamRight n m 0 ∧
      d.2.2.2.2.val.left = Fin.last (n + m) ∧ d.2.2.2.2.val.right = seamLeft n m R.right ∧
      z 0 = 0 := by
  rcases d with ⟨x, y, e, r, f⟩
  obtain ⟨hCn, hCv, hP⟩ := seamOneStepData_first u v z ⟨x, y, e, r, f⟩ h
  have hs : (r.val.left = seamComplementFirst x.val ∧ r.val.right = r.val.left) ∨
      (r.val.right = seamComplementFirst x.val ∧ r.val.left = r.val.left) := Or.inr ⟨hP, rfl⟩
  obtain ⟨_, hfR, hAeq, _⟩ := seamOneStep_same_second_low_first_orientations
    u v z x y e.val r.val f.val e.property r.property.2 f.property _ hCn hCv hs
  have hcut := seamOneStep_low_first_cut r.val r.property.2 _ hCn hCv hs
  have hlast := seamOneStep_same_second_low_first_last
    u v z x y e.val r.val f.val e.property r.property.2 f.property _ hCn hCv hs
  have hYsecond := (seamOneStep_low_first r.val r.property.2 _ hCn hCv hs).2.2.2.2.1
  obtain ⟨hL, hR⟩ := oneStepProjection_first_columns u v z ⟨x, y, e, r, f⟩ h
  have hEL : e.val.left = Fin.last (n + m) :=
    (seamMatchingEntry_left_eq_second_of_right_lt (u, z) x e.val e.property h).trans hlast
  have hER : e.val.right = seamLeft n m
      (seamOneStepProjection u v z ⟨x, y, e, r, f⟩).val.right := Fin.ext hR.symm
  exact ⟨hEL, hER, Fin.ext hL.symm, hP.trans hcut,
    ((seamMatchingExit_left_eq_second_of_right_lt (v, z) y f.val f.property hfR).trans
      hYsecond).trans hlast, hAeq.symm.trans hER,
    seamOneStep_same_second_low_first_zero
      u v z x y e.val r.val f.val e.property r.property.2 f.property _ hCn hCv hs⟩

/-- In the last-column case, all six path sides are recovered from the projected rectangle. -/
theorem seamOneStepProjection_second_sides (d : SeamOneStepData (u, z) (v, z))
    (h : ¬ d.2.2.1.val.right.val < n) :
    let R := (seamOneStepProjection u v z d).val
    d.2.2.1.val.left = seamLeft n m R.left ∧ d.2.2.1.val.right = seamRight n m 0 ∧
      d.2.2.2.1.val.left = Fin.last (n + m) ∧ d.2.2.2.1.val.right = seamLeft n m R.right ∧
      d.2.2.2.2.val.left = seamLeft n m R.left ∧ d.2.2.2.2.val.right = seamRight n m 0 ∧
      z (Fin.last m) = 0 := by
  rcases d with ⟨x, y, e, r, f⟩
  obtain ⟨hCn, hCv, hQ⟩ := seamOneStepData_second u v z ⟨x, y, e, r, f⟩ h
  have hs : (r.val.left = seamComplementSecond x.val ∧ r.val.right = r.val.right) ∨
      (r.val.right = seamComplementSecond x.val ∧ r.val.left = r.val.right) := Or.inl ⟨hQ, rfl⟩
  obtain ⟨heL, hfL, hAeq, _⟩ := seamOneStep_same_second_low_second_orientations
    u v z x y e.val r.val f.val e.property r.property.2 f.property _ hCn hCv hs
  have hcut := seamOneStep_same_second_low_second_cut
    u v z x y e.val r.val f.val e.property r.property.2 f.property _ hCn hCv hs
  have hlast := seamOneStep_low_second_last r.val r.property.2
    (seamMatchingEntry_southwest_card (u, z) x e.val) _ hCn hCv hs
  have hYfirst := (seamOneStep_low_second r.val r.property.2 _ hCn hCv hs).2.2.2.1
  obtain ⟨hL, hR⟩ := oneStepProjection_second_columns u v z ⟨x, y, e, r, f⟩ h
  have hEL : e.val.left = seamLeft n m
      (seamOneStepProjection u v z ⟨x, y, e, r, f⟩).val.left := Fin.ext hL.symm
  exact ⟨hEL,
    (seamMatchingEntry_right_eq_first_of_left_lt (u, z) x e.val e.property heL).trans hcut,
    hQ.trans hlast, Fin.ext hR.symm, hAeq.symm.trans hEL,
    ((seamMatchingExit_right_eq_first_of_left_lt (v, z) y f.val f.property hfL).trans
      hYfirst).trans hcut,
    seamOneStep_same_second_low_second_zero
      u v z x y e.val r.val f.val e.property r.property.2 f.property _ hCn hCv hs⟩

/-- Every actual one-step path requires a nontrivial second grid. -/
theorem seamOneStepData_second_positive (d : SeamOneStepData (u, z) (v, z)) : 0 < m := by
  let R := seamOneStepProjection u v z d
  exact (seamFirstFactor_blocked_nonlast_ranges R.val z R.property.1 R.property.2.1
    R.property.2.2.1 R.property.2.2.2.1).1

/-- The entry orientation is forced by the zero row of the fixed second state. -/
theorem seamOneStepData_first_iff_zero (d : SeamOneStepData (u, z) (v, z)) :
    d.2.2.1.val.right.val < n ↔ z 0 = 0 := by
  constructor
  · intro h
    exact (seamOneStepProjection_first_sides u v z d h).2.2.2.2.2.2
  · intro hz
    by_contra h
    have hzlast := (seamOneStepProjection_second_sides u v z d h).2.2.2.2.2.2
    have heq := congrArg Fin.val (z.toPerm.injective (hz.trans hzlast.symm))
    have hm := seamOneStepData_second_positive u v z d
    simp only [Fin.val_zero, Fin.val_last] at heq
    omega

/-- Projection retains every choice of a complete one-step correction. -/
theorem seamOneStepProjection_injective : Function.Injective (seamOneStepProjection u v z) := by
  intro a b hh
  have hrect := congrArg Subtype.val hh
  by_cases hz : z 0 = 0
  · have ha := (seamOneStepData_first_iff_zero u v z a).mpr hz
    have hb := (seamOneStepData_first_iff_zero u v z b).mpr hz
    obtain ⟨haEL, haER, haRL, haRR, haFL, haFR, _⟩ := seamOneStepProjection_first_sides u v z a ha
    obtain ⟨hbEL, hbER, hbRL, hbRR, hbFL, hbFR, _⟩ := seamOneStepProjection_first_sides u v z b hb
    apply seamOneStepData_ext a b
    · exact haEL.trans hbEL.symm
    · rw [haER, hbER, hrect]
    · rw [haRL, hbRL, hrect]
    · exact haRR.trans hbRR.symm
    · exact haFL.trans hbFL.symm
    · rw [haFR, hbFR, hrect]
  · have ha : ¬ a.2.2.1.val.right.val < n := fun h =>
      hz ((seamOneStepData_first_iff_zero u v z a).mp h)
    have hb : ¬ b.2.2.1.val.right.val < n := fun h =>
      hz ((seamOneStepData_first_iff_zero u v z b).mp h)
    obtain ⟨haEL, haER, haRL, haRR, haFL, haFR, _⟩ := seamOneStepProjection_second_sides u v z a ha
    obtain ⟨hbEL, hbER, hbRL, hbRR, hbFL, hbFR, _⟩ := seamOneStepProjection_second_sides u v z b hb
    apply seamOneStepData_ext a b
    · rw [haEL, hbEL, hrect]
    · exact haER.trans hbER.symm
    · exact haRL.trans hbRL.symm
    · rw [haRR, hbRR, hrect]
    · rw [haFL, hbFL, hrect]
    · exact haFR.trans hbFR.symm


set_option backward.isDefEq.respectTransparency false in
/-- The zero-column forward lift retains the original projected column pair. -/
theorem seamFirstFactorOneStepLift_zero_projection_sides
    (r : GridRectangleBetween u v) (he : r.IsEmpty)
    (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n) (hz : z 0 = 0) :
    let d := seamCorrectionOneDataEquiv (u, z) (v, z)
      (seamFirstFactorOneStepLift_zero r z he hb hl hr hz)
    d.2.2.1.val.right = seamLeft n m r.right ∧
      d.2.2.2.1.val.left = seamLeft n m r.left := by
  unfold seamFirstFactorOneStepLift_zero
  generalize hspec : seamFirstFactor_blocked_nonlast_ranges r z he hb hl hr = spec
  rcases spec with ⟨hm, hcols, hln, hrn, hlo, hhi⟩
  simp only [seamCorrectionOneDataEquiv, Equiv.coe_fn_mk,
    ofSwapColumns_left, ofSwapColumns_right, and_self]

set_option backward.isDefEq.respectTransparency false in
/-- The last-column forward lift retains the original projected column pair. -/
theorem seamFirstFactorOneStepLift_last_projection_sides
    (r : GridRectangleBetween u v) (he : r.IsEmpty)
    (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n) (hz : z (Fin.last m) = 0) :
    let d := seamCorrectionOneDataEquiv (u, z) (v, z)
      (seamFirstFactorOneStepLift_last r z he hb hl hr hz)
    d.2.2.1.val.left = seamLeft n m r.left ∧
      d.2.2.1.val.right = seamRight n m 0 ∧ d.2.2.2.1.val.right = seamLeft n m r.right := by
  unfold seamFirstFactorOneStepLift_last
  generalize hspec : seamFirstFactor_blocked_nonlast_ranges r z he hb hl hr = spec
  rcases spec with ⟨hm, hcols, hln, hrn, hlo, hhi⟩
  simp only [seamCorrectionOneDataEquiv, Equiv.coe_fn_mk,
    ofSwapColumns_left, ofSwapColumns_right, and_self]

/-- Projection is a right inverse to the explicit zero-column lift. -/
theorem seamOneStepProjection_lift_zero
    (r : GridRectangleBetween u v) (he : r.IsEmpty)
    (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n) (hz : z 0 = 0) :
    (seamOneStepProjection u v z (seamCorrectionOneDataEquiv (u, z) (v, z)
      (seamFirstFactorOneStepLift_zero r z he hb hl hr hz))).val = r := by
  let d := seamCorrectionOneDataEquiv (u, z) (v, z)
    (seamFirstFactorOneStepLift_zero r z he hb hl hr hz)
  have hd := (seamOneStepData_first_iff_zero u v z d).mpr hz
  obtain ⟨hER, hRL⟩ := seamFirstFactorOneStepLift_zero_projection_sides u v z r he hb hl hr hz
  obtain ⟨hL, hR⟩ := oneStepProjection_first_columns u v z d hd
  apply GridRectangleBetween.ext
  · apply Fin.ext
    exact hL.trans (congrArg Fin.val hRL)
  · apply Fin.ext
    exact hR.trans (congrArg Fin.val hER)

/-- Projection is a right inverse to the explicit last-column lift. -/
theorem seamOneStepProjection_lift_last
    (r : GridRectangleBetween u v) (he : r.IsEmpty)
    (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n) (hz : z (Fin.last m) = 0) :
    (seamOneStepProjection u v z (seamCorrectionOneDataEquiv (u, z) (v, z)
      (seamFirstFactorOneStepLift_last r z he hb hl hr hz))).val = r := by
  let d := seamCorrectionOneDataEquiv (u, z) (v, z)
    (seamFirstFactorOneStepLift_last r z he hb hl hr hz)
  obtain ⟨hEL, hER, hRR⟩ := seamFirstFactorOneStepLift_last_projection_sides u v z r he hb hl hr hz
  have hd : ¬ d.2.2.1.val.right.val < n := by
    rw [hER]
    simp only [seamRight_val, Fin.val_zero, Nat.add_zero, lt_self_iff_false, not_false_eq_true]
  obtain ⟨hL, hR⟩ := oneStepProjection_second_columns u v z d hd
  apply GridRectangleBetween.ext
  · apply Fin.ext
    exact hL.trans (congrArg Fin.val hEL)
  · apply Fin.ext
    exact hR.trans (congrArg Fin.val hRR)


/-- The previously constructed boundary lift, with its redundant zero-length tail removed. -/
def seamOneStepLift (r : SeamObstructedFirstNonlastBoundaryRectangle u v z) :
    SeamOneStepData (u, z) (v, z) :=
  seamCorrectionOneDataEquiv (u, z) (v, z)
    (seamFirstFactorOneStepLift_boundary r.val z r.property.1 r.property.2.1
      r.property.2.2.1 r.property.2.2.2.1 r.property.2.2.2.2)

/-- The actual boundary lift projects to its original factor rectangle. -/
theorem seamOneStepProjection_lift (r : SeamObstructedFirstNonlastBoundaryRectangle u v z) :
    seamOneStepProjection u v z (seamOneStepLift u v z r) = r := by
  apply Subtype.ext
  unfold seamOneStepLift seamFirstFactorOneStepLift_boundary
  split_ifs with hz
  · exact seamOneStepProjection_lift_zero u v z r.val r.property.1 r.property.2.1
      r.property.2.2.1 r.property.2.2.2.1 hz
  · exact seamOneStepProjection_lift_last u v z r.val r.property.1 r.property.2.1
      r.property.2.2.1 r.property.2.2.2.1 (r.property.2.2.2.2.resolve_left hz)

/-- Every actual one-step correction is recovered, including all rectangle and node choices. -/
theorem seamOneStepLift_projection (d : SeamOneStepData (u, z) (v, z)) :
    seamOneStepLift u v z (seamOneStepProjection u v z d) = d :=
  seamOneStepProjection_injective u v z (seamOneStepProjection_lift u v z _)

/-- The finite correspondence on the three actual rectangles. -/
def seamOneStepDataEquiv :
    SeamOneStepData (u, z) (v, z) ≃ SeamObstructedFirstNonlastBoundaryRectangle u v z where
  toFun := seamOneStepProjection u v z
  invFun := seamOneStepLift u v z
  left_inv := seamOneStepLift_projection u v z
  right_inv := seamOneStepProjection_lift u v z

/-- Every one-internal-step correction with fixed second state has exactly one
empty blocked first-factor rectangle with nonfinal columns and a boundary zero preimage. -/
def seamFirstFactorOneStepEquiv :
    SeamCorrectionPath 1 (u, z) (v, z) ≃
      SeamObstructedFirstNonlastBoundaryRectangle u v z :=
  (seamCorrectionOneDataEquiv (u, z) (v, z)).trans (seamOneStepDataEquiv u v z)

/-- The inverse is precisely the previously verified explicit forward lift. -/
theorem seamFirstFactorOneStepEquiv_symm
    (r : SeamObstructedFirstNonlastBoundaryRectangle u v z) :
    (seamFirstFactorOneStepEquiv u v z).symm r =
      seamFirstFactorOneStepLift_boundary r.val z r.property.1 r.property.2.1
        r.property.2.2.1 r.property.2.2.2.1 r.property.2.2.2.2 := by
  change (seamCorrectionOneDataEquiv (u, z) (v, z)).symm
    (seamCorrectionOneDataEquiv (u, z) (v, z) _) = _
  exact (seamCorrectionOneDataEquiv (u, z) (v, z)).symm_apply_apply _

/-- Integer path counts equal integer rectangle counts in this complete one-step case. -/
theorem seamFirstFactorOneStep_card :
    Fintype.card (SeamCorrectionPath 1 (u, z) (v, z)) =
      Fintype.card (SeamObstructedFirstNonlastBoundaryRectangle u v z) :=
  Fintype.card_congr (seamFirstFactorOneStepEquiv u v z)

end Projection
end OnLeConjecture.KnotFloer.GridFull
