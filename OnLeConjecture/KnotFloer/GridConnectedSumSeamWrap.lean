/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamContraction
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# Laurent weights across the shared-corner seam

For a rectangle which wraps horizontally but not vertically, the final O
marking of the first diagram moves to the column of the second diagram whose
O marking has row zero. The column relocation below describes this change
exactly. Its injectivity preserves the number of O markings and hence the
full Laurent weight. The second state is explicitly required to fix its
initial corner throughout.

The full seam coefficient with that second state fixed is exactly the first
factor coefficient with its final X square blocked. The adjacent-column
return edge has a Laurent-unit coefficient under the stated corner
nonfixing hypothesis. Its source is itself a pair of factor states with a
changed second factor. Consequently this edge is not asserted to cancel a
state complementary to the image of all factor pairs.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween

variable {n m : ℕ}

/-- The column receiving the first diagram's final O marking. -/
def seamORelocation (H : GridDiagram (m + 1)) (a : Fin (n + 1)) : Fin (n + m + 1) :=
  if a = Fin.last n then seamRight n m (H.O.toPerm.symm 0) else seamLeft n m a

theorem seamORelocation_injective (H : GridDiagram (m + 1)) (hH : H.X 0 = 0) :
    Function.Injective (seamORelocation (n := n) H) := by
  have hO : H.O 0 ≠ 0 := by simpa only [hH] using H.disjoint 0
  have hb : H.O.toPerm.symm 0 ≠ 0 := by
    intro h
    have hh := H.O.toPerm.apply_symm_apply (0 : Fin (m + 1))
    rw [h] at hh
    exact hO hh
  intro a b hab
  by_cases ha : a = Fin.last n <;> by_cases hc : b = Fin.last n
  · exact ha.trans hc.symm
  · simp only [seamORelocation, if_pos ha, if_neg hc] at hab
    exact False.elim (hb ((seamLeft_eq_seamRight_iff b _).mp hab.symm).2)
  · simp only [seamORelocation, if_neg ha, if_pos hc] at hab
    exact False.elim (hb ((seamLeft_eq_seamRight_iff a _).mp hab).2)
  · simp only [seamORelocation, if_neg ha, if_neg hc] at hab
    exact seamLeft_injective hab

/-- Every second-block column belongs to a horizontally wrapping interval. -/
theorem seamRight_mem_left_cIco_of_wrap (a b : Fin (n + 1))
    (hab : b.val < a.val) (c : Fin (m + 1)) :
    seamRight n m c ∈ Grid.cIco (seamLeft n m a) (seamLeft n m b) := by
  rw [Grid.mem_cIco_iff_of_right_lt_left (by simpa only [seamLeft_val] using hab)]
  left
  change a.val ≤ n + c.val
  have := a.isLt
  omega

/-- A strictly second-block row misses every nonwrapping first-block row interval. -/
theorem seamRight_not_mem_left_cIco_of_ne_zero (a b : Fin (n + 1))
    (hab : a.val < b.val) (c : Fin (m + 1)) (hc : c ≠ 0) :
    seamRight n m c ∉ Grid.cIco (seamLeft n m a) (seamLeft n m b) := by
  obtain ⟨d, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hc
  exact seamRight_succ_not_mem_left_cIco a b hab d

/-- The relocated column has exactly the old O row. -/
theorem connectedSumSeamGrid_O_relocation
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (a : Fin (n + 1)) :
    (connectedSumSeamGrid G H hG hH).O (seamORelocation H a) =
      seamLeft n m (G.O a) := by
  by_cases ha : a = Fin.last n
  · subst a
    simp only [seamORelocation, ↓reduceIte]
    exact seamState_right_of_zero G.O H.O _ (H.O.toPerm.apply_symm_apply 0)
  · obtain ⟨b, rfl⟩ := Fin.eq_castSucc_of_ne_last ha
    simp only [seamORelocation, if_neg (Fin.castSucc_ne_last b)]
    exact seamState_left_castSucc G.O H.O b

/-- Exact O-column relocation for horizontal wrap and vertical nonwrap. -/
theorem connectedSumSeamGrid_OColumns_left_wrap
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0)
    (hc : r.right.val < r.left.val) (hv : r.bottom.val < r.top.val) :
    (connectedSumSeamGrid G H hG hH).OColumns (seamLeftRectangle r z hz).toGridRectangle =
      (G.OColumns r.toGridRectangle).image (seamORelocation H) := by
  classical
  have hmem (a : Fin (n + 1)) :
      seamORelocation H a ∈ (connectedSumSeamGrid G H hG hH).OColumns
          (seamLeftRectangle r z hz).toGridRectangle ↔ a ∈ G.OColumns r.toGridRectangle := by
    rw [GridDiagram.mem_OColumns, GridDiagram.mem_OColumns,
      mem_toGridRectangle_coveredSquares, mem_toGridRectangle_coveredSquares,
      connectedSumSeamGrid_O_relocation]
    simp only [seamLeftRectangle_left, seamLeftRectangle_right,
      seamState_left _ _ hz, seamLeft_mem_cIco_iff]
    by_cases ha : a = Fin.last n
    · subst a
      have hlast : Fin.last n ∈ Grid.cIco r.left r.right := by
        rw [Grid.mem_cIco_iff_of_right_lt_left hc]
        exact Or.inl (Nat.le_of_lt_succ r.left.isLt)
      simp only [seamORelocation, ↓reduceIte, hlast,
        seamRight_mem_left_cIco_of_wrap _ _ hc, true_and]
    · simp only [seamORelocation, if_neg ha, seamLeft_mem_cIco_iff]
  ext c
  constructor
  · intro hcO
    have hrow := ((mem_toGridRectangle_coveredSquares _).mp
      ((GridDiagram.mem_OColumns _).mp hcO)).2
    simp only [seamLeftRectangle_left, seamLeftRectangle_right,
      seamState_left _ _ hz] at hrow
    rcases seam_cases_succ c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · by_cases ha : a = Fin.last n
      · subst a
        have hO : H.O 0 ≠ 0 := by simpa only [hH] using H.disjoint 0
        change seamState G.O H.O (seamLeft n m (Fin.last n)) ∈ _ at hrow
        rw [seamLeft_last, seamState_right_of_ne_zero _ _ _ hO] at hrow
        exact False.elim (seamRight_not_mem_left_cIco_of_ne_zero _ _ hv _ hO hrow)
      · have he : seamORelocation H a = seamLeft n m a := by simp [seamORelocation, ha]
        exact Finset.mem_image.mpr ⟨a, (hmem a).mp (he.symm ▸ hcO), he⟩
    · by_cases hb : H.O b.succ = 0
      · have he : seamORelocation (n := n) H (Fin.last n) = seamRight n m b.succ := by
          simp only [seamORelocation, ↓reduceIte]
          apply congrArg (seamRight n m)
          exact (H.O.toPerm.symm_apply_eq).mpr hb.symm
        exact Finset.mem_image.mpr ⟨Fin.last n, (hmem _).mp (he.symm ▸ hcO), he⟩
      · change seamState G.O H.O (seamRight n m b.succ) ∈ _ at hrow
        rw [seamState_right_of_ne_zero _ _ _ hb] at hrow
        exact False.elim (seamRight_not_mem_left_cIco_of_ne_zero _ _ hv _ hb hrow)
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    exact (hmem a).mpr ha

/-- Full Laurent weight is unchanged also when only the horizontal interval wraps. -/
theorem connectedSumSeamGrid_rectangle_weight_left_wrap
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0)
    (hc : r.right.val < r.left.val) (hv : r.bottom.val < r.top.val)
    (R : Type*) [CommSemiring R] :
    (LaurentPolynomial.T (((connectedSumSeamGrid G H hG hH).OColumns
      (seamLeftRectangle r z hz).toGridRectangle).card : ℤ) : LaurentPolynomial R) =
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [connectedSumSeamGrid_OColumns_left_wrap G H hG hH r z hz hc hv,
    Finset.card_image_of_injective _ (seamORelocation_injective H hH)]

/-- Any lifted rectangle with a nonwrapping side has its original Laurent weight. -/
theorem connectedSumSeamGrid_rectangle_weight_left_nonwrap
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0)
    (hr : r.left.val < r.right.val ∨ r.bottom.val < r.top.val)
    (R : Type*) [CommSemiring R] :
    (LaurentPolynomial.T (((connectedSumSeamGrid G H hG hH).OColumns
      (seamLeftRectangle r z hz).toGridRectangle).card : ℤ) : LaurentPolynomial R) =
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  by_cases hc : r.left.val < r.right.val
  · exact connectedSumSeamGrid_rectangle_weight_left G H hG hH r z hz hc R
  · have hne : r.left.val ≠ r.right.val := fun h => r.left_ne_right (Fin.ext h)
    exact connectedSumSeamGrid_rectangle_weight_left_wrap G H hG hH r z hz
      (by omega) (hr.resolve_left hc) R

/-- A rectangle between two seam states with fixed second factor has first-block sides. -/
theorem seamRectangle_sides_in_left {x y : GridState (n + 1)}
    (z : GridState (m + 1)) (hz : z 0 = 0)
    (r : GridRectangleBetween (seamState x z) (seamState y z)) :
    (∃ a, r.left = seamLeft n m a) ∧ ∃ b, r.right = seamLeft n m b := by
  have outside (b : Fin m) : seamState y z (seamRight n m b.succ) =
      seamState x z (seamRight n m b.succ) := by
    have hb : z b.succ ≠ 0 := fun h =>
      Fin.succ_ne_zero b (z.toPerm.injective (h.trans hz.symm))
    rw [seamState_right_of_ne_zero _ _ _ hb, seamState_right_of_ne_zero _ _ _ hb]
  constructor
  · rcases seam_cases_succ r.left with h | ⟨b, hb⟩
    · exact h
    · have he : seamState x z r.left = seamState x z r.right := by
        rw [← r.map_left, hb, outside]
      exact False.elim (r.left_ne_right ((seamState x z).toPerm.injective he))
  · rcases seam_cases_succ r.right with h | ⟨b, hb⟩
    · exact h
    · have he : seamState x z r.right = seamState x z r.left := by
        rw [← r.map_right, hb, outside]
      exact False.elim (r.left_ne_right ((seamState x z).toPerm.injective he).symm)

/-- No additional rectangles occur between states with the same corner-fixing second factor. -/
theorem seamLeftRectangle_surjective {x y : GridState (n + 1)}
    (z : GridState (m + 1)) (hz : z 0 = 0) :
    Function.Surjective (fun r : GridRectangleBetween x y => seamLeftRectangle r z hz) := by
  intro r
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := seamRectangle_sides_in_left z hz r
  have hab : a ≠ b := fun h =>
    r.left_ne_right (ha.trans ((congrArg (seamLeft n m) h).trans hb.symm))
  let t : GridRectangleBetween x y := {
    left := a
    right := b
    left_ne_right := hab
    map_left := by
      apply seamLeft_injective (m := m)
      simpa only [ha, hb, seamState_left _ _ hz] using r.map_left
    map_right := by
      apply seamLeft_injective (m := m)
      simpa only [ha, hb, seamState_left _ _ hz] using r.map_right
    map_of_ne := by
      intro c hca hcb
      apply seamLeft_injective (m := m)
      have hc := r.map_of_ne (seamLeft n m c)
        (fun h => hca (seamLeft_injective (h.trans ha)))
        (fun h => hcb (seamLeft_injective (h.trans hb)))
      simpa only [seamState_left _ _ hz] using hc }
  exact ⟨t, GridRectangleBetween.ext ha.symm hb.symm⟩

theorem seamLeftRectangle_injective {x y : GridState (n + 1)}
    (z : GridState (m + 1)) (hz : z 0 = 0) :
    Function.Injective (fun r : GridRectangleBetween x y => seamLeftRectangle r z hz) := by
  intro r t h
  exact GridRectangleBetween.ext (seamLeft_injective (congrArg GridRectangleBetween.left h))
    (seamLeft_injective (congrArg GridRectangleBetween.right h))

/-- The empty seam rectangles are exactly the factor rectangles with a nonwrapping side. -/
theorem seam_emptyRectangles_eq_image (x y : GridState (n + 1))
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m) :
    emptyRectangles (seamState x z) (seamState y z) =
      ((emptyRectangles x y).filter
        (fun r => r.left.val < r.right.val ∨ r.bottom.val < r.top.val)).image
          (fun r => seamLeftRectangle r z hz) := by
  classical
  ext r
  obtain ⟨t, rfl⟩ := seamLeftRectangle_surjective z hz r
  rw [mem_emptyRectangles, seamLeftRectangle_isEmpty_iff_nonwrap t z hz hm]
  constructor
  · rintro ⟨he, hn⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨(mem_emptyRectangles t).mpr he, hn⟩, rfl⟩
  · rintro h
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp h
    have heq := seamLeftRectangle_injective z hz hut
    subst u
    exact ⟨(mem_emptyRectangles t).mp (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩

/-- Exact full Laurent differential coefficient in the fixed-second-factor sector. -/
theorem connectedSumSeamGrid_laurentCoefficient_left
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : GridState (n + 1)) (z : GridState (m + 1)) (hz : z 0 = 0)
    (R : Type*) [CommSemiring R] :
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R (seamState x z) (seamState y z) =
      ∑ r ∈ (emptyRectangles x y).filter
        (fun r => r.left.val < r.right.val ∨ r.bottom.val < r.top.val),
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst m
    apply H.disjoint 0
    apply Fin.ext
    have ho := (H.O 0).isLt
    have hx := (H.X 0).isLt
    omega
  rw [laurentCoefficient_eq, seam_emptyRectangles_eq_image x y z hz hm,
    Finset.sum_image (fun _ _ _ _ h => seamLeftRectangle_injective z hz h)]
  apply Finset.sum_congr rfl
  intro r hr
  exact connectedSumSeamGrid_rectangle_weight_left_nonwrap G H hG hH r z hz
    (Finset.mem_filter.mp hr).2 R

/-- The final square belongs to a nondegenerate half-open interval exactly when it wraps. -/
theorem seam_last_mem_cIco_iff (a b : Fin (n + 1)) (hab : a ≠ b) :
    Fin.last n ∈ Grid.cIco a b ↔ b.val < a.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  by_cases h : a.val < b.val
  · rw [Grid.mem_cIco_iff_of_left_lt_right h]
    simp only [Fin.val_last]
    omega
  · have h' : b.val < a.val := by omega
    rw [Grid.mem_cIco_iff_of_right_lt_left h']
    simp only [Fin.val_last]
    omega

/-- The shared X square is covered exactly by the rectangles wrapping in both directions. -/
theorem seam_last_corner_mem_iff {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) :
    (Fin.last n, Fin.last n) ∈ r.toGridRectangle.coveredSquares ↔
      r.right.val < r.left.val ∧ r.top.val < r.bottom.val := by
  rw [mem_toGridRectangle_coveredSquares]
  change (Fin.last n ∈ Grid.cIco r.left r.right ∧
    Fin.last n ∈ Grid.cIco r.bottom r.top) ↔ _
  rw [seam_last_mem_cIco_iff _ _ r.left_ne_right,
    seam_last_mem_cIco_iff _ _ r.bottom_ne_top]

/-- Exact avoidance criterion for the shared factor X square. -/
theorem seam_last_X_avoidance_iff (G : GridDiagram (n + 1))
    (hG : G.X (Fin.last n) = Fin.last n) {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) :
    (¬∃ a ∈ ({Fin.last n} : Finset (Fin (n + 1))),
      (a, G.X a) ∈ r.toGridRectangle.coveredSquares) ↔
        r.left.val < r.right.val ∨ r.bottom.val < r.top.val := by
  simp only [Finset.mem_singleton, exists_eq_left, hG, seam_last_corner_mem_iff]
  have hc : r.left.val ≠ r.right.val := fun h => r.left_ne_right (Fin.ext h)
  have hv : r.bottom.val ≠ r.top.val := fun h => r.bottom_ne_top (Fin.ext h)
  omega

/-- In the fixed-second-factor sector, the full seam coefficient is the factor coefficient
with only its final X square blocked. This does not assert that the sector is a subcomplex. -/
theorem connectedSumSeamGrid_laurentCoefficient_eq_cornerBlocked
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : GridState (n + 1)) (z : GridState (m + 1)) (hz : z 0 = 0)
    (R : Type*) [CommSemiring R] :
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R (seamState x z) (seamState y z) =
      laurentXBlockedDifferential G R {Fin.last n} (Finsupp.single x 1) y := by
  classical
  rw [connectedSumSeamGrid_laurentCoefficient_left G H hG hH x y z hz R,
    laurentXBlockedDifferential_apply_apply,
    Finsupp.sum_single_index (by simp only [zero_mul]), one_mul]
  apply Finset.sum_congr
  · apply Finset.filter_congr
    intro r _
    exact (seam_last_X_avoidance_iff G hG r).symm
  · intro r _
    rfl

/-- The exact missing coefficient is the differential counting the shared-X crossings. -/
theorem connectedSumSeamGrid_laurentCoefficient_add_cornerCrossing
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : GridState (n + 1)) (z : GridState (m + 1)) (hz : z 0 = 0)
    (R : Type*) [CommRing R] :
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R (seamState x z) (seamState y z) +
      laurentXCrossingDifferential G R {Fin.last n} (Finsupp.single x 1) y =
        laurentCoefficient G R x y := by
  rw [connectedSumSeamGrid_laurentCoefficient_eq_cornerBlocked G H hG hH x y z hz R]
  have he := congrArg (fun L : LaurentChain R (n + 1) →ₗ[LaurentPolynomial R]
      LaurentChain R (n + 1) => L (Finsupp.single x 1) y)
    (laurentXBlocked_add_crossing G R {Fin.last n})
  simpa only [LinearMap.add_apply, Finsupp.add_apply, laurentDifferential_single,
    laurentOnGenerator_apply] using he

/-- The first column strictly inside the second block. -/
def seamNextIndex (m : ℕ) (hm : 0 < m) : Fin (m + 1) := ⟨1, by omega⟩

@[simp] theorem seamNextIndex_val (hm : 0 < m) : (seamNextIndex m hm).val = 1 := rfl

theorem seamNextIndex_ne_zero (hm : 0 < m) : seamNextIndex m hm ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [seamNextIndex_val, Fin.val_zero] at this
  omega

theorem seamCorner_ne_next (hm : 0 < m) :
    seamLeft n m (Fin.last n) ≠ seamRight n m (seamNextIndex m hm) := by
  intro h
  exact seamNextIndex_ne_zero hm ((seamLeft_eq_seamRight_iff _ _).mp h).2

/-- Exchange the common column and its immediate successor. -/
def seamAdjacentState (x : GridState (n + 1)) (z : GridState (m + 1)) (hm : 0 < m) :
    GridState (n + m + 1) :=
  (seamState x z).swapColumns (seamLeft n m (Fin.last n))
    (seamRight n m (seamNextIndex m hm))

/-- The width-one rectangle from the exchanged state back to the fixed-second-factor sector. -/
def seamAdjacentRectangle (x : GridState (n + 1)) (z : GridState (m + 1)) (hm : 0 < m) :
    GridRectangleBetween (seamAdjacentState x z hm) (seamState x z) :=
  ofSwapColumns _ _ (seamLeft n m (Fin.last n)) (seamRight n m (seamNextIndex m hm))
    (seamCorner_ne_next hm) (GridState.swapColumns_swapColumns _ _ _).symm

@[simp] theorem seamAdjacentRectangle_left (x : GridState (n + 1))
    (z : GridState (m + 1)) (hm : 0 < m) :
    (seamAdjacentRectangle x z hm).left = seamLeft n m (Fin.last n) := by
  simp [seamAdjacentRectangle]

@[simp] theorem seamAdjacentRectangle_right (x : GridState (n + 1))
    (z : GridState (m + 1)) (hm : 0 < m) :
    (seamAdjacentRectangle x z hm).right = seamRight n m (seamNextIndex m hm) := by
  simp [seamAdjacentRectangle]

@[simp] theorem seamAdjacentRectangle_bottom (x : GridState (n + 1))
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m) :
    (seamAdjacentRectangle x z hm).bottom = seamRight n m (z (seamNextIndex m hm)) := by
  have hb : z (seamNextIndex m hm) ≠ 0 := fun h =>
    seamNextIndex_ne_zero hm (z.toPerm.injective (h.trans hz.symm))
  rw [bottom_def, seamAdjacentRectangle_left, seamAdjacentState,
    GridState.swapColumns_apply, Equiv.swap_apply_left, seamState_right_of_ne_zero _ _ _ hb]

@[simp] theorem seamAdjacentRectangle_top (x : GridState (n + 1))
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m) :
    (seamAdjacentRectangle x z hm).top = seamLeft n m (x (Fin.last n)) := by
  rw [top_def, seamAdjacentRectangle_right, seamAdjacentState,
    GridState.swapColumns_apply, Equiv.swap_apply_right, seamState_left _ _ hz]

/-- The exchanged state is outside the sector with the same fixed second factor. -/
theorem seamAdjacentState_ne_seamState (x y : GridState (n + 1))
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m) :
    seamAdjacentState x z hm ≠ seamState y z := by
  have hb : z (seamNextIndex m hm) ≠ 0 := fun h =>
    seamNextIndex_ne_zero hm (z.toPerm.injective (h.trans hz.symm))
  intro h
  have he := congrArg (fun w : GridState (n + m + 1) =>
    w (seamRight n m (seamNextIndex m hm))) h
  simp only [seamAdjacentState, GridState.swapColumns_apply, Equiv.swap_apply_right,
    seamState_left _ _ hz, seamState_right_of_ne_zero _ _ _ hb] at he
  exact hb ((seamLeft_eq_seamRight_iff _ _).mp he).2

/-- Its open column interval is empty, independently of the two factor states. -/
theorem seamAdjacentRectangle_isEmpty (x : GridState (n + 1))
    (z : GridState (m + 1)) (hm : 0 < m) : (seamAdjacentRectangle x z hm).IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo]
  intro c hc
  rw [seamAdjacentRectangle_left, seamAdjacentRectangle_right, Grid.mem_cIoo] at hc
  change _ ∧ (if n < n + 1 then n < c.val ∧ c.val < n + 1
    else n < c.val ∨ c.val < n + 1) at hc
  rw [if_pos (by omega)] at hc
  omega

/-- The return rectangle avoids the shared X square. -/
theorem seamAdjacentRectangle_avoids_corner (x : GridState (n + 1))
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m) :
    (seamLeft n m (Fin.last n), seamLeft n m (Fin.last n)) ∉
      (seamAdjacentRectangle x z hm).toGridRectangle.coveredSquares := by
  intro h
  have hr := ((mem_toGridRectangle_coveredSquares _).mp h).2
  change seamLeft n m (Fin.last n) ∈ Grid.cIco
    (seamAdjacentRectangle x z hm).bottom (seamAdjacentRectangle x z hm).top at hr
  rw [seamAdjacentRectangle_bottom _ _ hz, seamAdjacentRectangle_top _ _ hz] at hr
  have hb : z (seamNextIndex m hm) ≠ 0 := fun h =>
    seamNextIndex_ne_zero hm (z.toPerm.injective (h.trans hz.symm))
  have hbval : 0 < (z (seamNextIndex m hm)).val := by
    have hh : (z (seamNextIndex m hm)).val ≠ 0 := fun h => hb (Fin.ext h)
    omega
  have ha := (x (Fin.last n)).isLt
  rw [Grid.mem_cIco] at hr
  change _ ∧ (if n + (z (seamNextIndex m hm)).val < (x (Fin.last n)).val then
    n + (z (seamNextIndex m hm)).val ≤ n ∧ n < (x (Fin.last n)).val
    else n + (z (seamNextIndex m hm)).val ≤ n ∨ n < (x (Fin.last n)).val) at hr
  rw [if_neg (by omega)] at hr
  omega

/-- If the first state does not fix its corner, the other orientation contains a state point. -/
theorem seamAdjacentRectangle_swapSides_not_isEmpty (x : GridState (n + 1))
    (hx : x (Fin.last n) ≠ Fin.last n) (z : GridState (m + 1)) (hz : z 0 = 0)
    (hm : 0 < m) : ¬ (seamAdjacentRectangle x z hm).swapSides.IsEmpty := by
  let c := x.toPerm.symm (Fin.last n)
  have hxc : x c = Fin.last n := x.toPerm.apply_symm_apply _
  have hc : c ≠ Fin.last n := fun h => hx (h ▸ hxc)
  have hcval : c.val < n := by
    have hle := c.isLt
    have hne : c.val ≠ n := fun h => hc (Fin.ext h)
    omega
  have haval : (x (Fin.last n)).val < n := by
    have hle := (x (Fin.last n)).isLt
    have hne : (x (Fin.last n)).val ≠ n := fun h => hx (Fin.ext h)
    omega
  have hb : z (seamNextIndex m hm) ≠ 0 := fun h =>
    seamNextIndex_ne_zero hm (z.toPerm.injective (h.trans hz.symm))
  have hbval : 0 < (z (seamNextIndex m hm)).val := by
    have hh : (z (seamNextIndex m hm)).val ≠ 0 := fun h => hb (Fin.ext h)
    omega
  have hcol : seamLeft n m c ∈ Grid.cIoo (seamAdjacentRectangle x z hm).swapSides.left
      (seamAdjacentRectangle x z hm).swapSides.right := by
    rw [swapSides_left, swapSides_right, seamAdjacentRectangle_right,
      seamAdjacentRectangle_left, Grid.mem_cIoo]
    constructor
    · exact (seamCorner_ne_next hm).symm
    · change if n + 1 < n then n + 1 < c.val ∧ c.val < n
        else n + 1 < c.val ∨ c.val < n
      rw [if_neg (by omega)]
      exact Or.inr hcval
  have hpoint : seamAdjacentState x z hm (seamLeft n m c) = seamLeft n m (Fin.last n) := by
    have hcl : seamLeft n m c ≠ seamLeft n m (Fin.last n) :=
      fun h => hc (seamLeft_injective h)
    have hcr : seamLeft n m c ≠ seamRight n m (seamNextIndex m hm) :=
      fun h => seamNextIndex_ne_zero hm ((seamLeft_eq_seamRight_iff _ _).mp h).2
    rw [seamAdjacentState, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hcl hcr, seamState_left _ _ hz, hxc]
  have hrow : seamLeft n m (Fin.last n) ∈ Grid.cIoo
      (seamAdjacentRectangle x z hm).swapSides.bottom
        (seamAdjacentRectangle x z hm).swapSides.top := by
    rw [swapSides_bottom, swapSides_top, seamAdjacentRectangle_top _ _ hz,
      seamAdjacentRectangle_bottom _ _ hz, Grid.mem_cIoo]
    constructor
    · intro he
      have := congrArg Fin.val he
      simp only [seamLeft_val, seamRight_val] at this
      omega
    · change if (x (Fin.last n)).val < n + (z (seamNextIndex m hm)).val then
        (x (Fin.last n)).val < n ∧ n < n + (z (seamNextIndex m hm)).val
        else (x (Fin.last n)).val < n ∨ n < n + (z (seamNextIndex m hm)).val
      rw [if_pos (by omega)]
      exact ⟨haval, by omega⟩
  intro he
  have hf := ((isEmpty_iff_forall_notMem_cIoo _).mp he) (seamLeft n m c) hcol
  rw [hpoint] at hf
  exact hf hrow

/-- The return edge has exactly one empty rectangle. -/
theorem seamAdjacentRectangle_emptyRectangles (x : GridState (n + 1))
    (hx : x (Fin.last n) ≠ Fin.last n) (z : GridState (m + 1)) (hz : z 0 = 0)
    (hm : 0 < m) :
    emptyRectangles (seamAdjacentState x z hm) (seamState x z) =
      {seamAdjacentRectangle x z hm} := by
  classical
  ext r
  rw [mem_emptyRectangles, Finset.mem_singleton]
  constructor
  · intro he
    rcases (seamAdjacentRectangle x z hm).eq_or_eq_swapSides r with hr | hr
    · exact hr
    · subst r
      exact False.elim (seamAdjacentRectangle_swapSides_not_isEmpty x hx z hz hm he)
  · rintro rfl
    exact seamAdjacentRectangle_isEmpty x z hm

/-- The full differential coefficient of the return edge is an explicit Laurent monomial. -/
theorem connectedSumSeamGrid_adjacent_return_coefficient
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : GridState (n + 1)) (hx : x (Fin.last n) ≠ Fin.last n)
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m)
    (R : Type*) [CommSemiring R] :
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R
      (seamAdjacentState x z hm) (seamState x z) =
        LaurentPolynomial.T (((connectedSumSeamGrid G H hG hH).OColumns
          (seamAdjacentRectangle x z hm).toGridRectangle).card : ℤ) := by
  classical
  rw [laurentCoefficient_eq, seamAdjacentRectangle_emptyRectangles x hx z hz hm,
    Finset.sum_singleton]

/-- Blocking the shared X preserves this exact return coefficient. -/
theorem connectedSumSeamGrid_adjacent_return_blocked_coefficient
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : GridState (n + 1)) (hx : x (Fin.last n) ≠ Fin.last n)
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m)
    (R : Type*) [CommSemiring R] :
    laurentXBlockedDifferential (connectedSumSeamGrid G H hG hH) R
        {seamLeft n m (Fin.last n)} (Finsupp.single (seamAdjacentState x z hm) 1)
          (seamState x z) =
      LaurentPolynomial.T (((connectedSumSeamGrid G H hG hH).OColumns
        (seamAdjacentRectangle x z hm).toGridRectangle).card : ℤ) := by
  classical
  rw [laurentXBlockedDifferential_apply_apply,
    Finsupp.sum_single_index (by simp only [zero_mul]), one_mul,
    seamAdjacentRectangle_emptyRectangles x hx z hz hm]
  have havoid : ¬∃ a ∈ ({seamLeft n m (Fin.last n)} : Finset (Fin (n + m + 1))),
      (a, (connectedSumSeamGrid G H hG hH).X a) ∈
        (seamAdjacentRectangle x z hm).toGridRectangle.coveredSquares := by
    simp only [Finset.mem_singleton, exists_eq_left, connectedSumSeamGrid_X_corner]
    exact seamAdjacentRectangle_avoids_corner x z hz hm
  simp only [Finset.filter_singleton, if_pos havoid, Finset.sum_singleton]

/-- The concrete selected-X-blocked return coefficient is a unit. -/
theorem connectedSumSeamGrid_adjacent_return_isUnit
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : GridState (n + 1)) (hx : x (Fin.last n) ≠ Fin.last n)
    (z : GridState (m + 1)) (hz : z 0 = 0) (hm : 0 < m)
    (R : Type*) [CommSemiring R] :
    IsUnit (laurentXBlockedDifferential (connectedSumSeamGrid G H hG hH) R
      {seamLeft n m (Fin.last n)} (Finsupp.single (seamAdjacentState x z hm) 1)
        (seamState x z)) := by
  rw [connectedSumSeamGrid_adjacent_return_blocked_coefficient G H hG hH x hx z hz hm R]
  exact LaurentPolynomial.isUnit_T _

/-- A column exchange inside the second factor induces the same exchange in the seam grid. -/
theorem seamState_swapColumns_right (x : GridState (n + 1)) (z : GridState (m + 1))
    (a b : Fin (m + 1)) :
    (seamState x z).swapColumns (seamRight n m a) (seamRight n m b) =
      seamState x (z.swapColumns a b) := by
  have hswap (c : Fin (m + 1)) :
      Equiv.swap (seamRight n m a) (seamRight n m b) (seamRight n m c) =
        seamRight n m (Equiv.swap a b c) := by
    by_cases ha : c = a
    · subst c
      simp only [Equiv.swap_apply_left]
    · by_cases hb : c = b
      · subst c
        simp only [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha (seamRight_injective h))
          (fun h => hb (seamRight_injective h)), Equiv.swap_apply_of_ne_of_ne ha hb]
  have hright (c : Fin (m + 1)) :
      (seamState x z).swapColumns (seamRight n m a) (seamRight n m b) (seamRight n m c) =
        seamState x (z.swapColumns a b) (seamRight n m c) := by
    rw [GridState.swapColumns_apply, hswap]
    change seamExtendLeft x (seamExtendRight z (seamRight n m (Equiv.swap a b c))) =
      seamExtendLeft x (seamExtendRight (z.swapColumns a b) (seamRight n m c))
    rw [seamExtendRight_right, seamExtendRight_right, GridState.swapColumns_apply]
  apply GridState.ext
  intro c
  rcases seam_cases c with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · induction d using Fin.lastCases with
    | last => rw [seamLeft_last]; exact hright 0
    | cast d =>
      have ha : seamLeft n m d.castSucc ≠ seamRight n m a := fun h =>
        Fin.castSucc_ne_last d ((seamLeft_eq_seamRight_iff _ _).mp h).1
      have hb : seamLeft n m d.castSucc ≠ seamRight n m b := fun h =>
        Fin.castSucc_ne_last d ((seamLeft_eq_seamRight_iff _ _).mp h).1
      rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne ha hb,
        seamState_left_castSucc, seamState_left_castSucc]
  · exact hright d

/-- This return edge changes the second factor. Its source is still an embedded pair of states,
so the unit edge alone is not a matching of states complementary to the pair-state image. -/
theorem seamAdjacentState_eq_seamState_swap (x : GridState (n + 1))
    (z : GridState (m + 1)) (hm : 0 < m) :
    seamAdjacentState x z hm = seamState x (z.swapColumns 0 (seamNextIndex m hm)) := by
  rw [seamAdjacentState, seamLeft_last, seamState_swapColumns_right]

end OnLeConjecture.KnotFloer.GridFull
