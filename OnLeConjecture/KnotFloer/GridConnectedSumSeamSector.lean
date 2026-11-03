/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamWrap
public import Mathlib.Logic.Equiv.Fintype

/-!
# The image of all pairs of seam states

The image of `(x,z) ↦ seamState x z` consists exactly of permutations whose
first n columns have rows at most n. No condition on z(0) is imposed.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween

variable {n m : ℕ}

/-- A permutation on n+1 points is determined on its first n points. -/
theorem seam_gridState_eq_of_castSucc (x y : GridState (n + 1))
    (h : ∀ c : Fin n, x c.castSucc = y c.castSucc) : x = y := by
  apply GridState.ext
  intro a
  induction a using Fin.lastCases with
  | cast c => exact h c
  | last =>
    let c := y.toPerm.symm (x (Fin.last n))
    have hc : y c = x (Fin.last n) := y.toPerm.apply_symm_apply _
    by_cases hl : c = Fin.last n
    · exact (hl ▸ hc).symm
    · obtain ⟨b, hb⟩ := Fin.eq_castSucc_of_ne_last hl
      have he : x b.castSucc = x (Fin.last n) := (h b).trans (hb.symm ▸ hc)
      exact False.elim (Fin.castSucc_ne_last b (x.toPerm.injective he))

/-- Gluing all pairs of factor states is injective, even when the second corner moves. -/
theorem seamState_injective :
    Function.Injective (fun p : GridState (n + 1) × GridState (m + 1) => seamState p.1 p.2) := by
  rintro ⟨x, z⟩ ⟨y, w⟩ h
  have hxy : x = y := seam_gridState_eq_of_castSucc x y fun c => by
    have hc := congrArg (fun v : GridState (n + m + 1) => v (seamLeft n m c.castSucc)) h
    rw [seamState_left_castSucc, seamState_left_castSucc] at hc
    exact seamLeft_injective hc
  subst y
  have hzw : z = w := by
    apply GridState.ext
    intro c
    have hc := congrArg (fun v : GridState (n + m + 1) => v (seamRight n m c)) h
    change seamExtendLeft x (seamExtendRight z (seamRight n m c)) =
      seamExtendLeft x (seamExtendRight w (seamRight n m c)) at hc
    rw [seamExtendRight_right, seamExtendRight_right] at hc
    exact seamRight_injective ((seamExtendLeft x).toPerm.injective hc)
  subst w
  rfl

/-- The first n columns lie in the first n+1 rows. -/
def SeamPairSector (w : GridState (n + m + 1)) : Prop :=
  ∀ c : Fin n, (w (seamLeft n m c.castSucc)).val ≤ n

instance (w : GridState (n + m + 1)) : Decidable (SeamPairSector (n := n) (m := m) w) :=
  inferInstanceAs (Decidable (∀ c : Fin n, (w (seamLeft n m c.castSucc)).val ≤ n))

theorem seamState_mem_pairSector (x : GridState (n + 1)) (z : GridState (m + 1)) :
    SeamPairSector (seamState x z) := by
  intro c
  rw [seamState_left_castSucc, seamLeft_val]
  exact Nat.le_of_lt_succ (x c.castSucc).isLt

/-- Every permutation satisfying the row condition comes from a pair of factor states. -/
theorem exists_seamState_of_pairSector (w : GridState (n + m + 1))
    (hw : SeamPairSector (n := n) (m := m) w) :
    ∃ x : GridState (n + 1), ∃ z : GridState (m + 1), seamState x z = w := by
  let f : Fin n → Fin (n + 1) := fun c =>
    ⟨(w (seamLeft n m c.castSucc)).val, Nat.lt_succ_of_le (hw c)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he : w (seamLeft n m a.castSucc) = w (seamLeft n m b.castSucc) :=
      Fin.ext (congrArg (fun a : Fin (n + 1) => a.val) hab)
    exact Fin.castSucc_injective n (seamLeft_injective (w.toPerm.injective he))
  obtain ⟨xp, hxp⟩ := Equiv.Perm.exists_extending_pair Fin.castSucc f
    (Fin.castSucc_injective n) hf
  let x : GridState (n + 1) := ⟨xp⟩
  have hx (c : Fin n) : seamLeft n m (x c.castSucc) = w (seamLeft n m c.castSucc) := by
    apply Fin.ext
    exact congrArg (fun a : Fin (n + 1) => a.val) (hxp c)
  let p : Equiv.Perm (Fin (n + m + 1)) :=
    w.toPerm.trans (seamExtendLeft (m := m) x).toPerm.symm
  have hp (c : Fin n) : p (seamLeft n m c.castSucc) = seamLeft n m c.castSucc := by
    change (seamExtendLeft x).toPerm.symm (w (seamLeft n m c.castSucc)) = _
    rw [← hx c, ← seamExtendLeft_left]
    exact (seamExtendLeft x).toPerm.symm_apply_apply _
  have hright (c : Fin (m + 1)) : n ≤ (p (seamRight n m c)).val := by
    by_contra h
    let d : Fin n := ⟨(p (seamRight n m c)).val, by omega⟩
    have he : p (seamRight n m c) = seamLeft n m d.castSucc := Fin.ext rfl
    have hd : seamRight n m c = seamLeft n m d.castSucc :=
      p.injective (he.trans (hp d).symm)
    exact Fin.castSucc_ne_last d ((seamLeft_eq_seamRight_iff _ _).mp hd.symm).1
  let zf : Fin (m + 1) → Fin (m + 1) := fun c =>
    ⟨(p (seamRight n m c)).val - n, by
      have hlt := (p (seamRight n m c)).isLt
      have hle := hright c
      omega⟩
  have hz (c : Fin (m + 1)) : seamRight n m (zf c) = p (seamRight n m c) := by
    apply Fin.ext
    change n + ((p (seamRight n m c)).val - n) = _
    have := hright c
    omega
  have hzf : Function.Injective zf := by
    intro a b hab
    apply seamRight_injective
    apply p.injective
    exact (hz a).symm.trans ((congrArg (seamRight n m) hab).trans (hz b))
  let z : GridState (m + 1) := ⟨Equiv.ofBijective zf
    ⟨hzf, Finite.surjective_of_injective hzf⟩⟩
  refine ⟨x, z, ?_⟩
  apply GridState.ext
  have hr (c : Fin (m + 1)) : seamState x z (seamRight n m c) = w (seamRight n m c) := by
    change seamExtendLeft x (seamExtendRight z (seamRight n m c)) = _
    rw [seamExtendRight_right]
    change seamExtendLeft x (seamRight n m (zf c)) = _
    rw [hz]
    exact (seamExtendLeft x).toPerm.apply_symm_apply _
  intro c
  rcases seam_cases c with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · induction a using Fin.lastCases with
    | last => rw [seamLeft_last]; exact hr 0
    | cast a => rw [seamState_left_castSucc]; exact hx a
  · exact hr a

/-- Exact image characterization for all factor pairs. -/
theorem seamPairSector_iff_exists (w : GridState (n + m + 1)) :
    SeamPairSector (n := n) (m := m) w ↔
      ∃ x : GridState (n + 1), ∃ z : GridState (m + 1), seamState x z = w := by
  constructor
  · exact exists_seamState_of_pairSector w
  · rintro ⟨x, z, rfl⟩
    exact seamState_mem_pairSector x z

/-- The complement consists exactly of states with a first-block column above the first block. -/
theorem not_seamPairSector_iff (w : GridState (n + m + 1)) :
    ¬ SeamPairSector (n := n) (m := m) w ↔
      ∃ c : Fin n, n < (w (seamLeft n m c.castSucc)).val := by
  simp only [SeamPairSector, not_forall, Nat.not_le]

/-- The identity permutation, used to exhibit an outgoing differential term. -/
def seamIdentityState (k : ℕ) : GridState k := ⟨Equiv.refl _⟩

@[simp] theorem seamIdentityState_apply {k : ℕ} (c : Fin k) : seamIdentityState k c = c := rfl

/-- The identity state is the image of the two identity factor states. -/
theorem seamState_identity :
    seamState (seamIdentityState (n + 1)) (seamIdentityState (m + 1)) =
      seamIdentityState (n + m + 1) := by
  apply GridState.ext
  intro c
  rcases seam_cases c with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [seamState_left _ _ rfl]
    rfl
  · by_cases ha : a = 0
    · subst a
      rw [seamState_right_of_zero _ _ _ rfl, seamIdentityState_apply, seamLeft_last]
      rfl
    · rw [seamState_right_of_ne_zero _ _ _ ha]
      rfl

/-- Exchanging the two columns adjacent across the global cut leaves the pair-state image. -/
def seamEscapeState (n m : ℕ) : GridState (n + m + 1) :=
  (seamIdentityState (n + m + 1)).swapColumns (Fin.last (n + m)) 0

theorem seamEscapeState_not_pairSector (hn : 0 < n) (hm : 0 < m) :
    ¬ SeamPairSector (n := n) (m := m) (seamEscapeState n m) := by
  intro hs
  have hc := hs (⟨0, hn⟩ : Fin n)
  have he : seamLeft n m (⟨0, hn⟩ : Fin n).castSucc = 0 := Fin.ext rfl
  rw [he, seamEscapeState, GridState.swapColumns_apply, Equiv.swap_apply_right,
    seamIdentityState_apply, Fin.val_last] at hc
  omega

/-- The empty wrapping rectangle supported on the final square of the seam grid. -/
def seamEscapeRectangle (hn : 0 < n) (hm : 0 < m) :
    GridRectangleBetween (seamIdentityState (n + m + 1)) (seamEscapeState n m) :=
  ofSwapColumns _ _ (Fin.last (n + m)) 0 (by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at this
    omega) rfl

@[simp] theorem seamEscapeRectangle_left (hn : 0 < n) (hm : 0 < m) :
    (seamEscapeRectangle hn hm).left = Fin.last (n + m) := by
  unfold seamEscapeRectangle
  exact ofSwapColumns_left _ _ _ _ _ _

@[simp] theorem seamEscapeRectangle_right (hn : 0 < n) (hm : 0 < m) :
    (seamEscapeRectangle hn hm).right = 0 := by
  unfold seamEscapeRectangle
  exact ofSwapColumns_right _ _ _ _ _ _

@[simp] theorem seamEscapeRectangle_bottom (hn : 0 < n) (hm : 0 < m) :
    (seamEscapeRectangle hn hm).bottom = Fin.last (n + m) := by
  rw [bottom_def, seamEscapeRectangle_left, seamIdentityState_apply]

@[simp] theorem seamEscapeRectangle_top (hn : 0 < n) (hm : 0 < m) :
    (seamEscapeRectangle hn hm).top = 0 := by
  rw [top_def, seamEscapeRectangle_right, seamIdentityState_apply]

theorem seamEscapeRectangle_isEmpty (hn : 0 < n) (hm : 0 < m) :
    (seamEscapeRectangle hn hm).IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo]
  intro c hc
  rw [seamEscapeRectangle_left, seamEscapeRectangle_right, Grid.mem_cIoo] at hc
  change _ ∧ (if n + m < 0 then n + m < c.val ∧ c.val < 0
    else n + m < c.val ∨ c.val < 0) at hc
  rw [if_neg (by omega)] at hc
  have := c.isLt
  omega

/-- The opposite rectangle contains the identity point at the shared corner. -/
theorem seamEscapeRectangle_swap_not_isEmpty (hn : 0 < n) (hm : 0 < m) :
    ¬ (seamEscapeRectangle hn hm).swapSides.IsEmpty := by
  have hc : seamLeft n m (Fin.last n) ∈ Grid.cIoo
      (seamEscapeRectangle hn hm).swapSides.left (seamEscapeRectangle hn hm).swapSides.right := by
    rw [swapSides_left, swapSides_right, seamEscapeRectangle_left,
      seamEscapeRectangle_right, Grid.mem_cIoo]
    constructor
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    · change if 0 < n + m then 0 < n ∧ n < n + m else 0 < n ∨ n < n + m
      rw [if_pos (by omega)]
      exact ⟨hn, by omega⟩
  have hr : seamLeft n m (Fin.last n) ∈ Grid.cIoo
      (seamEscapeRectangle hn hm).swapSides.bottom (seamEscapeRectangle hn hm).swapSides.top := by
    simpa only [swapSides_bottom, swapSides_top, seamEscapeRectangle_bottom,
      seamEscapeRectangle_top, swapSides_left, swapSides_right,
      seamEscapeRectangle_left, seamEscapeRectangle_right] using hc
  intro he
  exact ((isEmpty_iff_forall_notMem_cIoo _).mp he) (seamLeft n m (Fin.last n)) hc hr

theorem seamEscapeRectangle_emptyRectangles (hn : 0 < n) (hm : 0 < m) :
    emptyRectangles (seamIdentityState (n + m + 1)) (seamEscapeState n m) =
      {seamEscapeRectangle hn hm} := by
  classical
  ext r
  rcases (seamEscapeRectangle hn hm).eq_or_eq_swapSides r with rfl | rfl <;>
    simp [seamEscapeRectangle_isEmpty, seamEscapeRectangle_swap_not_isEmpty,
      swapSides_ne_self]

/-- The final square is disjoint from the shared X column. -/
theorem seamEscapeRectangle_avoids_sharedX
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (hn : 0 < n) (hm : 0 < m) :
    ¬∃ a ∈ ({seamLeft n m (Fin.last n)} : Finset (Fin (n + m + 1))),
      (a, (connectedSumSeamGrid G H hG hH).X a) ∈
        (seamEscapeRectangle hn hm).toGridRectangle.coveredSquares := by
  simp only [Finset.mem_singleton, exists_eq_left]
  intro h
  have hc := ((mem_toGridRectangle_coveredSquares _).mp h).1
  rw [seamEscapeRectangle_left, seamEscapeRectangle_right, Grid.mem_cIco] at hc
  change _ ∧ (if n + m < 0 then n + m ≤ n ∧ n < 0 else n + m ≤ n ∨ n < 0) at hc
  rw [if_neg (by omega)] at hc
  omega

/-- The selected-X-blocked differential has a monomial-unit coefficient out of the pair image. -/
theorem connectedSumSeamGrid_escape_blocked_coefficient
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (hn : 0 < n) (hm : 0 < m) (R : Type*) [CommSemiring R] :
    laurentXBlockedDifferential (connectedSumSeamGrid G H hG hH) R
      {seamLeft n m (Fin.last n)} (Finsupp.single (seamIdentityState (n + m + 1)) 1)
        (seamEscapeState n m) =
      LaurentPolynomial.T (((connectedSumSeamGrid G H hG hH).OColumns
        (seamEscapeRectangle hn hm).toGridRectangle).card : ℤ) := by
  classical
  rw [laurentXBlockedDifferential_apply_apply,
    Finsupp.sum_single_index (by simp only [zero_mul]), one_mul,
    seamEscapeRectangle_emptyRectangles hn hm]
  simp only [Finset.filter_singleton,
    if_pos (seamEscapeRectangle_avoids_sharedX G H hG hH hn hm), Finset.sum_singleton]

theorem connectedSumSeamGrid_escape_blocked_isUnit
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (hn : 0 < n) (hm : 0 < m) (R : Type*) [CommSemiring R] :
    IsUnit (laurentXBlockedDifferential (connectedSumSeamGrid G H hG hH) R
      {seamLeft n m (Fin.last n)} (Finsupp.single (seamIdentityState (n + m + 1)) 1)
        (seamEscapeState n m)) := by
  rw [connectedSumSeamGrid_escape_blocked_coefficient G H hG hH hn hm R]
  exact LaurentPolynomial.isUnit_T _

/-- The pair-state image fails even the necessary entrywise condition for an invariant submodule. -/
theorem connectedSumSeamGrid_pairSector_not_invariant
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (hn : 0 < n) (hm : 0 < m) (R : Type*) [CommSemiring R] [Nontrivial R] :
    ¬ (∀ (x z : GridState (n + m + 1)), SeamPairSector (n := n) (m := m) x →
      ¬ SeamPairSector (n := n) (m := m) z →
      laurentXBlockedDifferential (connectedSumSeamGrid G H hG hH) R
        {seamLeft n m (Fin.last n)} (Finsupp.single x 1) z = 0) := by
  intro h
  have hi : SeamPairSector (n := n) (m := m) (seamIdentityState (n + m + 1)) := by
    rw [← seamState_identity]
    exact seamState_mem_pairSector _ _
  exact (connectedSumSeamGrid_escape_blocked_isUnit G H hG hH hn hm R).ne_zero
    (h _ _ hi (seamEscapeState_not_pairSector hn hm))

end OnLeConjecture.KnotFloer.GridFull
