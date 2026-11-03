/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyRootFamily
public import OnLeConjecture.Analytic.BraidMonodromyGrid

/-!
# The cut system of a grid for a root family

This module applies the grid factorization of `BraidMonodromyGrid.lean` to a root family
(`BraidMonodromyRootFamily.lean`) over a rectangle of the base. It realizes the cut system of the
subsection "Global factorization, exponent count, and transitivity" of Section 3 of the written
proof of Statement E (`statement-E-complete-proof.tex`) by the grid paths of a rectangular grid.

* `segmentPath p q`, `polygonPath w`: the segment from `p` to `q` on `[0, 1]`, and the polygon
  through the vertices `w 0, w 1, …`, whose `i`-th side is traversed during `[i, i + 1]`.
* `segWord Z S p q`: a root path word of the segment, and `polyWord Z S w m`, the concatenation of
  the words of the first `m` sides of a polygon.
* `isPathWord_polygon`: every labelling of the family along a polygon in `U` has the polygon word
  as path word. `segWord_swap` (reversal) and `segWord_subdivide` (subdivision of a segment) relate
  the segment words.
* For a grid with vertical lines `xs 0 < ⋯ < xs n` and horizontal lines `ys 0 < ⋯ < ys n`
  (`IsRootGrid`), the edge words `gridH`, `gridV` satisfy the cell relation on every unmarked cell
  (`IsRootGrid.cellRelation`, by the square relation of root families). The word of the boundary
  of the rectangle is the grid boundary word (`IsRootGrid.polyWord_outerLoop`), the word of the
  boundary of a cell is its cell loop (`IsRootGrid.polyWord_cellLoop`), and the word of the based
  loop of a cell, up the left column, along its row, around the cell and back, is the conjugated
  cell loop `γ_{ab} ℓ_{ab} γ_{ab}⁻¹` (`IsRootGrid.polyWord_basedLoop`).
* `IsRootGrid.outer_equiv_markedProduct`: the word of the boundary of the rectangle is the
  ordered product of the conjugated loops of the marked cells.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

variable {S : ℕ} {Z : ℂ → Set ℂ} {U : Set ℂ}

/-! ### Increasing finite sequences -/

theorem le_of_lt_succ_of_le {f : ℕ → ℝ} {n : ℕ} (hf : ∀ a < n, f a < f (a + 1)) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ n) : f a ≤ f b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (ih (by omega) (by omega)).trans (hf b (by omega)).le

theorem lt_of_lt_succ_of_lt {f : ℕ → ℝ} {n : ℕ} (hf : ∀ a < n, f a < f (a + 1)) {a b : ℕ}
    (hab : a < b) (hb : b ≤ n) : f a < f b :=
  (hf a (by omega)).trans_le (le_of_lt_succ_of_le hf (by omega) hb)

/-! ### Segments and polygons -/

/-- The segment from `p` to `q`, parametrized by `[0, 1]`. -/
def segmentPath (p q : ℂ) (t : ℝ) : ℂ := p + (t : ℂ) * (q - p)

theorem continuous_segmentPath (p q : ℂ) : Continuous (segmentPath p q) := by
  unfold segmentPath; fun_prop

@[simp] theorem segmentPath_zero (p q : ℂ) : segmentPath p q 0 = p := by simp [segmentPath]

@[simp] theorem segmentPath_one (p q : ℂ) : segmentPath p q 1 = q := by simp [segmentPath]

theorem segmentPath_symm (p q : ℂ) (t : ℝ) : segmentPath q p t = segmentPath p q (0 + 1 - t) := by
  simp only [segmentPath]; push_cast; ring

open Classical in
/-- A root path word of the segment from `p` to `q`, and `[]` if there is none. -/
def segWord (Z : ℂ → Set ℂ) (S : ℕ) (p q : ℂ) : SignedAdjacentWord S :=
  if h : ∃ W : SignedAdjacentWord S, IsRootPathWord Z (segmentPath p q) 0 1 W then h.choose
  else []

theorem IsRootFamily.isRootPathWord_segWord (hZ : IsRootFamily Z S U) {p q : ℂ}
    (hpq : MapsTo (segmentPath p q) (Icc 0 1) U) :
    IsRootPathWord Z (segmentPath p q) 0 1 (segWord Z S p q) := by
  have h : ∃ W : SignedAdjacentWord S, IsRootPathWord Z (segmentPath p q) 0 1 W :=
    hZ.exists_isRootPathWord zero_lt_one (continuous_segmentPath p q).continuousOn hpq
  rw [segWord, dif_pos h]
  exact h.choose_spec

theorem mapsTo_segmentPath_symm {p q : ℂ} (hpq : MapsTo (segmentPath p q) (Icc 0 1) U) :
    MapsTo (segmentPath q p) (Icc 0 1) U := fun t ht => by
  rw [segmentPath_symm]
  exact hpq ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- **Reversal of a segment** inverts its word. -/
theorem IsRootFamily.segWord_swap (hZ : IsRootFamily Z S U) {p q : ℂ}
    (hpq : MapsTo (segmentPath p q) (Icc 0 1) U) :
    SignedBraidEquiv (segWord Z S q p) (inv (segWord Z S p q)) := by
  have h1 := (hZ.isRootPathWord_segWord hpq).reverse.of_eqOn
    (γ' := segmentPath q p) fun t _ => (segmentPath_symm p q t).symm
  exact (hZ.isRootPathWord_segWord (mapsTo_segmentPath_symm hpq)).unique zero_lt_one h1

/-- The polygon through the vertices `w 0, w 1, …`: its `i`-th side, from `w i` to `w (i + 1)`,
is traversed during `[i, i + 1]`. -/
def polygonPath (w : ℕ → ℂ) (t : ℝ) : ℂ :=
  segmentPath (w ⌊t⌋₊) (w (⌊t⌋₊ + 1)) (t - ⌊t⌋₊)

theorem polygonPath_eq (w : ℕ → ℂ) (i : ℕ) {t : ℝ} (ht : t ∈ Icc (i : ℝ) (i + 1)) :
    polygonPath w t = segmentPath (w i) (w (i + 1)) (t - i) := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · have hf : ⌊t⌋₊ = i := (Nat.floor_eq_iff ((Nat.cast_nonneg i).trans ht.1)).mpr ⟨ht.1, hlt⟩
    rw [polygonPath, hf]
  · have hf : ⌊t⌋₊ = i + 1 := by
      rw [heq]; exact_mod_cast Nat.floor_natCast (R := ℝ) (i + 1)
    rw [polygonPath, hf, heq]
    simp

/-- The polygon word: the concatenation of the words of the first `m` sides. -/
def polyWord (Z : ℂ → Set ℂ) (S : ℕ) (w : ℕ → ℂ) (m : ℕ) : SignedAdjacentWord S :=
  (List.range m).flatMap fun i => segWord Z S (w i) (w (i + 1))

theorem polyWord_succ (w : ℕ → ℂ) (m : ℕ) :
    polyWord Z S w (m + 1) = polyWord Z S w m ++ segWord Z S (w m) (w (m + 1)) := by
  simp [polyWord, List.range_succ]

theorem polyWord_add (w : ℕ → ℂ) (m₁ m₂ : ℕ) :
    polyWord Z S w (m₁ + m₂) = polyWord Z S w m₁ ++ polyWord Z S (fun i => w (m₁ + i)) m₂ := by
  simp only [polyWord, List.range_add, List.flatMap_append, List.flatMap_map, add_assoc]

theorem polyWord_congr {w w' : ℕ → ℂ} {m : ℕ} (h : ∀ i ≤ m, w i = w' i) :
    polyWord Z S w m = polyWord Z S w' m := by
  refine List.flatMap_congr fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [h i hi'.le, h (i + 1) hi']

/-- The polygon is continuous on `[0, m]`. -/
theorem continuousOn_polygonPath (w : ℕ → ℂ) (m : ℕ) :
    ContinuousOn (polygonPath w) (Icc 0 m) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, Icc_self]
    exact continuousOn_singleton _ _
  | succ m ih =>
    have hseg : ContinuousOn (polygonPath w) (Icc (m : ℝ) (m + 1)) :=
      ((continuous_segmentPath (w m) (w (m + 1))).comp (continuous_sub_right (m : ℝ))).continuousOn
        |>.congr fun t ht => polygonPath_eq w m ht
    have hunion : Icc (0 : ℝ) ((m + 1 : ℕ) : ℝ) = Icc 0 (m : ℝ) ∪ Icc (m : ℝ) (m + 1) := by
      push_cast
      exact (Icc_union_Icc_eq_Icc (Nat.cast_nonneg m) (by linarith)).symm
    rw [hunion]
    exact ih.union_of_isClosed hseg isClosed_Icc isClosed_Icc

/-- A polygon whose first `m ≥ 1` sides lie in `U` maps `[0, m]` into `U`. -/
theorem mapsTo_polygonPath {w : ℕ → ℂ} {m : ℕ} (hm : 0 < m)
    (hseg : ∀ i < m, MapsTo (segmentPath (w i) (w (i + 1))) (Icc 0 1) U) :
    MapsTo (polygonPath w) (Icc 0 m) U := by
  intro t ht
  set i := min ⌊t⌋₊ (m - 1) with hi
  have him : i ≤ m - 1 := min_le_right _ _
  have hti : t ∈ Icc (i : ℝ) (i + 1) := by
    have h0 : 0 ≤ t := ht.1
    by_cases hfl : ⌊t⌋₊ ≤ m - 1
    · rw [hi, min_eq_left hfl]
      exact ⟨Nat.floor_le h0, (Nat.lt_floor_add_one t).le⟩
    · push Not at hfl
      rw [hi, min_eq_right hfl.le]
      have hm1 : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      refine ⟨?_, by rw [hm1]; exact ht.2⟩
      have := Nat.floor_le h0
      have : ((m - 1 : ℕ) : ℝ) + 1 ≤ ⌊t⌋₊ := by exact_mod_cast hfl
      linarith
  rw [polygonPath_eq w i hti]
  exact hseg i (by omega) ⟨by linarith [hti.1], by linarith [hti.2]⟩

/-- **The word of a polygon.** Every labelling of the family along a polygon whose first `m ≥ 1`
sides lie in `U` has the polygon word as path word on `[0, m]`. -/
theorem IsRootFamily.isPathWord_polygon (hZ : IsRootFamily Z S U) {w : ℕ → ℂ} :
    ∀ {m : ℕ}, 0 < m → (∀ i < m, MapsTo (segmentPath (w i) (w (i + 1))) (Icc 0 1) U) →
      ∀ {K : Fin S → ℝ → ℂ}, IsRootLabellingOn Z (polygonPath w) (Icc 0 m) K →
        IsPathWord K 0 m (polyWord Z S w m) := by
  -- The root path word of the `i`-th side.
  have hside : ∀ i : ℕ, MapsTo (segmentPath (w i) (w (i + 1))) (Icc 0 1) U →
      IsRootPathWord Z (polygonPath w) i (i + 1) (segWord Z S (w i) (w (i + 1))) := by
    intro i hi
    have h1 := hZ.isRootPathWord_segWord hi
    have h2 : IsRootPathWord Z (fun t => segmentPath (w i) (w (i + 1)) (t - i)) i (i + 1)
        (segWord Z S (w i) (w (i + 1))) := by
      refine IsRootPathWord.comp_affine (φ := fun t => t - i) (α := 1) (β := -i) one_pos
        (fun t => by ring) ?_
      simpa using h1
    exact h2.of_eqOn fun t ht => (polygonPath_eq w i ht).symm
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    intro hseg K hK
    rw [Nat.cast_succ] at hK ⊢
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      have := (hside 0 (hseg 0 (by omega))).isPathWord (by simpa using hK)
      simpa [polyWord] using this
    · have h1 := ih hpos (fun i hi => hseg i (by omega))
        (hK.mono (Icc_subset_Icc le_rfl (by linarith)))
      have h2 := (hside m (hseg m (by omega))).isPathWord
        (hK.mono (Icc_subset_Icc (Nat.cast_nonneg m) le_rfl))
      rw [polyWord_succ]
      exact h1.append (by exact_mod_cast hpos) (by linarith) hK.continuousOn hK.injective
        (by simpa using h2)

/-- Labels continue along every polygon in `U`. -/
theorem IsRootFamily.exists_polygon_labelling (hZ : IsRootFamily Z S U) {w : ℕ → ℂ} {m : ℕ}
    (hm : 0 < m) (hseg : ∀ i < m, MapsTo (segmentPath (w i) (w (i + 1))) (Icc 0 1) U) :
    ∃ K : Fin S → ℝ → ℂ, IsRootLabellingOn Z (polygonPath w) (Icc 0 m) K :=
  hZ.exists_path_labelling (by exact_mod_cast hm) (continuousOn_polygonPath w m)
    (mapsTo_polygonPath hm hseg)

/-- Traversing a polygon backwards inverts its word. -/
theorem IsRootFamily.polyWord_reverse (hZ : IsRootFamily Z S U) {w : ℕ → ℂ} :
    ∀ {m : ℕ}, (∀ i < m, MapsTo (segmentPath (w i) (w (i + 1))) (Icc 0 1) U) →
      SignedBraidEquiv (polyWord Z S (fun i => w (m - i)) m) (inv (polyWord Z S w m))
  | 0, _ => by simpa [polyWord] using SignedBraidEquiv.refl ([] : SignedAdjacentWord S)
  | m + 1, hseg => by
    have ih := hZ.polyWord_reverse (w := w) (m := m) fun i hi => hseg i (by omega)
    have hsplit := polyWord_add (Z := Z) (S := S) (fun i => w (m + 1 - i)) 1 m
    rw [show 1 + m = m + 1 by omega] at hsplit
    rw [hsplit, polyWord_succ w m, inv_append]
    have e1 : polyWord Z S (fun i => w (m + 1 - i)) 1 = segWord Z S (w (m + 1)) (w m) := by
      simp [polyWord]
    have e2 : polyWord Z S (fun i => w (m + 1 - (1 + i))) m = polyWord Z S (fun i => w (m - i)) m :=
      polyWord_congr fun i _ => by rw [show m + 1 - (1 + i) = m - i by omega]
    rw [e1, e2]
    exact (hZ.segWord_swap (hseg m (by omega))).append ih

/-- **Subdivision of a segment.** For `0 = s 0 < s 1 < ⋯ < s m = 1`, the word of the segment from
`p` to `q` is the concatenation of the words of the subsegments between the points
`segmentPath p q (s i)`. -/
theorem IsRootFamily.segWord_subdivide (hZ : IsRootFamily Z S U) {p q : ℂ}
    (hpq : MapsTo (segmentPath p q) (Icc 0 1) U) {s : ℕ → ℝ} {m : ℕ} (hm : 0 < m)
    (hs0 : s 0 = 0) (hsm : s m = 1) (hmono : ∀ i < m, s i < s (i + 1)) :
    SignedBraidEquiv (segWord Z S p q)
      (polyWord Z S (fun i => segmentPath p q (s i)) m) := by
  have hle : ∀ i ≤ m, s i ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨hs0 ▸ le_of_lt_succ_of_le hmono (Nat.zero_le i) hi, hsm ▸ le_of_lt_succ_of_le hmono hi le_rfl⟩
  obtain ⟨K, hK⟩ := hZ.exists_path_labelling zero_lt_one (continuous_segmentPath p q).continuousOn
    hpq
  -- The piece over `[s i, s (i + 1)]`.
  have hpiece : ∀ i < m, IsRootPathWord Z (segmentPath p q) (s i) (s (i + 1))
      (segWord Z S (segmentPath p q (s i)) (segmentPath p q (s (i + 1)))) := by
    intro i hi
    have hsi := hle i hi.le
    have hsi1 := hle (i + 1) hi
    have hd : 0 < s (i + 1) - s i := sub_pos.mpr (hmono i hi)
    have hsub : MapsTo (segmentPath (segmentPath p q (s i)) (segmentPath p q (s (i + 1))))
        (Icc 0 1) U := by
      intro t ht
      have : segmentPath (segmentPath p q (s i)) (segmentPath p q (s (i + 1))) t =
          segmentPath p q (s i + t * (s (i + 1) - s i)) := by
        simp only [segmentPath]; push_cast; ring
      rw [this]
      exact hpq ⟨by nlinarith [ht.1, hsi.1], by nlinarith [ht.2, hsi1.2]⟩
    have h1 := hZ.isRootPathWord_segWord hsub
    have h2 := IsRootPathWord.comp_affine (u := s i) (v := s (i + 1))
      (φ := fun t => (t - s i) / (s (i + 1) - s i)) (α := 1 / (s (i + 1) - s i))
      (β := -s i / (s (i + 1) - s i)) (by positivity) (fun t => by field_simp; ring)
      (by simpa [div_self hd.ne'] using h1)
    refine h2.of_eqOn fun t _ => ?_
    simp only [segmentPath]
    have hd' : ((s (i + 1) : ℂ) - s i) ≠ 0 := by
      rw [← Complex.ofReal_sub]; exact_mod_cast hd.ne'
    push_cast
    field_simp
    ring
  -- Accumulate the pieces.
  have hacc : ∀ j, 1 ≤ j → j ≤ m →
      IsPathWord K 0 (s j) (polyWord Z S (fun i => segmentPath p q (s i)) j) := by
    intro j hj1 hjm
    induction j with
    | zero => omega
    | succ j ih =>
      have hp := (hpiece j (by omega)).isPathWord
        (hK.mono (Icc_subset_Icc (hle j (by omega)).1 (hle (j + 1) hjm).2))
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        simpa [polyWord, hs0] using hp
      · rw [polyWord_succ]
        have h1 := ih hpos (by omega)
        have hsj : 0 < s j := hs0 ▸ lt_of_lt_succ_of_lt hmono hpos (by omega)
        refine h1.append hsj (hmono j (by omega)) ?_ ?_ hp
        · exact fun k => (hK.continuousOn k).mono (Icc_subset_Icc le_rfl (hle (j + 1) hjm).2)
        · exact fun t ht => hK.injective t ⟨ht.1, ht.2.trans (hle (j + 1) hjm).2⟩
  have hfull := hacc m hm le_rfl
  rw [hsm] at hfull
  exact (hZ.isRootPathWord_segWord hpq).isPathWord hK |>.unique zero_lt_one hfull

/-! ### Grids -/

/-- The vertex `(a, b)` of the grid with vertical lines `xs` and horizontal lines `ys`. -/
def gridPoint (xs ys : ℕ → ℝ) (a b : ℕ) : ℂ := ⟨xs a, ys b⟩

/-- The word of the horizontal edge from `(a, b)` to `(a + 1, b)`. -/
def gridH (Z : ℂ → Set ℂ) (S : ℕ) (xs ys : ℕ → ℝ) (a b : ℕ) : SignedAdjacentWord S :=
  segWord Z S (gridPoint xs ys a b) (gridPoint xs ys (a + 1) b)

/-- The word of the vertical edge from `(a, b)` to `(a, b + 1)`. -/
def gridV (Z : ℂ → Set ℂ) (S : ℕ) (xs ys : ℕ → ℝ) (a b : ℕ) : SignedAdjacentWord S :=
  segWord Z S (gridPoint xs ys a b) (gridPoint xs ys a (b + 1))

/-- The closed cell `(a, b)` of the grid. -/
def gridCell (xs ys : ℕ → ℝ) (a b : ℕ) : Set ℂ :=
  {z | z.re ∈ Icc (xs a) (xs (a + 1)) ∧ z.im ∈ Icc (ys b) (ys (b + 1))}

/-- The open cell `(a, b)` of the grid. -/
def gridCellInterior (xs ys : ℕ → ℝ) (a b : ℕ) : Set ℂ :=
  {z | z.re ∈ Ioo (xs a) (xs (a + 1)) ∧ z.im ∈ Ioo (ys b) (ys (b + 1))}

/-- **A grid for a root family**: an `n × n` grid with increasing vertical lines `xs` and
horizontal lines `ys`, whose grid lines lie in `U`, together with a set of marked cells such that
every unmarked closed cell lies in `U`. -/
structure IsRootGrid (U : Set ℂ) (xs ys : ℕ → ℝ) (n : ℕ) (marked : ℕ → ℕ → Prop) : Prop where
  pos : 0 < n
  xs_lt : ∀ a < n, xs a < xs (a + 1)
  ys_lt : ∀ b < n, ys b < ys (b + 1)
  horizontal : ∀ b ≤ n, ∀ x ∈ Icc (xs 0) (xs n), (⟨x, ys b⟩ : ℂ) ∈ U
  vertical : ∀ a ≤ n, ∀ y ∈ Icc (ys 0) (ys n), (⟨xs a, y⟩ : ℂ) ∈ U
  cell : ∀ a < n, ∀ b < n, ¬ marked a b → gridCell xs ys a b ⊆ U

namespace IsRootGrid

variable {xs ys : ℕ → ℝ} {n : ℕ} {marked : ℕ → ℕ → Prop}

theorem segmentPath_horizontal (a b : ℕ) (t : ℝ) :
    segmentPath (gridPoint xs ys a b) (gridPoint xs ys (a + 1) b) t =
      ⟨xs a + t * (xs (a + 1) - xs a), ys b⟩ := by
  apply Complex.ext <;> simp [segmentPath, gridPoint]

theorem segmentPath_vertical (a b : ℕ) (t : ℝ) :
    segmentPath (gridPoint xs ys a b) (gridPoint xs ys a (b + 1)) t =
      ⟨xs a, ys b + t * (ys (b + 1) - ys b)⟩ := by
  apply Complex.ext <;> simp [segmentPath, gridPoint]

/-- The horizontal edges of the grid lie in `U`. -/
theorem mapsTo_horizontal (G : IsRootGrid U xs ys n marked) {a b : ℕ} (ha : a < n)
    (hb : b ≤ n) :
    MapsTo (segmentPath (gridPoint xs ys a b) (gridPoint xs ys (a + 1) b)) (Icc 0 1) U := by
  intro t ht
  rw [segmentPath_horizontal]
  have h1 := G.xs_lt a ha
  have h2 := le_of_lt_succ_of_le G.xs_lt (Nat.zero_le a) ha.le
  have h3 := le_of_lt_succ_of_le G.xs_lt (Nat.succ_le_of_lt ha) le_rfl
  exact G.horizontal b hb _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩

/-- The vertical edges of the grid lie in `U`. -/
theorem mapsTo_vertical (G : IsRootGrid U xs ys n marked) {a b : ℕ} (ha : a ≤ n)
    (hb : b < n) :
    MapsTo (segmentPath (gridPoint xs ys a b) (gridPoint xs ys a (b + 1))) (Icc 0 1) U := by
  intro t ht
  rw [segmentPath_vertical]
  have h1 := G.ys_lt b hb
  have h2 := le_of_lt_succ_of_le G.ys_lt (Nat.zero_le b) hb.le
  have h3 := le_of_lt_succ_of_le G.ys_lt (Nat.succ_le_of_lt hb) le_rfl
  exact G.vertical a ha _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩

/-- **The cell relation** on every unmarked cell. -/
theorem cellRelation (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked) {a b : ℕ}
    (ha : a < n) (hb : b < n) (hm : ¬ marked a b) :
    SignedBraidEquiv (gridH Z S xs ys a b ++ gridV Z S xs ys (a + 1) b)
      (gridV Z S xs ys a b ++ gridH Z S xs ys a (b + 1)) := by
  set P : ℝ × ℝ → ℂ := fun x =>
    ⟨xs a + x.2 * (xs (a + 1) - xs a), ys b + x.1 * (ys (b + 1) - ys b)⟩ with hPdef
  have hPeq : P = fun x : ℝ × ℝ => (((xs a + x.2 * (xs (a + 1) - xs a) : ℝ)) : ℂ) +
      (((ys b + x.1 * (ys (b + 1) - ys b) : ℝ)) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp [hPdef]
  have hP : ContinuousOn P (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [hPeq]; exact Continuous.continuousOn (by fun_prop)
  have hxa := G.xs_lt a ha
  have hyb := G.ys_lt b hb
  have hPU : MapsTo P (Icc 0 1 ×ˢ Icc 0 1) U := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    refine G.cell a ha b hb hm ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [hPdef] <;>
      nlinarith [hs.1, hs.2, ht.1, ht.2]
  have e1 : ∀ t, P (0, t) = segmentPath (gridPoint xs ys a b) (gridPoint xs ys (a + 1) b) t :=
    fun t => by rw [segmentPath_horizontal]; apply Complex.ext <;> simp [hPdef]
  have e2 : ∀ t, P (1, t) =
      segmentPath (gridPoint xs ys a (b + 1)) (gridPoint xs ys (a + 1) (b + 1)) t :=
    fun t => by rw [segmentPath_horizontal]; apply Complex.ext <;> simp [hPdef]
  have e3 : ∀ s, P (s, 0) = segmentPath (gridPoint xs ys a b) (gridPoint xs ys a (b + 1)) s :=
    fun s => by rw [segmentPath_vertical]; apply Complex.ext <;> simp [hPdef]
  have e4 : ∀ s, P (s, 1) =
      segmentPath (gridPoint xs ys (a + 1) b) (gridPoint xs ys (a + 1) (b + 1)) s :=
    fun s => by rw [segmentPath_vertical]; apply Complex.ext <;> simp [hPdef]
  refine hZ.square_relation hP hPU ?_ ?_ ?_ ?_
  · exact (hZ.isRootPathWord_segWord (G.mapsTo_horizontal ha hb.le)).of_eqOn
      fun t _ => (e1 t).symm
  · exact (hZ.isRootPathWord_segWord (G.mapsTo_horizontal ha hb)).of_eqOn
      fun t _ => (e2 t).symm
  · exact (hZ.isRootPathWord_segWord (G.mapsTo_vertical ha.le hb)).of_eqOn
      fun s _ => (e3 s).symm
  · exact (hZ.isRootPathWord_segWord (G.mapsTo_vertical ha hb)).of_eqOn
      fun s _ => (e4 s).symm

end IsRootGrid

/-- The closed polygon through four vertices `p₀ p₁ p₂ p₃ p₀`. -/
def quadLoop (p₀ p₁ p₂ p₃ : ℂ) : ℕ → ℂ
  | 0 => p₀
  | 1 => p₁
  | 2 => p₂
  | 3 => p₃
  | _ => p₀

theorem polyWord_quadLoop (p₀ p₁ p₂ p₃ : ℂ) :
    polyWord Z S (quadLoop p₀ p₁ p₂ p₃) 4 =
      segWord Z S p₀ p₁ ++ segWord Z S p₁ p₂ ++ segWord Z S p₂ p₃ ++ segWord Z S p₃ p₀ := by
  simp [polyWord, List.range_succ, quadLoop]

/-- The boundary of the grid rectangle, counterclockwise from the lower left corner. -/
def outerLoop (xs ys : ℕ → ℝ) (n : ℕ) : ℕ → ℂ :=
  quadLoop (gridPoint xs ys 0 0) (gridPoint xs ys n 0) (gridPoint xs ys n n) (gridPoint xs ys 0 n)

/-- The boundary of the cell `(a, b)`, counterclockwise from its lower left corner. -/
def cellBoundary (xs ys : ℕ → ℝ) (a b : ℕ) : ℕ → ℂ :=
  quadLoop (gridPoint xs ys a b) (gridPoint xs ys (a + 1) b) (gridPoint xs ys (a + 1) (b + 1))
    (gridPoint xs ys a (b + 1))

namespace IsRootGrid

variable {xs ys : ℕ → ℝ} {n : ℕ} {marked : ℕ → ℕ → Prop}

/-- The word of a horizontal side of the rectangle is the row word. -/
theorem segWord_row (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked) {b : ℕ}
    (hb : b ≤ n) :
    SignedBraidEquiv (segWord Z S (gridPoint xs ys 0 b) (gridPoint xs ys n b))
      (rowWord (gridH Z S xs ys) b n) := by
  have hx0n : xs 0 < xs n := lt_of_lt_succ_of_lt G.xs_lt G.pos le_rfl
  have hd : 0 < xs n - xs 0 := sub_pos.mpr hx0n
  have hpq : MapsTo (segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b)) (Icc 0 1) U := by
    intro t ht
    have : segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b) t =
        ⟨xs 0 + t * (xs n - xs 0), ys b⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.horizontal b hb _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have h := hZ.segWord_subdivide hpq (s := fun a => (xs a - xs 0) / (xs n - xs 0)) G.pos
    (by simp) (by simp [div_self hd.ne']) fun a ha =>
      div_lt_div_of_pos_right (by linarith [G.xs_lt a ha]) hd
  refine h.trans (SignedBraidEquiv.of_eq ?_)
  have hpt : ∀ c, segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b)
      ((xs c - xs 0) / (xs n - xs 0)) = gridPoint xs ys c b := fun c => by
    have hs : ∀ t : ℝ, segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b) t =
        ⟨xs 0 + t * (xs n - xs 0), ys b⟩ := fun t => by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [hs, gridPoint]
    congr 1
    field_simp
    ring
  unfold polyWord rowWord gridH
  refine List.flatMap_congr fun a _ => ?_
  simp only [hpt]

/-- The word of a vertical side of the rectangle is the column word. -/
theorem segWord_col (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked) {a : ℕ}
    (ha : a ≤ n) :
    SignedBraidEquiv (segWord Z S (gridPoint xs ys a 0) (gridPoint xs ys a n))
      (colWord (gridV Z S xs ys) a n) := by
  have hy0n : ys 0 < ys n := lt_of_lt_succ_of_lt G.ys_lt G.pos le_rfl
  have hd : 0 < ys n - ys 0 := sub_pos.mpr hy0n
  have hpq : MapsTo (segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n)) (Icc 0 1) U := by
    intro t ht
    have : segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n) t =
        ⟨xs a, ys 0 + t * (ys n - ys 0)⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.vertical a ha _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have h := hZ.segWord_subdivide hpq (s := fun b => (ys b - ys 0) / (ys n - ys 0)) G.pos
    (by simp) (by simp [div_self hd.ne']) fun b hb =>
      div_lt_div_of_pos_right (by linarith [G.ys_lt b hb]) hd
  refine h.trans (SignedBraidEquiv.of_eq ?_)
  have hpt : ∀ c, segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n)
      ((ys c - ys 0) / (ys n - ys 0)) = gridPoint xs ys a c := fun c => by
    have hs : ∀ t : ℝ, segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n) t =
        ⟨xs a, ys 0 + t * (ys n - ys 0)⟩ := fun t => by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [hs, gridPoint]
    congr 1
    field_simp
    ring
  unfold polyWord colWord gridV
  refine List.flatMap_congr fun b _ => ?_
  simp only [hpt]

/-- **The boundary of the rectangle**: its polygon word is the grid boundary word. -/
theorem polyWord_outerLoop (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked) :
    SignedBraidEquiv (polyWord Z S (outerLoop xs ys n) 4)
      (boundaryWord (gridH Z S xs ys) (gridV Z S xs ys) n) := by
  rw [outerLoop, polyWord_quadLoop]
  have hx0n : xs 0 ≤ xs n := le_of_lt_succ_of_le G.xs_lt (Nat.zero_le n) le_rfl
  have hy0n : ys 0 ≤ ys n := le_of_lt_succ_of_le G.ys_lt (Nat.zero_le n) le_rfl
  have hsegh : ∀ b ≤ n,
      MapsTo (segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b)) (Icc 0 1) U := by
    intro b hb t ht
    have : segmentPath (gridPoint xs ys 0 b) (gridPoint xs ys n b) t =
        ⟨xs 0 + t * (xs n - xs 0), ys b⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.horizontal b hb _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hsegv : ∀ a ≤ n,
      MapsTo (segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n)) (Icc 0 1) U := by
    intro a ha t ht
    have : segmentPath (gridPoint xs ys a 0) (gridPoint xs ys a n) t =
        ⟨xs a, ys 0 + t * (ys n - ys 0)⟩ := by
      apply Complex.ext <;> simp [segmentPath, gridPoint]
    rw [this]
    exact G.vertical a ha _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have h1 := segWord_row hZ G (Nat.zero_le n)
  have h2 := segWord_col hZ G (le_refl n)
  have h3 := (hZ.segWord_swap (hsegh n le_rfl)).trans (segWord_row hZ G le_rfl).inv
  have h4 := (hZ.segWord_swap (hsegv 0 (Nat.zero_le n))).trans
    (segWord_col hZ G (Nat.zero_le n)).inv
  unfold boundaryWord
  exact ((h1.append h2).append h3).append h4

/-- **The boundary of a cell**: its polygon word is the cell loop. -/
theorem polyWord_cellBoundary (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked)
    {a b : ℕ} (ha : a < n) (hb : b < n) :
    SignedBraidEquiv (polyWord Z S (cellBoundary xs ys a b) 4)
      (cellLoop (gridH Z S xs ys) (gridV Z S xs ys) a b) := by
  rw [cellBoundary, polyWord_quadLoop]
  have h3 := hZ.segWord_swap (G.mapsTo_horizontal ha (Nat.succ_le_of_lt hb))
  have h4 := hZ.segWord_swap (G.mapsTo_vertical ha.le hb)
  unfold cellLoop gridH gridV
  exact ((SignedBraidEquiv.refl _).append h3).append h4

end IsRootGrid

/-- The vertices of the based loop of the cell `(a, b)`: from `(0, 0)` up the left column to
`(0, b)`, along the row to `(a, b)`, counterclockwise around the cell, and back along the same
grid path. It has `2 a + 2 b + 4` sides. -/
def basedLoop (xs ys : ℕ → ℝ) (a b : ℕ) (i : ℕ) : ℂ :=
  if i ≤ b then gridPoint xs ys 0 i
  else if i ≤ b + a then gridPoint xs ys (i - b) b
  else if i = b + a + 1 then gridPoint xs ys (a + 1) b
  else if i = b + a + 2 then gridPoint xs ys (a + 1) (b + 1)
  else if i = b + a + 3 then gridPoint xs ys a (b + 1)
  else if i ≤ b + 2 * a + 4 then gridPoint xs ys (b + 2 * a + 4 - i) b
  else gridPoint xs ys 0 (2 * b + 2 * a + 4 - i)

/-- The number of sides of the based loop of the cell `(a, b)`. -/
def basedLength (a b : ℕ) : ℕ := 2 * a + 2 * b + 4

section BasedLoop

variable (xs ys : ℕ → ℝ) (a b : ℕ)

theorem basedLoop_col {i : ℕ} (h : i ≤ b) : basedLoop xs ys a b i = gridPoint xs ys 0 i := by
  rw [basedLoop, if_pos h]

theorem basedLoop_row {i : ℕ} (h1 : b ≤ i) (h2 : i ≤ b + a) :
    basedLoop xs ys a b i = gridPoint xs ys (i - b) b := by
  by_cases h : i ≤ b
  · obtain rfl : i = b := le_antisymm h h1
    rw [basedLoop, if_pos h, Nat.sub_self]
  · rw [basedLoop, if_neg h, if_pos h2]

theorem basedLoop_c1 : basedLoop xs ys a b (b + a + 1) = gridPoint xs ys (a + 1) b := by
  rw [basedLoop, if_neg (show ¬ (b + a + 1 ≤ b) by omega),
    if_neg (show ¬ (b + a + 1 ≤ b + a) by omega), if_pos rfl]

theorem basedLoop_c2 : basedLoop xs ys a b (b + a + 2) = gridPoint xs ys (a + 1) (b + 1) := by
  rw [basedLoop, if_neg (show ¬ (b + a + 2 ≤ b) by omega),
    if_neg (show ¬ (b + a + 2 ≤ b + a) by omega), if_neg (show ¬ (b + a + 2 = b + a + 1) by omega),
    if_pos rfl]

theorem basedLoop_c3 : basedLoop xs ys a b (b + a + 3) = gridPoint xs ys a (b + 1) := by
  rw [basedLoop, if_neg (show ¬ (b + a + 3 ≤ b) by omega),
    if_neg (show ¬ (b + a + 3 ≤ b + a) by omega), if_neg (show ¬ (b + a + 3 = b + a + 1) by omega),
    if_neg (show ¬ (b + a + 3 = b + a + 2) by omega), if_pos rfl]

theorem basedLoop_back {i : ℕ} (h1 : b + a + 4 ≤ i) (h2 : i ≤ b + 2 * a + 4) :
    basedLoop xs ys a b i = gridPoint xs ys (b + 2 * a + 4 - i) b := by
  rw [basedLoop, if_neg (show ¬ (i ≤ b) by omega), if_neg (show ¬ (i ≤ b + a) by omega),
    if_neg (show ¬ (i = b + a + 1) by omega), if_neg (show ¬ (i = b + a + 2) by omega),
    if_neg (show ¬ (i = b + a + 3) by omega), if_pos h2]

theorem basedLoop_down {i : ℕ} (h1 : b + 2 * a + 4 ≤ i) :
    basedLoop xs ys a b i = gridPoint xs ys 0 (2 * b + 2 * a + 4 - i) := by
  by_cases h : i ≤ b + 2 * a + 4
  · obtain rfl : i = b + 2 * a + 4 := by omega
    rw [basedLoop_back xs ys a b (by omega) le_rfl]
    congr 1 <;> omega
  · rw [basedLoop, if_neg (show ¬ (i ≤ b) by omega), if_neg (show ¬ (i ≤ b + a) by omega),
      if_neg (show ¬ (i = b + a + 1) by omega), if_neg (show ¬ (i = b + a + 2) by omega),
      if_neg (show ¬ (i = b + a + 3) by omega), if_neg h]

theorem basedLoop_zero : basedLoop xs ys a b 0 = gridPoint xs ys 0 0 :=
  basedLoop_col xs ys a b (Nat.zero_le b)

theorem basedLoop_length : basedLoop xs ys a b (basedLength a b) = gridPoint xs ys 0 0 := by
  rw [basedLength, basedLoop_down xs ys a b (by omega)]
  congr 1; omega

theorem basedLoop_corner : basedLoop xs ys a b (b + a) = gridPoint xs ys a b := by
  rw [basedLoop_row xs ys a b (by omega) le_rfl, show b + a - b = a by omega]

end BasedLoop

namespace IsRootGrid

variable {xs ys : ℕ → ℝ} {n : ℕ} {marked : ℕ → ℕ → Prop}

/-- The sides of the based loop are grid edges. -/
theorem mapsTo_basedLoop (G : IsRootGrid U xs ys n marked) {a b : ℕ} (ha : a < n)
    (hb : b < n) : ∀ i < basedLength a b,
      MapsTo (segmentPath (basedLoop xs ys a b i) (basedLoop xs ys a b (i + 1))) (Icc 0 1) U := by
  intro i hi
  unfold basedLength at hi
  by_cases h1 : i < b
  · rw [basedLoop_col xs ys a b h1.le, basedLoop_col xs ys a b (show i + 1 ≤ b by omega)]
    exact G.mapsTo_vertical (Nat.zero_le n) (by omega)
  by_cases h2 : i < b + a
  · rw [basedLoop_row xs ys a b (by omega) h2.le,
      basedLoop_row xs ys a b (show b ≤ i + 1 by omega) (by omega),
      show i + 1 - b = i - b + 1 by omega]
    exact G.mapsTo_horizontal (by omega) hb.le
  by_cases h3 : i < b + a + 4
  · have hi3 : i = b + a ∨ i = b + a + 1 ∨ i = b + a + 2 ∨ i = b + a + 3 := by omega
    have e4 : basedLoop xs ys a b (b + a + 3 + 1) = gridPoint xs ys a b := by
      rw [basedLoop_back xs ys a b (by omega) (by omega), show b + 2 * a + 4 - (b + a + 3 + 1) = a
        by omega]
    rcases hi3 with rfl | rfl | rfl | rfl
    · rw [basedLoop_corner, basedLoop_c1]; exact G.mapsTo_horizontal ha hb.le
    · rw [basedLoop_c1, basedLoop_c2]; exact G.mapsTo_vertical ha hb
    · rw [basedLoop_c2, basedLoop_c3]; exact mapsTo_segmentPath_symm (G.mapsTo_horizontal ha hb)
    · rw [basedLoop_c3, e4]; exact mapsTo_segmentPath_symm (G.mapsTo_vertical ha.le hb)
  by_cases h4 : i < b + 2 * a + 4
  · rw [basedLoop_back xs ys a b (by omega) h4.le,
      basedLoop_back xs ys a b (show b + a + 4 ≤ i + 1 by omega) (by omega)]
    have := G.mapsTo_horizontal (a := b + 2 * a + 4 - (i + 1)) (b := b) (by omega) hb.le
    rw [show b + 2 * a + 4 - (i + 1) + 1 = b + 2 * a + 4 - i by omega] at this
    exact mapsTo_segmentPath_symm this
  · rw [basedLoop_down xs ys a b (by omega), basedLoop_down xs ys a b (show b + 2 * a + 4 ≤ i + 1
      by omega)]
    have := G.mapsTo_vertical (a := 0) (b := 2 * b + 2 * a + 4 - (i + 1)) (Nat.zero_le n)
      (by omega)
    rw [show 2 * b + 2 * a + 4 - (i + 1) + 1 = 2 * b + 2 * a + 4 - i by omega] at this
    exact mapsTo_segmentPath_symm this

/-- **The based loop of a cell**: its polygon word is the conjugated cell loop
`γ_{ab} ℓ_{ab} γ_{ab}⁻¹`, where `γ_{ab}` is the word of the grid path from `(0, 0)` up the left
column and along the row to `(a, b)`. -/
theorem polyWord_basedLoop (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked) {a b : ℕ}
    (ha : a < n) (hb : b < n) :
    SignedBraidEquiv (polyWord Z S (basedLoop xs ys a b) (basedLength a b))
      (conjugateWord (cellConjugator (gridH Z S xs ys) (gridV Z S xs ys) a b)
        (cellLoop (gridH Z S xs ys) (gridV Z S xs ys) a b)) := by
  set w := basedLoop xs ys a b with hw
  have hlen : basedLength a b = b + (a + (4 + (a + b))) := by unfold basedLength; omega
  rw [hlen, polyWord_add, polyWord_add, polyWord_add, polyWord_add]
  -- The column up.
  have p1 : polyWord Z S w b = colWord (gridV Z S xs ys) 0 b := by
    rw [polyWord_congr (w' := fun i => gridPoint xs ys 0 i) fun i hi =>
      basedLoop_col xs ys a b hi]
    rfl
  -- The row.
  have p2 : polyWord Z S (fun i => w (b + i)) a = rowWord (gridH Z S xs ys) b a := by
    rw [polyWord_congr (w' := fun i => gridPoint xs ys i b) fun i hi => by
      simp only [hw]
      rw [basedLoop_row xs ys a b (by omega) (by omega), show b + i - b = i by omega]]
    rfl
  -- The cell.
  have p3 : polyWord Z S (fun i => w (b + (a + i))) 4 =
      polyWord Z S (cellBoundary xs ys a b) 4 := by
    refine polyWord_congr fun i hi => ?_
    simp only [hw]
    interval_cases i
    · rw [add_zero, basedLoop_corner]; rfl
    · rw [show b + (a + 1) = b + a + 1 by omega, basedLoop_c1]; rfl
    · rw [show b + (a + 2) = b + a + 2 by omega, basedLoop_c2]; rfl
    · rw [show b + (a + 3) = b + a + 3 by omega, basedLoop_c3]; rfl
    · rw [basedLoop_back xs ys a b (by omega) (by omega),
        show b + 2 * a + 4 - (b + (a + 4)) = a by omega]; rfl
  -- The row back.
  have p4 : SignedBraidEquiv (polyWord Z S (fun i => w (b + (a + (4 + i)))) a)
      (inv (rowWord (gridH Z S xs ys) b a)) := by
    rw [polyWord_congr (w' := fun i => (fun j => gridPoint xs ys j b) (a - i)) fun i hi => by
      simp only [hw]
      rw [basedLoop_back xs ys a b (by omega) (by omega),
        show b + 2 * a + 4 - (b + (a + (4 + i))) = a - i by omega]]
    exact hZ.polyWord_reverse (w := fun j => gridPoint xs ys j b) fun j hj =>
      G.mapsTo_horizontal (by omega) hb.le
  -- The column down.
  have p5 : SignedBraidEquiv (polyWord Z S (fun i => w (b + (a + (4 + (a + i))))) b)
      (inv (colWord (gridV Z S xs ys) 0 b)) := by
    rw [polyWord_congr (w' := fun i => (fun j => gridPoint xs ys 0 j) (b - i)) fun i hi => by
      simp only [hw]
      rw [basedLoop_down xs ys a b (by omega),
        show 2 * b + 2 * a + 4 - (b + (a + (4 + (a + i)))) = b - i by omega]]
    exact hZ.polyWord_reverse (w := fun j => gridPoint xs ys 0 j) fun j hj =>
      G.mapsTo_vertical (Nat.zero_le n) (by omega)
  rw [p1, p2, p3]
  have hcell := polyWord_cellBoundary hZ G ha hb
  have htot := ((((SignedBraidEquiv.refl (colWord (gridV Z S xs ys) 0 b)).append
    (SignedBraidEquiv.refl (rowWord (gridH Z S xs ys) b a))).append hcell).append p4).append p5
  refine (SignedBraidEquiv.of_eq (by simp only [List.append_assoc])).trans
    (htot.trans (SignedBraidEquiv.of_eq ?_))
  simp [conjugateWord, cellConjugator, inv_append, List.append_assoc]

/-- **The outer boundary as a product of conjugated marked cell loops.** The word of the
boundary of the grid rectangle is the ordered product, over the rows `b = 0, …, n - 1` and within
a row over `a = n - 1, …, 0`, of the conjugated loops `γ_{ab} ℓ_{ab} γ_{ab}⁻¹` of the marked
cells. -/
theorem outer_equiv_markedProduct (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked)
    [DecidableRel marked] :
    SignedBraidEquiv (polyWord Z S (outerLoop xs ys n) 4)
      ((List.range n).flatMap fun b => (List.range n).reverse.flatMap fun a =>
        if marked a b then conjugateWord (cellConjugator (gridH Z S xs ys) (gridV Z S xs ys) a b)
          (cellLoop (gridH Z S xs ys) (gridV Z S xs ys) a b) else []) :=
  (polyWord_outerLoop hZ G).trans (boundaryWord_equiv_markedProduct _ _ n marked
    fun _ ha _ hb hm => cellRelation hZ G ha hb hm)

end IsRootGrid

end OnLeConjecture.Analytic
