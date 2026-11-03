/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyRootGrid

/-!
# Placing a grid around finitely many critical values

The cut system of the subsection "Global factorization, exponent count, and transitivity" of
Section 3 of the written proof of Statement E (`statement-E-complete-proof.tex`) is realized by a
rectangular grid (`BraidMonodromyRootGrid.lean`). This module chooses such a grid for a finite set
`V` of critical values in the open square `(-a, a)²`.

`exists_gridChoice`: for every function `R` positive on `V` there are `n` and increasing
sequences `xs`, `ys` with `xs 0 = ys 0 = -a`, `xs n = ys n = a`, such that no grid line meets `V`,
every point `c ∈ V` lies in the interior of a cell `cellOf c`, distinct points of `V` lie in
distinct cells, and the closed cell of `c` lies in the ball `B(c, R c)`. The vertical lines
are `-a + i δ + τ` for `0 < i < n`, with a uniform step `δ` and a shift `τ ∈ (0, δ/2)` avoiding the
finitely many values at which a line meets `V`.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

/-- A point of `(f 0, f n)` that is not a value `f i`, `i ≤ n`, lies strictly between two
consecutive values. -/
theorem exists_Ioo_of_lt {f : ℕ → ℝ} {n : ℕ} {x : ℝ} (h0 : f 0 < x) (hn : x < f n)
    (hne : ∀ i ≤ n, x ≠ f i) :
    ∃ i < n, x ∈ Ioo (f i) (f (i + 1)) := by
  classical
  set i := Nat.findGreatest (fun i => f i < x) n with hi
  have hi_le : i ≤ n := Nat.findGreatest_le n
  have hfi : f i < x := Nat.findGreatest_spec (P := fun i => f i < x) (Nat.zero_le n) h0
  have hin : i < n := by
    rcases eq_or_lt_of_le hi_le with h | h
    · rw [h] at hfi; linarith
    · exact h
  refine ⟨i, hin, hfi, ?_⟩
  have hnot : ¬ f (i + 1) < x := Nat.findGreatest_is_greatest (Nat.lt_succ_self i) (by omega)
  exact lt_of_le_of_ne (not_lt.mp hnot) (hne (i + 1) (by omega))

/-- The cell containing a point in the interior of the grid is unique. -/
theorem Ioo_index_unique {f : ℕ → ℝ} {n : ℕ} (hf : ∀ i < n, f i < f (i + 1)) {x : ℝ} {i j : ℕ}
    (hi : i < n) (hj : j < n) (hxi : x ∈ Icc (f i) (f (i + 1))) (hxj : x ∈ Ioo (f j) (f (j + 1))) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := le_of_lt_succ_of_le hf (show i + 1 ≤ j by omega) hj.le
    linarith [hxi.2, hxj.1]
  · have := le_of_lt_succ_of_le hf (show j + 1 ≤ i by omega) hi.le
    linarith [hxj.2, hxi.1]

/-- The lines `-a + i δ + τ` for `0 < i < n`, completed by `-a` and `a`. -/
def shiftedLines (a δ τ : ℝ) (n : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then -a else if n ≤ i then a else -a + i * δ + τ

theorem shiftedLines_succ_sub {a δ τ : ℝ} {n : ℕ} (hn : 2 ≤ n) (hδ : (n : ℝ) * δ = 2 * a)
    {i : ℕ} (hi : i < n) :
    shiftedLines a δ τ n (i + 1) - shiftedLines a δ τ n i =
      if i = 0 then δ + τ else if i + 1 = n then δ - τ else δ := by
  unfold shiftedLines
  rw [if_neg (by omega)]
  by_cases h0 : i = 0
  · subst h0
    rw [if_neg (by omega), if_pos rfl, if_pos rfl]
    push_cast; ring
  · rw [if_neg h0, if_neg h0, if_neg (show ¬ n ≤ i by omega)]
    by_cases h1 : i + 1 = n
    · rw [if_pos (show n ≤ i + 1 by omega), if_pos h1]
      have : (i : ℝ) + 1 = n := by exact_mod_cast h1
      have : (i : ℝ) = n - 1 := by linarith
      rw [this]; linarith
    · rw [if_neg (show ¬ n ≤ i + 1 by omega), if_neg h1]
      push_cast; ring

theorem shiftedLines_lt {a δ τ : ℝ} {n : ℕ} (hn : 2 ≤ n) (hδ : (n : ℝ) * δ = 2 * a)
    (hτ : 0 < τ) (hτδ : τ < δ) : ∀ i < n,
    shiftedLines a δ τ n i < shiftedLines a δ τ n (i + 1) := by
  intro i hi
  have h := shiftedLines_succ_sub (τ := τ) hn hδ hi
  split_ifs at h <;> linarith

/-- The width of a cell of the shifted grid is less than `2 δ`. -/
theorem shiftedLines_width {a δ τ : ℝ} {n : ℕ} (hn : 2 ≤ n) (hδ : (n : ℝ) * δ = 2 * a)
    (hτ : 0 < τ) (hτδ : τ < δ) {i : ℕ} (hi : i < n) :
    shiftedLines a δ τ n (i + 1) - shiftedLines a δ τ n i < 2 * δ := by
  have h := shiftedLines_succ_sub (τ := τ) hn hδ hi
  split_ifs at h <;> linarith

/-- **A grid around finitely many points.** -/
theorem exists_gridChoice (V : Finset ℂ) {a : ℝ} (ha : 0 < a)
    (hV : ∀ c ∈ V, c.re ∈ Ioo (-a) a ∧ c.im ∈ Ioo (-a) a) (R : ℂ → ℝ)
    (hR : ∀ c ∈ V, 0 < R c) :
    ∃ (n : ℕ) (xs ys : ℕ → ℝ) (cellOf : ℂ → ℕ × ℕ),
      0 < n ∧ (∀ i < n, xs i < xs (i + 1)) ∧ (∀ i < n, ys i < ys (i + 1)) ∧
      xs 0 = -a ∧ xs n = a ∧ ys 0 = -a ∧ ys n = a ∧
      (∀ c ∈ V, ∀ i ≤ n, c.re ≠ xs i ∧ c.im ≠ ys i) ∧
      (∀ c ∈ V, (cellOf c).1 < n ∧ (cellOf c).2 < n ∧
        c ∈ gridCellInterior xs ys (cellOf c).1 (cellOf c).2 ∧
        gridCell xs ys (cellOf c).1 (cellOf c).2 ⊆ Metric.ball c (R c)) ∧
      Set.InjOn cellOf V := by
  classical
  -- A positive lower bound for the radii and for the distances between distinct points.
  obtain ⟨m, hm, hmR, hmsep⟩ : ∃ m > 0, (∀ c ∈ V, m ≤ R c) ∧
      ∀ c ∈ V, ∀ c' ∈ V, c ≠ c' → m ≤ ‖c - c'‖ := by
    set P := (V ×ˢ V).filter fun p => p.1 ≠ p.2
    set T : Finset ℝ := V.image R ∪ P.image fun p => ‖p.1 - p.2‖
    have hT : ∀ x ∈ T, 0 < x := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
        exact hR c hc
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_filter] at hp
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hp.2)
    by_cases hTe : T.Nonempty
    · refine ⟨T.min' hTe, hT _ (T.min'_mem hTe), fun c hc => T.min'_le _ ?_,
        fun c hc c' hc' hne => T.min'_le _ ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c, c'), ?_, rfl⟩)
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hc, hc'⟩, hne⟩
    · refine ⟨1, one_pos, fun c hc => ?_, fun c hc c' hc' hne => ?_⟩
      · exact absurd ⟨R c, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)⟩ hTe
      · refine absurd ⟨‖c - c'‖, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c, c'), ?_, rfl⟩)⟩
          hTe
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hc, hc'⟩, hne⟩
  -- The number of cells and the step.
  obtain ⟨n, hn2, hnbig⟩ : ∃ n : ℕ, 2 ≤ n ∧ 8 * a / m < n := by
    obtain ⟨k, hk⟩ := exists_nat_gt (8 * a / m)
    exact ⟨k + 2, by omega, by push_cast; linarith⟩
  set δ : ℝ := 2 * a / n with hδdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδpos : 0 < δ := div_pos (by linarith) hnpos
  have hδn : (n : ℝ) * δ = 2 * a := by rw [hδdef]; field_simp
  have hδm : 4 * δ < m := by
    rw [div_lt_iff₀ hm] at hnbig
    rw [hδdef]
    rw [show 4 * (2 * a / n) = 8 * a / n by ring, div_lt_iff₀ hnpos]
    linarith
  -- The shift avoids finitely many values.
  set B : Finset ℝ := (V ×ˢ Finset.range n).image (fun p => p.1.re + a - p.2 * δ) ∪
    (V ×ˢ Finset.range n).image (fun p => p.1.im + a - p.2 * δ)
  obtain ⟨τ, ⟨hτ0, hτδ⟩, hτB⟩ : ∃ τ ∈ Ioo 0 (δ / 2), τ ∉ (B : Set ℝ) :=
    ((Set.Ioo_infinite (half_pos hδpos)).sdiff B.finite_toSet).nonempty
  have hτδ' : τ < δ := by linarith
  set xs := shiftedLines a δ τ n
  have hxs : ∀ i < n, xs i < xs (i + 1) := shiftedLines_lt hn2 hδn hτ0 hτδ'
  have hxs0 : xs 0 = -a := by simp [xs, shiftedLines]
  have hxsn : xs n = a := by simp [xs, shiftedLines, show n ≠ 0 by omega]
  -- No line meets `V`.
  have havoid : ∀ c ∈ V, ∀ i ≤ n, c.re ≠ xs i ∧ c.im ≠ xs i := by
    intro c hc i hi
    have hcV := hV c hc
    by_cases h0 : i = 0
    · subst h0; rw [hxs0]; exact ⟨hcV.1.1.ne', hcV.2.1.ne'⟩
    by_cases h1 : n ≤ i
    · have : i = n := by omega
      subst this; rw [hxsn]; exact ⟨hcV.1.2.ne, hcV.2.2.ne⟩
    have hxi : xs i = -a + i * δ + τ := by simp [xs, shiftedLines, h0, h1]
    rw [hxi]
    have him : (c, i) ∈ V ×ˢ Finset.range n :=
      Finset.mem_product.mpr ⟨hc, Finset.mem_range.mpr (by omega)⟩
    constructor
    · intro heq
      apply hτB
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(c, i), him, ?_⟩)
      simp only
      linarith
    · intro heq
      apply hτB
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c, i), him, ?_⟩)
      simp only
      linarith
  -- The cell of a point.
  have hcell : ∀ c ∈ V, ∃ p : ℕ × ℕ, p.1 < n ∧ p.2 < n ∧ c.re ∈ Ioo (xs p.1) (xs (p.1 + 1)) ∧
      c.im ∈ Ioo (xs p.2) (xs (p.2 + 1)) := by
    intro c hc
    have hcV := hV c hc
    obtain ⟨i, hi, hix⟩ := exists_Ioo_of_lt (by rw [hxs0]; exact hcV.1.1)
      (by rw [hxsn]; exact hcV.1.2) fun j hj => (havoid c hc j hj).1
    obtain ⟨j, hj, hjy⟩ := exists_Ioo_of_lt (by rw [hxs0]; exact hcV.2.1)
      (by rw [hxsn]; exact hcV.2.2) fun j' hj' => (havoid c hc j' hj').2
    exact ⟨(i, j), hi, hj, hix, hjy⟩
  choose! cellOf hcn1 hcn2 hcre hcim using hcell
  have hwidth : ∀ i < n, xs (i + 1) - xs i < 2 * δ := fun i hi =>
    shiftedLines_width hn2 hδn hτ0 hτδ' hi
  -- Points of a closed cell are close to each other.
  have hclose : ∀ i < n, ∀ j < n, ∀ z ∈ gridCell xs xs i j, ∀ w ∈ gridCell xs xs i j,
      ‖z - w‖ < 4 * δ := by
    intro i hi j hj z hz w hw
    have h1 := hwidth i hi
    have h2 := hwidth j hj
    calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < 2 * δ + 2 * δ := by
          refine add_lt_add_of_le_of_lt ?_ ?_
          · rw [Complex.sub_re, abs_le]
            constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
          · rw [Complex.sub_im, abs_lt]
            constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
      _ = 4 * δ := by ring
  refine ⟨n, xs, xs, cellOf, by omega, hxs, hxs, hxs0, hxsn, hxs0, hxsn, havoid,
    fun c hc => ⟨hcn1 c hc, hcn2 c hc, ⟨hcre c hc, hcim c hc⟩, ?_⟩, ?_⟩
  · intro z hz
    have hcz : c ∈ gridCell xs xs (cellOf c).1 (cellOf c).2 :=
      ⟨Ioo_subset_Icc_self (hcre c hc), Ioo_subset_Icc_self (hcim c hc)⟩
    have := hclose _ (hcn1 c hc) _ (hcn2 c hc) z hz c hcz
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [hmR c hc]
  · intro c hc c' hc' heq
    by_contra hne
    have hc'z : c' ∈ gridCell xs xs (cellOf c).1 (cellOf c).2 := by
      rw [heq]
      exact ⟨Ioo_subset_Icc_self (hcre c' hc'), Ioo_subset_Icc_self (hcim c' hc')⟩
    have hcz : c ∈ gridCell xs xs (cellOf c).1 (cellOf c).2 :=
      ⟨Ioo_subset_Icc_self (hcre c hc), Ioo_subset_Icc_self (hcim c hc)⟩
    have := hclose _ (hcn1 c hc) _ (hcn2 c hc) c hcz c' hc'z
    linarith [hmsep c hc c' hc' hne]

/-- **A grid adapted to a finite set `V`** in the open square `(-a, a)²` and to radii `R`. -/
structure GridChoice (V : Finset ℂ) (a : ℝ) (R : ℂ → ℝ) where
  /-- The number of rows and columns. -/
  n : ℕ
  /-- The vertical lines. -/
  xs : ℕ → ℝ
  /-- The horizontal lines. -/
  ys : ℕ → ℝ
  /-- The cell of each point of `V`. -/
  cellOf : ℂ → ℕ × ℕ
  pos : 0 < n
  xs_lt : ∀ i < n, xs i < xs (i + 1)
  ys_lt : ∀ i < n, ys i < ys (i + 1)
  xs_zero : xs 0 = -a
  xs_last : xs n = a
  ys_zero : ys 0 = -a
  ys_last : ys n = a
  avoid : ∀ c ∈ V, ∀ i ≤ n, c.re ≠ xs i ∧ c.im ≠ ys i
  cellOf_spec : ∀ c ∈ V, (cellOf c).1 < n ∧ (cellOf c).2 < n ∧
    c ∈ gridCellInterior xs ys (cellOf c).1 (cellOf c).2 ∧
    gridCell xs ys (cellOf c).1 (cellOf c).2 ⊆ Metric.ball c (R c)
  injOn : Set.InjOn cellOf V

theorem nonempty_gridChoice (V : Finset ℂ) {a : ℝ} (ha : 0 < a)
    (hV : ∀ c ∈ V, c.re ∈ Ioo (-a) a ∧ c.im ∈ Ioo (-a) a) (R : ℂ → ℝ)
    (hR : ∀ c ∈ V, 0 < R c) : Nonempty (GridChoice V a R) := by
  obtain ⟨n, xs, ys, cellOf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    exists_gridChoice V ha hV R hR
  exact ⟨⟨n, xs, ys, cellOf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩

namespace GridChoice

variable {V : Finset ℂ} {a : ℝ} {R : ℂ → ℝ} (G : GridChoice V a R)

/-- A point of `V` in a closed cell lies in the interior of that cell, which is its cell. -/
theorem cellOf_eq_of_mem {c : ℂ} (hc : c ∈ V) {i j : ℕ} (hi : i < G.n) (hj : j < G.n)
    (hcell : c ∈ gridCell G.xs G.ys i j) : G.cellOf c = (i, j) := by
  obtain ⟨h1, h2, ⟨hre, him⟩, -⟩ := G.cellOf_spec c hc
  have e1 := Ioo_index_unique G.xs_lt hi h1 hcell.1 hre
  have e2 := Ioo_index_unique G.ys_lt hj h2 hcell.2 him
  exact Prod.ext e1.symm e2.symm

/-- Every point of the closed grid rectangle lies in the square `[-a, a]²`. -/
theorem mem_square_of_le {i : ℕ} (hi : i ≤ G.n) :
    -a ≤ G.xs i ∧ G.xs i ≤ a ∧ -a ≤ G.ys i ∧ G.ys i ≤ a := by
  have h1 := le_of_lt_succ_of_le G.xs_lt (Nat.zero_le i) hi
  have h2 := le_of_lt_succ_of_le G.xs_lt hi le_rfl
  have h3 := le_of_lt_succ_of_le G.ys_lt (Nat.zero_le i) hi
  have h4 := le_of_lt_succ_of_le G.ys_lt hi le_rfl
  rw [G.xs_zero] at h1
  rw [G.xs_last] at h2
  rw [G.ys_zero] at h3
  rw [G.ys_last] at h4
  exact ⟨h1, h2, h3, h4⟩

end GridChoice

end OnLeConjecture.Analytic
