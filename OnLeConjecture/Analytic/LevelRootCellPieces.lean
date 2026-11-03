/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelRootTransport

/-!
# Labellings over the pieces of a grid cell

For the transitivity argument of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`, subsection "Global factorization, exponent count, and
transitivity") the closed grid rectangle minus the critical values is covered by finitely many
convex pieces: the unmarked closed cells, and the four closed quadrants of each marked cell around
its critical value `m`, with `m` removed. A closed rectangle minus one of its corners is convex
(`convex_rectSet_diff`), so every piece carries a labelling of the roots
(`IsRootFamily.exists_convex_labelling`).

* `exists_quadrant_labellings`: given labellings of the roots over the four sides of a rectangle,
  compatible at three corners and differing by a permutation `π` at the fourth corner, the four
  punctured quadrants carry labellings agreeing with the side labellings on the sides (with `π` on
  the top and left sides), agreeing with each other on the three internal half-segments from the
  bottom, the right and the top, and differing by `π` on the left internal half-segment.
* `exists_rect_labelling`: an unpunctured rectangle in the base carries one labelling agreeing with
  the four side labellings.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

variable {S : ℕ} {Z : ℂ → Set ℂ} {U : Set ℂ}

/-! ### Rectangles -/

/-- The closed rectangle `[u₀, u₁] × [v₀, v₁]`. -/
def rectSet (u₀ u₁ v₀ v₁ : ℝ) : Set ℂ := {z | z.re ∈ Icc u₀ u₁ ∧ z.im ∈ Icc v₀ v₁}

theorem convex_rectSet (u₀ u₁ v₀ v₁ : ℝ) : Convex ℝ (rectSet u₀ u₁ v₀ v₁) :=
  ((convex_Icc _ _).is_linear_preimage Complex.reLm.isLinear).inter
    ((convex_Icc _ _).is_linear_preimage Complex.imLm.isLinear)

theorem isClosed_rectSet (u₀ u₁ v₀ v₁ : ℝ) : IsClosed (rectSet u₀ u₁ v₀ v₁) :=
  (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage Complex.continuous_im)

theorem rectSet_subset {u₀ u₁ v₀ v₁ u₀' u₁' v₀' v₁' : ℝ} (h0 : u₀' ≤ u₀) (h1 : u₁ ≤ u₁')
    (h2 : v₀' ≤ v₀) (h3 : v₁ ≤ v₁') : rectSet u₀ u₁ v₀ v₁ ⊆ rectSet u₀' u₁' v₀' v₁' :=
  fun _ hz => ⟨⟨h0.trans hz.1.1, hz.1.2.trans h1⟩, ⟨h2.trans hz.2.1, hz.2.2.trans h3⟩⟩

theorem gridCell_eq_rectSet (xs ys : ℕ → ℝ) (a b : ℕ) :
    gridCell xs ys a b = rectSet (xs a) (xs (a + 1)) (ys b) (ys (b + 1)) := rfl

/-- A convex combination with positive weights of two points of an interval equals an endpoint
only if both points are that endpoint. -/
theorem eq_of_comb_eq_endpoint {u₀ u₁ x y p a b : ℝ} (hx : x ∈ Icc u₀ u₁) (hy : y ∈ Icc u₀ u₁)
    (hp : p = u₀ ∨ p = u₁) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (h : a * x + b * y = p) : x = p := by
  have e : a * (x - p) + b * (y - p) = 0 := by linear_combination h - p * hab
  rcases hp with rfl | rfl
  · have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.1)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.1)
    have h3 : a * (x - p) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 ha.ne'
    · linarith
  · have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.2)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.2)
    have h3 : a * (p - x) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 ha.ne'
    · linarith

/-- **A closed rectangle minus a corner is convex.** -/
theorem convex_rectSet_diff {u₀ u₁ v₀ v₁ : ℝ} {m : ℂ} (hre : m.re = u₀ ∨ m.re = u₁)
    (him : m.im = v₀ ∨ m.im = v₁) : Convex ℝ (rectSet u₀ u₁ v₀ v₁ \ {m}) := by
  rw [convex_iff_forall_pos]
  intro z hz w hw a b ha hb hab
  refine ⟨(convex_iff_forall_pos.mp (convex_rectSet u₀ u₁ v₀ v₁)) hz.1 hw.1 ha hb hab,
    fun h => hz.2 ?_⟩
  have h' : a • z + b • w = m := h
  have hr := congrArg Complex.re h'
  have hi := congrArg Complex.im h'
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hr hi
  exact Complex.ext (eq_of_comb_eq_endpoint hz.1.1 hw.1.1 hre ha hb hab hr)
    (eq_of_comb_eq_endpoint hz.1.2 hw.1.2 him ha hb hab hi)

theorem mem_rectSet_diff {u₀ u₁ v₀ v₁ x y : ℝ} {m : ℂ} (hx : x ∈ Icc u₀ u₁) (hy : y ∈ Icc v₀ v₁)
    (hne : x ≠ m.re ∨ y ≠ m.im) : (⟨x, y⟩ : ℂ) ∈ rectSet u₀ u₁ v₀ v₁ \ {m} := by
  refine ⟨⟨hx, hy⟩, fun h => ?_⟩
  have h' : (⟨x, y⟩ : ℂ) = m := h
  rcases hne with hne | hne
  · exact hne (congrArg Complex.re h')
  · exact hne (congrArg Complex.im h')

theorem mem_rectSet' {u₀ u₁ v₀ v₁ x y : ℝ} (hx : x ∈ Icc u₀ u₁) (hy : y ∈ Icc v₀ v₁) :
    (⟨x, y⟩ : ℂ) ∈ rectSet u₀ u₁ v₀ v₁ := ⟨hx, hy⟩

/-! ### Labellings over the pieces of a cell -/

/-- Restriction of an equality of labellings to a convex intersection. -/
theorem labelling_eq_on {D₁ D₂ : Set ℂ} (hD : Convex ℝ (D₁ ∩ D₂)) {Λ₁ Λ₂ : Fin S → ℂ → ℂ}
    (h₁ : IsRootLabellingOn Z id D₁ Λ₁) (h₂ : IsRootLabellingOn Z id D₂ Λ₂) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D₁ ∩ D₂) (h : ∀ k, Λ₁ k z₀ = Λ₂ k z₀) : ∀ k, ∀ z ∈ D₁ ∩ D₂, Λ₁ k z = Λ₂ k z :=
  IsRootLabellingOn.eq_of_eq hD.isPreconnected (h₁.mono inter_subset_left)
    (h₂.mono inter_subset_right) hz₀ h

/-- **Labellings over the four punctured quadrants of a cell.** -/
theorem IsRootFamily.exists_quadrant_labellings (hZ : IsRootFamily Z S U)
    {x₀ x₁ y₀ y₁ : ℝ} {m : ℂ} (h0 : x₀ < m.re) (h1 : m.re < x₁) (h2 : y₀ < m.im) (h3 : m.im < y₁)
    (hU : rectSet x₀ x₁ y₀ y₁ \ {m} ⊆ U) {EB EL ER ET : Fin S → ℂ → ℂ}
    (hEB : IsRootLabellingOn Z id (rectSet x₀ x₁ y₀ y₀) EB)
    (hEL : IsRootLabellingOn Z id (rectSet x₀ x₀ y₀ y₁) EL)
    (hER : IsRootLabellingOn Z id (rectSet x₁ x₁ y₀ y₁) ER)
    (hET : IsRootLabellingOn Z id (rectSet x₀ x₁ y₁ y₁) ET)
    (hBL : ∀ k, EL k ⟨x₀, y₀⟩ = EB k ⟨x₀, y₀⟩) (hBR : ∀ k, ER k ⟨x₁, y₀⟩ = EB k ⟨x₁, y₀⟩)
    (hLT : ∀ k, ET k ⟨x₀, y₁⟩ = EL k ⟨x₀, y₁⟩) (π : Equiv.Perm (Fin S))
    (hπ : ∀ k, ER k ⟨x₁, y₁⟩ = ET (π k) ⟨x₁, y₁⟩) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : Fin S → ℂ → ℂ,
      IsRootLabellingOn Z id (rectSet x₀ m.re y₀ m.im \ {m}) Λ₀ ∧
      IsRootLabellingOn Z id (rectSet m.re x₁ y₀ m.im \ {m}) Λ₁ ∧
      IsRootLabellingOn Z id (rectSet m.re x₁ m.im y₁ \ {m}) Λ₂ ∧
      IsRootLabellingOn Z id (rectSet x₀ m.re m.im y₁ \ {m}) Λ₃ ∧
      (∀ k, ∀ z ∈ (rectSet x₀ m.re y₀ m.im \ {m}) ∩ rectSet x₀ x₁ y₀ y₀, Λ₀ k z = EB k z) ∧
      (∀ k, ∀ z ∈ (rectSet x₀ m.re y₀ m.im \ {m}) ∩ rectSet x₀ x₀ y₀ y₁, Λ₀ k z = EL k z) ∧
      (∀ k, ∀ z ∈ (rectSet m.re x₁ y₀ m.im \ {m}) ∩ rectSet x₀ x₁ y₀ y₀, Λ₁ k z = EB k z) ∧
      (∀ k, ∀ z ∈ (rectSet m.re x₁ y₀ m.im \ {m}) ∩ rectSet x₁ x₁ y₀ y₁, Λ₁ k z = ER k z) ∧
      (∀ k, ∀ z ∈ (rectSet m.re x₁ m.im y₁ \ {m}) ∩ rectSet x₁ x₁ y₀ y₁, Λ₂ k z = ER k z) ∧
      (∀ k, ∀ z ∈ (rectSet m.re x₁ m.im y₁ \ {m}) ∩ rectSet x₀ x₁ y₁ y₁, Λ₂ k z = ET (π k) z) ∧
      (∀ k, ∀ z ∈ (rectSet x₀ m.re m.im y₁ \ {m}) ∩ rectSet x₀ x₁ y₁ y₁, Λ₃ k z = ET (π k) z) ∧
      (∀ k, ∀ z ∈ (rectSet x₀ m.re m.im y₁ \ {m}) ∩ rectSet x₀ x₀ y₀ y₁, Λ₃ k z = EL (π k) z) ∧
      (∀ k, ∀ z ∈ (rectSet x₀ m.re y₀ m.im \ {m}) ∩ (rectSet m.re x₁ y₀ m.im \ {m}),
        Λ₁ k z = Λ₀ k z) ∧
      (∀ k, ∀ z ∈ (rectSet m.re x₁ y₀ m.im \ {m}) ∩ (rectSet m.re x₁ m.im y₁ \ {m}),
        Λ₂ k z = Λ₁ k z) ∧
      (∀ k, ∀ z ∈ (rectSet m.re x₁ m.im y₁ \ {m}) ∩ (rectSet x₀ m.re m.im y₁ \ {m}),
        Λ₃ k z = Λ₂ k z) ∧
      (∀ k, ∀ z ∈ (rectSet x₀ m.re m.im y₁ \ {m}) ∩ (rectSet x₀ m.re y₀ m.im \ {m}),
        Λ₃ k z = Λ₀ (π k) z) := by
  -- The pieces.
  set Q₀ := rectSet x₀ m.re y₀ m.im \ {m}
  set Q₁ := rectSet m.re x₁ y₀ m.im \ {m}
  set Q₂ := rectSet m.re x₁ m.im y₁ \ {m}
  set Q₃ := rectSet x₀ m.re m.im y₁ \ {m}
  set B := rectSet x₀ x₁ y₀ y₀
  set Lf := rectSet x₀ x₀ y₀ y₁
  set R := rectSet x₁ x₁ y₀ y₁
  set T := rectSet x₀ x₁ y₁ y₁
  have cQ₀ : Convex ℝ Q₀ := convex_rectSet_diff (Or.inr rfl) (Or.inr rfl)
  have cQ₁ : Convex ℝ Q₁ := convex_rectSet_diff (Or.inl rfl) (Or.inr rfl)
  have cQ₂ : Convex ℝ Q₂ := convex_rectSet_diff (Or.inl rfl) (Or.inl rfl)
  have cQ₃ : Convex ℝ Q₃ := convex_rectSet_diff (Or.inr rfl) (Or.inl rfl)
  have cB := convex_rectSet x₀ x₁ y₀ y₀
  have cLf := convex_rectSet x₀ x₀ y₀ y₁
  have cR := convex_rectSet x₁ x₁ y₀ y₁
  have cT := convex_rectSet x₀ x₁ y₁ y₁
  have sub : ∀ {u₀ u₁ v₀ v₁ : ℝ}, x₀ ≤ u₀ → u₁ ≤ x₁ → y₀ ≤ v₀ → v₁ ≤ y₁ →
      rectSet u₀ u₁ v₀ v₁ \ {m} ⊆ U := fun a b c d z hz =>
    hU ⟨rectSet_subset a b c d hz.1, hz.2⟩
  -- The marked points.
  have hv0 : (⟨x₀, y₀⟩ : ℂ) ∈ Q₀ := mem_rectSet_diff ⟨le_rfl, h0.le⟩ ⟨le_rfl, h2.le⟩
    (Or.inl h0.ne)
  have hb0 : (⟨m.re, y₀⟩ : ℂ) ∈ Q₀ := mem_rectSet_diff ⟨h0.le, le_rfl⟩ ⟨le_rfl, h2.le⟩
    (Or.inr h2.ne)
  have hb1 : (⟨m.re, y₀⟩ : ℂ) ∈ Q₁ := mem_rectSet_diff ⟨le_rfl, h1.le⟩ ⟨le_rfl, h2.le⟩
    (Or.inr h2.ne)
  have hv1 : (⟨x₁, y₀⟩ : ℂ) ∈ Q₁ := mem_rectSet_diff ⟨h1.le, le_rfl⟩ ⟨le_rfl, h2.le⟩
    (Or.inl h1.ne')
  have hr1 : (⟨x₁, m.im⟩ : ℂ) ∈ Q₁ := mem_rectSet_diff ⟨h1.le, le_rfl⟩ ⟨h2.le, le_rfl⟩
    (Or.inl h1.ne')
  have hr2 : (⟨x₁, m.im⟩ : ℂ) ∈ Q₂ := mem_rectSet_diff ⟨h1.le, le_rfl⟩ ⟨le_rfl, h3.le⟩
    (Or.inl h1.ne')
  have hv2 : (⟨x₁, y₁⟩ : ℂ) ∈ Q₂ := mem_rectSet_diff ⟨h1.le, le_rfl⟩ ⟨h3.le, le_rfl⟩
    (Or.inl h1.ne')
  have ht2 : (⟨m.re, y₁⟩ : ℂ) ∈ Q₂ := mem_rectSet_diff ⟨le_rfl, h1.le⟩ ⟨h3.le, le_rfl⟩
    (Or.inr h3.ne')
  have ht3 : (⟨m.re, y₁⟩ : ℂ) ∈ Q₃ := mem_rectSet_diff ⟨h0.le, le_rfl⟩ ⟨h3.le, le_rfl⟩
    (Or.inr h3.ne')
  have hv3 : (⟨x₀, y₁⟩ : ℂ) ∈ Q₃ := mem_rectSet_diff ⟨le_rfl, h0.le⟩ ⟨h3.le, le_rfl⟩
    (Or.inl h0.ne)
  have hl3 : (⟨x₀, m.im⟩ : ℂ) ∈ Q₃ := mem_rectSet_diff ⟨le_rfl, h0.le⟩ ⟨le_rfl, h3.le⟩
    (Or.inl h0.ne)
  have hl0 : (⟨x₀, m.im⟩ : ℂ) ∈ Q₀ := mem_rectSet_diff ⟨le_rfl, h0.le⟩ ⟨h2.le, le_rfl⟩
    (Or.inl h0.ne)
  have hv0B : (⟨x₀, y₀⟩ : ℂ) ∈ B := mem_rectSet' ⟨le_rfl, by linarith⟩ ⟨le_rfl, le_rfl⟩
  have hv0L : (⟨x₀, y₀⟩ : ℂ) ∈ Lf := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨le_rfl, by linarith⟩
  have hbB : (⟨m.re, y₀⟩ : ℂ) ∈ B := mem_rectSet' ⟨h0.le, h1.le⟩ ⟨le_rfl, le_rfl⟩
  have hv1B : (⟨x₁, y₀⟩ : ℂ) ∈ B := mem_rectSet' ⟨by linarith, le_rfl⟩ ⟨le_rfl, le_rfl⟩
  have hv1R : (⟨x₁, y₀⟩ : ℂ) ∈ R := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨le_rfl, by linarith⟩
  have hrR : (⟨x₁, m.im⟩ : ℂ) ∈ R := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨h2.le, h3.le⟩
  have hv2R : (⟨x₁, y₁⟩ : ℂ) ∈ R := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨by linarith, le_rfl⟩
  have hv2T : (⟨x₁, y₁⟩ : ℂ) ∈ T := mem_rectSet' ⟨by linarith, le_rfl⟩ ⟨le_rfl, le_rfl⟩
  have htT : (⟨m.re, y₁⟩ : ℂ) ∈ T := mem_rectSet' ⟨h0.le, h1.le⟩ ⟨le_rfl, le_rfl⟩
  have hv3T : (⟨x₀, y₁⟩ : ℂ) ∈ T := mem_rectSet' ⟨le_rfl, by linarith⟩ ⟨le_rfl, le_rfl⟩
  have hv3L : (⟨x₀, y₁⟩ : ℂ) ∈ Lf := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨by linarith, le_rfl⟩
  have hlL : (⟨x₀, m.im⟩ : ℂ) ∈ Lf := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨h2.le, h3.le⟩
  -- The four labellings.
  obtain ⟨Λ₀, hΛ₀, hΛ₀0⟩ := hZ.exists_convex_labelling cQ₀ (sub le_rfl h1.le le_rfl h3.le) hv0
    (hEB.isFibreLabel hv0B)
  obtain ⟨Λ₁, hΛ₁, hΛ₁0⟩ := hZ.exists_convex_labelling cQ₁ (sub h0.le le_rfl le_rfl h3.le) hb1
    (hΛ₀.isFibreLabel hb0)
  obtain ⟨Λ₂, hΛ₂, hΛ₂0⟩ := hZ.exists_convex_labelling cQ₂ (sub h0.le le_rfl h2.le le_rfl) hr2
    (hΛ₁.isFibreLabel hr1)
  obtain ⟨Λ₃, hΛ₃, hΛ₃0⟩ := hZ.exists_convex_labelling cQ₃ (sub le_rfl h1.le h2.le le_rfl) ht3
    (hΛ₂.isFibreLabel ht2)
  -- The comparisons, one connected intersection at a time.
  have ea := labelling_eq_on (cQ₀.inter cB) hΛ₀ hEB ⟨hv0, hv0B⟩ hΛ₀0
  have eb := labelling_eq_on (cQ₀.inter cLf) hΛ₀ hEL ⟨hv0, hv0L⟩ fun k => by
    rw [hΛ₀0, hBL]
  have ec := labelling_eq_on (cQ₁.inter cQ₀) hΛ₁ hΛ₀ ⟨hb1, hb0⟩ hΛ₁0
  have ed := labelling_eq_on (cQ₁.inter cB) hΛ₁ hEB ⟨hb1, hbB⟩ fun k => by
    rw [hΛ₁0, ea k _ ⟨hb0, hbB⟩]
  have ee := labelling_eq_on (cQ₁.inter cR) hΛ₁ hER ⟨hv1, hv1R⟩ fun k => by
    rw [ed k _ ⟨hv1, hv1B⟩, hBR]
  have ef := labelling_eq_on (cQ₂.inter cQ₁) hΛ₂ hΛ₁ ⟨hr2, hr1⟩ hΛ₂0
  have eg := labelling_eq_on (cQ₂.inter cR) hΛ₂ hER ⟨hr2, hrR⟩ fun k => by
    rw [hΛ₂0, ee k _ ⟨hr1, hrR⟩]
  have hETπ : IsRootLabellingOn Z id T fun k z => ET (π k) z := hET.relabel π
  have eh := labelling_eq_on (cQ₂.inter cT) hΛ₂ hETπ ⟨hv2, hv2T⟩ fun k => by
    rw [eg k _ ⟨hv2, hv2R⟩, hπ]
  have ei := labelling_eq_on (cQ₃.inter cQ₂) hΛ₃ hΛ₂ ⟨ht3, ht2⟩ hΛ₃0
  have ej := labelling_eq_on (cQ₃.inter cT) hΛ₃ hETπ ⟨ht3, htT⟩ fun k => by
    rw [hΛ₃0, eh k _ ⟨ht2, htT⟩]
  have hELπ : IsRootLabellingOn Z id Lf fun k z => EL (π k) z := hEL.relabel π
  have ek := labelling_eq_on (cQ₃.inter cLf) hΛ₃ hELπ ⟨hv3, hv3L⟩ fun k => by
    rw [ej k _ ⟨hv3, hv3T⟩]; exact hLT (π k)
  have hΛ₀π : IsRootLabellingOn Z id Q₀ fun k z => Λ₀ (π k) z := hΛ₀.relabel π
  have el := labelling_eq_on (cQ₃.inter cQ₀) hΛ₃ hΛ₀π ⟨hl3, hl0⟩ fun k => by
    rw [ek k _ ⟨hl3, hlL⟩]; exact (eb (π k) _ ⟨hl0, hlL⟩).symm
  refine ⟨Λ₀, Λ₁, Λ₂, Λ₃, hΛ₀, hΛ₁, hΛ₂, hΛ₃, ea, eb, ed, ee, eg, eh, ej, ek,
    fun k z hz => ec k z ⟨hz.2, hz.1⟩, fun k z hz => ef k z ⟨hz.2, hz.1⟩,
    fun k z hz => ei k z ⟨hz.2, hz.1⟩, el⟩

/-- **A labelling over an unpunctured rectangle** agreeing with the labellings of its sides. -/
theorem IsRootFamily.exists_rect_labelling (hZ : IsRootFamily Z S U)
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (hU : rectSet x₀ x₁ y₀ y₁ ⊆ U)
    {EB EL ER ET : Fin S → ℂ → ℂ}
    (hEB : IsRootLabellingOn Z id (rectSet x₀ x₁ y₀ y₀) EB)
    (hEL : IsRootLabellingOn Z id (rectSet x₀ x₀ y₀ y₁) EL)
    (hER : IsRootLabellingOn Z id (rectSet x₁ x₁ y₀ y₁) ER)
    (hET : IsRootLabellingOn Z id (rectSet x₀ x₁ y₁ y₁) ET)
    (hBL : ∀ k, EL k ⟨x₀, y₀⟩ = EB k ⟨x₀, y₀⟩) (hBR : ∀ k, ER k ⟨x₁, y₀⟩ = EB k ⟨x₁, y₀⟩)
    (hLT : ∀ k, ET k ⟨x₀, y₁⟩ = EL k ⟨x₀, y₁⟩) :
    ∃ Λ : Fin S → ℂ → ℂ, IsRootLabellingOn Z id (rectSet x₀ x₁ y₀ y₁) Λ ∧
      (∀ k, ∀ z ∈ rectSet x₀ x₁ y₀ y₁ ∩ rectSet x₀ x₁ y₀ y₀, Λ k z = EB k z) ∧
      (∀ k, ∀ z ∈ rectSet x₀ x₁ y₀ y₁ ∩ rectSet x₀ x₀ y₀ y₁, Λ k z = EL k z) ∧
      (∀ k, ∀ z ∈ rectSet x₀ x₁ y₀ y₁ ∩ rectSet x₁ x₁ y₀ y₁, Λ k z = ER k z) ∧
      (∀ k, ∀ z ∈ rectSet x₀ x₁ y₀ y₁ ∩ rectSet x₀ x₁ y₁ y₁, Λ k z = ET k z) := by
  have cC := convex_rectSet x₀ x₁ y₀ y₁
  have hv0 : (⟨x₀, y₀⟩ : ℂ) ∈ rectSet x₀ x₁ y₀ y₁ := mem_rectSet' ⟨le_rfl, hx⟩ ⟨le_rfl, hy⟩
  have hv1 : (⟨x₁, y₀⟩ : ℂ) ∈ rectSet x₀ x₁ y₀ y₁ := mem_rectSet' ⟨hx, le_rfl⟩ ⟨le_rfl, hy⟩
  have hv3 : (⟨x₀, y₁⟩ : ℂ) ∈ rectSet x₀ x₁ y₀ y₁ := mem_rectSet' ⟨le_rfl, hx⟩ ⟨hy, le_rfl⟩
  have hv0B : (⟨x₀, y₀⟩ : ℂ) ∈ rectSet x₀ x₁ y₀ y₀ := mem_rectSet' ⟨le_rfl, hx⟩ ⟨le_rfl, le_rfl⟩
  have hv0L : (⟨x₀, y₀⟩ : ℂ) ∈ rectSet x₀ x₀ y₀ y₁ := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨le_rfl, hy⟩
  have hv1B : (⟨x₁, y₀⟩ : ℂ) ∈ rectSet x₀ x₁ y₀ y₀ := mem_rectSet' ⟨hx, le_rfl⟩ ⟨le_rfl, le_rfl⟩
  have hv1R : (⟨x₁, y₀⟩ : ℂ) ∈ rectSet x₁ x₁ y₀ y₁ := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨le_rfl, hy⟩
  have hv3L : (⟨x₀, y₁⟩ : ℂ) ∈ rectSet x₀ x₀ y₀ y₁ := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨hy, le_rfl⟩
  have hv3T : (⟨x₀, y₁⟩ : ℂ) ∈ rectSet x₀ x₁ y₁ y₁ := mem_rectSet' ⟨le_rfl, hx⟩ ⟨le_rfl, le_rfl⟩
  obtain ⟨Λ, hΛ, hΛ0⟩ := hZ.exists_convex_labelling cC hU hv0 (hEB.isFibreLabel hv0B)
  have ea := labelling_eq_on (cC.inter (convex_rectSet _ _ _ _)) hΛ hEB ⟨hv0, hv0B⟩ hΛ0
  have eb := labelling_eq_on (cC.inter (convex_rectSet _ _ _ _)) hΛ hEL ⟨hv0, hv0L⟩ fun k => by
    rw [hΛ0, hBL]
  have ec := labelling_eq_on (cC.inter (convex_rectSet _ _ _ _)) hΛ hER ⟨hv1, hv1R⟩ fun k => by
    rw [ea k _ ⟨hv1, hv1B⟩, hBR]
  have ed := labelling_eq_on (cC.inter (convex_rectSet _ _ _ _)) hΛ hET ⟨hv3, hv3T⟩ fun k => by
    rw [eb k _ ⟨hv3, hv3L⟩, hLT]
  exact ⟨Λ, hΛ, ea, eb, ec, ed⟩

end OnLeConjecture.Analytic
