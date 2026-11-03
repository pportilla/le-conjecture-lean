/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DifferentialTopology.RationalCurveHomology
public import OnLeConjecture.Analytic.PlaneMilnorPolydisc

/-!
# Rational homology of a branched covering of a square

Let `p : E → ℂ` be continuous, let `η > 0`, and let `A ⊆ E` lie over the closed square
`closedSquare η = {x | max |Re x| |Im x| ≤ η}`. For an open set `W ⊆ ℂ`, the part of `A`
over `W` is `A ∩ p⁻¹ W`. Let `B` be a finite set of points of the open square, let
`d : ℕ`, and let `n : ℂ → ℕ`. Assume the following.

* For every open rectangle `W` meeting the closed square and containing no point of `B`,
  the part of `A` over `W` has the rational homology of `d` points.
* For every `b ∈ B` there is `δ > 0` such that, for every open rectangle `W` with
  `b ∈ W ⊆ ball b δ`, the part of `A` over `W` has the rational homology of `n b` points.

Then `A` has curve homology with Euler characteristic `d − ∑_{b ∈ B} (d − n b)`
(`hasCurveRatHomology_of_branchedSquare`), a count of Riemann–Hurwitz type.

The proof is by induction on the number of points of `B` in an open rectangle meeting the
closed square. An open rectangle is cut along a vertical or horizontal line into two
overlapping open rectangles whose overlap contains no point of `B`, and the Mayer–Vietoris
count `HasCurveRatHomology.mayerVietoris` is applied to the parts of `A` over the two
pieces. A rectangle containing two points of `B` is cut along a line separating them. A
rectangle containing exactly one point `b` of `B` is cut down by four cuts, each removing
a piece without points of `B`, to a box around `b` contained in the ball given by the
second assumption.
-/

@[expose] public noncomputable section

open Set Metric OnLeConjecture.Analytic

namespace OnLeConjecture.DifferentialTopology

/-- Open rectangle with real parts in `(a₁, a₂)` and imaginary parts in `(c₁, c₂)`. -/
def openRect (a₁ a₂ c₁ c₂ : ℝ) : Set ℂ := {x | a₁ < x.re ∧ x.re < a₂ ∧ c₁ < x.im ∧ x.im < c₂}

section Rect

variable {a₁ a₂ c₁ c₂ : ℝ}

theorem mem_openRect {x : ℂ} :
    x ∈ openRect a₁ a₂ c₁ c₂ ↔ a₁ < x.re ∧ x.re < a₂ ∧ c₁ < x.im ∧ x.im < c₂ :=
  Iff.rfl

theorem mk_mem_openRect {s t : ℝ} (h₁ : a₁ < s) (h₂ : s < a₂) (h₃ : c₁ < t) (h₄ : t < c₂) :
    (⟨s, t⟩ : ℂ) ∈ openRect a₁ a₂ c₁ c₂ :=
  ⟨h₁, h₂, h₃, h₄⟩

theorem isOpen_openRect (a₁ a₂ c₁ c₂ : ℝ) : IsOpen (openRect a₁ a₂ c₁ c₂) :=
  (isOpen_lt continuous_const Complex.continuous_re).and <|
    (isOpen_lt Complex.continuous_re continuous_const).and <|
      (isOpen_lt continuous_const Complex.continuous_im).and
        (isOpen_lt Complex.continuous_im continuous_const)

theorem openRect_mono {a₁' a₂' c₁' c₂' : ℝ} (ha₁ : a₁ ≤ a₁') (ha₂ : a₂' ≤ a₂) (hc₁ : c₁ ≤ c₁')
    (hc₂ : c₂' ≤ c₂) : openRect a₁' a₂' c₁' c₂' ⊆ openRect a₁ a₂ c₁ c₂ :=
  fun _ hx => ⟨ha₁.trans_lt hx.1, hx.2.1.trans_le ha₂, hc₁.trans_lt hx.2.2.1,
    hx.2.2.2.trans_le hc₂⟩

theorem openRect_union_re {u v : ℝ} (hu : a₁ ≤ u) (huv : u < v) (hv : v ≤ a₂) :
    openRect a₁ v c₁ c₂ ∪ openRect u a₂ c₁ c₂ = openRect a₁ a₂ c₁ c₂ := by
  ext x
  simp only [mem_union, mem_openRect]
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.1.trans_le hv, h.2.2⟩
    · exact ⟨hu.trans_lt h.1, h.2⟩
  · rintro ⟨h₁, h₂, h₃⟩
    rcases lt_or_ge x.re v with h | h
    · exact Or.inl ⟨h₁, h, h₃⟩
    · exact Or.inr ⟨huv.trans_le h, h₂, h₃⟩

theorem openRect_inter_re {u v : ℝ} (hu : a₁ ≤ u) (hv : v ≤ a₂) :
    openRect a₁ v c₁ c₂ ∩ openRect u a₂ c₁ c₂ = openRect u v c₁ c₂ := by
  ext x
  simp only [mem_inter_iff, mem_openRect]
  constructor
  · rintro ⟨⟨_, h₂, h₃⟩, h₄, _⟩
    exact ⟨h₄, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨hu.trans_lt h₁, h₂, h₃⟩, h₁, h₂.trans_le hv, h₃⟩

theorem openRect_union_im {u v : ℝ} (hu : c₁ ≤ u) (huv : u < v) (hv : v ≤ c₂) :
    openRect a₁ a₂ c₁ v ∪ openRect a₁ a₂ u c₂ = openRect a₁ a₂ c₁ c₂ := by
  ext x
  simp only [mem_union, mem_openRect]
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans_le hv⟩
    · exact ⟨h.1, h.2.1, hu.trans_lt h.2.2.1, h.2.2.2⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    rcases lt_or_ge x.im v with h | h
    · exact Or.inl ⟨h₁, h₂, h₃, h⟩
    · exact Or.inr ⟨h₁, h₂, huv.trans_le h, h₄⟩

theorem openRect_inter_im {u v : ℝ} (hu : c₁ ≤ u) (hv : v ≤ c₂) :
    openRect a₁ a₂ c₁ v ∩ openRect a₁ a₂ u c₂ = openRect a₁ a₂ u v := by
  ext x
  simp only [mem_inter_iff, mem_openRect]
  constructor
  · rintro ⟨⟨h₁, h₂, _, h₄⟩, _, _, h₇, _⟩
    exact ⟨h₁, h₂, h₇, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂, hu.trans_lt h₃, h₄⟩, h₁, h₂, h₃, h₄.trans_le hv⟩

end Rect

theorem abs_re_le_squareNorm (x : ℂ) : |x.re| ≤ squareNorm x :=
  le_max_left _ _

theorem abs_im_le_squareNorm (x : ℂ) : |x.im| ≤ squareNorm x :=
  le_max_right _ _

theorem mk_mem_closedSquare {η s t : ℝ} (hs : |s| ≤ η) (ht : |t| ≤ η) :
    (⟨s, t⟩ : ℂ) ∈ closedSquare η :=
  max_le hs ht

section Euler

variable {B : Finset ℂ} {d : ℕ} {n : ℂ → ℕ}

/-- The Euler characteristic `d − ∑ (d − n b)`, where the sum runs over the points `b` of
`B` lying in `W`. -/
def branchedEuler (B : Finset ℂ) (d : ℕ) (n : ℂ → ℕ) (W : Set ℂ) : ℤ :=
  d - ∑ b ∈ B, W.indicator (fun b => (d : ℤ) - n b) b

theorem branchedEuler_eq_of_forall_notMem {W : Set ℂ} (h : ∀ b ∈ B, b ∉ W) :
    branchedEuler B d n W = d := by
  rw [branchedEuler, Finset.sum_eq_zero fun b hb => indicator_of_notMem (h b hb) _, sub_zero]

theorem branchedEuler_eq_of_forall_mem {W : Set ℂ} (h : ∀ b ∈ B, b ∈ W) :
    branchedEuler B d n W = (d : ℤ) - ∑ b ∈ B, ((d : ℤ) - n b) := by
  rw [branchedEuler, Finset.sum_congr rfl fun b hb => indicator_of_mem (h b hb) _]

theorem branchedEuler_eq_of_unique {W : Set ℂ} {b : ℂ} (hb : b ∈ B) (hbW : b ∈ W)
    (h : ∀ c ∈ B, c ∈ W → c = b) : branchedEuler B d n W = n b := by
  rw [branchedEuler, Finset.sum_eq_single_of_mem b hb fun c hc hcb =>
    indicator_of_notMem (fun hcW => hcb (h c hc hcW)) _, indicator_of_mem hbW]
  ring

theorem branchedEuler_union {W₁ W₂ : Set ℂ} (h : ∀ b ∈ B, b ∉ W₁ ∩ W₂) :
    branchedEuler B d n (W₁ ∪ W₂) = branchedEuler B d n W₁ + branchedEuler B d n W₂ - d := by
  simp only [branchedEuler]
  rw [Finset.sum_congr rfl fun b hb => indicator_union_of_notMem_inter (h b hb) _,
    Finset.sum_add_distrib]
  ring

end Euler

section Subspace

variable {E : Type} [TopologicalSpace E]

/-- If `S ⊆ T` and `U` is the set of points of the subspace `T` lying in `S`, then `U` is
homeomorphic to `S`. -/
def homeomorphOfSubtypeMemIff {S T : Set E} {U : Set T} (hST : S ⊆ T)
    (hU : ∀ t : T, t ∈ U ↔ (t : E) ∈ S) : U ≃ₜ S where
  toFun x := ⟨x.1.1, (hU x.1).1 x.2⟩
  invFun y := ⟨⟨y.1, hST y.2⟩, (hU _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable {p : E → ℂ} {A : Set E}

/-- **Mayer–Vietoris count over two open sets.** If the parts of `A` over open sets `W₁`
and `W₂` have curve homology with Euler characteristics `x` and `y`, and the part of `A`
over `W₁ ∩ W₂` has the homology of `k` points, then the part of `A` over `W₁ ∪ W₂` has
curve homology with Euler characteristic `x + y − k`. -/
theorem hasCurveRatHomology_inter_preimage_union (hp : Continuous p) {W₁ W₂ : Set ℂ}
    (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) {x y : ℤ} {k : ℕ}
    (h₁ : HasCurveRatHomology ↥(A ∩ p ⁻¹' W₁) x)
    (h₂ : HasCurveRatHomology ↥(A ∩ p ⁻¹' W₂) y)
    (h₁₂ : HasDiscreteRatHomology ↥(A ∩ p ⁻¹' (W₁ ∩ W₂)) k) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' (W₁ ∪ W₂)) (x + y - k) := by
  have hpT : Continuous fun t : ↥(A ∩ p ⁻¹' (W₁ ∪ W₂)) => p t :=
    hp.comp continuous_subtype_val
  refine HasCurveRatHomology.mayerVietoris (X := ↥(A ∩ p ⁻¹' (W₁ ∪ W₂)))
    ((fun t => p t) ⁻¹' W₁) ((fun t => p t) ⁻¹' W₂) (hW₁.preimage hpT) (hW₂.preimage hpT)
    (eq_univ_of_forall fun t => t.2.2) ?_ ?_ ?_
  · exact h₁.of_homeomorph (homeomorphOfSubtypeMemIff (S := A ∩ p ⁻¹' W₁)
      (fun z hz => ⟨hz.1, Or.inl hz.2⟩) fun t => ⟨fun h => ⟨t.2.1, h⟩, fun h => h.2⟩)
  · exact h₂.of_homeomorph (homeomorphOfSubtypeMemIff (S := A ∩ p ⁻¹' W₂)
      (fun z hz => ⟨hz.1, Or.inr hz.2⟩) fun t => ⟨fun h => ⟨t.2.1, h⟩, fun h => h.2⟩)
  · exact h₁₂.of_homeomorph (homeomorphOfSubtypeMemIff (S := A ∩ p ⁻¹' (W₁ ∩ W₂))
      (fun z hz => ⟨hz.1, Or.inl hz.2.1⟩) fun t => ⟨fun h => ⟨t.2.1, h⟩, fun h => h.2⟩)

/-- Mayer–Vietoris count for an open rectangle cut along the vertical strip
`u < Re < v`. -/
theorem hasCurveRatHomology_split_re (hp : Continuous p) {a₁ a₂ u v c₁ c₂ : ℝ}
    (hu : a₁ ≤ u) (huv : u < v) (hv : v ≤ a₂) {x y : ℤ} {k : ℕ}
    (h₁ : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ v c₁ c₂) x)
    (h₂ : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect u a₂ c₁ c₂) y)
    (h₁₂ : HasDiscreteRatHomology ↥(A ∩ p ⁻¹' openRect u v c₁ c₂) k) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) (x + y - k) := by
  rw [← openRect_union_re hu huv hv]
  exact hasCurveRatHomology_inter_preimage_union hp (isOpen_openRect _ _ _ _)
    (isOpen_openRect _ _ _ _) h₁ h₂ (by rwa [openRect_inter_re hu hv])

/-- Mayer–Vietoris count for an open rectangle cut along the horizontal strip
`u < Im < v`. -/
theorem hasCurveRatHomology_split_im (hp : Continuous p) {a₁ a₂ u v c₁ c₂ : ℝ}
    (hu : c₁ ≤ u) (huv : u < v) (hv : v ≤ c₂) {x y : ℤ} {k : ℕ}
    (h₁ : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ v) x)
    (h₂ : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ u c₂) y)
    (h₁₂ : HasDiscreteRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ u v) k) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) (x + y - k) := by
  rw [← openRect_union_im hu huv hv]
  exact hasCurveRatHomology_inter_preimage_union hp (isOpen_openRect _ _ _ _)
    (isOpen_openRect _ _ _ _) h₁ h₂ (by rwa [openRect_inter_im hu hv])

end Subspace

section Induction

variable {E : Type} [TopologicalSpace E] {p : E → ℂ} {A : Set E} {η : ℝ} {B : Finset ℂ}
  {d : ℕ} (hp : Continuous p)
  (h0 : ∀ a₁ a₂ c₁ c₂ : ℝ, (openRect a₁ a₂ c₁ c₂ ∩ closedSquare η).Nonempty →
    (∀ b ∈ B, b ∉ openRect a₁ a₂ c₁ c₂) →
    HasDiscreteRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) d)

include hp h0

/-- Removing the part of an open rectangle to the right of `Re = Re b + r`, when `b` is
the only point of `B` in the rectangle, does not change the curve homology. -/
theorem hasCurveRatHomology_trim_re_right {a₁ a₂ c₁ c₂ r : ℝ} {b : ℂ}
    (hbW : b ∈ openRect a₁ a₂ c₁ c₂) (huniq : ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c = b)
    (hr : 0 < r) (hbr : squareNorm b + r ≤ η) {x : ℤ}
    (h : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ (min a₂ (b.re + r)) c₁ c₂) x) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) x := by
  rcases le_or_gt a₂ (b.re + r) with ha | ha
  · rwa [min_eq_left ha] at h
  rw [min_eq_right ha.le] at h
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbW
  have hre := abs_re_le_squareNorm b
  have him := abs_im_le_squareNorm b
  have hQ : (⟨b.re + 3 * r / 4, b.im⟩ : ℂ) ∈ closedSquare η :=
    mk_mem_closedSquare (abs_le.2 ⟨by linarith [neg_abs_le b.re], by
      linarith [le_abs_self b.re]⟩) (by linarith)
  have hfree : ∀ v ≤ a₂, ∀ c ∈ B, c ∉ openRect (b.re + r / 2) v c₁ c₂ := by
    intro v hv c hc hcW
    have hcb := huniq c hc ⟨by linarith [hcW.1], by linarith [hcW.2.1], hcW.2.2⟩
    rw [hcb] at hcW
    linarith [hcW.1]
  have hsplit := hasCurveRatHomology_split_re hp (u := b.re + r / 2) (v := b.re + r)
    (by linarith) (by linarith) ha.le h
    (h0 _ _ _ _ ⟨_, mk_mem_openRect (by linarith) (by linarith) hb₃ hb₄, hQ⟩
      (hfree _ le_rfl)).toCurve
    (h0 _ _ _ _ ⟨_, mk_mem_openRect (by linarith) (by linarith) hb₃ hb₄, hQ⟩
      (hfree _ ha.le))
  rwa [add_sub_cancel_right] at hsplit

/-- Removing the part of an open rectangle to the left of `Re = Re b − r`, when `b` is
the only point of `B` in the rectangle, does not change the curve homology. -/
theorem hasCurveRatHomology_trim_re_left {a₁ a₂ c₁ c₂ r : ℝ} {b : ℂ}
    (hbW : b ∈ openRect a₁ a₂ c₁ c₂) (huniq : ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c = b)
    (hr : 0 < r) (hbr : squareNorm b + r ≤ η) {x : ℤ}
    (h : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect (max a₁ (b.re - r)) a₂ c₁ c₂) x) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) x := by
  rcases le_or_gt (b.re - r) a₁ with ha | ha
  · rwa [max_eq_left ha] at h
  rw [max_eq_right ha.le] at h
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbW
  have hre := abs_re_le_squareNorm b
  have him := abs_im_le_squareNorm b
  have hQ : (⟨b.re - 3 * r / 4, b.im⟩ : ℂ) ∈ closedSquare η :=
    mk_mem_closedSquare (abs_le.2 ⟨by linarith [neg_abs_le b.re], by
      linarith [le_abs_self b.re]⟩) (by linarith)
  have hfree : ∀ u, a₁ ≤ u → ∀ c ∈ B, c ∉ openRect u (b.re - r / 2) c₁ c₂ := by
    intro u hu c hc hcW
    have hcb := huniq c hc ⟨by linarith [hcW.1], by linarith [hcW.2.1], hcW.2.2⟩
    rw [hcb] at hcW
    linarith [hcW.2.1]
  have hsplit := hasCurveRatHomology_split_re hp (u := b.re - r) (v := b.re - r / 2)
    ha.le (by linarith) (by linarith)
    (h0 _ _ _ _ ⟨_, mk_mem_openRect (by linarith) (by linarith) hb₃ hb₄, hQ⟩
      (hfree _ le_rfl)).toCurve h
    (h0 _ _ _ _ ⟨_, mk_mem_openRect (by linarith) (by linarith) hb₃ hb₄, hQ⟩
      (hfree _ ha.le))
  rwa [add_sub_cancel_left] at hsplit

/-- Removing the part of an open rectangle above `Im = Im b + r`, when `b` is the only
point of `B` in the rectangle, does not change the curve homology. -/
theorem hasCurveRatHomology_trim_im_top {a₁ a₂ c₁ c₂ r : ℝ} {b : ℂ}
    (hbW : b ∈ openRect a₁ a₂ c₁ c₂) (huniq : ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c = b)
    (hr : 0 < r) (hbr : squareNorm b + r ≤ η) {x : ℤ}
    (h : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ (min c₂ (b.im + r))) x) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) x := by
  rcases le_or_gt c₂ (b.im + r) with hc | hc
  · rwa [min_eq_left hc] at h
  rw [min_eq_right hc.le] at h
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbW
  have hre := abs_re_le_squareNorm b
  have him := abs_im_le_squareNorm b
  have hQ : (⟨b.re, b.im + 3 * r / 4⟩ : ℂ) ∈ closedSquare η :=
    mk_mem_closedSquare (by linarith) (abs_le.2 ⟨by linarith [neg_abs_le b.im], by
      linarith [le_abs_self b.im]⟩)
  have hfree : ∀ v ≤ c₂, ∀ c ∈ B, c ∉ openRect a₁ a₂ (b.im + r / 2) v := by
    intro v hv c hc hcW
    have hcb := huniq c hc
      ⟨hcW.1, hcW.2.1, by linarith [hcW.2.2.1], by linarith [hcW.2.2.2]⟩
    rw [hcb] at hcW
    linarith [hcW.2.2.1]
  have hsplit := hasCurveRatHomology_split_im hp (u := b.im + r / 2) (v := b.im + r)
    (by linarith) (by linarith) hc.le h
    (h0 _ _ _ _ ⟨_, mk_mem_openRect hb₁ hb₂ (by linarith) (by linarith), hQ⟩
      (hfree _ le_rfl)).toCurve
    (h0 _ _ _ _ ⟨_, mk_mem_openRect hb₁ hb₂ (by linarith) (by linarith), hQ⟩
      (hfree _ hc.le))
  rwa [add_sub_cancel_right] at hsplit

/-- Removing the part of an open rectangle below `Im = Im b − r`, when `b` is the only
point of `B` in the rectangle, does not change the curve homology. -/
theorem hasCurveRatHomology_trim_im_bottom {a₁ a₂ c₁ c₂ r : ℝ} {b : ℂ}
    (hbW : b ∈ openRect a₁ a₂ c₁ c₂) (huniq : ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c = b)
    (hr : 0 < r) (hbr : squareNorm b + r ≤ η) {x : ℤ}
    (h : HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ (max c₁ (b.im - r)) c₂) x) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) x := by
  rcases le_or_gt (b.im - r) c₁ with hc | hc
  · rwa [max_eq_left hc] at h
  rw [max_eq_right hc.le] at h
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbW
  have hre := abs_re_le_squareNorm b
  have him := abs_im_le_squareNorm b
  have hQ : (⟨b.re, b.im - 3 * r / 4⟩ : ℂ) ∈ closedSquare η :=
    mk_mem_closedSquare (by linarith) (abs_le.2 ⟨by linarith [neg_abs_le b.im], by
      linarith [le_abs_self b.im]⟩)
  have hfree : ∀ u, c₁ ≤ u → ∀ c ∈ B, c ∉ openRect a₁ a₂ u (b.im - r / 2) := by
    intro u hu c hc hcW
    have hcb := huniq c hc
      ⟨hcW.1, hcW.2.1, by linarith [hcW.2.2.1], by linarith [hcW.2.2.2]⟩
    rw [hcb] at hcW
    linarith [hcW.2.2.2]
  have hsplit := hasCurveRatHomology_split_im hp (u := b.im - r) (v := b.im - r / 2)
    hc.le (by linarith) (by linarith)
    (h0 _ _ _ _ ⟨_, mk_mem_openRect hb₁ hb₂ (by linarith) (by linarith), hQ⟩
      (hfree _ le_rfl)).toCurve h
    (h0 _ _ _ _ ⟨_, mk_mem_openRect hb₁ hb₂ (by linarith) (by linarith), hQ⟩
      (hfree _ hc.le))
  rwa [add_sub_cancel_left] at hsplit

/-- An open rectangle containing exactly one point `b` of `B`: the part of `A` over it has
curve homology with Euler characteristic `n b`. -/
theorem hasCurveRatHomology_openRect_of_unique {n : ℂ → ℕ} {b : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hδb : ∀ a₁ a₂ c₁ c₂ : ℝ, b ∈ openRect a₁ a₂ c₁ c₂ → openRect a₁ a₂ c₁ c₂ ⊆ ball b δ →
      HasDiscreteRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) (n b))
    (hbη : squareNorm b < η) {a₁ a₂ c₁ c₂ : ℝ} (hbW : b ∈ openRect a₁ a₂ c₁ c₂)
    (huniq : ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c = b) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) (n b) := by
  obtain ⟨r, hr, hrδ, hrη⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r ≤ δ ∧ squareNorm b + r ≤ η :=
    ⟨min (δ / 2) (η - squareNorm b), lt_min (by linarith) (by linarith),
      by linarith [min_le_left (δ / 2) (η - squareNorm b)],
      by linarith [min_le_right (δ / 2) (η - squareNorm b)]⟩
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbW
  have hmem : b ∈ openRect (max a₁ (b.re - r)) (min a₂ (b.re + r)) (max c₁ (b.im - r))
      (min c₂ (b.im + r)) :=
    ⟨max_lt hb₁ (by linarith), lt_min hb₂ (by linarith), max_lt hb₃ (by linarith),
      lt_min hb₄ (by linarith)⟩
  have hball : openRect (max a₁ (b.re - r)) (min a₂ (b.re + r)) (max c₁ (b.im - r))
      (min c₂ (b.im + r)) ⊆ ball b δ := by
    rintro x ⟨hx₁, hx₂, hx₃, hx₄⟩
    rw [mem_ball, Complex.dist_eq]
    have hx := Complex.norm_le_abs_re_add_abs_im (x - b)
    rw [Complex.sub_re, Complex.sub_im] at hx
    have hre : |x.re - b.re| < r := abs_sub_lt_iff.2
      ⟨by linarith [min_le_right a₂ (b.re + r)], by linarith [le_max_right a₁ (b.re - r)]⟩
    have him : |x.im - b.im| < r := abs_sub_lt_iff.2
      ⟨by linarith [min_le_right c₂ (b.im + r)], by linarith [le_max_right c₁ (b.im - r)]⟩
    linarith
  have h₄ := (hδb _ _ _ _ hmem hball).toCurve
  have h₃ := hasCurveRatHomology_trim_im_top hp h0
    ⟨hmem.1, hmem.2.1, hmem.2.2.1, hb₄⟩
    (fun c hc hcW => huniq c hc (openRect_mono (le_max_left _ _) (min_le_left _ _)
      (le_max_left _ _) le_rfl hcW)) hr hrη h₄
  have h₂ := hasCurveRatHomology_trim_im_bottom hp h0 ⟨hmem.1, hmem.2.1, hb₃, hb₄⟩
    (fun c hc hcW => huniq c hc (openRect_mono (le_max_left _ _) (min_le_left _ _)
      le_rfl le_rfl hcW)) hr hrη h₃
  have h₁ := hasCurveRatHomology_trim_re_right hp h0 ⟨hmem.1, hb₂, hb₃, hb₄⟩
    (fun c hc hcW => huniq c hc (openRect_mono (le_max_left _ _) le_rfl le_rfl le_rfl hcW))
    hr hrη h₂
  exact hasCurveRatHomology_trim_re_left hp h0 ⟨hb₁, hb₂, hb₃, hb₄⟩ huniq hr hrη h₁

/-- An open rectangle containing two points `b`, `b'` of `B` with `Re b < Re b'`, given
the result for subrectangles containing fewer points of `B`. -/
theorem hasCurveRatHomology_openRect_sep_re {n : ℂ → ℕ} (hB : ∀ b ∈ B, squareNorm b < η)
    {a₁ a₂ c₁ c₂ : ℝ} {b b' : ℂ} (hb : b ∈ B) (hbW : b ∈ openRect a₁ a₂ c₁ c₂)
    (hb' : b' ∈ B) (hb'W : b' ∈ openRect a₁ a₂ c₁ c₂) (hlt : b.re < b'.re)
    (ih : ∀ a₁' a₂' c₁' c₂' : ℝ, openRect a₁' a₂' c₁' c₂' ⊆ openRect a₁ a₂ c₁ c₂ →
      ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c ∉ openRect a₁' a₂' c₁' c₂' →
      (openRect a₁' a₂' c₁' c₂' ∩ closedSquare η).Nonempty →
      HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁' a₂' c₁' c₂')
        (branchedEuler B d n (openRect a₁' a₂' c₁' c₂'))) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂)
      (branchedEuler B d n (openRect a₁ a₂ c₁ c₂)) := by
  classical
  have hbF : b ∈ B.filter fun c => c.re < b'.re := Finset.mem_filter.2 ⟨hb, hlt⟩
  obtain ⟨e, he, hemax⟩ := Finset.exists_max_image _ Complex.re ⟨b, hbF⟩
  have hbe : b.re ≤ e.re := hemax b hbF
  have heb' : e.re < b'.re := (Finset.mem_filter.1 he).2
  have hgap : ∀ c ∈ B, c ∉ openRect e.re b'.re c₁ c₂ := by
    intro c hc hcW
    have := hemax c (Finset.mem_filter.2 ⟨hc, hcW.2.1⟩)
    linarith [hcW.1]
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbW
  obtain ⟨hb'₁, hb'₂, hb'₃, hb'₄⟩ := hb'W
  have hbQ := hB b hb
  have hb'Q := hB b' hb'
  have hre := abs_re_le_squareNorm b
  have hre' := abs_re_le_squareNorm b'
  have him' := abs_im_le_squareNorm b'
  have hmid : (⟨(e.re + b'.re) / 2, b'.im⟩ : ℂ) ∈ openRect e.re b'.re c₁ c₂ ∩ closedSquare η :=
    ⟨mk_mem_openRect (by linarith) (by linarith) hb'₃ hb'₄,
      mk_mem_closedSquare (abs_le.2 ⟨by linarith [neg_abs_le b.re], by
        linarith [le_abs_self b'.re]⟩) (by linarith)⟩
  have h₁ := ih a₁ b'.re c₁ c₂ (openRect_mono le_rfl hb'₂.le le_rfl le_rfl) b' hb'
    ⟨hb'₁, hb'₂, hb'₃, hb'₄⟩ (fun h => lt_irrefl _ h.2.1)
    ⟨b, ⟨hb₁, hlt, hb₃, hb₄⟩, hbQ.le⟩
  have h₂ := ih e.re a₂ c₁ c₂ (openRect_mono (by linarith) le_rfl le_rfl le_rfl) b hb
    ⟨hb₁, hb₂, hb₃, hb₄⟩ (fun h => by linarith [h.1])
    ⟨b', ⟨heb', hb'₂, hb'₃, hb'₄⟩, hb'Q.le⟩
  have hsplit := hasCurveRatHomology_split_re hp (by linarith) heb' hb'₂.le h₁ h₂
    (h0 _ _ _ _ ⟨_, hmid⟩ hgap)
  rwa [← branchedEuler_union (by rwa [openRect_inter_re (by linarith) hb'₂.le]),
    openRect_union_re (by linarith) heb' hb'₂.le] at hsplit

/-- An open rectangle containing two points `b`, `b'` of `B` with `Im b < Im b'`, given
the result for subrectangles containing fewer points of `B`. -/
theorem hasCurveRatHomology_openRect_sep_im {n : ℂ → ℕ} (hB : ∀ b ∈ B, squareNorm b < η)
    {a₁ a₂ c₁ c₂ : ℝ} {b b' : ℂ} (hb : b ∈ B) (hbW : b ∈ openRect a₁ a₂ c₁ c₂)
    (hb' : b' ∈ B) (hb'W : b' ∈ openRect a₁ a₂ c₁ c₂) (hlt : b.im < b'.im)
    (ih : ∀ a₁' a₂' c₁' c₂' : ℝ, openRect a₁' a₂' c₁' c₂' ⊆ openRect a₁ a₂ c₁ c₂ →
      ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c ∉ openRect a₁' a₂' c₁' c₂' →
      (openRect a₁' a₂' c₁' c₂' ∩ closedSquare η).Nonempty →
      HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁' a₂' c₁' c₂')
        (branchedEuler B d n (openRect a₁' a₂' c₁' c₂'))) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂)
      (branchedEuler B d n (openRect a₁ a₂ c₁ c₂)) := by
  classical
  have hbF : b ∈ B.filter fun c => c.im < b'.im := Finset.mem_filter.2 ⟨hb, hlt⟩
  obtain ⟨e, he, hemax⟩ := Finset.exists_max_image _ Complex.im ⟨b, hbF⟩
  have hbe : b.im ≤ e.im := hemax b hbF
  have heb' : e.im < b'.im := (Finset.mem_filter.1 he).2
  have hgap : ∀ c ∈ B, c ∉ openRect a₁ a₂ e.im b'.im := by
    intro c hc hcW
    have := hemax c (Finset.mem_filter.2 ⟨hc, hcW.2.2.2⟩)
    linarith [hcW.2.2.1]
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbW
  obtain ⟨hb'₁, hb'₂, hb'₃, hb'₄⟩ := hb'W
  have hbQ := hB b hb
  have hb'Q := hB b' hb'
  have him := abs_im_le_squareNorm b
  have him' := abs_im_le_squareNorm b'
  have hre' := abs_re_le_squareNorm b'
  have hmid : (⟨b'.re, (e.im + b'.im) / 2⟩ : ℂ) ∈ openRect a₁ a₂ e.im b'.im ∩ closedSquare η :=
    ⟨mk_mem_openRect hb'₁ hb'₂ (by linarith) (by linarith),
      mk_mem_closedSquare (by linarith) (abs_le.2 ⟨by linarith [neg_abs_le b.im], by
        linarith [le_abs_self b'.im]⟩)⟩
  have h₁ := ih a₁ a₂ c₁ b'.im (openRect_mono le_rfl le_rfl le_rfl hb'₄.le) b' hb'
    ⟨hb'₁, hb'₂, hb'₃, hb'₄⟩ (fun h => lt_irrefl _ h.2.2.2)
    ⟨b, ⟨hb₁, hb₂, hb₃, hlt⟩, hbQ.le⟩
  have h₂ := ih a₁ a₂ e.im c₂ (openRect_mono le_rfl le_rfl (by linarith) le_rfl) b hb
    ⟨hb₁, hb₂, hb₃, hb₄⟩ (fun h => by linarith [h.2.2.1])
    ⟨b', ⟨hb'₁, hb'₂, heb', hb'₄⟩, hb'Q.le⟩
  have hsplit := hasCurveRatHomology_split_im hp (by linarith) heb' hb'₄.le h₁ h₂
    (h0 _ _ _ _ ⟨_, hmid⟩ hgap)
  rwa [← branchedEuler_union (by rwa [openRect_inter_im (by linarith) hb'₄.le]),
    openRect_union_im (by linarith) heb' hb'₄.le] at hsplit

/-- **Curve homology over open rectangles.** The part of `A` over an open rectangle `W`
meeting the closed square has curve homology with Euler characteristic
`d − ∑ (d − n b)`, the sum running over the points `b` of `B` lying in `W`. -/
theorem hasCurveRatHomology_openRect {n : ℂ → ℕ} (hB : ∀ b ∈ B, squareNorm b < η)
    (h1 : ∀ b ∈ B, ∃ δ > 0, ∀ a₁ a₂ c₁ c₂ : ℝ, b ∈ openRect a₁ a₂ c₁ c₂ →
      openRect a₁ a₂ c₁ c₂ ⊆ ball b δ →
      HasDiscreteRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) (n b))
    (a₁ a₂ c₁ c₂ : ℝ) (hW : (openRect a₁ a₂ c₁ c₂ ∩ closedSquare η).Nonempty) :
    HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂)
      (branchedEuler B d n (openRect a₁ a₂ c₁ c₂)) := by
  classical
  suffices H : ∀ m : ℕ, ∀ a₁ a₂ c₁ c₂ : ℝ,
      (B.filter (· ∈ openRect a₁ a₂ c₁ c₂)).card = m →
      (openRect a₁ a₂ c₁ c₂ ∩ closedSquare η).Nonempty →
      HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂)
        (branchedEuler B d n (openRect a₁ a₂ c₁ c₂)) from
    H _ a₁ a₂ c₁ c₂ rfl hW
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a₁ a₂ c₁ c₂ hm hW
  have ih' : ∀ a₁' a₂' c₁' c₂' : ℝ, openRect a₁' a₂' c₁' c₂' ⊆ openRect a₁ a₂ c₁ c₂ →
      ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c ∉ openRect a₁' a₂' c₁' c₂' →
      (openRect a₁' a₂' c₁' c₂' ∩ closedSquare η).Nonempty →
      HasCurveRatHomology ↥(A ∩ p ⁻¹' openRect a₁' a₂' c₁' c₂')
        (branchedEuler B d n (openRect a₁' a₂' c₁' c₂')) := by
    intro a₁' a₂' c₁' c₂' hsub c hc hcW hcW' hne
    refine ih _ ?_ _ _ _ _ rfl hne
    rw [← hm]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨c, ?_, ?_⟩)
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hsub hz.2⟩
    · exact Finset.mem_filter.2 ⟨hc, hcW⟩
    · exact fun h => hcW' (Finset.mem_filter.1 h).2
  by_cases hfree : ∀ b ∈ B, b ∉ openRect a₁ a₂ c₁ c₂
  · rw [branchedEuler_eq_of_forall_notMem hfree]
    exact (h0 _ _ _ _ hW hfree).toCurve
  push Not at hfree
  obtain ⟨b, hb, hbW⟩ := hfree
  by_cases huniq : ∀ c ∈ B, c ∈ openRect a₁ a₂ c₁ c₂ → c = b
  · obtain ⟨δ, hδ, hδb⟩ := h1 b hb
    rw [branchedEuler_eq_of_unique hb hbW huniq]
    exact hasCurveRatHomology_openRect_of_unique hp h0 hδ hδb (hB b hb) hbW huniq
  push Not at huniq
  obtain ⟨c, hc, hcW, hcb⟩ := huniq
  rcases lt_trichotomy b.re c.re with hlt | heq | hgt
  · exact hasCurveRatHomology_openRect_sep_re hp h0 hB hb hbW hc hcW hlt ih'
  · have him : b.im ≠ c.im := fun h => hcb (Complex.ext heq.symm h.symm)
    rcases lt_or_gt_of_ne him with hlt | hgt
    · exact hasCurveRatHomology_openRect_sep_im hp h0 hB hb hbW hc hcW hlt ih'
    · exact hasCurveRatHomology_openRect_sep_im hp h0 hB hc hcW hb hbW hgt ih'
  · exact hasCurveRatHomology_openRect_sep_re hp h0 hB hc hcW hb hbW hgt ih'

end Induction

/-- **Riemann–Hurwitz count for a branched covering of a square.** Let `A ⊆ E` lie over
the closed square of radius `η > 0` under a continuous map `p : E → ℂ`, and let `B` be a
finite set of points of the open square. Suppose that the part of `A` over every open
rectangle meeting the closed square and containing no point of `B` has the rational
homology of `d` points, and that for every `b ∈ B` the part of `A` over every sufficiently
small open rectangle containing `b` has the rational homology of `n b` points. Then `A` has
curve homology with Euler characteristic `d − ∑_{b ∈ B} (d − n b)`. -/
theorem hasCurveRatHomology_of_branchedSquare {E : Type} [TopologicalSpace E] (p : E → ℂ)
    (hp : Continuous p) (A : Set E) (η : ℝ) (hη : 0 < η)
    (hA : A ⊆ p ⁻¹' OnLeConjecture.Analytic.closedSquare η)
    (B : Finset ℂ) (hB : ∀ b ∈ B, OnLeConjecture.Analytic.squareNorm b < η) (d : ℕ)
    (n : ℂ → ℕ)
    (h0 : ∀ a₁ a₂ c₁ c₂ : ℝ,
      (openRect a₁ a₂ c₁ c₂ ∩ OnLeConjecture.Analytic.closedSquare η).Nonempty →
      (∀ b ∈ B, b ∉ openRect a₁ a₂ c₁ c₂) →
      HasDiscreteRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) d)
    (h1 : ∀ b ∈ B, ∃ δ > 0, ∀ a₁ a₂ c₁ c₂ : ℝ, b ∈ openRect a₁ a₂ c₁ c₂ →
      openRect a₁ a₂ c₁ c₂ ⊆ Metric.ball b δ →
      HasDiscreteRatHomology ↥(A ∩ p ⁻¹' openRect a₁ a₂ c₁ c₂) (n b)) :
    HasCurveRatHomology ↥A ((d : ℤ) - ∑ b ∈ B, ((d : ℤ) - n b)) := by
  have hsq : closedSquare η ⊆ openRect (-(2 * η)) (2 * η) (-(2 * η)) (2 * η) := by
    intro x hx
    have hre := abs_le.1 ((abs_re_le_squareNorm x).trans hx)
    have him := abs_le.1 ((abs_im_le_squareNorm x).trans hx)
    exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩
  have h0Q : (0 : ℂ) ∈ closedSquare η := by
    simp [closedSquare, squareNorm, hη.le]
  have key := hasCurveRatHomology_openRect hp h0 hB h1 (-(2 * η)) (2 * η) (-(2 * η)) (2 * η)
    ⟨0, hsq h0Q, h0Q⟩
  have hAW : A ∩ p ⁻¹' openRect (-(2 * η)) (2 * η) (-(2 * η)) (2 * η) = A :=
    inter_eq_left.2 fun x hx => hsq (hA hx)
  rwa [hAW, branchedEuler_eq_of_forall_mem fun b hb => hsq (hB b hb).le] at key

end OnLeConjecture.DifferentialTopology
