/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.BifilteredSpectral

/-!
# Comparison of class-Upsilon under shifted chain maps

A map with shifts `r₁` and `r₂` in the two filtrations shifts the weighted
filtration by `(1 - t/2) r₁ + (t/2) r₂`. Two such maps that are inverse on
one homology class give the corresponding bound on its class-Upsilon
values. In particular, shifts `(0,g)` give the bound `t*g`.

These are consequences of actual filtered chain maps. Constructing such
maps from a geometric cobordism, and identifying `g` with its genus, are
separate requirements not asserted in this file.
-/

@[expose] public section

universe u v w

namespace OnLeConjecture.KnotFloer.Bifiltration

open CategoryTheory HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}
variable {C D E : HomologicalComplex (ModuleCat.{v} R) c}

/-- A chain map increases the two filtration coordinates by at most the
specified constants. -/
def Shifts (F : Bifiltration C) (G : Bifiltration D) (φ : C ⟶ D)
    (r₁ r₂ : ℝ) : Prop :=
  ∀ a b i x, x ∈ F.level a b i → φ.f i x ∈ G.level (a + r₁) (b + r₂) i

theorem shifts_zero_zero_iff {F : Bifiltration C} {G : Bifiltration D}
    {φ : C ⟶ D} : F.Shifts G φ 0 0 ↔ F.Preserves G φ := by
  simp [Shifts, Preserves]

/-- The shift of a composite is the sum of the shifts. -/
theorem Shifts.comp {F : Bifiltration C} {G : Bifiltration D} {H : Bifiltration E}
    {φ : C ⟶ D} {ψ : D ⟶ E} {r₁ r₂ s₁ s₂ : ℝ}
    (hφ : F.Shifts G φ r₁ r₂) (hψ : G.Shifts H ψ s₁ s₂) :
    F.Shifts H (φ ≫ ψ) (r₁ + s₁) (r₂ + s₂) := by
  intro a b i x hx
  simpa [add_assoc] using hψ (a + r₁) (b + r₂) i _ (hφ a b i x hx)

/-- The shift of the weighted filtration is the same weighted combination
of the two shifts. No restriction on `t` is needed for this identity. -/
theorem Shifts.weighted {F : Bifiltration C} {G : Bifiltration D}
    {φ : C ⟶ D} {r₁ r₂ : ℝ} (hφ : F.Shifts G φ r₁ r₂) (t : ℝ) :
    (F.weighted t).Shifts (G.weighted t) φ ((1 - t / 2) * r₁ + (t / 2) * r₂) := by
  intro s i x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, hx, hab⟩ := hx
    apply Submodule.subset_span
    refine ⟨a + r₁, b + r₂, hφ a b i x hx, ?_⟩
    nlinarith
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

/-- Finite class-Upsilon values are real and equal minus twice the
corresponding real thresholds. -/
theorem classUpsilon_eq_coe_of_spectralThreshold_eq {F : Bifiltration C}
    {i : ι} {ξ : C.homology i} {t a : ℝ}
    (ha : (F.weighted t).spectralThreshold i ξ = (a : EReal)) :
    F.classUpsilon i ξ t = ((-2 * a : ℝ) : EReal) := by
  simp only [classUpsilon, ha, EReal.coe_mul, EReal.coe_neg, neg_mul]
  rfl

/-- Two shifted maps inverse on the selected homology class bound the
absolute difference of its finite class-Upsilon values. -/
theorem classUpsilon_abs_sub_le_of_shifted_maps
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D} {ψ : D ⟶ C}
    {r₁ r₂ : ℝ} (hφ : F.Shifts G φ r₁ r₂) (hψ : G.Shifts F ψ r₁ r₂)
    (i : ι) (ξ : C.homology i)
    (hinverse : homologyMap ψ i (homologyMap φ i ξ) = ξ)
    (t a b : ℝ) (ha : (F.weighted t).spectralThreshold i ξ = (a : EReal))
    (hb : (G.weighted t).spectralThreshold i (homologyMap φ i ξ) = (b : EReal)) :
    |(-2 * a) - (-2 * b)| ≤ 2 * ((1 - t / 2) * r₁ + (t / 2) * r₂) := by
  have h := RealFiltration.abs_sub_le_of_shifted_maps
    (hφ.weighted t) (hψ.weighted t) i ξ hinverse ha hb
  calc
    |(-2 * a) - (-2 * b)| = 2 * |a - b| := by
      rw [show -2 * a - -2 * b = -2 * (a - b) by ring, abs_mul]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- Shifts only in the second filtration coordinate give the expression
`t*g` used in the class-Upsilon comparison. This theorem does not provide
geometric maps or identify `g` with a surface genus. -/
theorem classUpsilon_abs_sub_le_of_second_shift
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D} {ψ : D ⟶ C}
    {g : ℝ} (hφ : F.Shifts G φ 0 g) (hψ : G.Shifts F ψ 0 g)
    (i : ι) (ξ : C.homology i)
    (hinverse : homologyMap ψ i (homologyMap φ i ξ) = ξ)
    (t a b : ℝ) (ha : (F.weighted t).spectralThreshold i ξ = (a : EReal))
    (hb : (G.weighted t).spectralThreshold i (homologyMap φ i ξ) = (b : EReal)) :
    |(-2 * a) - (-2 * b)| ≤ t * g := by
  have h := classUpsilon_abs_sub_le_of_shifted_maps hφ hψ i ξ hinverse t a b ha hb
  convert h using 1
  ring

end OnLeConjecture.KnotFloer.Bifiltration
