/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullMaslovBifiltration

/-!
# Finite spectral thresholds in each Maslov degree

A fixed Maslov degree bounds the exponents of all monomials which can occur, since the grid
has finitely many states. Both filtration coordinates therefore have a finite lower bound.
For weights in `[0,2]`, the weighted filtration is bounded below and exhaustive in that degree.
Every nonzero homology class of this full polynomial grid complex has a finite real threshold.
No distinguished knot homology generator or invariance under grid moves is assumed or asserted.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n)

/-- A uniform bound for the absolute Maslov degrees of the finitely many grid states. -/
noncomputable def maslovStateBound : ℝ := ∑ x : GridState n, |(G.maslovOℤ x : ℝ)|

/-- A common lower-coordinate bound in the specified Maslov degree. -/
noncomputable def maslovCoordinateBound (m : ℤ) : ℝ :=
  maslovStateBound G + |(m : ℝ)| + alexanderBound G

/-- Both coordinates of a monomial in a fixed Maslov degree are uniformly bounded below. -/
theorem monomial_coordinates_lower_bound (m : ℤ) (e : Fin n →₀ ℕ) (x : GridState n)
    (hdegree : maslovDegree G e x = m) :
    -maslovCoordinateBound G m ≤ -(exponentSize e : ℝ) ∧
      -maslovCoordinateBound G m ≤ (G.alexander x : ℝ) - exponentSize e := by
  have hM : (G.maslovOℤ x : ℝ) ≤ maslovStateBound G :=
    (le_abs_self _).trans (Finset.single_le_sum
      (fun y _ => abs_nonneg (G.maslovOℤ y : ℝ)) (Finset.mem_univ x))
  have hA : -(G.alexander x : ℝ) ≤ alexanderBound G :=
    (neg_le_abs _).trans (Finset.single_le_sum
      (fun y _ => abs_nonneg (G.alexander y : ℝ)) (Finset.mem_univ x))
  have hAnonneg : 0 ≤ alexanderBound G := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hm := neg_le_abs (m : ℝ)
  have he := Nat.cast_nonneg (α := ℝ) (exponentSize e)
  have hreal : (G.maslovOℤ x : ℝ) - 2 * (exponentSize e : ℝ) = m := by
    exact_mod_cast hdegree
  unfold maslovCoordinateBound
  constructor <;> linarith

/-- Integer exponents in a fixed Maslov degree satisfy upper and lower coordinate bounds.
This version also applies to Laurent monomials with negative exponents. -/
theorem integer_monomial_coordinates_bounds (m k : ℤ) (x : GridState n)
    (hdegree : G.maslovOℤ x - 2 * k = m) :
    -maslovCoordinateBound G m ≤ -(k : ℝ) ∧ -(k : ℝ) ≤ maslovCoordinateBound G m ∧
      -maslovCoordinateBound G m ≤ (G.alexander x : ℝ) - k ∧
      (G.alexander x : ℝ) - k ≤ maslovCoordinateBound G m := by
  have hMabs : |(G.maslovOℤ x : ℝ)| ≤ maslovStateBound G :=
    Finset.single_le_sum (fun y _ => abs_nonneg (G.maslovOℤ y : ℝ)) (Finset.mem_univ x)
  have hAabs : |(G.alexander x : ℝ)| ≤ alexanderBound G :=
    Finset.single_le_sum (fun y _ => abs_nonneg (G.alexander y : ℝ)) (Finset.mem_univ x)
  have hAnonneg : 0 ≤ alexanderBound G := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMnonneg : 0 ≤ maslovStateBound G := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmnonneg := abs_nonneg (m : ℝ)
  have hMupper := (le_abs_self _).trans hMabs
  have hMlower := (neg_le_abs _).trans hMabs
  have hAupper := (le_abs_self _).trans hAabs
  have hAlower := (neg_le_abs _).trans hAabs
  have hmupper := le_abs_self (m : ℝ)
  have hmlower := neg_le_abs (m : ℝ)
  have hreal : (G.maslovOℤ x : ℝ) - 2 * (k : ℝ) = m := by exact_mod_cast hdegree
  unfold maslovCoordinateBound
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable (R : Type*) [CommRing R] [CharP R 2]

/-- A nonzero homogeneous chain at a bifiltration level forces both bounds to be above
the uniform lower-coordinate bound. -/
theorem lower_bounds_of_nonzero_mem_maslovBifiltration (m : ℤ)
    (c : (maslovComplex G R).X m) (hc : c ≠ 0) {a b : ℝ}
    (hmem : c ∈ (maslovBifiltration G R).level a b m) :
    -maslovCoordinateBound G m ≤ a ∧ -maslovCoordinateBound G m ≤ b := by
  let v := maslovChainEquiv G R m c
  have hv : (v : GridChainMinus R n) ≠ 0 := by
    intro h
    apply hc
    apply (maslovChainEquiv G R m).injective
    rw [map_zero]
    exact Subtype.ext h
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hv
  rw [Finsupp.zero_apply] at hx
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hx
  have hb := (mem_bifiltrationLevel_iff G R a b v).mp hmem x e he
  have hl := monomial_coordinates_lower_bound G m e x (v.property x e he)
  exact ⟨hl.1.trans hb.1, hl.2.trans hb.2⟩

/-- The weighted filtration is zero below a uniform bound in each Maslov degree
for every parameter in the knot Floer interval. -/
theorem weighted_maslov_level_eq_bot (m : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    {s : ℝ} (hs : s < -maslovCoordinateBound G m) :
    ((maslovBifiltration G R).weighted t).level s m = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨a, b, hmem, hweight⟩ := hc
    obtain ⟨ha, hb⟩ := lower_bounds_of_nonzero_mem_maslovBifiltration G R m c hne hmem
    have htA : 0 ≤ 1 - t / 2 := by linarith
    have htB : 0 ≤ t / 2 := by linarith
    have ha' := mul_le_mul_of_nonneg_left ha htA
    have hb' := mul_le_mul_of_nonneg_left hb htB
    nlinarith
  | zero => exact Submodule.zero_mem _
  | add c d _ _ hc hd => exact Submodule.add_mem _ hc hd
  | smul p c _ hc => exact Submodule.smul_mem _ p hc

/-- Weighted levels exhaust each Maslov chain group. -/
theorem weighted_maslov_exhaustive (m : ℤ) (t : ℝ) (c : (maslovComplex G R).X m) :
    ∃ s : ℝ, c ∈ ((maslovBifiltration G R).weighted t).level s m := by
  obtain ⟨a, b, hmem⟩ := maslovBifiltration_exhaustive G R m c
  exact ⟨(1 - t / 2) * a + (t / 2) * b,
    Submodule.subset_span ⟨a, b, hmem, le_rfl⟩⟩

/-- Every nonzero class of the full polynomial grid complex has a finite real spectral
threshold at each parameter in `[0,2]`. -/
theorem exists_real_weighted_maslov_spectralThreshold (m : ℤ)
    (ξ : (maslovComplex G R).homology m) (hξ : ξ ≠ 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ∃ s : ℝ, ((maslovBifiltration G R).weighted t).spectralThreshold m ξ = (s : EReal) :=
  RealFiltration.exists_real_spectralThreshold _ m ξ hξ
    (weighted_maslov_exhaustive G R m t) (-maslovCoordinateBound G m)
    (fun _ hs => weighted_maslov_level_eq_bot G R m t ht0 ht2 hs)

end OnLeConjecture.KnotFloer.GridFull
