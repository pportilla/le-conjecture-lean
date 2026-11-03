/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentBifiltration
public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov
public import OnLeConjecture.KnotFloer.GridFullSpectralFiniteness

/-!
# Finite spectral thresholds of the full Laurent grid complex

Restricting the two monomial-coordinate bounds to the Maslov homogeneous pieces supplies
a bifiltration of the integer-graded full Laurent grid complex over the base ring.
Fixed Maslov degree bounds both coordinates even when the Laurent exponent is negative.
Every nonzero homology class consequently has a finite real spectral threshold
for parameters in `[0,2]`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- The two-coordinate submodule in a fixed Maslov degree. -/
noncomputable def laurentMaslovBifiltrationLevel (a b : ℝ) (m : ℤ) :
    Submodule R (laurentMaslovPiece G R m) :=
  (laurentBifiltrationLevel G R a b).comap (laurentMaslovPiece G R m).subtype

/-- Exact coefficient bounds for a homogeneous chain at a bifiltration level. -/
theorem mem_laurentMaslovBifiltrationLevel_iff (a b : ℝ) (m : ℤ) (c : laurentMaslovPiece G R m) :
    c ∈ laurentMaslovBifiltrationLevel G R a b m ↔
      ∀ x k, k ∈ ((c : LaurentChain R n) x).coeff.support →
        -(k : ℝ) ≤ a ∧ (G.alexander x : ℝ) - k ≤ b :=
  mem_laurentBifiltrationLevel_iff G R a b c

variable [CharP R 2]

/-- Identify a native Maslov complex object with its homogeneous Laurent chain submodule. -/
noncomputable def laurentMaslovChainEquiv (m : ℤ) :
    (laurentMaslovComplex G R).X m ≃ₗ[R] laurentMaslovPiece G R m :=
  (eqToIso (laurentMaslovComplex_X G R m)).toLinearEquiv

/-- The native graded differential is the full rectangle map on the underlying chains. -/
theorem laurentMaslovChainEquiv_d (m : ℤ) (c : (laurentMaslovComplex G R).X (m + 1)) :
    (laurentMaslovChainEquiv G R m ((laurentMaslovComplex G R).d (m + 1) m c) : LaurentChain R n) =
      laurentDifferential G R (laurentMaslovChainEquiv G R (m + 1) c) := by
  have h : laurentMaslovChainEquiv G R m ((laurentMaslovComplex G R).d (m + 1) m c) =
      laurentGradedDifferential G R m (laurentMaslovChainEquiv G R (m + 1) c) := by
    change (eqToHom (laurentMaslovComplex_X G R m)) ((laurentMaslovComplex G R).d (m + 1) m c) =
      laurentGradedDifferential G R m ((eqToHom (laurentMaslovComplex_X G R (m + 1))) c)
    rw [laurentMaslovComplex_d]
    simp only [ModuleCat.comp_apply]
    rw [← ModuleCat.comp_apply, Category.assoc, eqToHom_trans]
    simp
  exact congrArg Subtype.val h

/-- The full Laurent grid complex with its Maslov grading and both filtration coordinates. -/
noncomputable def laurentMaslovBifiltration : Bifiltration (laurentMaslovComplex G R) where
  level a b m := (laurentMaslovBifiltrationLevel G R a b m).comap
    (laurentMaslovChainEquiv G R m).toLinearMap
  mono m _ _ _ _ ha hb := Submodule.comap_mono
    (Submodule.comap_mono (laurentBifiltrationLevel_mono G R ha hb))
  differential_mem a b i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      change (laurentMaslovChainEquiv G R j ((laurentMaslovComplex G R).d (j + 1) j c) :
        LaurentChain R n) ∈ laurentBifiltrationLevel G R a b
      rw [laurentMaslovChainEquiv_d]
      exact laurentDifferential_mem_bifiltrationLevel G R a b
        (laurentMaslovChainEquiv G R (j + 1) c) hc
    · have hrel : ¬ (ComplexShape.down ℤ).Rel i j := by
        simpa only [ComplexShape.down_Rel] using h
      rw [(laurentMaslovComplex G R).shape i j hrel]
      exact Submodule.zero_mem _

/-- Every homogeneous Laurent chain satisfies a common finite upper pair of bounds. -/
theorem laurentMaslovBifiltration_bound (m : ℤ) (c : (laurentMaslovComplex G R).X m) :
    c ∈ (laurentMaslovBifiltration G R).level
      (maslovCoordinateBound G m) (maslovCoordinateBound G m) m := by
  intro x k hk
  have h := integer_monomial_coordinates_bounds G m k x
    ((laurentMaslovChainEquiv G R m c).property x k hk)
  exact ⟨h.2.1, h.2.2.2⟩

/-- A nonzero Laurent homogeneous chain forces both coordinate bounds above a finite value. -/
theorem lower_bounds_of_nonzero_mem_laurentMaslovBifiltration (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) (hc : c ≠ 0) {a b : ℝ}
    (hmem : c ∈ (laurentMaslovBifiltration G R).level a b m) :
    -maslovCoordinateBound G m ≤ a ∧ -maslovCoordinateBound G m ≤ b := by
  let v := laurentMaslovChainEquiv G R m c
  have hv : (v : LaurentChain R n) ≠ 0 := by
    intro h
    apply hc
    apply (laurentMaslovChainEquiv G R m).injective
    rw [map_zero]
    exact Subtype.ext h
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hv
  rw [Finsupp.zero_apply] at hx
  have hx' : ((v : LaurentChain R n) x).coeff ≠ 0 := by simpa using hx
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hx'
  have hb := hmem x k hk
  have hl := integer_monomial_coordinates_bounds G m k x (v.property x k hk)
  exact ⟨hl.1.trans hb.1, hl.2.2.1.trans hb.2⟩

/-- In each Maslov degree the weighted Laurent filtration vanishes below a finite bound. -/
theorem weighted_laurentMaslov_level_eq_bot (m : ℤ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) {s : ℝ} (hs : s < -maslovCoordinateBound G m) :
    ((laurentMaslovBifiltration G R).weighted t).level s m = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨a, b, hmem, hweight⟩ := hc
    obtain ⟨ha, hb⟩ := lower_bounds_of_nonzero_mem_laurentMaslovBifiltration
      G R m c hne hmem
    have htA : 0 ≤ 1 - t / 2 := by linarith
    have htB : 0 ≤ t / 2 := by linarith
    have ha' := mul_le_mul_of_nonneg_left ha htA
    have hb' := mul_le_mul_of_nonneg_left hb htB
    nlinarith
  | zero => exact Submodule.zero_mem _
  | add c d _ _ hc hd => exact Submodule.add_mem _ hc hd
  | smul p c _ hc => exact Submodule.smul_mem _ p hc

/-- The weighted Laurent filtration exhausts every Maslov chain group. -/
theorem weighted_laurentMaslov_exhaustive (m : ℤ) (t : ℝ)
    (c : (laurentMaslovComplex G R).X m) :
    ∃ s : ℝ, c ∈ ((laurentMaslovBifiltration G R).weighted t).level s m := by
  refine ⟨maslovCoordinateBound G m, Submodule.subset_span
    ⟨maslovCoordinateBound G m, maslovCoordinateBound G m,
      laurentMaslovBifiltration_bound G R m c, ?_⟩⟩
  nlinarith

/-- Each nonzero native homology class of the full Laurent grid complex has a finite real
spectral threshold at every parameter in `[0,2]`. -/
theorem exists_real_weighted_laurentMaslov_spectralThreshold (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (hξ : ξ ≠ 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ∃ s : ℝ, ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ = (s : EReal) :=
  RealFiltration.exists_real_spectralThreshold _ m ξ hξ
    (weighted_laurentMaslov_exhaustive G R m t) (-maslovCoordinateBound G m)
    (fun _ hs => weighted_laurentMaslov_level_eq_bot G R m t ht0 ht2 hs)

end OnLeConjecture.KnotFloer.GridFull
