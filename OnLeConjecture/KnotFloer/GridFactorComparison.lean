/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalClass
public import OnLeConjecture.KnotFloer.SpectralShift

/-!
# Comparison of thresholds at rescaled parameters

Let `G` and `H` be grids of the same size with the same `O`-markings. Their full Laurent complexes
coincide, and the identity map `laurentMaslovMarkingIso` carries the canonical class of `G` to
that of `H`. Suppose that `h + b A_H(x) ≤ A_G(x)` for every grid state `x`. A monomial `U^k x` has
weighted level `(t/2) A_G(x) - k` in `G` at the parameter `t`, and weighted level
`(b t/2) A_H(x) - k` in `H` at the parameter `b t`. For `0 ≤ t ≤ 2` the second level is at most
the first minus `t h/2`. Consequently

`t h/2 + ν_H(b t) ≤ ν_G(t)`

(Lemma 1.3 of the factor lower bound proof). The parameters `t` and `b t` differ, so this is not
an instance of the same-parameter transfer along a bifiltered map.

The argument needs the description of a weighted level by its monomials. One inclusion is
`mem_weighted_level_of_monomials`: a homogeneous chain whose monomials all have weighted level at
most `s` lies in the weighted level `s`. Each monomial `U^k x` lies in the bifiltration level
`(-k, A(x) - k)`, and a homogeneous chain is the sum of its monomials.

## Main results

* `mem_weighted_level_of_monomials`: the monomial criterion for weighted levels.
* `spectralThreshold_add_le_of_alexander_le`: Lemma 1.3.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ}

section Monomials

variable (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- The single-state part of a homogeneous Laurent chain is homogeneous of the same degree. -/
theorem single_mem_laurentMaslovPiece_of_mem {m : ℤ} (v : LaurentChain R n)
    (hv : v ∈ laurentMaslovPiece G R m) (x : GridState n) :
    (Finsupp.single x (v x) : LaurentChain R n) ∈ laurentMaslovPiece G R m := by
  rw [mem_laurentMaslovPiece]
  intro y k hk
  by_cases hyx : y = x
  · subst hyx
    rw [Finsupp.single_eq_same] at hk
    exact hv y k hk
  · rw [Finsupp.single_eq_of_ne hyx] at hk
    simp at hk

/-- **Weighted levels from monomials.** A homogeneous chain lies in the weighted level `s` at the
parameter `t` when every monomial `U^k x` in its support satisfies `(t/2) A(x) - k ≤ s`. -/
theorem mem_weighted_level_of_monomials (t s : ℝ) (m : ℤ) (c : (laurentMaslovComplex G R).X m)
    (h : ∀ x k, k ∈ ((laurentMaslovChainEquiv G R m c : LaurentChain R n) x).coeff.support →
      t / 2 * (G.alexander x : ℝ) - k ≤ s) :
    c ∈ ((laurentMaslovBifiltration G R).weighted t).level s m := by
  classical
  set e := laurentMaslovChainEquiv G R m with he
  set v := e c with hvdef
  have hpiece := fun x => single_mem_laurentMaslovPiece_of_mem G R (v : LaurentChain R n)
    v.property x
  have hsum : c = ∑ x : GridState n, e.symm ⟨_, hpiece x⟩ := by
    apply e.injective
    rw [map_sum]
    simp only [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (Finsupp.univ_sum_single (v : LaurentChain R n)).symm
  rw [hsum]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hvx : (v : LaurentChain R n) x = 0
  · have hz : (⟨_, hpiece x⟩ : laurentMaslovPiece G R m) = 0 :=
      Subtype.ext (by simp [hvx])
    rw [hz, map_zero]
    exact Submodule.zero_mem _
  · have hne : ((v : LaurentChain R n) x).coeff ≠ 0 := by
      intro h0
      apply hvx
      ext k
      exact Finsupp.ext_iff.mp h0 k
    obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hne
    apply Submodule.subset_span
    refine ⟨-(k : ℝ), (G.alexander x : ℝ) - k, ?_, ?_⟩
    · change e (e.symm ⟨_, hpiece x⟩) ∈ laurentMaslovBifiltrationLevel G R _ _ m
      rw [LinearEquiv.apply_symm_apply, mem_laurentMaslovBifiltrationLevel_iff]
      intro y j hj
      by_cases hyx : y = x
      · subst hyx
        change j ∈ ((Finsupp.single y ((v : LaurentChain R n) y) : LaurentChain R n)
          y).coeff.support at hj
        rw [Finsupp.single_eq_same] at hj
        have hdj := v.property y j hj
        have hdk := v.property y k hk
        have hjk : j = k := by
          have h2 := hdj.trans hdk.symm
          unfold laurentMaslovDegree at h2
          omega
        subst hjk
        exact ⟨le_rfl, le_rfl⟩
      · change j ∈ ((Finsupp.single x ((v : LaurentChain R n) x) : LaurentChain R n)
          y).coeff.support at hj
        rw [Finsupp.single_eq_of_ne hyx] at hj
        simp at hj
    · have hk' := h x k hk
      nlinarith

end Monomials

/-- **Lemma 1.3 (comparison at a rescaled parameter).** Let `G` and `H` have the same
`O`-markings, and suppose that `h + b A_H(x) ≤ A_G(x)` for every grid state `x`. For
`0 ≤ t ≤ 2`, the canonical classes satisfy `t h/2 + ν_H(b t) ≤ ν_G(t)`. -/
theorem spectralThreshold_add_le_of_alexander_le (G H : GridDiagram n) (hn : 2 ≤ n)
    (hO : G.O = H.O) (b h t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (hA : ∀ x : GridState n, h + b * (H.alexander x : ℝ) ≤ (G.alexander x : ℝ)) :
    ((t * h / 2 : ℝ) : EReal) +
        ((laurentMaslovBifiltration H (ZMod 2)).weighted (b * t)).spectralThreshold 0
          (gridCanonicalClass H hn) ≤
      ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
        (gridCanonicalClass G hn) := by
  have hα : 0 ≤ 1 - t / 2 := by linarith
  have hβ : 0 ≤ t / 2 := by linarith
  have hshift : ((laurentMaslovBifiltration G (ZMod 2)).weighted t).Shifts
      ((laurentMaslovBifiltration H (ZMod 2)).weighted (b * t))
      (laurentMaslovMarkingIso (ZMod 2) hO).hom (-(t * h / 2)) := by
    intro s m c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a', b', hc, hab⟩ := hc
      apply mem_weighted_level_of_monomials H (ZMod 2)
      intro x k hk
      have hk' : k ∈ ((laurentMaslovChainEquiv G (ZMod 2) m c :
          LaurentChain (ZMod 2) n) x).coeff.support := hk
      obtain ⟨h1, h2⟩ := hc x k hk'
      have hAx := hA x
      have e1 := mul_le_mul_of_nonneg_left h1 hα
      have e2 := mul_le_mul_of_nonneg_left h2 hβ
      have e3 := mul_le_mul_of_nonneg_left hAx hβ
      nlinarith
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add c d _ _ hc hd => simpa only [map_add] using Submodule.add_mem _ hc hd
    | smul a c _ hc => simpa only [map_smul] using Submodule.smul_mem _ a hc
  have hmap := RealFiltration.spectralThreshold_map_le_add hshift 0 (gridCanonicalClass G hn)
  rw [gridCanonicalClass_markingIso G H hn hO] at hmap
  calc ((t * h / 2 : ℝ) : EReal) +
        ((laurentMaslovBifiltration H (ZMod 2)).weighted (b * t)).spectralThreshold 0
          (gridCanonicalClass H hn)
      ≤ ((t * h / 2 : ℝ) : EReal) +
          (((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
            (gridCanonicalClass G hn) + ((-(t * h / 2) : ℝ) : EReal)) :=
        add_le_add_right hmap _
    _ = ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) := by
        rw [add_comm, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

end OnLeConjecture.KnotFloer.GridFull
