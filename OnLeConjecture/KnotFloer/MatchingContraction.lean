/-
Copyright (c) 2026 The Tau Ceti contributors and Pablo Portilla Cuadrado.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Algebra.Homology.Contraction.Perturbation
public import Mathlib.Algebra.Module.PUnit

/-!
# A special contraction from an acyclic generator matching

The reverse matching homotopy is normalized by the inverse of `d h + h d`.
The normalized homotopy squares to zero and contracts the differential module onto zero.
The inverse is obtained from the well-founded decrease of the nonmatching terms.

The support-decrease argument is adapted from `LinearMap.ker_le_range_of_matching` in
TauCetiProject/TauCeti, commit `eb4dd2412a1cd62f73128361bfd3cb422df32e37`, file
`TauCeti/Algebra/Homology/SquareZero/Contraction.lean` (retrieved 2026-10-29).
That source concludes exactness. Here the homotopy and its normalization are retained
as explicit special contraction data.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open TauCeti Finsupp

namespace MatchingContraction

section Normalization

variable {S M : Type*} [Semiring S] [AddCommGroup M] [Module S M]

private theorem commute_ringInverse {a b : Module.End S M} (hb : IsUnit b)
    (hab : Commute a b) : Commute a (Ring.inverse b) := by
  obtain ⟨u, rfl⟩ := hb
  simpa only [Ring.inverse_unit] using hab.units_inv_right

/-- Normalize a reverse matching homotopy by its contracting commutator. -/
noncomputable def normalizedHomotopy (d h : Module.End S M) : Module.End S M :=
  h * Ring.inverse (d * h + h * d)

/-- Normalization makes the contracting equation exact. -/
theorem normalizedHomotopy_contracts (d h : Module.End S M)
    (hd : d * d = 0) (hu : IsUnit (d * h + h * d)) :
    d * normalizedHomotopy d h + normalizedHomotopy d h * d = 1 := by
  have hc : Commute d (d * h + h * d) := by
    simp only [Commute, SemiconjBy, mul_add, add_mul, ← mul_assoc, hd, zero_mul, zero_add]
    simp only [mul_assoc, hd, mul_zero, add_zero]
  have hi := (commute_ringInverse hu hc).eq
  unfold normalizedHomotopy
  calc
    d * (h * Ring.inverse (d * h + h * d)) +
        (h * Ring.inverse (d * h + h * d)) * d =
      (d * h + h * d) * Ring.inverse (d * h + h * d) := by
        simp only [add_mul, mul_assoc, ← hi]
    _ = 1 := Ring.mul_inverse_cancel _ hu

/-- A square-zero reverse matching remains square zero after normalization. -/
theorem normalizedHomotopy_comp_self (d h : Module.End S M)
    (hh : h * h = 0) (hu : IsUnit (d * h + h * d)) :
    normalizedHomotopy d h * normalizedHomotopy d h = 0 := by
  have hc : Commute h (d * h + h * d) := by
    simp only [Commute, SemiconjBy, mul_add, add_mul, ← mul_assoc, hh, zero_mul]
    simp only [mul_assoc, hh, mul_zero, add_zero, zero_add]
  have hi := (commute_ringInverse hu hc).eq
  unfold normalizedHomotopy
  calc
    h * Ring.inverse (d * h + h * d) * (h * Ring.inverse (d * h + h * d)) =
        h * (Ring.inverse (d * h + h * d) * h) * Ring.inverse (d * h + h * d) := by
      simp only [mul_assoc]
    _ = 0 := by rw [← hi, ← mul_assoc h, hh, zero_mul, zero_mul]

/-- The normalized homotopy gives an explicit special contraction onto the zero module. -/
noncomputable def toZero (d h : Module.End S M) (hd : d * d = 0) (hh : h * h = 0)
    (hu : IsUnit (d * h + h * d)) :
    LinearSpecialContraction d (0 : Module.End S PUnit) where
  incl := 0
  proj := 0
  homotopy := normalizedHomotopy d h
  dM_comp_incl := by simp
  proj_comp_dM := by simp
  proj_comp_incl := Subsingleton.elim _ _
  dM_comp_homotopy_add_homotopy_comp_dM := by
    simpa only [LinearMap.zero_comp, sub_zero, ← Module.End.mul_eq_comp,
      ← Module.End.one_eq_id] using normalizedHomotopy_contracts d h hd hu
  homotopy_comp_incl := by simp
  proj_comp_homotopy := by simp
  homotopy_comp_homotopy := normalizedHomotopy_comp_self d h hh hu

/-- A pointwise finite geometric inverse preserves every invariant additive subgroup. -/
theorem ringInverse_one_add_mem (f : Module.End S M)
    (hnil : ∀ x, ∃ k : ℕ, (f ^ k) x = 0) (Q : AddSubgroup M)
    (hf : ∀ x ∈ Q, f x ∈ Q) {z : M} (hz : z ∈ Q) : Ring.inverse (1 + f) z ∈ Q := by
  obtain ⟨k, hk⟩ := hnil z
  have hpow (j : ℕ) : ((-f) ^ j) z ∈ Q := by
    induction j with
    | zero => simpa using hz
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact Q.neg_mem (hf _ ih)
  let y := (∑ j ∈ Finset.range k, (-f) ^ j) z
  have hy : (1 + f) y = z := by
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-f) k) z
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, neg_pow, Module.End.mul_apply, hk, map_zero, sub_zero] at h
  have hinv : Ring.inverse (1 + f) z = y := by
    rw [← hy, ← Module.End.mul_apply, Ring.inverse_mul_cancel _
      (Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero f hnil),
      Module.End.one_apply]
  rw [hinv]
  dsimp only [y]
  rw [LinearMap.sum_apply]
  exact Q.sum_mem fun j _ => hpow j

/-- Normalization preserves the filtration or grading bound of the reverse matching homotopy. -/
theorem normalizedHomotopy_mem (d h : Module.End S M)
    (hnil : ∀ x, ∃ k : ℕ, ((d * h + h * d - 1) ^ k) x = 0)
    (Q T : AddSubgroup M)
    (hrem : ∀ x ∈ Q, (d * h + h * d - 1) x ∈ Q)
    (hh : ∀ x ∈ Q, h x ∈ T) {z : M} (hz : z ∈ Q) :
    normalizedHomotopy d h z ∈ T := by
  unfold normalizedHomotopy
  rw [Module.End.mul_apply]
  apply hh
  have heq : d * h + h * d = 1 + (d * h + h * d - 1) := by abel
  rw [heq]
  exact ringInverse_one_add_mem _ hnil Q hrem hz

end Normalization

section Matching

variable {S ι α : Type*} [Ring S] [LT α]

open Classical in
/-- Reverse the unit-weight matching edges and kill the matching sources. -/
noncomputable def reverseHomotopy (d : Module.End S (ι →₀ S)) (p : ι → ι)
    (src : ι → Prop) : Module.End S (ι →₀ S) :=
  Finsupp.linearCombination S fun j =>
    if src j then 0 else Finsupp.single (p j) (Ring.inverse (d (Finsupp.single (p j) 1) j))

open Classical in
theorem reverseHomotopy_single (d : Module.End S (ι →₀ S)) (p : ι → ι)
    (src : ι → Prop) (j : ι) (c : S) :
    reverseHomotopy d p src (Finsupp.single j c) = if src j then 0 else
      Finsupp.single (p j) (c * Ring.inverse (d (Finsupp.single (p j) 1) j)) := by
  classical
  simp only [reverseHomotopy, Finsupp.linearCombination_single]
  split_ifs
  · exact smul_zero c
  · rw [Finsupp.smul_single, smul_eq_mul]

/-- Reversing a matching twice is zero, since each reverse edge ends at a source. -/
theorem reverseHomotopy_comp_self (d : Module.End S (ι →₀ S)) (p : ι → ι)
    (src : ι → Prop) (hp : Function.Involutive p) (hsrc : ∀ i, src i ↔ ¬src (p i)) :
    reverseHomotopy d p src * reverseHomotopy d p src = 0 := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    reverseHomotopy_single, LinearMap.zero_apply]
  by_cases hi : src i
  · simp [hi]
  · have hpi : src (p i) := by rw [hsrc (p i), hp i]; exact hi
    simp [hi, reverseHomotopy_single, hpi]

/-- The matching commutator differs from the identity by a strictly lower-weight operator. -/
theorem remainder_support_lt (d : Module.End S (ι →₀ S)) (w : ι → α)
    (p : ι → ι) (src : ι → Prop) (hp : Function.Involutive p)
    (hwp : ∀ i, w (p i) = w i) (hsrc : ∀ i, src i ↔ ¬src (p i))
    (hcoef : ∀ i, src i → IsUnit (d (Finsupp.single i 1) (p i)))
    (hsupp : ∀ i, ∀ j ∈ (d (Finsupp.single i 1)).support,
      w j < w i ∨ (src i ∧ j = p i)) :
    ∀ i, ∀ j ∈ ((d * reverseHomotopy d p src + reverseHomotopy d p src * d - 1)
      (Finsupp.single i 1)).support, w j < w i := by
  classical
  let h := reverseHomotopy d p src
  have hh := reverseHomotopy_single d p src
  -- `h` preserves the span of the basis vectors of weight below `a`.
  have hlow : ∀ a v, v ∈ supported S S {j | w j < a} → h v ∈ supported S S {j | w j < a} := by
    intro a v hv
    rw [← Finsupp.sum_single v, map_finsuppSum]
    refine Submodule.sum_mem _ fun j hj ↦ ?_
    dsimp only
    rw [hh]
    split_ifs
    · exact Submodule.zero_mem _
    · refine single_mem_supported S _ ?_
      rw [Set.mem_ofPred_eq, hwp]
      exact (mem_supported S v).1 hv hj
  -- The terms of `d` on a source other than the matching term have lower weight.
  have hsrc_low : ∀ k, src k → d (Finsupp.single k 1) -
      Finsupp.single (p k) (d (Finsupp.single k 1) (p k)) ∈ supported S S {j | w j < w k} := by
    intro k _
    refine (mem_supported S _).2 fun j hj ↦ ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply] at hj
    by_cases hjk : j = p k
    · subst hjk
      simp at hj
    · rw [Finsupp.single_eq_of_ne hjk, sub_zero] at hj
      exact (hsupp k j (Finsupp.mem_support_iff.2 hj)).resolve_right fun h' ↦ hjk h'.2
  intro i
  suffices H : (d * h + h * d - 1 : Module.End S (ι →₀ S)) (Finsupp.single i 1) ∈
      supported S S {j | w j < w i} from fun j hj ↦ (mem_supported S _).1 H hj
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply]
  by_cases hi : src i
  · -- `h` kills the source `i` and sends the matching term of `d i` back to `i`.
    have hpi : ¬src (p i) := (hsrc i).1 hi
    have hpair : h (Finsupp.single (p i) (d (Finsupp.single i 1) (p i))) = Finsupp.single i 1 := by
      rw [hh, if_neg hpi, hp i, Ring.mul_inverse_cancel _ (hcoef i hi)]
    have heq : d (h (Finsupp.single i 1)) + h (d (Finsupp.single i 1)) - Finsupp.single i 1 =
        h (d (Finsupp.single i 1) - Finsupp.single (p i) (d (Finsupp.single i 1) (p i))) := by
      rw [map_sub, hpair]
      simp [h, reverseHomotopy_single, hi]
    rw [heq]
    exact hlow _ _ (hsrc_low i hi)
  · -- `h` sends the non-source `i` to `u⁻¹ • p i`, where `u` is the coefficient of `i` in
    -- `d (p i)`, and `d (u⁻¹ • p i)` is `i` up to lower terms.
    have hpi : src (p i) := by rw [hsrc (p i), hp i]; exact hi
    have hu : IsUnit (d (Finsupp.single (p i) 1) i) := by simpa only [hp i] using hcoef (p i) hpi
    have hr : d (Finsupp.single (p i) 1) - Finsupp.single i (d (Finsupp.single (p i) 1) i) ∈
        supported S S {j | w j < w i} := by
      simpa only [hp i, hwp] using hsrc_low (p i) hpi
    have hdh : d (h (Finsupp.single i 1)) =
        Ring.inverse (d (Finsupp.single (p i) 1) i) • d (Finsupp.single (p i) 1) := by
      rw [hh, if_neg hi, one_mul, ← map_smul, Finsupp.smul_single_one]
    have hcancel : Ring.inverse (d (Finsupp.single (p i) 1) i) •
        Finsupp.single i (d (Finsupp.single (p i) 1) i) = Finsupp.single i 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, Ring.inverse_mul_cancel _ hu]
    have heq : d (h (Finsupp.single i 1)) + h (d (Finsupp.single i 1)) - Finsupp.single i 1 =
        Ring.inverse (d (Finsupp.single (p i) 1) i) •
            (d (Finsupp.single (p i) 1) - Finsupp.single i (d (Finsupp.single (p i) 1) i)) +
          h (d (Finsupp.single i 1)) := by
      rw [hdh, smul_sub, hcancel]
      abel
    rw [heq]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ hr)
      (hlow _ _ ((mem_supported S _).2 fun j hj ↦ ?_))
    exact (hsupp i j hj).resolve_right fun h' ↦ hi h'.1


/-- The matching commutator is invertible by the finite geometric-series argument. -/
theorem isUnit_commutator (d : Module.End S (ι →₀ S)) (w : ι → α)
    (hw : WellFounded (InvImage (· < ·) w)) (p : ι → ι) (src : ι → Prop)
    (hp : Function.Involutive p) (hwp : ∀ i, w (p i) = w i)
    (hsrc : ∀ i, src i ↔ ¬src (p i))
    (hcoef : ∀ i, src i → IsUnit (d (Finsupp.single i 1) (p i)))
    (hsupp : ∀ i, ∀ j ∈ (d (Finsupp.single i 1)).support,
      w j < w i ∨ (src i ∧ j = p i)) :
    IsUnit (d * reverseHomotopy d p src + reverseHomotopy d p src * d) := by
  have hn := Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt _ w hw
    (remainder_support_lt d w p src hp hwp hsrc hcoef hsupp)
  have hu := Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _ hn
  convert hu using 1
  abel

/-- A well-founded perfect matching supplies an explicit special contraction onto zero. -/
noncomputable def ofMatching (d : Module.End S (ι →₀ S)) (hd : d * d = 0)
    (w : ι → α) (hw : WellFounded (InvImage (· < ·) w)) (p : ι → ι) (src : ι → Prop)
    (hp : Function.Involutive p) (hwp : ∀ i, w (p i) = w i)
    (hsrc : ∀ i, src i ↔ ¬src (p i))
    (hcoef : ∀ i, src i → IsUnit (d (Finsupp.single i 1) (p i)))
    (hsupp : ∀ i, ∀ j ∈ (d (Finsupp.single i 1)).support,
      w j < w i ∨ (src i ∧ j = p i)) : LinearSpecialContraction d (0 : Module.End S PUnit) :=
  toZero d (reverseHomotopy d p src) hd (reverseHomotopy_comp_self d p src hp hsrc)
    (isUnit_commutator d w hw p src hp hwp hsrc hcoef hsupp)

end Matching


end MatchingContraction

end OnLeConjecture.KnotFloer
