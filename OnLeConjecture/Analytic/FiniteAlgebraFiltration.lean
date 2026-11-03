/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FilteredElimination
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Cofinality for a finite local algebra

For a finite algebra between Noetherian local rings, a power of the target
maximal ideal lies in the extension of the source maximal ideal. This turns
cofinality with the target maximal-ideal filtration into the cofinality
needed for filtered elimination over the source ring.
-/

public section

namespace OnLeConjecture.Analytic

variable {R B : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B]

omit [IsNoetherianRing R] in
/-- The extension of the maximal ideal of a finite local algebra has the
target maximal ideal as its radical. -/
theorem radical_map_maximalIdeal_of_finite :
    (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)).radical =
      IsLocalRing.maximalIdeal B := by
  have hcomap : Ideal.comap (algebraMap R B) (IsLocalRing.maximalIdeal B) =
      IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (R := R) (IsLocalRing.maximalIdeal B))
  apply le_antisymm
  · apply (inferInstance : (IsLocalRing.maximalIdeal B).IsPrime).radical_le_iff.mpr
    rw [Ideal.map_le_iff_le_comap, hcomap]
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro Q hQ
    obtain ⟨hmapQ, hprime⟩ := hQ
    let _ : Q.IsPrime := hprime
    have hcontains : IsLocalRing.maximalIdeal R ≤
        Ideal.comap (algebraMap R B) Q :=
      Ideal.map_le_iff_le_comap.mp hmapQ
    have heq : Ideal.comap (algebraMap R B) Q =
        IsLocalRing.maximalIdeal R :=
      le_antisymm
        (IsLocalRing.le_maximalIdeal
          (Ideal.comap_ne_top (algebraMap R B) hprime.ne_top)) hcontains
    have hmax : Q.IsMaximal := by
      apply Ideal.IsIntegral.isMaximal_of_isMaximal_comap (R := R) Q
      rw [heq]
      infer_instance
    exact (IsLocalRing.eq_maximalIdeal hmax).symm.le

/-- A power of the target maximal ideal lies in the extension of the
source maximal ideal. -/
theorem exists_maximalIdeal_pow_le_map_of_finite :
    ∃ N : ℕ, IsLocalRing.maximalIdeal B ^ N ≤
      Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) := by
  let _ : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · rw [radical_map_maximalIdeal_of_finite (R := R) (B := B)]
  · exact Ideal.fg_of_isNoetherianRing _

/-- Cofinality with the target maximal ideal implies cofinality with
powers of the source maximal ideal acting on the finite algebra. -/
theorem cofinal_source_maximalIdeal_of_target
    (F : ℕ → Submodule R B)
    (hcofinal : ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ (IsLocalRing.maximalIdeal B ^ n).restrictScalars R) :
    ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R B) := by
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map_of_finite (R := R) (B := B)
  intro n
  obtain ⟨q, hq⟩ := hcofinal (N * n)
  refine ⟨q, ?_⟩
  rw [Ideal.smul_top_eq_map]
  have hpower : IsLocalRing.maximalIdeal B ^ (N * n) ≤
      Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R ^ n) := by
    rw [pow_mul, Ideal.map_pow]
    exact pow_le_pow_left' hN n
  exact hq.trans (fun _ hx ↦ hpower hx)

/-- The filtered elimination lemma for a finite local algebra, stated
using cofinality with its own maximal ideal as in the manuscript. -/
theorem finite_algebra_filtered_elimination
    (F : ℕ → Submodule R B) (hzero : F 0 = ⊤)
    (hcofinal : ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ (IsLocalRing.maximalIdeal B ^ n).restrictScalars R)
    (x : B) :
    x ∈ LinearMap.range (Algebra.linearMap R B) ∨
      ∃ n : ℕ, ∃ a : R,
        x - algebraMap R B a ∈ F n ∧
        ∀ b : R, x - algebraMap R B a - algebraMap R B b ∉ F (n + 1) := by
  rcases filtered_elimination (LinearMap.range (Algebra.linearMap R B)) F hzero
      (cofinal_source_maximalIdeal_of_target F hcofinal) x with hmem | hrem
  · exact Or.inl hmem
  · obtain ⟨n, a, ⟨a₀, rfl⟩, ha, hterminal⟩ := hrem
    exact Or.inr ⟨n, a₀, ha, fun b ↦ hterminal _ ⟨b, rfl⟩⟩

end OnLeConjecture.Analytic
