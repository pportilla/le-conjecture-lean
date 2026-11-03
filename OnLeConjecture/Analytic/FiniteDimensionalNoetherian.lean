/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.LocalComplexGeometry.Noetherian.Ruckert
public import OnLeConjecture.Analytic.Dimension

/-!
# Noetherianity and regularity in every finite dimension

The identity on underlying function germs identifies this project's analytic
subring with the analytic subring in Bochao Kong's checked Rückert theorem.
Noetherianity transfers along that ring equivalence. The project's existing
cotangent-space and dimension calculation then proves regularity and the
expected Krull dimension, including dimension three.
-/

@[expose] public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

theorem analyticGermSubring_eq_holomorphicGermSubring (n : ℕ) :
    analyticGermSubring n = LocalComplexGeometry.holomorphicGermSubring n := by
  ext φ
  induction φ using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun]
      change AnalyticAt ℂ f 0 ↔
        ∃ h : Source n → ℂ, AnalyticAt ℂ h 0 ∧
          (h : FunctionGerm n) = (f : FunctionGerm n)
      constructor
      · intro hf
        exact ⟨f, hf, rfl⟩
      · rintro ⟨h, hh, heq⟩
        exact hh.congr (Filter.Germ.coe_eq.mp heq)

noncomputable def holomorphicGermRingEquiv (n : ℕ) :
    Germ n ≃+* LocalComplexGeometry.HolomorphicGerm n :=
  by
    change ↥(analyticGermSubring n) ≃+* ↥(LocalComplexGeometry.holomorphicGermSubring n)
    rw [analyticGermSubring_eq_holomorphicGermSubring n]

theorem Germ.isNoetherianRing_all (n : ℕ) : IsNoetherianRing (Germ n) :=
  isNoetherianRing_of_ringEquiv _ (holomorphicGermRingEquiv n).symm

theorem Germ.isRegularLocalRing_all (n : ℕ) : IsRegularLocalRing (Germ n) := by
  let := Germ.isNoetherianRing_all n
  exact Germ.isRegularLocalRing_of_isNoetherianRing n

theorem Germ.ringKrullDim_all (n : ℕ) :
    ringKrullDim (Germ n) = (n : WithBot ℕ∞) := by
  let := Germ.isNoetherianRing_all n
  exact Germ.ringKrullDim_eq_natCast n

end OnLeConjecture.Analytic
