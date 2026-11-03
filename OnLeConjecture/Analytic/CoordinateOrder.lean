/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AdicSeparated
public import OnLeConjecture.Analytic.Finite
public import OnLeConjecture.Analytic.Dimension
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Order of the coordinate ideal

For a finite pointed analytic map with positive source dimension, the order of
its coordinate ideal is the largest power of the maximal ideal that contains
it. This is the integer denoted by `d` in the reduction theorem.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

theorem coordinateIdeal_ne_bot_of_isFiniteAtOrigin
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    f.1.coordinateIdeal ≠ ⊥ := by
  intro hbot
  have hradical := f.radical_coordinateIdeal_eq_maximalIdeal hfinite
  rw [hbot, Ideal.radical_bot_of_isReduced] at hradical
  let i : Fin n := ⟨0, hn⟩
  have hi : Germ.coordinate i ∈ Germ.maximalIdeal n :=
    Germ.coordinate_mem_maximalIdeal i
  rw [← hradical] at hi
  exact Germ.coordinate_ne_zero i (by simpa only [Ideal.mem_bot] using hi)

theorem exists_not_coordinateIdeal_le_maximalIdeal_pow_succ
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    ∃ k : ℕ,
      ¬f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ (k + 1) := by
  by_contra h
  push Not at h
  have hall : ∀ k : ℕ,
      f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ k := by
    intro k
    cases k with
    | zero =>
        rw [pow_zero, Ideal.one_eq_top]
        exact le_top
    | succ k => exact h k
  have hinf : f.1.coordinateIdeal ≤
      ⨅ k : ℕ, Germ.maximalIdeal n ^ k := le_iInf hall
  rw [Germ.iInf_maximalIdeal_pow] at hinf
  exact coordinateIdeal_ne_bot_of_isFiniteAtOrigin hn f hfinite
    (le_bot_iff.mp hinf)

/-- The order of the coordinate ideal of a finite pointed map germ. -/
@[expose] noncomputable def coordinateOrder {n m : ℕ} (hn : 0 < n)
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin) : ℕ := by
  classical
  exact Nat.find
    (exists_not_coordinateIdeal_le_maximalIdeal_pow_succ hn f hfinite)

/-- The coordinate ideal is contained in the power indexed by its order. -/
theorem coordinateIdeal_le_maximalIdeal_pow_coordinateOrder
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    f.1.coordinateIdeal ≤
      Germ.maximalIdeal n ^ f.coordinateOrder hn hfinite := by
  classical
  by_cases hzero : f.coordinateOrder hn hfinite = 0
  · rw [hzero, pow_zero, Ideal.one_eq_top]
    exact le_top
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [hk]
    have hlt : k < f.coordinateOrder hn hfinite := by omega
    rw [coordinateOrder] at hlt
    have hminimal := @Nat.find_min
      (fun j : ℕ ↦
        ¬f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ (j + 1))
      _
      (exists_not_coordinateIdeal_le_maximalIdeal_pow_succ hn f hfinite)
      k hlt
    simpa only [not_not] using hminimal

/-- The coordinate ideal is not contained in the next power of the maximal
ideal. -/
theorem not_coordinateIdeal_le_maximalIdeal_pow_coordinateOrder_add_one
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    ¬f.1.coordinateIdeal ≤
      Germ.maximalIdeal n ^ (f.coordinateOrder hn hfinite + 1) := by
  classical
  unfold coordinateOrder
  exact Nat.find_spec
    (exists_not_coordinateIdeal_le_maximalIdeal_pow_succ hn f hfinite)

/-- Every component belongs to the power indexed by the coordinate order. -/
theorem component_mem_maximalIdeal_pow_coordinateOrder
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) (i : Fin m) :
    f.1.component i ∈
      Germ.maximalIdeal n ^ f.coordinateOrder hn hfinite := by
  exact f.coordinateIdeal_le_maximalIdeal_pow_coordinateOrder hn hfinite
    (f.1.component_mem_coordinateIdeal i)

/-- At least one component does not belong to the power following the
coordinate order. -/
theorem exists_component_not_mem_maximalIdeal_pow_coordinateOrder_add_one
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    ∃ i : Fin m,
      f.1.component i ∉
        Germ.maximalIdeal n ^ (f.coordinateOrder hn hfinite + 1) := by
  classical
  by_contra h
  push Not at h
  apply f.not_coordinateIdeal_le_maximalIdeal_pow_coordinateOrder_add_one
    hn hfinite
  rw [MapGerm.coordinateIdeal_le]
  exact h

/-- The coordinate ideal of a pointed finite germ has positive order. -/
theorem coordinateOrder_pos
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    0 < f.coordinateOrder hn hfinite := by
  by_contra hnot
  have hzero : f.coordinateOrder hn hfinite = 0 := by omega
  have hfailure :=
    f.not_coordinateIdeal_le_maximalIdeal_pow_coordinateOrder_add_one
      hn hfinite
  rw [hzero, zero_add, pow_one] at hfailure
  exact hfailure f.coordinateIdeal_le_maximalIdeal

/-- If the differential vanishes, then the coordinate ideal has order at
least two. -/
theorem two_le_coordinateOrder_of_differential_eq_zero
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) (hdf : f.differential = 0) :
    2 ≤ f.coordinateOrder hn hfinite := by
  have hsq : f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ 2 :=
    (f.differential_eq_zero_iff_coordinateIdeal_le_sq).mp hdf
  by_contra hnot
  have hsmall : f.coordinateOrder hn hfinite = 0 ∨
      f.coordinateOrder hn hfinite = 1 := by omega
  rcases hsmall with hzero | hone
  · have hmaximal : f.1.coordinateIdeal ≤ Germ.maximalIdeal n :=
      f.coordinateIdeal_le_maximalIdeal
    have hfailure :=
      f.not_coordinateIdeal_le_maximalIdeal_pow_coordinateOrder_add_one
        hn hfinite
    rw [hzero, zero_add, pow_one] at hfailure
    exact hfailure hmaximal
  · have hfailure :=
      f.not_coordinateIdeal_le_maximalIdeal_pow_coordinateOrder_add_one
        hn hfinite
    rw [hone] at hfailure
    norm_num at hfailure
    exact hfailure hsq

/-- A finite pointed germ of coordinate order one has nonzero differential. -/
theorem differential_ne_zero_of_coordinateOrder_eq_one
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin)
    (horder : f.coordinateOrder hn hfinite = 1) :
    f.differential ≠ 0 := by
  intro hdf
  have htwo :=
    f.two_le_coordinateOrder_of_differential_eq_zero hn hfinite hdf
  omega

private theorem ideal_le_iff_map_le_map_equiv {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) (I J : Ideal R) :
    I ≤ J ↔ Ideal.map e.toRingHom I ≤ Ideal.map e.toRingHom J := by
  constructor
  · exact Ideal.map_mono
  · intro h
    have hmap := Ideal.map_mono (f := e.symm.toRingHom) h
    simpa only [Ideal.map_map, RingEquiv.toRingHom_eq_coe,
      RingEquiv.symm_comp, RingHom.coe_coe, Ideal.map_id] using hmap

/-- Right left equivalent finite map germs have the same coordinate ideal
order. -/
theorem RightLeftEquivalent.coordinateOrder_eq
    {n m : ℕ} (hn : 0 < n) {f g : PointedMapGerm n m}
    (hfg : f.RightLeftEquivalent g)
    (hf : f.IsFiniteAtOrigin) (hg : g.IsFiniteAtOrigin) :
    f.coordinateOrder hn hf = g.coordinateOrder hn hg := by
  classical
  rcases hfg.exists_map_coordinateIdeal with ⟨source, hcoordinate⟩
  have hpower : ∀ k : ℕ,
      Ideal.map source.pullbackRingEquiv.toRingHom
          (Germ.maximalIdeal n ^ k) = Germ.maximalIdeal n ^ k := by
    intro k
    rw [Ideal.map_pow, source.map_maximalIdeal_pullbackRingEquiv]
  have hcontain : ∀ k : ℕ,
      f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ k ↔
        g.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ k := by
    intro k
    calc
      f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ k ↔
          Ideal.map source.pullbackRingEquiv.toRingHom
              f.1.coordinateIdeal ≤
            Ideal.map source.pullbackRingEquiv.toRingHom
              (Germ.maximalIdeal n ^ k) :=
        ideal_le_iff_map_le_map_equiv
          source.pullbackRingEquiv f.1.coordinateIdeal
            (Germ.maximalIdeal n ^ k)
      _ ↔ g.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ k := by
        rw [hcoordinate, hpower]
  unfold coordinateOrder
  apply Nat.find_congr'
  exact fun {_k} ↦ not_congr (hcontain (_k + 1))

end PointedMapGerm

end OnLeConjecture.Analytic
