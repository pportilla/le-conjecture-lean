/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.ResidualCollision

/-!
# The initial collision in the order two case

This file formalizes the polynomial calculation at the end of the order two
case. It includes the prepared family \(\Psi_N\), the two source points, and
the three initial differences. The first two differences have nonzero
derivatives. After restricting to their branches, the third difference is a
nonzero polynomial with a finite root set.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- The properties of the polynomial family \(\Psi_N(X,T)\) used by the
residual subgroup argument. -/
structure PreparedOddFamily (N : ℕ) where
  polynomial : ℂ → _root_.Polynomial ℂ
  monic : ∀ T, (polynomial T).Monic
  natDegree_eq : ∀ T, (polynomial T).natDegree = N
  coeff_sub_two : ∀ T, (polynomial T).coeff (N - 2) = (N : ℂ) / 2 * T
  odd : ∀ T, (polynomial T).comp (-X) = -(polynomial T)

/-- The initial map after fixing the first noninvariant coefficient. -/
noncomputable def residualInitialMap
    (k L N : ℕ) (c T : ℂ) (Ψ : PreparedOddFamily N)
    (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.2 ^ k,
    -c * (z.1 ^ 2 + T * z.2 ^ L),
    (Ψ.polynomial (T * z.2 ^ L)).eval z.1]

/-- The first difference in the chart where the first \(y\) coordinate is
one. -/
noncomputable def firstInitialDifference (k : ℕ) : _root_.Polynomial ℂ :=
  1 - X ^ k

/-- The second difference as a polynomial in the second \(x\) coordinate. -/
noncomputable def secondInitialDifference (c x : ℂ) : _root_.Polynomial ℂ :=
  C (-c) * (C (x ^ 2) - X ^ 2)

/-- The third difference after imposing the branch \(X=-x\). -/
noncomputable def restrictedThirdDifference
    (p : _root_.Polynomial ℂ) : _root_.Polynomial ℂ :=
  p - p.comp (-X)

theorem PreparedOddFamily.eval_neg
    {N : ℕ} (Ψ : PreparedOddFamily N) (T x : ℂ) :
    (Ψ.polynomial T).eval (-x) = -(Ψ.polynomial T).eval x := by
  have h := congrArg (fun p : _root_.Polynomial ℂ ↦ p.eval x) (Ψ.odd T)
  simpa [_root_.Polynomial.eval_comp] using h

theorem PreparedOddFamily.degree_odd
    {N : ℕ} (Ψ : PreparedOddFamily N) (T : ℂ) : Odd N := by
  have h := congrArg _root_.Polynomial.leadingCoeff (Ψ.odd T)
  have hpow : (-1 : ℂ) ^ N = -1 := by
    simpa [Ψ.natDegree_eq T, (Ψ.monic T).leadingCoeff] using h
  exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)).mp hpow

theorem restrictedThirdDifference_eq_two_mul
    {N : ℕ} (Ψ : PreparedOddFamily N) (T : ℂ) :
    restrictedThirdDifference (Ψ.polynomial T) = 2 * Ψ.polynomial T := by
  rw [restrictedThirdDifference, Ψ.odd]
  ring

theorem firstInitialDifference_eval_of_pow_eq_one
    {k : ℕ} {η : ℂ} (hη : η ^ k = 1) :
    (firstInitialDifference k).eval η = 0 := by
  simp [firstInitialDifference, hη]

theorem firstInitialDifference_derivative_eval (k : ℕ) (η : ℂ) :
    (firstInitialDifference k).derivative.eval η =
      -(k : ℂ) * η ^ (k - 1) := by
  simp [firstInitialDifference, _root_.Polynomial.derivative_sub,
    _root_.Polynomial.derivative_X_pow]

theorem firstInitialDifference_derivative_ne_zero
    {k : ℕ} {η : ℂ} (hk : 0 < k) (hη : η ^ k = 1) :
    (firstInitialDifference k).derivative.eval η ≠ 0 := by
  rw [firstInitialDifference_derivative_eval]
  have hη0 : η ≠ 0 := by
    intro h
    subst η
    simp [zero_pow hk.ne'] at hη
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  exact mul_ne_zero (neg_ne_zero.mpr hkC) (pow_ne_zero (k - 1) hη0)

theorem secondInitialDifference_eval (c x : ℂ) :
    (secondInitialDifference c x).eval (-x) = 0 := by
  simp [secondInitialDifference]

theorem secondInitialDifference_derivative_eval (c x : ℂ) :
    (secondInitialDifference c x).derivative.eval (-x) = -2 * c * x := by
  rw [secondInitialDifference, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_C, _root_.Polynomial.derivative_sub,
    _root_.Polynomial.derivative_C, _root_.Polynomial.derivative_X_pow]
  simp
  ring

theorem secondInitialDifference_derivative_ne_zero
    {c x : ℂ} (hc : c ≠ 0) (hx : x ≠ 0) :
    (secondInitialDifference c x).derivative.eval (-x) ≠ 0 := by
  rw [secondInitialDifference_derivative_eval]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hc) hx

/-- The algebraic data at the collision used in the last order two case. -/
structure InitialCollisionCertificate
    (k L N : ℕ) (c T : ℂ) (Ψ : PreparedOddFamily N) where
  eta : ℂ
  x : ℂ
  eta_ne_one : eta ≠ 1
  eta_pow_k : eta ^ k = 1
  eta_pow_L : eta ^ L = 1
  x_ne_zero : x ≠ 0
  source_points_ne : (x, 1) ≠ (-x, eta)
  values_eq :
    residualInitialMap k L N c T Ψ (x, 1) =
      residualInitialMap k L N c T Ψ (-x, eta)
  first_difference_zero : (firstInitialDifference k).eval eta = 0
  first_derivative_ne_zero :
    (firstInitialDifference k).derivative.eval eta ≠ 0
  second_difference_zero : (secondInitialDifference c x).eval (-x) = 0
  second_derivative_ne_zero :
    (secondInitialDifference c x).derivative.eval (-x) ≠ 0
  third_difference_zero :
    (restrictedThirdDifference (Ψ.polynomial T)).eval x = 0
  third_difference_ne_zero :
    restrictedThirdDifference (Ψ.polynomial T) ≠ 0
  third_root_set_finite :
    Set.Finite {z : ℂ |
      (restrictedThirdDifference (Ψ.polynomial T)).IsRoot z}
  third_root_set_discrete :
    IsDiscrete {z : ℂ |
      (restrictedThirdDifference (Ψ.polynomial T)).IsRoot z}

/-- A prepared family and the subgroup \(\mu_a\), where \(k=2a\), determine
distinct points with equal initial values. The first two equations have
nonzero derivatives and the roots of the restricted third equation form a
finite set. -/
theorem exists_initialCollisionCertificate
    (a k L N : ℕ) (c T : ℂ) (Ψ : PreparedOddFamily N)
    (ha : 2 ≤ a) (hk : k = 2 * a) (haL : a ∣ L)
    (hN : 3 ≤ N) (hc : c ≠ 0) (hT : T ≠ 0) :
    Nonempty (InitialCollisionCertificate k L N c T Ψ) := by
  have hak : a ∣ k := by
    rw [hk]
    exact dvd_mul_left a 2
  have hcoeff : (Ψ.polynomial T).coeff (N - 2) ≠ 0 := by
    rw [Ψ.coeff_sub_two]
    exact mul_ne_zero (div_ne_zero (by exact_mod_cast (by omega : N ≠ 0)) (by norm_num)) hT
  have hodd : ∀ z : ℂ,
      (Ψ.polynomial T).eval (-z) = -(Ψ.polynomial T).eval z :=
    Ψ.eval_neg T
  obtain ⟨η, x, hη1, hηk, hηL, hx, hpx, hpnx⟩ :=
    exists_residual_collision_coordinates
      a k L N (Ψ.polynomial T) ha hak haL (Ψ.monic T)
        (Ψ.natDegree_eq T) (by omega) hcoeff hodd
  have hpx0 : (Ψ.polynomial T).eval x = 0 := hpx
  have hpnx0 : (Ψ.polynomial T).eval (-x) = 0 := hpnx
  have hkpos : 0 < k := by omega
  have hsource : (x, 1) ≠ (-x, η) := by
    intro h
    have : (1 : ℂ) = η := congrArg Prod.snd h
    exact hη1 this.symm
  have hvalues :
      residualInitialMap k L N c T Ψ (x, 1) =
        residualInitialMap k L N c T Ψ (-x, η) := by
    funext i
    fin_cases i
    · simp [residualInitialMap, hηk]
    · simp [residualInitialMap, hηL]
    · simp [residualInitialMap, hηL, hpx0, hpnx0]
  have hthirdzero :
      (restrictedThirdDifference (Ψ.polynomial T)).eval x = 0 := by
    rw [restrictedThirdDifference_eq_two_mul]
    simp [hpx0]
  have hthirdne : restrictedThirdDifference (Ψ.polynomial T) ≠ 0 := by
    rw [restrictedThirdDifference_eq_two_mul]
    exact mul_ne_zero (by norm_num) (Ψ.monic T).ne_zero
  have hthirdfinite :
      Set.Finite {z : ℂ |
        (restrictedThirdDifference (Ψ.polynomial T)).IsRoot z} :=
    _root_.Polynomial.finite_setOfPred_isRoot hthirdne
  exact ⟨{
    eta := η
    x := x
    eta_ne_one := hη1
    eta_pow_k := hηk
    eta_pow_L := hηL
    x_ne_zero := hx
    source_points_ne := hsource
    values_eq := hvalues
    first_difference_zero := firstInitialDifference_eval_of_pow_eq_one hηk
    first_derivative_ne_zero :=
      firstInitialDifference_derivative_ne_zero hkpos hηk
    second_difference_zero := secondInitialDifference_eval c x
    second_derivative_ne_zero :=
      secondInitialDifference_derivative_ne_zero hc hx
    third_difference_zero := hthirdzero
    third_difference_ne_zero := hthirdne
    third_root_set_finite := hthirdfinite
    third_root_set_discrete := hthirdfinite.isDiscrete
  }⟩

end OnLeConjecture.DTwo
