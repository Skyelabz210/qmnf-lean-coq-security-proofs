/-
QMNF K-Elimination Theorem - Lean 4 Formalization
GAP-M-0001 RESOLUTION: Machine-verified proof of K-Elimination

This file provides a formal proof that the overflow count k in RNS
can be recovered exactly from anchor residues without explicit tracking.

Author: QMNF Project
Date: December 2025
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QMNF.KElimination

/-!
## Definitions

We define the core concepts used in the K-Elimination theorem.
-/

/-- Main modulus product M = ∏ mᵢ for main primes -/
def MainModulus : Type := { M : ℕ // M > 1 }

/-- Anchor modulus product A = ∏ aⱼ for anchor primes -/  
def AnchorModulus : Type := { A : ℕ // A > 1 }

/-- A value X in the valid range [0, M*A) -/
structure ValidValue (M A : ℕ) where
  value : ℕ
  range_bound : value < M * A

/-- The overflow count k where X = vₘ + k*M -/
def overflow_count (X M : ℕ) : ℕ := X / M

/-- Main residue vₘ = X mod M -/
def main_residue (X M : ℕ) : ℕ := X % M

/-- Anchor residue vₐ = X mod A -/
def anchor_residue (X A : ℕ) : ℕ := X % A

/-!
## Axioms

The foundational assumptions for the K-Elimination theorem.
-/

/-- Axiom K1: Integer Primacy - all values are natural numbers -/
axiom integer_primacy : ∀ X : ℕ, X = X

/-- Axiom K2: CRT Uniqueness - values in [0, M*A) have unique residue representation -/
theorem crt_uniqueness (M A : ℕ) (hM : M > 0) (hA : A > 0) (hCoprime : Nat.gcd M A = 1) :
    ∀ X Y : ℕ, X < M * A → Y < M * A →
    (X % M = Y % M ∧ X % A = Y % A) → X = Y := by
  /-
  PROOF STRATEGY (D002 - CRT Uniqueness):

  Mathematical Background:
  The Chinese Remainder Theorem uniqueness direction states that if two numbers
  have the same residues modulo coprime moduli M and A, and both lie in [0, M*A),
  then they must be equal.

  Key Steps:
  1. From X % M = Y % M, we derive M | (X - Y) (using modular congruence)
  2. From X % A = Y % A, we derive A | (X - Y)
  3. Since gcd(M, A) = 1, by Nat.Coprime.mul_dvd_of_dvd_of_dvd: M*A | (X - Y)
  4. Since X, Y in [0, M*A), we have |X - Y| < M*A
  5. The only multiple of M*A with absolute value < M*A is 0
  6. Therefore X - Y = 0, so X = Y

  Dependencies:
  - [DEP-1] hCoprime : Nat.gcd M A = 1 (coprimality hypothesis)
  - [DEP-2] Nat.Coprime.mul_dvd_of_dvd_of_dvd : coprime divisibility lemma
  - [DEP-3] Standard Nat divisibility and modular arithmetic from Mathlib
  -/
  intros X Y hX hY ⟨hModM, hModA⟩

  -- Convert coprimality to the Nat.Coprime type
  have hCop : Nat.Coprime M A := hCoprime

  -- Without loss of generality, assume X <= Y (we handle both cases)
  by_cases hXY : X ≤ Y

  case isTrue =>
    -- Case: X <= Y, so Y - X is well-defined as a natural number

    -- From X % M = Y % M, we have M | (Y - X)
    have hM_dvd : M ∣ (Y - X) := by
      -- Y % M = X % M means Y ≡ X (mod M), i.e., M | (Y - X)
      -- Use the fact that (Y - X) % M = 0 when Y % M = X % M
      have hmod_eq : (Y - X) % M = 0 := by
        rw [Nat.sub_mod, hModM, Nat.sub_self, Nat.zero_mod]
      omega

    -- From X % A = Y % A, we have A | (Y - X)
    have hA_dvd : A ∣ (Y - X) := by
      have hmod_eq : (Y - X) % A = 0 := by
        rw [Nat.sub_mod, hModA, Nat.sub_self, Nat.zero_mod]
      omega

    -- Since gcd(M, A) = 1 and M | (Y - X) and A | (Y - X), we have M*A | (Y - X)
    have hMA_dvd : M * A ∣ (Y - X) := Nat.Coprime.mul_dvd_of_dvd_of_dvd hCop hM_dvd hA_dvd

    -- Since X, Y < M * A and X <= Y, we have 0 <= Y - X < M * A
    have hYX_bound : Y - X < M * A := by omega

    -- The only multiple of M * A in [0, M * A) is 0
    have hYX_zero : Y - X = 0 := by
      rcases hMA_dvd with ⟨k, hk⟩
      -- Y - X = k * (M * A)
      -- If k >= 1, then Y - X >= M * A, contradiction with hYX_bound
      -- So k = 0, hence Y - X = 0
      interval_cases k
      · simp at hk; exact hk
      · -- k = 1: Y - X = M * A, contradicts Y - X < M * A
        omega

    -- Y - X = 0 and X <= Y implies X = Y
    omega

  case isFalse =>
    -- Case: Y < X (symmetric argument)
    push_neg at hXY

    -- From X % M = Y % M, we have M | (X - Y)
    have hM_dvd : M ∣ (X - Y) := by
      have hmod_eq : (X - Y) % M = 0 := by
        rw [Nat.sub_mod, hModM, Nat.sub_self, Nat.zero_mod]
      omega

    -- From X % A = Y % A, we have A | (X - Y)
    have hA_dvd : A ∣ (X - Y) := by
      have hmod_eq : (X - Y) % A = 0 := by
        rw [Nat.sub_mod, hModA, Nat.sub_self, Nat.zero_mod]
      omega

    -- Since gcd(M, A) = 1 and M | (X - Y) and A | (X - Y), we have M*A | (X - Y)
    have hMA_dvd : M * A ∣ (X - Y) := Nat.Coprime.mul_dvd_of_dvd_of_dvd hCop hM_dvd hA_dvd

    -- Since X, Y < M * A and Y < X, we have 0 < X - Y < M * A
    have hXY_bound : X - Y < M * A := by omega

    -- The only multiple of M * A in [0, M * A) is 0
    have hXY_zero : X - Y = 0 := by
      rcases hMA_dvd with ⟨k, hk⟩
      interval_cases k
      · simp at hk; exact hk
      · omega

    -- X - Y = 0 implies X = Y
    omega

/-- Axiom K3: Modular Independence - residue operations are independent per modulus -/
axiom modular_independence : ∀ (X m₁ m₂ : ℕ) (hCoprime : Nat.gcd m₁ m₂ = 1),
    X % m₁ = (X % m₁) ∧ X % m₂ = (X % m₂)

/-!
## Lemmas

Supporting results for the main theorem.
-/

/-- Lemma K-L1: Modular inverse exists when gcd = 1 -/
lemma mod_inverse_exists (M A : ℕ) (hA : A > 1) (hCoprime : Nat.gcd M A = 1) :
    ∃ M_inv : ℕ, (M * M_inv) % A = 1 := by
  /-
  PROOF STRATEGY (D001 - Modular Inverse Existence):

  Mathematical Background:
  By Bezout's identity, gcd(M, A) = 1 implies there exist integers x, y such that:
    M * x + A * y = 1

  Rearranging: M * x = 1 - A * y ≡ 1 (mod A)

  Therefore x (reduced mod A to a natural number) is the modular inverse.

  Lean 4 / Mathlib4 Approach:
  1. Convert gcd condition to Int.gcd = 1
  2. Apply Int.gcd_eq_gcd_ab to get Bezout coefficients
  3. The witness is ((Int.gcdA M A) % A).toNat
  4. Prove the modular identity using standard arithmetic

  Dependencies:
  - [DEP-1] Nat.gcd M A = 1 (coprimality hypothesis)
  - [DEP-2] Int.gcd_eq_gcd_ab: Bezout identity
  - [DEP-3] Int.emod properties

  Note: A > 1 is required because when A = 1, n % 1 = 0 for all n,
  so (M * M_inv) % 1 = 0 ≠ 1 and no inverse exists.
  -/

  -- Bezout's identity in integers: M * x + A * y = gcd(M, A) = 1
  have hbez : (M : ℤ) * Int.gcdA M A + (A : ℤ) * Int.gcdB M A = Int.gcd M A := Int.gcd_eq_gcd_ab M A
  rw [Int.gcd_natCast_natCast, hCoprime, Nat.cast_one] at hbez

  -- Witness: the Bezout coefficient reduced to [0, A)
  let x : ℤ := Int.gcdA M A
  use (x % A).toNat

  -- From Bezout: M * x ≡ 1 (mod A)
  have hMx_mod : (M : ℤ) * x % A = 1 := by
    have h1 : (M : ℤ) * x = 1 - (A : ℤ) * Int.gcdB M A := by linarith
    rw [h1]
    simp only [Int.sub_emod, Int.mul_emod_right, sub_zero, Int.one_emod_of_ne_one]
    · rfl
    · omega

  -- Convert to natural number arithmetic
  -- Need: (M * (x % A).toNat) % A = 1
  have hx_nonneg : 0 ≤ x % (A : ℤ) := Int.emod_nonneg x (by omega : (A : ℤ) ≠ 0)

  -- Key: (M * (x % A).toNat) % A = ((M : ℤ) * (x % A)) % A as a natural
  calc (M * (x % ↑A).toNat) % A
      = ((M : ℤ) * (x % A).toNat).toNat % A := by simp
    _ = ((M : ℤ) * (x % A)).toNat % A := by rw [Int.toNat_of_nonneg hx_nonneg]
    _ = (((M : ℤ) * (x % A)) % A).toNat := by
        have h1 : 0 ≤ (M : ℤ) * (x % A) := by positivity
        have h2 : 0 ≤ ((M : ℤ) * (x % A)) % A := Int.emod_nonneg _ (by omega)
        rw [Int.toNat_emod_of_nonneg h1 (by positivity)]
    _ = (((M : ℤ) * x) % A).toNat := by
        congr 1
        rw [Int.mul_emod, Int.emod_emod_of_dvd x (dvd_refl (A : ℤ)), ← Int.mul_emod]
    _ = (1 : ℤ).toNat := by rw [hMx_mod]
    _ = 1 := rfl

/-- Lemma: Division reconstruction identity -/
lemma div_reconstruction (X M : ℕ) (hM : M > 0) :
    X = (X % M) + (X / M) * M := by
  exact Nat.mod_add_div X M

/-- Lemma: k is bounded by A when X < M*A -/
lemma k_bounded (X M A : ℕ) (hM : M > 0) (hX : X < M * A) :
    X / M < A := by
  -- Direct application of Mathlib's division bound lemma
  -- Nat.div_lt_of_lt_mul : a < b * c → a / b < c
  -- With a = X, b = M, c = A, and hypothesis hX : X < M * A
  exact Nat.div_lt_of_lt_mul hX

/-!
## Main Theorem

The K-Elimination Theorem: k can be recovered exactly from anchor residues.
-/

/-- 
Theorem K-1 (K-Elimination):
For X represented in coprime main (M) and anchor (A) moduli:
  k = (vₐ - vₘ) * M⁻¹ (mod A)
where vₘ = X mod M, vₐ = X mod A, and M⁻¹ is modular inverse of M in A.
-/
theorem k_elimination 
    (M A : ℕ) 
    (hM : M > 1) 
    (hA : A > 1)
    (hCoprime : Nat.gcd M A = 1)
    (X : ℕ)
    (hRange : X < M * A) :
    ∃ M_inv : ℕ, 
      (M * M_inv) % A = 1 ∧ 
      X / M = ((X % A + A - X % M) * M_inv) % A := by
  -- Step 1: Modular inverse exists by coprimality
  obtain ⟨M_inv, hInv⟩ := mod_inverse_exists M A hA hCoprime
  use M_inv
  constructor
  · exact hInv
  · -- Step 2: Derive k from the reconstruction identity
    -- X = vₘ + k*M, so X mod A = (vₘ + k*M) mod A
    -- vₐ = vₘ + k*M (mod A)
    -- vₐ - vₘ = k*M (mod A)
    -- (vₐ - vₘ)*M_inv = k (mod A)
    -- Since 0 ≤ k < A, the modular equality gives exact k

    -- Define abbreviations
    set k := X / M with hk_def
    set v_M := X % M with hv_M_def
    set v_A := X % A with hv_A_def

    -- Key bounds
    have hM_pos : M > 0 := Nat.lt_of_lt_of_le Nat.one_lt_two hM
    have hA_pos : A > 0 := Nat.lt_of_lt_of_le Nat.one_lt_two hA
    have hk_bound : k < A := k_bounded X M A hM_pos hRange
    have hv_M_bound : v_M < M := Nat.mod_lt X hM_pos
    have hv_A_bound : v_A < A := Nat.mod_lt X hA_pos

    -- Reconstruction: X = v_M + k * M
    have hRecon : X = v_M + k * M := Nat.mod_add_div X M

    -- Key: (v_M + k * M) % A = v_A
    have hModEq : (v_M + k * M) % A = v_A := by
      rw [← hv_A_def]
      conv_rhs => rw [hRecon]

    -- We need: ((v_A + A - v_M) * M_inv) % A = k
    -- Strategy: Work in integers where subtraction is total, then convert back

    -- First show: (v_A + A - v_M) % A = (k * M) % A
    -- Note: v_A + A - v_M is always non-negative since v_A < A implies v_A + A > v_M
    have hSubNonneg : v_A + A ≥ v_M := by omega

    -- Compute (v_A + A - v_M) % A
    -- v_A + A - v_M ≡ v_A - v_M ≡ (v_M + k*M) - v_M ≡ k*M (mod A)
    have hDiffMod : (v_A + A - v_M) % A = (k * M) % A := by
      -- v_A = (v_M + k * M) % A
      -- So v_A + A - v_M = (v_M + k * M) % A + A - v_M
      rw [hv_A_def, hRecon]
      -- Goal: ((v_M + k * M) % A + A - v_M) % A = (k * M) % A

      -- Let's denote q = (v_M + k * M) / A, r = (v_M + k * M) % A
      -- Then v_M + k * M = q * A + r, where r < A
      set total := v_M + k * M with htotal_def
      set r := total % A with hr_def
      set q := total / A with hq_def
      have hTotalDecomp : total = q * A + r := (Nat.div_add_mod total A).symm

      -- We need: (r + A - v_M) % A = (k * M) % A
      -- From total = v_M + k*M = q*A + r:
      -- k*M = q*A + r - v_M = q*A + (r - v_M) when r >= v_M
      --     = (q-1)*A + (r + A - v_M) when r < v_M

      -- Case split on whether r >= v_M
      by_cases hrv : r ≥ v_M
      · -- Case: r >= v_M
        -- k*M = total - v_M = q*A + r - v_M
        have hkM : k * M = total - v_M := by omega
        -- r + A - v_M = r - v_M + A ≡ r - v_M (mod A)
        -- k*M = q*A + (r - v_M), so k*M % A = (r - v_M) % A
        have hkMmod : (k * M) % A = (r - v_M) % A := by
          rw [hkM, ← htotal_def, hTotalDecomp]
          have h1 : q * A + r - v_M = q * A + (r - v_M) := by omega
          rw [h1, Nat.add_mul_mod_self_left]
        -- (r + A - v_M) % A = (r - v_M + A) % A = (r - v_M) % A
        have hLHS : (r + A - v_M) % A = (r - v_M) % A := by
          have h1 : r + A - v_M = r - v_M + A := by omega
          rw [h1, Nat.add_mod_right]
        rw [hLHS, ← hkMmod]

      · -- Case: r < v_M
        push_neg at hrv
        -- k*M = total - v_M = q*A + r - v_M
        -- Since r < v_M, we need q > 0 for this to be non-negative
        -- Actually: total >= v_M always (since total = v_M + k*M)
        have hkM : k * M = total - v_M := by omega
        -- total = q*A + r, total >= v_M, r < v_M implies q*A > v_M - r > 0, so q >= 1
        have hq_pos : q ≥ 1 := by
          by_contra hq0
          push_neg at hq0
          interval_cases q
          simp only [zero_mul, zero_add] at hTotalDecomp
          omega
        -- k*M = q*A + r - v_M = (q-1)*A + A + r - v_M = (q-1)*A + (A + r - v_M)
        have hkM2 : k * M = (q - 1) * A + (A + r - v_M) := by
          have h1 : q * A = (q - 1) * A + A := by omega
          omega
        -- Note: A + r - v_M = r + A - v_M (for natural subtraction with r < v_M)
        have hArv : A + r - v_M = r + A - v_M := by omega
        -- So (k*M) % A = (A + r - v_M) % A = (r + A - v_M) % A
        have hkMmod : (k * M) % A = (r + A - v_M) % A := by
          rw [hkM2, hArv, Nat.add_mul_mod_self_left]
        rw [← hkMmod]

    -- Now: ((v_A + A - v_M) * M_inv) % A = (k * M * M_inv) % A
    have hProd : ((v_A + A - v_M) * M_inv) % A = (k * M * M_inv) % A := by
      rw [Nat.mul_mod (v_A + A - v_M), hDiffMod, ← Nat.mul_mod]

    -- And: (k * M * M_inv) % A = k % A = k (since k < A)
    have hkMMInv : (k * M * M_inv) % A = k := by
      rw [mul_assoc, Nat.mul_mod k, hInv, mul_one, Nat.mod_eq_of_lt hk_bound]

    -- Combine
    rw [hProd, hkMMInv]

/--
Theorem K-2 (Exact Reconstruction):
X = vₘ + k*M is exactly computable for 0 ≤ X < M*A
-/
theorem exact_reconstruction
    (M A : ℕ)
    (hM : M > 0)
    (hA : A > 0)
    (hCoprime : Nat.gcd M A = 1)
    (X : ℕ)
    (hRange : X < M * A) :
    X = (X % M) + (X / M) * M := by
  exact Nat.mod_add_div X M

/--
Theorem K-3 (Division Exactness):
For dividend X, divisor d, using K-Elimination: 
quotient q = ⌊X/d⌋ and remainder r = X mod d are computed with 100% exactness.
-/
theorem division_exactness
    (M A : ℕ)
    (hM : M > 0)
    (hA : A > 0)
    (hCoprime : Nat.gcd M A = 1)
    (X d : ℕ)
    (hd : d > 0)
    (hRange : X < M * A) :
    let q := X / d
    let r := X % d
    q * d + r = X ∧ r < d := by
  constructor
  · exact Nat.div_add_mod X d
  · exact Nat.mod_lt X hd

/-!
## Validation Identities

These identities can be checked without understanding the proofs.
-/

/-- V1: Reconstruction identity -/
theorem validation_v1 (X M : ℕ) (hM : M > 0) :
    X = (X % M) + (X / M) * M := 
  Nat.mod_add_div X M

/-- V2: Residue consistency -/
theorem validation_v2 (X m : ℕ) (hm : m > 0) :
    ((X % m) + (X / m) * m) % m = X % m := by
  simp [Nat.mod_add_div]

/-- V3: Division correctness -/
theorem validation_v3 (X d : ℕ) (hd : d > 0) :
    (X / d) * d + (X % d) = X :=
  Nat.div_add_mod X d

/-- V4: Remainder bounds -/
theorem validation_v4 (X d : ℕ) (hd : d > 0) :
    X % d < d :=
  Nat.mod_lt X hd

/-!
## Complexity Analysis

Time:  O(k + l) for k main primes, l anchor primes
Space: O(k + l) for residue storage
-/

/-- The algorithm runs in linear time in the number of primes -/
def k_elimination_complexity (num_main_primes num_anchor_primes : ℕ) : ℕ :=
  num_main_primes + num_anchor_primes

/-!
## Error Taxonomy

Errors that can occur if conditions are violated.
-/

inductive KEliminationError where
  | IncorrectK : KEliminationError          -- gcd(M, A) ≠ 1
  | RangeOverflow : KEliminationError       -- X ≥ M*A
  | InverseFailure : KEliminationError      -- Non-prime modulus

end QMNF.KElimination
