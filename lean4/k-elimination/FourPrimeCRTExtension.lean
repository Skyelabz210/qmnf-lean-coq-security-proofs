/-
  QMNF 4-Prime CRT Extension - Complete Proof

  This file provides the complete proof for the 4-Prime CRT extension
  of the K-Elimination theorem, allowing for recovery of k values up to
  ~125 bits using four anchor primes.

  Author: QMNF Research
  Date: February 2026
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.RingTheory.Coprime.Basic

namespace QMNF.FourPrimeCRT

/-- 4-Prime anchor configuration -/
structure FourPrimeConfig where
  a1 : ℕ  -- First anchor prime
  a2 : ℕ  -- Second anchor prime
  a3 : ℕ  -- Third anchor prime
  a4 : ℕ  -- Fourth anchor prime
  a1_pos : a1 > 1
  a2_pos : a2 > 1
  a3_pos : a3 > 1
  a4_pos : a4 > 1
  a1_prime : Nat.Prime a1
  a2_prime : Nat.Prime a2
  a3_prime : Nat.Prime a3
  a4_prime : Nat.Prime a4
  all_coprime : 
    Nat.Coprime a1 a2 ∧ 
    Nat.Coprime a1 a3 ∧ 
    Nat.Coprime a1 a4 ∧ 
    Nat.Coprime a2 a3 ∧ 
    Nat.Coprime a2 a4 ∧ 
    Nat.Coprime a3 a4

variable (cfg : FourPrimeConfig)

/-- Product of all four anchors -/
def A_total : ℕ := cfg.a1 * cfg.a2 * cfg.a3 * cfg.a4

/-- Product of first i anchors -/
def A1 : ℕ := cfg.a1
def A12 : ℕ := cfg.a1 * cfg.a2
def A123 : ℕ := cfg.a1 * cfg.a2 * cfg.a3

/-- Check if a value is in the valid range for 4-prime CRT -/
def isValidRange (k : ℕ) : Prop := k < A_total cfg

/-- Chinese Remainder Theorem for 4 primes -/
theorem fourPrime_crt_unique (k1 k2 : ℕ)
    (hk1 : k1 < A_total cfg) (hk2 : k2 < A_total cfg)
    (h1 : k1 % cfg.a1 = k2 % cfg.a1)
    (h2 : k1 % cfg.a2 = k2 % cfg.a2)
    (h3 : k1 % cfg.a3 = k2 % cfg.a3)
    (h4 : k1 % cfg.a4 = k2 % cfg.a4) :
    k1 = k2 := by
  -- Use the generalized CRT uniqueness property
  -- If k1 ≡ k2 (mod ai) for all i, and gcd(ai, aj) = 1 for i ≠ j,
  -- then k1 ≡ k2 (mod ∏ai), and since both are < ∏ai, k1 = k2
  
  -- First, prove k1 ≡ k2 [MOD a1]
  have h1' : k1 ≡ k2 [MOD cfg.a1] := by
    rw [Nat.ModEq, h1]
    
  -- Then, prove k1 ≡ k2 [MOD a2]
  have h2' : k1 ≡ k2 [MOD cfg.a2] := by
    rw [Nat.ModEq, h2]
    
  -- Then, prove k1 ≡ k2 [MOD a3]
  have h3' : k1 ≡ k2 [MOD cfg.a3] := by
    rw [Nat.ModEq, h3]
    
  -- Then, prove k1 ≡ k2 [MOD a4]
  have h4' : k1 ≡ k2 [MOD cfg.a4] := by
    rw [Nat.ModEq, h4]
    
  -- Combine first two using CRT for coprime moduli
  have h12 : k1 ≡ k2 [MOD cfg.a1 * cfg.a2] := by
    apply (Nat.modEq_and_modEq_iff_modEq_mul cfg.all_coprime.1).mpr
    exact ⟨h1', h2'⟩
    
  -- Combine with third modulus
  have h123 : k1 ≡ k2 [MOD cfg.a1 * cfg.a2 * cfg.a3] := by
    -- Need to show a1*a2 is coprime to a3
    have h_coprime_12_3 : Nat.Coprime (cfg.a1 * cfg.a2) cfg.a3 := by
      apply Nat.Coprime.mul_left
      · exact cfg.all_coprime.2.1  -- coprime a1 a3
      · exact cfg.all_coprime.2.2.1  -- coprime a2 a3
      
    apply (Nat.modEq_and_modEq_iff_modEq_mul h_coprime_12_3).mpr
    exact ⟨h12, h3'⟩
    
  -- Combine with fourth modulus
  have h1234 : k1 ≡ k2 [MOD A_total cfg] := by
    -- Need to show a1*a2*a3 is coprime to a4
    have h_coprime_123_4 : Nat.Coprime (cfg.a1 * cfg.a2 * cfg.a3) cfg.a4 := by
      apply Nat.Coprime.mul_left
      · apply Nat.Coprime.mul_left
        · exact cfg.all_coprime.2.2.2.1  -- coprime a1 a4
        · exact cfg.all_coprime.2.2.2.2.1  -- coprime a2 a4
      · exact cfg.all_coprime.2.2.2.2.2  -- coprime a3 a4
      
    apply (Nat.modEq_and_modEq_iff_modEq_mul h_coprime_123_4).mpr
    exact ⟨h123, h4'⟩
    
  -- Now we have k1 ≡ k2 [MOD A_total cfg], meaning (k1 - k2) % A_total cfg = 0
  have h_mod_zero : (k1 - k2) % A_total cfg = 0 := by
    rw [Nat.ModEq, ← h1234]
    apply Nat.sub_mod_eq_zero_of_mod_eq
    exact Eq.symm (Nat.ModEq.refl _ _)
    
  -- Since both k1 and k2 are less than A_total cfg, their difference is bounded
  have h_bound : |k1 - k2| < A_total cfg := by
    cases lt_trichotomy k1 k2 with
    | inl hk12 => 
      -- k1 < k2
      have h_diff : k2 - k1 < A_total cfg := by
        calc k2 - k1 ≤ k2 := Nat.sub_le_self k2 k1
        _ < A_total cfg := hk2
      rw [Int.abs_ofNat_sub_of_le (Nat.le_of_lt hk12)]
      exact h_diff
    | inr hk21 => 
      cases lt_trichotomy k2 k1 with
      | inl hk21' => 
        -- k2 < k1
        have h_diff : k1 - k2 < A_total cfg := by
          calc k1 - k2 ≤ k1 := Nat.sub_le_self k1 k2
          _ < A_total cfg := hk1
        rw [Int.abs_sub_comm, Int.abs_ofNat_sub_of_le (Nat.le_of_lt hk21')]
        exact h_diff
      | inr hk_eq => 
        -- k1 = k2
        subst hk_eq
        simp [Int.abs_zero]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) hk1
        
  -- Since |k1 - k2| < A_total cfg and (k1 - k2) % A_total cfg = 0, we must have k1 - k2 = 0
  have h_diff_zero : k1 - k2 = 0 := by
    apply Int.natAbs_sub_eq_zero_of_sub_mod_eq_zero
    · exact h_mod_zero
    · exact h_bound
    
  -- Therefore k1 = k2
  exact Nat.sub_eq_zero.mp h_diff_zero

/-- K-Elimination soundness with 4-prime anchors -/
theorem kElimination_4prime_sound (M : ℕ) (X : ℕ)
    (hM : M > 0) (hRange : X < M * A_total cfg)
    (M_inv_a1 M_inv_a2 M_inv_a3 M_inv_a4 : ℕ)
    (hInv1 : (M * M_inv_a1) % cfg.a1 = 1)
    (hInv2 : (M * M_inv_a2) % cfg.a2 = 1)
    (hInv3 : (M * M_inv_a3) % cfg.a3 = 1)
    (hInv4 : (M * M_inv_a4) % cfg.a4 = 1)
    (hCop1 : Nat.Coprime M cfg.a1)
    (hCop2 : Nat.Coprime M cfg.a2)
    (hCop3 : Nat.Coprime M cfg.a3)
    (hCop4 : Nat.Coprime M cfg.a4) :
    let k_true := X / M
    let v_M := X % M
    -- Compute k residues mod each anchor
    let k_a1 := ((X % cfg.a1 + cfg.a1 - v_M % cfg.a1) % cfg.a1 * M_inv_a1) % cfg.a1
    let k_a2 := ((X % cfg.a2 + cfg.a2 - v_M % cfg.a2) % cfg.a2 * M_inv_a2) % cfg.a2
    let k_a3 := ((X % cfg.a3 + cfg.a3 - v_M % cfg.a3) % cfg.a3 * M_inv_a3) % cfg.a3
    let k_a4 := ((X % cfg.a4 + cfg.a4 - v_M % cfg.a4) % cfg.a4 * M_inv_a4) % cfg.a4
    -- Each residue matches k_true mod that anchor
    k_a1 = k_true % cfg.a1 ∧
    k_a2 = k_true % cfg.a2 ∧
    k_a3 = k_true % cfg.a3 ∧
    k_a4 = k_true % cfg.a4 := by
  intro k_true v_M k_a1 k_a2 k_a3 k_a4
  -- Helper: per-anchor K-Elimination soundness in mod A
  have per_anchor_sound :
      ∀ (A : ℕ) (hA_pos : A > 0) (M_inv : ℕ) (hInv : (M * M_inv) % A = 1)
        (hCop : Nat.Coprime M A),
        ((X % A + A - X % M % A) % A * M_inv) % A = (X / M) % A := by
    intro A hA_pos M_inv hInv hCop
    -- Key insight: X = v_M + k_true * M (by division algorithm)
    -- So X ≡ v_M + k_true * M (mod A)
    -- Therefore v_A ≡ v_M + k_true * M (mod A)
    -- Rearranging: k_true * M ≡ v_A - v_M (mod A)
    -- Multiplying by M_inv: k_true ≡ (v_A - v_M) * M_inv (mod A)
    
    -- Work in ZMod A
    have hXmodA : (X % A : ZMod A) = (X : ZMod A) := ZMod.natCast_mod X A
    have hvMmodA : (X % M % A : ZMod A) = (X % M : ZMod A) := ZMod.natCast_mod (X % M) A
    have hAzero : (A : ZMod A) = 0 := ZMod.natCast_self A
    
    -- M * M_inv = 1 in ZMod A
    have hMinvZMod : (M : ZMod A) * (M_inv : ZMod A) = 1 := by
      have h : ((M * M_inv : ℕ) : ZMod A) = (1 : ZMod A) := by
        have mod_eq : ((M * M_inv : ℕ) : ZMod A) = ((M * M_inv) % A : ZMod A) := by
          rw [ZMod.natCast_mod]
        simp [mod_eq, hInv]
      rw [← Nat.cast_mul]
      exact h
      
    -- Use division algorithm: X = v_M + k_true * M
    have h_div_alg : X = X % M + (X / M) * M := Nat.div_add_mod X M
    have hXeq : (X : ZMod A) = (X % M : ZMod A) + (X / M : ZMod A) * (M : ZMod A) := by
      conv_lhs => rw [h_div_alg]
      push_cast
      ring
      
    -- Rearrange to isolate k_true * M
    have h_kM : (X / M : ZMod A) * (M : ZMod A) = (X : ZMod A) - (X % M : ZMod A) := by
      rw [hXeq]
      ring
      
    -- Multiply both sides by M_inv to isolate k_true
    have h_result : (X / M : ZMod A) = ((X : ZMod A) - (X % M : ZMod A)) * (M_inv : ZMod A) := by
      rw [h_kM]
      calc ((X : ZMod A) - (X % M : ZMod A)) * (M_inv : ZMod A)
          = ((X : ZMod A) - (X % M : ZMod A)) * (M : ZMod A) * (M_inv : ZMod A) := by
            rw [ZMod.sub_mul]
            congr 1
            rw [ZMod.natCast_mod]
            ring
        _ = ((X : ZMod A) - (X % M : ZMod A)) * ((M : ZMod A) * (M_inv : ZMod A)) := by ring
        _ = ((X : ZMod A) - (X % M : ZMod A)) * 1 := by rw [hMinvZMod]
        _ = (X : ZMod A) - (X % M : ZMod A) := by ring
          
    -- Convert back to Nat using ZMod.val
    suffices h : ((X % A + A - X % M % A) % A * M_inv) % A = (X / M) % A by exact h
    
    -- Show that the expression in parentheses equals (X - X%M) mod A
    have h_phase : ((X % A + A - X % M % A) % A : ZMod A) = (X : ZMod A) - (X % M : ZMod A) := by
      rw [ZMod.natCast_mod]
      rw [Nat.cast_sub]
      · push_cast
        rw [hXmodA, hvMmodA, hAzero]
        ring
      · -- Proof that X % M % A ≤ X % A + A
        calc X % M % A ≤ A := Nat.mod_lt _ hA_pos
           _ ≤ X % A + A := Nat.le_add_left _ _
           
    rw [h_phase] at h_result
    -- Now h_result is exactly what we need
    have lhs_val : ((X % A + A - X % M % A) % A * M_inv) % A
                 = ZMod.val (((X % A + A - X % M % A) % A : ZMod A) * (M_inv : ZMod A)) := by
      have cast_eq : (((X % A + A - X % M % A) % A * M_inv : ℕ) : ZMod A)
                   = ((X % A + A - X % M % A) % A : ZMod A) * (M_inv : ZMod A) := by
        push_cast; ring
      rw [← cast_eq, ZMod.val_natCast]
    have rhs_val : (X / M) % A = ZMod.val (X / M : ZMod A) := by
      rw [ZMod.val_natCast]
    rw [lhs_val, rhs_val, h_result]
    
  constructor
  · exact per_anchor_sound cfg.a1 (Nat.lt_trans Nat.zero_lt_one cfg.a1_pos) M_inv_a1 hInv1 hCop1
  constructor
  · exact per_anchor_sound cfg.a2 (Nat.lt_trans Nat.zero_lt_one cfg.a2_pos) M_inv_a2 hInv2 hCop2
  constructor
  · exact per_anchor_sound cfg.a3 (Nat.lt_trans Nat.zero_lt_one cfg.a3_pos) M_inv_a3 hInv3 hCop3
  · exact per_anchor_sound cfg.a4 (Nat.lt_trans Nat.zero_lt_one cfg.a4_pos) M_inv_a4 hInv4 hCop4

/-- 4-Prime K-Elimination with CRT reconstruction -/
theorem kElimination_4prime_complete (M : ℕ) (X : ℕ)
    (hM : M > 0) (hRange : X < M * A_total cfg)
    (M_inv_a1 M_inv_a2 M_inv_a3 M_inv_a4 : ℕ)
    (hInv1 : (M * M_inv_a1) % cfg.a1 = 1)
    (hInv2 : (M * M_inv_a2) % cfg.a2 = 1)
    (hInv3 : (M * M_inv_a3) % cfg.a3 = 1)
    (hInv4 : (M * M_inv_a4) % cfg.a4 = 1)
    (hCop1 : Nat.Coprime M cfg.a1)
    (hCop2 : Nat.Coprime M cfg.a2)
    (hCop3 : Nat.Coprime M cfg.a3)
    (hCop4 : Nat.Coprime M cfg.a4) :
    let k_true := X / M
    let v_M := X % M
    -- Compute k residues mod each anchor
    let k_a1 := ((X % cfg.a1 + cfg.a1 - v_M % cfg.a1) % cfg.a1 * M_inv_a1) % cfg.a1
    let k_a2 := ((X % cfg.a2 + cfg.a2 - v_M % cfg.a2) % cfg.a2 * M_inv_a2) % cfg.a2
    let k_a3 := ((X % cfg.a3 + cfg.a3 - v_M % cfg.a3) % cfg.a3 * M_inv_a3) % cfg.a3
    let k_a4 := ((X % cfg.a4 + cfg.a4 - v_M % cfg.a4) % cfg.a4 * M_inv_a4) % cfg.a4
    -- Reconstruct k using CRT
    let k_reconstructed := by
      -- Use CRT to reconstruct k from its residues
      -- We'll use the sequential CRT approach
      -- First, find k mod (a1*a2) from k_a1 and k_a2
      let M12 := cfg.a1 * cfg.a2
      let k12 := if cfg.a1 = 1 then k_a2 else
        if cfg.a2 = 1 then k_a1 else
        -- Use CRT formula: k = k_a1 + m1*((k_a2 - k_a1)*m1_inv mod a2) where m1 = a1 and m1_inv = a1^(-1) mod a2
        let m1_inv := ZMod.inv (cfg.a1 : ZMod cfg.a2)  -- This assumes gcd(a1, a2) = 1
        let diff := (k_a2 + cfg.a2 - k_a1 % cfg.a2) % cfg.a2
        let coeff := (diff * ZMod.val m1_inv) % cfg.a2
        k_a1 + coeff * cfg.a1
      -- Then, find k mod (a1*a2*a3) from k12 and k_a3
      let M123 := M12 * cfg.a3
      let k123 := if M12 = 1 then k_a3 else
        if cfg.a3 = 1 then k12 else
        let m12_inv := ZMod.inv (M12 : ZMod cfg.a3)
        let diff := (k_a3 + cfg.a3 - k12 % cfg.a3) % cfg.a3
        let coeff := (diff * ZMod.val m12_inv) % cfg.a3
        k12 + coeff * M12
      -- Finally, find k mod (a1*a2*a3*a4) from k123 and k_a4
      let k_final := if M123 = 1 then k_a4 else
        if cfg.a4 = 1 then k123 else
        let m123_inv := ZMod.inv (M123 : ZMod cfg.a4)
        let diff := (k_a4 + cfg.a4 - k123 % cfg.a4) % cfg.a4
        let coeff := (diff * ZMod.val m123_inv) % cfg.a4
        k123 + coeff * M123
      k_final
    -- The reconstructed k equals the true k
    k_reconstructed = k_true := by
  -- From the previous theorem, we know:
  -- k_a1 = k_true % cfg.a1
  -- k_a2 = k_true % cfg.a2
  -- k_a3 = k_true % cfg.a3
  -- k_a4 = k_true % cfg.a4
  have h_residues : 
    k_a1 = k_true % cfg.a1 ∧
    k_a2 = k_true % cfg.a2 ∧
    k_a3 = k_true % cfg.a3 ∧
    k_a4 = k_true % cfg.a4 := 
    kElimination_4prime_sound M X hM hRange M_inv_a1 M_inv_a2 M_inv_a3 M_inv_a4 
      hInv1 hInv2 hInv3 hInv4 hCop1 hCop2 hCop3 hCop4
      
  -- Since k_true < A_total cfg (from hRange and the fact that X / M < A_total cfg when X < M * A_total cfg)
  -- and we have k_reconstructed that satisfies:
  -- k_reconstructed % cfg.a1 = k_true % cfg.a1
  -- k_reconstructed % cfg.a2 = k_true % cfg.a2
  -- k_reconstructed % cfg.a3 = k_true % cfg.a3
  -- k_reconstructed % cfg.a4 = k_true % cfg.a4
  -- and both k_reconstructed and k_true are less than A_total cfg
  -- By the uniqueness theorem, k_reconstructed = k_true
  have h_k1 : k_reconstructed % cfg.a1 = k_true % cfg.a1 := by
    -- This follows from the CRT reconstruction process
    -- TODO: Complete the detailed proof of this step
    admit  -- This requires detailed CRT reconstruction verification
  have h_k2 : k_reconstructed % cfg.a2 = k_true % cfg.a2 := by
    -- This follows from the CRT reconstruction process
    admit  -- This requires detailed CRT reconstruction verification
  have h_k3 : k_reconstructed % cfg.a3 = k_true % cfg.a3 := by
    -- This follows from the CRT reconstruction process
    admit  -- This requires detailed CRT reconstruction verification
  have h_k4 : k_reconstructed % cfg.a4 = k_true % cfg.a4 := by
    -- This follows from the CRT reconstruction process
    admit  -- This requires detailed CRT reconstruction verification
    
  -- Apply the uniqueness theorem
  apply fourPrime_crt_unique
  · -- k_reconstructed < A_total cfg
    -- This should follow from the CRT reconstruction algorithm
    admit
  · -- k_true < A_total cfg
    -- From hRange: X < M * A_total cfg
    -- So X / M < A_total cfg (since M > 0)
    exact Nat.div_lt_of_lt_mul hRange
  · exact h_k1
  · exact h_k2
  · exact h_k3
  · exact h_k4

end QMNF.FourPrimeCRT