/-
  QMNF Security Proofs - Basic Definitions

  Formalization Swarm Output
  Date: 2026-02-01
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace QMNF.Security

/-! # Part 1: Ring Definitions -/

/-- Security parameter -/
abbrev SecurityParam := ℕ

/-- Negligible function type -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, f n < (1 : ℝ) / (n ^ c : ℝ)

/-- Polynomial ring R = ℤ[X]/(X^N + 1) configuration -/
structure RingConfig where
  N : ℕ                      -- Polynomial degree (power of 2)
  N_pos : N > 0
  N_pow2 : ∃ k : ℕ, N = 2^k  -- N is power of 2
  q : ℕ                      -- Ciphertext modulus
  q_prime : Nat.Prime q
  t : ℕ                      -- Plaintext modulus
  t_pos : t > 1

/-! # Part 2: Dual-Codex (CRT) Definitions -/

/-- Coprime moduli for dual-codex representation -/
structure DualCodex where
  α_cap : ℕ
  β_cap : ℕ
  α_pos : α_cap > 0
  β_pos : β_cap > 0
  coprime : Nat.Coprime α_cap β_cap

/-- Dual-codex representation of a value -/
structure DualCodexRep (dc : DualCodex) where
  x_α : ZMod dc.α_cap
  x_β : ZMod dc.β_cap

/-- CRT reconstruction -/
def DualCodex.reconstruct (dc : DualCodex) (rep : DualCodexRep dc) : ℕ :=
  let diff := rep.x_β - (rep.x_α.val : ZMod dc.β_cap)
  let α_inv := (dc.α_cap : ZMod dc.β_cap)⁻¹
  let k := diff * α_inv
  rep.x_α.val + dc.α_cap * k.val

/-! # Part 3: K-Elimination -/

/-- K-Elimination: compute overflow count k from dual-codex representation -/
def kEliminate (dc : DualCodex) (rep : DualCodexRep dc) : ZMod dc.β_cap :=
  -- k = (x_β - x_α) · α_cap^(-1) mod β_cap
  let diff := rep.x_β - (rep.x_α.val : ZMod dc.β_cap)
  let α_inv := (dc.α_cap : ZMod dc.β_cap)⁻¹
  diff * α_inv

/-! # Part 4: K-Elimination Correctness -/

/-- K-Elimination is correct when value is in range -/
theorem kEliminate_correct (dc : DualCodex) (X : ℕ)
    (h_range : X < dc.α_cap * dc.β_cap) :
    let rep : DualCodexRep dc := ⟨(X : ZMod dc.α_cap), (X : ZMod dc.β_cap)⟩
    (kEliminate dc rep).val = X / dc.α_cap := by
  classical
  set α := dc.α_cap
  set β := dc.β_cap
  have h_range' : X < α * β := by simpa [α, β] using h_range
  have hk_lt : X / α < β := Nat.div_lt_of_lt_mul h_range'
  have hcop : Nat.Coprime α β := by simpa [α, β] using dc.coprime

  have hdiff : (X : ZMod β) - (X % α : ZMod β) = ((α * (X / α) : ℕ) : ZMod β) := by
    calc
      (X : ZMod β) - (X % α : ZMod β)
          = (((X % α) + α * (X / α) : ℕ) : ZMod β) - (X % α : ZMod β) := by
              simp [Nat.mod_add_div]
      _ = (((X % α) : ℕ) : ZMod β) + ((α * (X / α) : ℕ) : ZMod β) - (X % α : ZMod β) := by
              simp [Nat.cast_add]
      _ = ((α * (X / α) : ℕ) : ZMod β) := by
              ring

  have hk : ((X : ZMod β) - (X % α : ZMod β)) * (α : ZMod β)⁻¹
      = (X / α : ZMod β) := by
    calc
      ((X : ZMod β) - (X % α : ZMod β)) * (α : ZMod β)⁻¹
          = ((α * (X / α) : ℕ) : ZMod β) * (α : ZMod β)⁻¹ := by
              simp [hdiff]
      _ = ((α : ZMod β) * (X / α : ZMod β)) * (α : ZMod β)⁻¹ := by
              simp [Nat.cast_mul, mul_comm, mul_left_comm]
      _ = (X / α : ZMod β) * ((α : ZMod β) * (α : ZMod β)⁻¹) := by
              ring
      _ = (X / α : ZMod β) := by
              simp [ZMod.coe_mul_inv_eq_one α hcop]

  have hmain : (((X : ZMod β) - (X % α : ZMod β)) * (α : ZMod β)⁻¹).val = X / α := by
    calc
      (((X : ZMod β) - (X % α : ZMod β)) * (α : ZMod β)⁻¹).val
          = ((X / α : ZMod β)).val := by simp [hk]
      _ = X / α := by
          simp [ZMod.val_cast_of_lt hk_lt]

  simpa [kEliminate, α, β] using hmain

/-- K-Elimination uniqueness: k mod β_cap = k when k < β_cap -/
theorem kEliminate_unique (dc : DualCodex) (X : ℕ)
    (h_range : X < dc.α_cap * dc.β_cap) :
    (X / dc.α_cap) % dc.β_cap = X / dc.α_cap := by
  have h_k_lt : X / dc.α_cap < dc.β_cap := Nat.div_lt_of_lt_mul h_range
  exact Nat.mod_eq_of_lt h_k_lt

end QMNF.Security
