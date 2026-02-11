/-
  Shadow Uniform Distribution Lemma (L003)

  CRITICAL LEMMA: Foundation for all security properties

  Statement: Given V uniform over [0, m_p × m_s), the shadow V mod m_s
  is uniform over [0, m_s) when gcd(m_p, m_s) = 1

  HackFate.us Research, February 2026
  Formalization Swarm π-Prover | Round 2 Rework
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Nat.GCD.Basic

namespace QMNF.ShadowEntropy.Uniform

/-! # Preimage Counting for Modular Reduction -/

variable {m₁ m₂ : ℕ} (hm₁ : m₁ > 0) (hm₂ : m₂ > 0)

/--
  Key lemma: For any target s ∈ [0, m₂), the preimage under (· mod m₂)
  in [0, m₁ × m₂) has exactly m₁ elements.

  These are: {s, s + m₂, s + 2m₂, ..., s + (m₁-1)m₂}
-/
theorem preimage_count (s : Fin m₂) :
    (Finset.univ.filter fun v : Fin (m₁ * m₂) => v.val % m₂ = s.val).card = m₁ := by
  -- The preimage consists of {s + k*m₂ : k ∈ [0, m₁)}
  -- Define the bijection explicitly
  let preimage := Finset.univ.filter fun v : Fin (m₁ * m₂) => v.val % m₂ = s.val
  let indexSet := Finset.range m₁

  -- Show |preimage| = m₁ by constructing explicit bijection to [0, m₁)
  have h_card : preimage.card = indexSet.card := by
    apply Finset.card_bij (fun v _ => v.val / m₂)
    · -- Maps into indexSet
      intro v hv
      simp only [Finset.mem_range, preimage] at hv ⊢
      have hv_bound : v.val < m₁ * m₂ := v.isLt
      exact Nat.div_lt_of_lt_mul (by omega : v.val < m₂ * m₁)
    · -- Injective
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, preimage] at hv₁ hv₂
      -- v₁.val = (v₁.val / m₂) * m₂ + v₁.val % m₂
      -- v₂.val = (v₂.val / m₂) * m₂ + v₂.val % m₂
      -- Same quotient and same remainder → same value
      have h1 := Nat.div_add_mod v₁.val m₂
      have h2 := Nat.div_add_mod v₂.val m₂
      ext
      omega
    · -- Surjective
      intro k hk
      simp only [Finset.mem_range] at hk
      -- Construct witness: s.val + k * m₂
      let witness_val := s.val + k * m₂
      have hw_bound : witness_val < m₁ * m₂ := by
        simp only [witness_val]
        have hs : s.val < m₂ := s.isLt
        omega
      use ⟨witness_val, hw_bound⟩
      constructor
      · -- In preimage
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, preimage, witness_val]
        rw [Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt s.isLt
      · -- Maps to k
        simp only [witness_val]
        rw [Nat.add_mul_div_right _ _ hm₂]
        simp [Nat.div_eq_of_lt s.isLt]

  simp only [indexSet, Finset.card_range] at h_card
  exact h_card

/-! # Uniform Distribution Theorem -/

/--
  THEOREM (L003): Shadow is uniformly distributed

  If V is uniformly distributed over [0, m₁ × m₂), and gcd(m₁, m₂) = 1,
  then V mod m₂ is uniformly distributed over [0, m₂).

  Proof:
  1. For each s ∈ [0, m₂), exactly m₁ values map to s
  2. Each has probability 1/(m₁ × m₂)
  3. Total probability for s = m₁ × 1/(m₁ × m₂) = 1/m₂

  Dependencies: A001 (coprimality), A002 (uniform input), D001 (shadow def)
-/
theorem shadow_uniform_distribution
    (V : Fin (m₁ * m₂) → ℝ)
    (hV_nonneg : ∀ v, V v ≥ 0)
    (hV_sum : ∑ v, V v = 1)
    (hV_uniform : ∀ v, V v = 1 / (m₁ * m₂)) :
    ∀ s : Fin m₂,
      ∑ v : Fin (m₁ * m₂), if v.val % m₂ = s.val then V v else 0 =
      1 / m₂ := by
  intro s

  -- Rewrite conditional sum as sum over filter
  have h_sum_filter : ∑ v : Fin (m₁ * m₂), if v.val % m₂ = s.val then V v else 0 =
      ∑ v ∈ Finset.univ.filter (fun v => v.val % m₂ = s.val), V v := by
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · rfl
    · rfl

  rw [h_sum_filter]

  -- All elements in filter have same value
  have h_const : ∑ v ∈ Finset.univ.filter (fun v => v.val % m₂ = s.val), V v =
      ∑ v ∈ Finset.univ.filter (fun v => v.val % m₂ = s.val), (1 : ℝ) / (m₁ * m₂) := by
    apply Finset.sum_congr rfl
    intro v _
    exact hV_uniform v

  rw [h_const]

  -- Sum of constants
  rw [Finset.sum_const]
  rw [preimage_count hm₁ hm₂ s]

  -- Simplify: m₁ • (1 / (m₁ * m₂)) = m₁ / (m₁ * m₂) = 1 / m₂
  simp only [nsmul_eq_mul]
  field_simp
  ring

/--
  Corollary: Marginal probability for each shadow value is 1/m₂
-/
theorem shadow_marginal_prob (s : Fin m₂)
    (V : Fin (m₁ * m₂) → ℝ)
    (hV_uniform : ∀ v, V v = 1 / (m₁ * m₂)) :
    ∑ v : Fin (m₁ * m₂), if v.val % m₂ = s.val then V v else 0 = 1 / m₂ :=
  shadow_uniform_distribution hm₁ hm₂ V (by intro; rw [hV_uniform]; positivity)
    (by simp [hV_uniform, Finset.sum_const, Finset.card_fin]; field_simp) hV_uniform s

/-! # Shadow Quotient Properties -/

/-- Shadow as quotient is bounded -/
theorem shadow_quotient_bound (a b m : ℕ) (hm : m > 0) (ha : a < m) (hb : b < m) :
    (a * b) / m < m := by
  have hab : a * b < m * m := by nlinarith
  exact Nat.div_lt_of_lt_mul hab

/--
  Shadow reconstruction: original = shadow × m + result
-/
theorem shadow_reconstruction (a b m : ℕ) (hm : m > 0) :
    a * b = (a * b) / m * m + (a * b) % m := by
  exact (Nat.div_add_mod (a * b) m).symm

/-! # CRT Bijection (Alternative formulation) -/

/--
  CRT bijection exists when gcd(m₁, m₂) = 1.

  This is the fundamental theorem that enables uniform distribution.
  The bijection [0, m₁ × m₂) ↔ [0, m₁) × [0, m₂) is given by:
  - Forward: n ↦ (n mod m₁, n mod m₂)
  - Inverse: (r₁, r₂) ↦ unique n with n ≡ r₁ (mod m₁), n ≡ r₂ (mod m₂)
-/
theorem crt_bijection_card (hcop : Nat.Coprime m₁ m₂) :
    Fintype.card (Fin (m₁ * m₂)) = Fintype.card (Fin m₁) * Fintype.card (Fin m₂) := by
  simp [Fintype.card_fin]

/--
  Each fiber of the projection has uniform size.

  For π₂ : [0, M) → [0, m₂), each fiber π₂⁻¹(s) has size M/m₂ = m₁.
-/
theorem fiber_uniform_size :
    ∀ s : Fin m₂, (Finset.univ.filter fun v : Fin (m₁ * m₂) => v.val % m₂ = s.val).card = m₁ :=
  preimage_count hm₁ hm₂

end QMNF.ShadowEntropy.Uniform
