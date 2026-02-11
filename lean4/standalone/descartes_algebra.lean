/-
  Descartes Circle Theorem - Algebraic Verification
  QMNF/PLMG Sprint 7
  
  Prove that the Vieta reflection preserves the Descartes relation
  through explicit algebraic expansion.
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Polyrith

namespace DescartesAlgebra

-- ============================================================================
-- THE DESCARTES RELATION
-- ============================================================================

/-- The Descartes Circle Theorem polynomial relation -/
def descartes_poly (k₁ k₂ k₃ k₄ : ℤ) : ℤ :=
  (k₁ + k₂ + k₃ + k₄)^2 - 2 * (k₁^2 + k₂^2 + k₃^2 + k₄^2)

/-- A quadruple satisfies Descartes iff the polynomial vanishes -/
def satisfies_descartes (k₁ k₂ k₃ k₄ : ℤ) : Prop :=
  descartes_poly k₁ k₂ k₃ k₄ = 0

-- ============================================================================
-- VIETA REFLECTION
-- ============================================================================

/-- The Vieta reflection formula: k'₁ = 2(k₂ + k₃ + k₄) - k₁ -/
def vieta_reflect (k₁ k₂ k₃ k₄ : ℤ) : ℤ :=
  2 * (k₂ + k₃ + k₄) - k₁

-- ============================================================================
-- MAIN PRESERVATION THEOREM
-- ============================================================================

/-- Vieta reflection preserves the Descartes relation -/
theorem vieta_preserves_descartes (k₁ k₂ k₃ k₄ : ℤ) 
    (h : satisfies_descartes k₁ k₂ k₃ k₄) :
    satisfies_descartes (vieta_reflect k₁ k₂ k₃ k₄) k₂ k₃ k₄ := by
  unfold satisfies_descartes descartes_poly vieta_reflect at *
  -- Let k'₁ = 2(k₂ + k₃ + k₄) - k₁
  -- Need: (k'₁ + k₂ + k₃ + k₄)² = 2(k'₁² + k₂² + k₃² + k₄²)
  --
  -- Expand k'₁ + k₂ + k₃ + k₄:
  --   = 2(k₂ + k₃ + k₄) - k₁ + k₂ + k₃ + k₄
  --   = 3(k₂ + k₃ + k₄) - k₁
  --   = 2S - 3k₁  where S = k₁ + k₂ + k₃ + k₄
  --
  -- From Descartes: S² = 2(k₁² + k₂² + k₃² + k₄²)
  -- So: k₁² + k₂² + k₃² + k₄² = S²/2
  --
  -- The algebra works out because Vieta's formulas for the quadratic
  -- ensure the new root also satisfies the relation.
  ring_nf
  -- After ring normalization, use the hypothesis h
  linarith

/-- Alternative: direct polynomial identity -/
theorem descartes_vieta_identity (k₁ k₂ k₃ k₄ : ℤ) :
    descartes_poly (vieta_reflect k₁ k₂ k₃ k₄) k₂ k₃ k₄ = 
    descartes_poly k₁ k₂ k₃ k₄ := by
  unfold descartes_poly vieta_reflect
  ring

-- ============================================================================
-- INVOLUTION PROPERTY
-- ============================================================================

/-- The reflection is an involution -/
theorem vieta_involution (k₁ k₂ k₃ k₄ : ℤ) :
    vieta_reflect (vieta_reflect k₁ k₂ k₃ k₄) k₂ k₃ k₄ = k₁ := by
  unfold vieta_reflect
  ring

-- ============================================================================
-- SUM RELATION
-- ============================================================================

/-- Vieta formula is equivalent to: k₁ + k'₁ = 2(k₂ + k₃ + k₄) -/
theorem vieta_sum (k₁ k₂ k₃ k₄ : ℤ) :
    k₁ + vieta_reflect k₁ k₂ k₃ k₄ = 2 * (k₂ + k₃ + k₄) := by
  unfold vieta_reflect
  ring

/-- Product relation from Vieta -/
theorem vieta_product (k₁ k₂ k₃ k₄ : ℤ) (h : satisfies_descartes k₁ k₂ k₃ k₄) :
    k₁ * vieta_reflect k₁ k₂ k₃ k₄ = 
    (k₂ + k₃ + k₄)^2 - (k₂^2 + k₃^2 + k₄^2) - 2*(k₂*k₃ + k₂*k₄ + k₃*k₄) := by
  unfold vieta_reflect satisfies_descartes descartes_poly at *
  -- This follows from the quadratic formula applied to the Descartes equation
  -- viewed as a quadratic in k₁
  ring_nf at *
  linarith

end DescartesAlgebra
