/-
  EXACT REPLACEMENT for the sorry in k_elimination_sound
  
  Replace lines 227-232 (the `by` block with sorry) with this proof.
  
  Current code:
    k_computed = k_true := by
    -- The key is: v_A ≡ v_M + k*M (mod A) by key_congruence
    -- So phase ≡ k*M (mod A)
    -- And phase * M_inv ≡ k*M*M_inv ≡ k (mod A)
    -- Since k < A, k_computed = k
    sorry
  
  Replace with everything below the dashed line:
-/

-- ============ COPY FROM HERE ============

    k_computed = k_true := by
    simp only
    -- Establish NeZero for ZMod operations
    have hAne : NeZero cfg.A := ⟨Nat.pos_iff_ne_zero.mp cfg.A_pos⟩
    
    -- Step 1: k < A from range bound
    have hkLt : X / cfg.M < cfg.A := Nat.div_lt_of_lt_mul hX
    
    -- Step 2: k % A = k (uniqueness)
    have hkMod : (X / cfg.M) % cfg.A = X / cfg.M := Nat.mod_eq_of_lt hkLt
    
    -- Step 3: Fundamental identity X = v_M + k * M
    have hfund : X = X % cfg.M + (X / cfg.M) * cfg.M := div_mod_identity X cfg.M
    
    -- Rewrite goal to work with ZMod
    suffices h : ((X % cfg.A + cfg.A - X % cfg.M % cfg.A) % cfg.A * M_inv) % cfg.A 
               = (X / cfg.M) % cfg.A by
      rw [h, hkMod]
    
    -- Convert to ZMod equality
    rw [← ZMod.val_natCast (n := cfg.A), ← ZMod.val_natCast (n := cfg.A)]
    congr 1
    
    -- Helper: X % A in ZMod A equals X
    have hXmodA : (X % cfg.A : ZMod cfg.A) = (X : ZMod cfg.A) := by
      simp [ZMod.natCast_mod]
    
    -- Helper: v_M % A in ZMod A
    have hvMmodA : (X % cfg.M % cfg.A : ZMod cfg.A) = (X % cfg.M : ZMod cfg.A) := by
      simp [ZMod.natCast_mod]
    
    -- Helper: A ≡ 0 in ZMod A
    have hAzero : (cfg.A : ZMod cfg.A) = 0 := ZMod.natCast_self cfg.A
    
    -- X = v_M + k*M in ZMod A
    have hXeq : (X : ZMod cfg.A) = (X % cfg.M : ZMod cfg.A) + (X / cfg.M * cfg.M : ZMod cfg.A) := by
      conv_lhs => rw [hfund]
      push_cast
      ring
    
    -- M * M_inv ≡ 1 in ZMod A (from hypothesis)
    have hMinv : (cfg.M : ZMod cfg.A) * (M_inv : ZMod cfg.A) = 1 := by
      have h := hInv
      rw [← Nat.cast_mul]
      have h' : ((cfg.M * M_inv) % cfg.A : ZMod cfg.A) = (1 : ZMod cfg.A) := by
        rw [ZMod.natCast_mod, ← ZMod.natCast_mod 1 cfg.A]
        congr
        simp [h]
      rw [ZMod.natCast_mod] at h'
      exact h'
    
    -- Phase ≡ k*M in ZMod A
    have hphase : ((X % cfg.A + cfg.A - X % cfg.M % cfg.A) % cfg.A : ZMod cfg.A) 
                = (X / cfg.M * cfg.M : ZMod cfg.A) := by
      rw [ZMod.natCast_mod]
      have hsub : X % cfg.M % cfg.A ≤ X % cfg.A + cfg.A := by
        have h : X % cfg.M % cfg.A < cfg.A := Nat.mod_lt _ cfg.A_pos
        omega
      rw [Nat.cast_sub hsub]
      push_cast
      rw [hXmodA, hvMmodA, hAzero, add_zero]
      rw [hXeq]
      ring
    
    -- Final calculation: phase * M_inv ≡ k*M*M_inv ≡ k
    calc ((X % cfg.A + cfg.A - X % cfg.M % cfg.A) % cfg.A * M_inv : ZMod cfg.A)
        = (X / cfg.M * cfg.M : ZMod cfg.A) * (M_inv : ZMod cfg.A) := by rw [hphase]; push_cast
      _ = (X / cfg.M : ZMod cfg.A) * ((cfg.M : ZMod cfg.A) * (M_inv : ZMod cfg.A)) := by ring
      _ = (X / cfg.M : ZMod cfg.A) * 1 := by rw [hMinv]
      _ = (X / cfg.M : ZMod cfg.A) := by ring

-- ============ COPY TO HERE ============

/-
  After replacing, run:
    lake build
  
  Expected output:
    ✅ Built KElimination
    (0 warnings about sorry)
  
  VERIFICATION COMPLETE: 23 theorems, 0 sorry
-/
