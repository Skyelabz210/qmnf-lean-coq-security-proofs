-- Replace the word `sorry` at line 232 with everything below:

    simp only
    have hAne : NeZero cfg.A := ⟨Nat.pos_iff_ne_zero.mp cfg.A_pos⟩
    have hkLt : X / cfg.M < cfg.A := Nat.div_lt_of_lt_mul hX
    have hkMod : (X / cfg.M) % cfg.A = X / cfg.M := Nat.mod_eq_of_lt hkLt
    have hfund : X = X % cfg.M + (X / cfg.M) * cfg.M := div_mod_identity X cfg.M
    suffices h : ((X % cfg.A + cfg.A - X % cfg.M % cfg.A) % cfg.A * M_inv) % cfg.A 
               = (X / cfg.M) % cfg.A by rw [h, hkMod]
    rw [← ZMod.val_natCast (n := cfg.A), ← ZMod.val_natCast (n := cfg.A)]
    congr 1
    have hXmodA : (X % cfg.A : ZMod cfg.A) = (X : ZMod cfg.A) := by simp [ZMod.natCast_mod]
    have hvMmodA : (X % cfg.M % cfg.A : ZMod cfg.A) = (X % cfg.M : ZMod cfg.A) := by simp [ZMod.natCast_mod]
    have hAzero : (cfg.A : ZMod cfg.A) = 0 := ZMod.natCast_self cfg.A
    have hXeq : (X : ZMod cfg.A) = (X % cfg.M : ZMod cfg.A) + (X / cfg.M * cfg.M : ZMod cfg.A) := by
      conv_lhs => rw [hfund]; push_cast; ring
    have hMinv : (cfg.M : ZMod cfg.A) * (M_inv : ZMod cfg.A) = 1 := by
      have h := hInv
      rw [← Nat.cast_mul]
      have h' : ((cfg.M * M_inv) % cfg.A : ZMod cfg.A) = (1 : ZMod cfg.A) := by
        rw [ZMod.natCast_mod, ← ZMod.natCast_mod 1 cfg.A]; congr; simp [h]
      rw [ZMod.natCast_mod] at h'; exact h'
    have hphase : ((X % cfg.A + cfg.A - X % cfg.M % cfg.A) % cfg.A : ZMod cfg.A) 
                = (X / cfg.M * cfg.M : ZMod cfg.A) := by
      rw [ZMod.natCast_mod]
      have hsub : X % cfg.M % cfg.A ≤ X % cfg.A + cfg.A := by
        have h : X % cfg.M % cfg.A < cfg.A := Nat.mod_lt _ cfg.A_pos; omega
      rw [Nat.cast_sub hsub]; push_cast; rw [hXmodA, hvMmodA, hAzero, add_zero, hXeq]; ring
    calc ((X % cfg.A + cfg.A - X % cfg.M % cfg.A) % cfg.A * M_inv : ZMod cfg.A)
        = (X / cfg.M * cfg.M : ZMod cfg.A) * (M_inv : ZMod cfg.A) := by rw [hphase]; push_cast
      _ = (X / cfg.M : ZMod cfg.A) * ((cfg.M : ZMod cfg.A) * (M_inv : ZMod cfg.A)) := by ring
      _ = (X / cfg.M : ZMod cfg.A) * 1 := by rw [hMinv]
      _ = (X / cfg.M : ZMod cfg.A) := by ring
