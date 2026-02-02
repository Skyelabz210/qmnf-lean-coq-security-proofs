# L003 Critique: K-Elimination Information Preservation Proof

**Reviewer**: kappa-Critic Agent
**Date**: 2026-02-01
**Target**: L003_proof.md (K-Elimination Information Preservation)
**Final Verdict**: MINOR ISSUES - CAN VERIFY (with documentation)

---

## Executive Summary

The information preservation proof presents a valid security argument but has several areas requiring clarification. The core claim (K-Elimination doesn't leak additional information) is CORRECT, but the proof mixes information-theoretic and computational arguments in ways that need careful handling. The reduction argument is sound but incompletely formalized.

---

## Detailed Analysis

### 1. DEFINITION CHECK: "Information Preservation"

**Definition (Lines 32-39)**:
> A deterministic function f "preserves information" (with respect to a secret s) if for any distinguisher D:
> |Pr[D(f(RLWE_s)) = 1] - Pr[D(f(Uniform)) = 1]| <= |Pr[D(RLWE_s) = 1] - Pr[D(Uniform) = 1]|

**Issue 1.1 (MINOR): Non-Standard Definition**

This definition is REASONABLE but non-standard. The standard information-theoretic notion would be:
- Mutual information: I(s; f(X)) <= I(s; X)
- Or entropy: H(s | f(X)) >= H(s | X)

The definition given is a COMPUTATIONAL definition (distinguishing advantage), not information-theoretic.

**Impact**: The proof later (Step 4) switches to entropy notation without acknowledging this is a different framework.

**Severity**: MINOR (both frameworks support the same conclusion)

---

### 2. STEP 1: Determinism Claim

**Claim**: K-Elimination is deterministic.

**Analysis**: CORRECT. The function K_ELIM(v_alpha, v_beta) = ((v_beta - v_alpha) * alpha_cap_inv) mod beta_cap uses only:
- Subtraction (deterministic)
- Multiplication (deterministic)
- Modulo (deterministic)
- Precomputed inverse (deterministic given parameters)

**Verdict**: CLEAN

---

### 3. STEP 2: Public Data Only

**Claim**: K-Elimination operates only on public data (ciphertext coefficients, public parameters).

**Issue 3.1 (MINOR): Scope Clarification Needed**

The claim is correct IN ISOLATION, but the context matters:
- In BFV encryption, ciphertext components are ct0, ct1
- K-Elimination operates on the NOISE or INTERMEDIATE values, not raw ciphertext
- The proof should clarify WHEN K-Elimination is applied (during rescaling? during homomorphic operations?)

**Severity**: MINOR (scope clarification needed, not a flaw)

---

### 4. STEP 3: Reduction Argument

**Construction**:
```
Adversary B(challenge):
  1. Receive challenge (a, b) where b is either a*s + e or uniform u
  2. Compute c = b mod alpha_cap (main residue)
  3. Compute c' = b mod beta_cap (anchor residue)
  4. Apply K-Elimination: k = K_ELIM(c, c')
  5. Run A(k)
  6. Return A's output
```

**Issue 4.1 (MAJOR): Reduction Is Incomplete**

**Problem**: This reduction shows that distinguishing K_ELIM(RLWE) from K_ELIM(Uniform) is no easier than distinguishing RLWE from Uniform. But the original claim is about INFORMATION ABOUT THE SECRET s.

The reduction proves:
> Adv_A^{K-RLWE} <= Adv_B^{RLWE}

But this doesn't directly address information about s. It addresses distinguishing RLWE from uniform, which is a DIFFERENT security notion.

**Analysis**: The argument IS valid for the following reason: If K-Elimination leaked information about s that wasn't in the RLWE sample, then there would exist a distinguisher that performs better after K-Elimination. Since no such distinguisher exists (by reduction), no new information is leaked.

However, this logical chain is not explicitly stated in the proof.

**Severity**: MAJOR (argument structure gap)
**Resolution**: Add explicit statement: "If f(RLWE_s) leaked more information about s than RLWE_s, there would exist a distinguisher D such that Adv_D^{f(RLWE)} > Adv_D^{RLWE}. But we've shown no such D exists, hence f preserves information."

---

### 5. STEP 4: Information-Theoretic Argument

**Claim**: H(s | K_ELIM(RLWE_s)) = H(s | RLWE_s)

**Issue 5.1 (MINOR): Data Processing Inequality Application**

The proof states:
> By data processing inequality: For any deterministic function f, H(X | f(Y)) >= H(X | Y)

This is CORRECT. The data processing inequality states that processing cannot increase information.

**However**, the proof then claims:
> H(s | K_ELIM(RLWE_s)) = H(s | RLWE_s)

The DPI gives >= (inequality), not = (equality). The proof justifies equality by noting K_ELIM is derivable from RLWE_s, so:
> H(s | K_ELIM(RLWE_s), RLWE_s) = H(s | RLWE_s)  [since K_ELIM is deterministic function of RLWE_s]

But what we need is:
> H(s | K_ELIM(RLWE_s)) = H(s | RLWE_s)

**Issue**: These are NOT the same! H(s | K_ELIM(RLWE_s)) could be GREATER than H(s | RLWE_s) (information loss is allowed, increase is forbidden).

**Clarification**: The proof's claim is that K_ELIM(RLWE_s) alone (without the original RLWE_s) reveals no MORE about s. This is true by DPI. But the equality requires showing K_ELIM is a SUFFICIENT STATISTIC, which is a stronger claim.

**Severity**: MINOR (the inequality version suffices for security; equality may not hold)

**Corrected Statement**: H(s | K_ELIM(RLWE_s)) >= H(s | RLWE_s), meaning K-Elimination reveals at most as much about s as the original RLWE sample (and possibly less).

---

### 6. STEP 5: Side-Channel Analysis

**Claim**: K-Elimination has no timing or data-dependent branches that could leak information.

**Gap Acknowledged**: The proof notes (Line 169):
> [GAP] Timing Analysis: The modulo operation's constant-time property depends on implementation.

**Assessment**: This gap is CORRECTLY IDENTIFIED. The mathematical proof is about information-theoretic security. Implementation security (side channels) requires separate verification.

**Severity**: ACKNOWLEDGED GAP (not a proof flaw)

---

### 7. STEP 6: Dual-Codex Equivalence

**Claim**: Computing dual-codex (x_alpha, x_beta) from X reveals no information beyond X itself.

**Analysis**: CORRECT by CRT bijection. For X < alpha_cap * beta_cap:
- Z/(alpha_cap * beta_cap)Z is isomorphic to Z/alpha_cap Z x Z/beta_cap Z
- The mapping X -> (X mod alpha_cap, X mod beta_cap) is bijective
- Hence information-equivalent

**Verdict**: CLEAN

---

### 8. STEP 7: Final Synthesis

The synthesis brings together Steps 1-6. The argument is:
1. RLWE reveals bounded information about s (assumption)
2. K-Elimination is deterministic (Step 1)
3. K-Elimination uses only public data (Step 2)
4. Distinguishing advantage is preserved (Step 3)
5. Entropy is non-decreasing (Step 4)
6. Representation is information-equivalent (Step 6)

**Conclusion**: K-Elimination reveals NO ADDITIONAL information.

**Assessment**: The synthesis is CORRECT given the corrected interpretation of Step 4 (inequality, not equality).

---

## Hidden Assumptions Check

**Hidden Assumption 1**: RLWE samples are the ONLY input to K-Elimination
- The proof assumes K_ELIM receives residues derived from RLWE samples
- If K_ELIM received additional inputs (e.g., error terms from elsewhere), the analysis would change
- **Status**: IMPLICITLY ASSUMED, should be explicit

**Hidden Assumption 2**: The distinguisher has no auxiliary information
- The reduction assumes A receives only K_ELIM output
- If A had side information (e.g., partial key exposure), the analysis changes
- **Status**: STANDARD ASSUMPTION in cryptographic reductions

**Hidden Assumption 3**: Modular operations are lossless within the valid range
- For X < alpha_cap * beta_cap, the CRT representation is exact
- If X exceeds this range, information IS lost (which is the point of K-Elimination)
- **Status**: CORRECTLY HANDLED by L002's range assumption

---

## Counterexample Search

**Attempted counterexample 1**: What if K reveals the parity of k?

The k value computed by K-Elimination is (X / alpha_cap) mod beta_cap = X / alpha_cap (when in range). This is derivable from the RLWE sample itself:
- If you have RLWE sample b = a*s + e
- And you compute b mod alpha_cap and b mod beta_cap
- The k value you recover is b / alpha_cap

Since b is public (part of RLWE sample), its quotient is also derivable from b. No new information about s.

**Result**: NOT A COUNTEREXAMPLE

**Attempted counterexample 2**: What if alpha_cap, beta_cap leak information about s?

The moduli are PUBLIC PARAMETERS chosen before s is sampled. They cannot depend on s.

**Result**: NOT A COUNTEREXAMPLE

**No counterexamples found.**

---

## Formalization Status

The proof acknowledges (Gap 2, Line 255-265):
> The reduction argument and information-theoretic analysis are informal. Full formalization in Lean 4 would strengthen confidence.

**Assessment**: This is a FAIR acknowledgment. The argument is sound but not machine-verified. The K-Elimination CORRECTNESS (L002) is formalized; the SECURITY (L003) is not yet.

---

## Integer-Only Compliance

**Verified**: All K-Elimination operations are integer-only:
- Subtraction: v_beta - v_alpha (integers)
- Addition: + beta_cap (integer)
- Modulo: mod beta_cap (integer)
- Multiplication: * alpha_cap_inv (integer)

**No floating-point violations.**

---

## Issue Summary

| Issue | Location | Severity | Resolution Required? |
|-------|----------|----------|---------------------|
| 1.1 | Step 0 | MINOR | Note mixed frameworks |
| 3.1 | Step 2 | MINOR | Clarify application context |
| 4.1 | Step 3 | MAJOR | Complete reduction logic |
| 5.1 | Step 4 | MINOR | Correct equality to inequality |
| Side-channel | Step 5 | ACKNOWLEDGED | Separate implementation audit |

---

## Final Verdict

**MINOR ISSUES - CAN VERIFY (with documentation)**

The core security claim is CORRECT: K-Elimination does not leak additional information about the secret beyond what the underlying RLWE samples reveal. The proof's structure is sound, but:
1. The reduction argument needs explicit completion (Issue 4.1)
2. The entropy equality should be corrected to inequality (Issue 5.1)

These are DOCUMENTATION issues, not fundamental flaws. The security property holds.

**Conditions for VERIFIED status**:
1. Add explicit statement connecting distinguishing advantage to information leakage
2. Correct Step 4 to state H(s | K_ELIM(RLWE_s)) >= H(s | RLWE_s) (not equality)
3. Clarify the context in which K-Elimination is applied (Step 2)

---

**Reviewer Signature**: kappa-Critic
**Confidence**: HIGH
**Recommendation**: CONDITIONALLY VERIFIED - address Issue 4.1 for full verification
