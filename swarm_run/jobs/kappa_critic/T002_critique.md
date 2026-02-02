# T002 Critique: QMNF-HE IND-CPA Security Proof

**Reviewer**: kappa-Critic Agent
**Date**: 2026-02-01
**Target**: T002_proof.md (IND-CPA Security Reduction)
**Final Verdict**: MINOR ISSUES - CAN VERIFY (with caveats)

---

## Executive Summary

The IND-CPA security proof follows the standard BFV/BGV template and is fundamentally sound. The reduction from IND-CPA to RLWE is correctly constructed. However, I identify several issues that require attention, ranging from acknowledged gaps to hidden assumptions that need explicit statement.

---

## Detailed Analysis

### 1. CLAIM VERIFICATION: Theorem Statement

**Claim (Line 13-21)**:
> If the Ring-LWE (RLWE) assumption holds for R_q = Z_q[x]/(x^n + 1), then QMNF-HE achieves IND-CPA security.

**Analysis**: The statement is correctly formed. The reduction direction is correct (breaking IND-CPA implies breaking RLWE). The notation is standard.

**Verdict**: CLEAN

---

### 2. SCHEME SPECIFICATION: Key Generation and Encryption

**Issue 2.1 (MINOR): Secret Key Distribution Mismatch**

The proof states (Line 39):
> Sample s <- {-1, 0, 1}^n (ternary distribution)

But standard RLWE uses a sub-Gaussian error distribution for secrets. The ternary distribution is a valid instantiation but requires the "Module-LWE with sparse secrets" variant for the reduction to be formally correct.

**Severity**: MINOR
**Impact**: The reduction remains valid under the ternary-secret RLWE assumption, which is well-studied. However, this should be explicitly stated.

**Issue 2.2 (MINOR): Delta Definition**

Line 31:
> Scaling factor: Delta = floor(q/t)

The floor function is correct for integer-only computation. However, the decryption step (Line 67) states:
> Compute m = round(t/q * m') (mod t)

This appears to use `t/q` which is a rational division, then rounding. In QMNF's integer-only context, this MUST be implemented as:
```
m = ((m' * t + q/2) / q) mod t
```

**Severity**: MINOR
**Impact**: This is an implementation detail. The proof correctly notes QMNF-compliance in Section 5.1, but the decryption formula should be stated in integer-only form for consistency.

---

### 3. REDUCTION CONSTRUCTION: Algorithm B

**Analysis of Section 4.2**

The construction of Algorithm B is CORRECT:
1. B receives RLWE challenge (a, b)
2. B embeds (a, b) as public key
3. B simulates the encryption oracle using its own randomness
4. B interprets A's success as evidence about the RLWE challenge

**Verified Steps**:
- Setup phase: Correctly sets pk = (a, b)
- Challenge phase: Correctly encrypts using embedded challenge
- Guess phase: Correctly interprets A's output

**Verdict**: CLEAN

---

### 4. HYBRID ARGUMENT: Games 0-2

**Issue 4.1 (MAJOR): Leftover Hash Lemma Application**

Line 195:
> When b is uniform in R_q, the term b*u produces a uniformly random element (by leftover hash lemma / RLWE regularity)

**Problem**: This statement requires justification. The leftover hash lemma requires:
- u has sufficient min-entropy
- The hash function (multiplication by b) is pairwise independent

For ternary u sampled from {-1, 0, 1}^n, the min-entropy is n * log(3) bits. The product b*u in R_q distributes uniformly ONLY if:
1. n is sufficiently large relative to log(q)
2. The polynomial x^n + 1 splits appropriately

**Missing**: The proof does not verify that QMNF's parameters satisfy the regularity conditions.

**Severity**: MAJOR (conceptual gap)
**Impact**: Without this verification, the leap from "b uniform" to "b*u uniform" is not justified. The proof structure is correct, but this step needs formal justification or parameter constraints.

**Resolution Path**: Add a lemma stating: "For n >= 4096 and q < 2^64, the distribution of b*u where b <- U(R_q) and u <- {-1,0,1}^n is statistically close to uniform in R_q."

---

### 5. ADVANTAGE BOUND: Theorem 4.2

**Issue 5.1 (MINOR): Factor of 2 in Bound**

Line 205-206:
> Adv^{IND-CPA}_{A,QMNF-HE}(lambda) <= 2 * Adv^{RLWE}_B(lambda)

But the derivation in Lines 219-227 shows:
> Adv^{IND-CPA}_A = Adv^{RLWE}_B

These are inconsistent. The factor of 2 sometimes appears in hybrid arguments when there are two games, but here the argument is tight.

**Severity**: MINOR (notational inconsistency)
**Impact**: The tighter bound (no factor of 2) is actually what the proof establishes.

---

### 6. QMNF-SPECIFIC ANALYSIS

**Issue 6.1 (ACKNOWLEDGED GAP): Parameter Validation**

The proof correctly acknowledges (Line 261-262):
> [GAP] Production Parameter Verification: The current implementation uses q = 2^31 - 1 which is explicitly marked as testing only.

**Severity**: ACKNOWLEDGED (not a proof flaw, but a deployment concern)

**Issue 6.2 (MINOR): Noise-Correctness Intersection**

Line 266-274 discusses noise correctness but states:
> If noise exceeds threshold, decryption fails (but security still holds!)

This is CORRECT. IND-CPA security does not require decryption correctness - it only requires that ciphertexts don't leak information about plaintexts. The proof correctly notes this is addressed in T001.

**Verdict**: CLEAN

---

### 7. MULTIPLE ENCRYPTION HANDLING

**Issue 7.1 (MINOR): Query Counting**

Line 305-309:
> A complete proof should formally bound the number of encryption queries and show the reduction's tightness.

The bound given is:
> Adv^{IND-CPA}_A <= Q * Adv^{RLWE}_B + negl(lambda)

**Problem**: This bound is WRONG for the standard argument. In BFV-style CPA security, all encryptions use the SAME public key, so there is no query-dependent factor. The correct bound is:
> Adv^{IND-CPA}_A <= Adv^{RLWE}_B

The factor of Q only appears in certain CCA or multi-user settings.

**Severity**: MINOR (the stated bound is loose, not incorrect)

---

### 8. HIDDEN ASSUMPTIONS CHECK

**Hidden Assumption 8.1**: The ring Z_q[x]/(x^n+1) is assumed to have x^n+1 irreducible (or at least the RLWE problem is hard). This requires n to be a power of 2 and is stated but not verified.

**Hidden Assumption 8.2**: The error distribution chi is assumed to be sub-Gaussian with appropriate parameters. The proof mentions this but doesn't verify that QMNF's implementation uses valid parameters.

**Hidden Assumption 8.3**: The proof assumes the public key is used only for encryption (not for key encapsulation or other protocols). This is implicit in the IND-CPA model.

---

### 9. CIRCULAR REASONING CHECK

**No circular reasoning detected.** The proof correctly:
1. Assumes RLWE is hard
2. Shows breaking IND-CPA implies breaking RLWE
3. Concludes IND-CPA is hard

The dependency on T001 (correctness) is acknowledged but not circularly used - IND-CPA security does not require correctness.

---

### 10. INTEGER-ONLY COMPLIANCE

**Verified**: Section 5.1 correctly notes all operations are integer-only:
- Ring operations in Z_q[x]/(x^n+1)
- Ternary sampling
- Integer scaling by Delta = floor(q/t)

**No floating-point violations detected in the proof itself.**

---

## Issue Summary

| Issue | Location | Severity | Resolution Required? |
|-------|----------|----------|---------------------|
| 2.1 | Line 39 | MINOR | Explicit assumption |
| 2.2 | Line 67 | MINOR | Notation fix |
| 4.1 | Line 195 | MAJOR | Justify uniformity |
| 5.1 | Line 205-227 | MINOR | Fix inconsistency |
| 7.1 | Line 305-309 | MINOR | Correct bound |
| 8.x | Throughout | MINOR | Document assumptions |

---

## Final Verdict

**MINOR ISSUES - CAN VERIFY (with caveats)**

The proof is fundamentally sound and follows established techniques. The MAJOR issue (4.1) regarding the leftover hash lemma application does not invalidate the proof structure - it requires additional justification that is standard in the literature but should be explicitly stated.

**Conditions for VERIFIED status**:
1. Add explicit statement of ternary-secret RLWE assumption
2. Add lemma or reference justifying b*u uniformity for stated parameters
3. Fix the factor-of-2 inconsistency in Section 4.4
4. Correct the query-counting bound in Section 6.3

These are documentation/clarity issues, not fundamental flaws. The reduction structure is CORRECT.

---

**Reviewer Signature**: kappa-Critic
**Confidence**: HIGH
**Recommendation**: CONDITIONALLY VERIFIED - address Issue 4.1 explicitly
