# T001: K-Enhanced RLWE Security - Proof Sketch

**Node ID**: T001
**Type**: Theorem
**Status**: Proof Sketch Complete
**Author**: pi-Prover Agent
**Date**: 2026-02-01

---

## Statement

If RLWE assumption A001 holds, then K-enhanced RLWE (with dual-codex representation
and K-Elimination) is also computationally indistinguishable from uniform:

For all A in PPT:
```
|Pr[A(K-RLWE sample) = 1] - Pr[A(uniform) = 1]| <= negl(lambda)
```

---

## Dependencies

| Node ID | Description | Status |
|---------|-------------|--------|
| A001 | RLWE Hardness Assumption | Axiom (Required) |
| L002 | K-Elimination Correctness | Proven |
| L003 | K-Elimination Information Preservation | Proven |
| L004 | RLWE Sample Indistinguishability | Follows from A001 |

---

## Definitions

### Definition (K-RLWE Distribution)

For parameters (N, q, sigma, t, alpha_cap, beta_cap) where:
- gcd(alpha_cap, beta_cap) = 1
- q = alpha_cap * beta_cap (or q is a multiple thereof)

The K-RLWE distribution is defined as:
```
K-RLWE_{s,chi}:
  1. Sample a <- U(R_q)
  2. Sample e <- chi_sigma(R)
  3. Compute b = a * s + e in R_q
  4. Compute dual-codex: (b_alpha, b_beta) where
       b_alpha = b mod alpha_cap
       b_beta = b mod beta_cap
  5. Optionally compute k = K_ELIM(b_alpha, b_beta)
  6. Output (a, b_alpha, b_beta) or (a, b, k)
```

### Definition (K-RLWE Uniform)

```
K-Uniform:
  1. Sample a <- U(R_q)
  2. Sample u <- U(R_q)
  3. Compute dual-codex: (u_alpha, u_beta)
  4. Output (a, u_alpha, u_beta)
```

---

## Proof Sketch

### Step 1: RLWE Assumption Setup

**Assumption A001 (RLWE Hardness)**:
For parameters (N, q, sigma, t) with N a power of 2, prime q, and discrete Gaussian chi_sigma:
```
For all A in PPT:
|Pr[A(a, b <- RLWE_{s,chi}) = 1] - Pr[A(a, b <- U(R_q^2)) = 1]| <= negl(lambda)
```

**Dependencies**: A001 (axiom)

---

### Step 2: Dual-Codex is a Bijection

**Claim**: The mapping X -> (X mod alpha_cap, X mod beta_cap) is a bijection
for X in [0, alpha_cap * beta_cap).

**Proof**: By Chinese Remainder Theorem (L001).

**Implication**: Knowing (b_alpha, b_beta) is information-theoretically equivalent
to knowing b (within the range).

**Dependencies**: L001 (CRT Reconstruction)

---

### Step 3: K-Elimination is Deterministic and Information-Preserving

**Claim**: The K-Elimination function k = K_ELIM(b_alpha, b_beta) does not
leak additional information about the secret s.

**Proof**: By L003 (K-Elimination Information Preservation).

**Key Points**:
1. K-Elimination uses only ciphertext data and public parameters
2. No secret material is accessed
3. The function is deterministic

**Dependencies**: L003

---

### Step 4: Reduction Construction

**Theorem**: If there exists PPT adversary A that distinguishes K-RLWE from K-Uniform
with non-negligible advantage, then there exists PPT adversary B that breaks RLWE.

**Construction of B**:

```
Adversary B^{RLWE}(challenge = (a, b)):
  // b is either a*s + e (RLWE) or uniform u

  Input: (a, b) in R_q x R_q

  Step 1: Compute dual-codex representation
    b_alpha := b mod alpha_cap
    b_beta := b mod beta_cap

  Step 2: Compute K-Elimination value
    k := ((b_beta - b_alpha) * alpha_cap_inv) mod beta_cap

  Step 3: Form K-RLWE sample
    sample := (a, b_alpha, b_beta, k)
    // Or just (a, b_alpha, b_beta) depending on A's expected input

  Step 4: Run distinguisher A
    bit := A(sample)

  Step 5: Return A's guess
    return bit

End
```

**Dependencies**: Standard reduction template

---

### Step 5: Advantage Analysis

**Claim**:
```
Adv_B^{RLWE} = Adv_A^{K-RLWE}
```

**Proof**:

Case 1: Challenge is RLWE sample (a, a*s + e)
- B computes dual-codex of b = a*s + e
- B computes K-Elimination on this
- A receives a valid K-RLWE sample
- A's behavior matches its K-RLWE distinguishing probability

Case 2: Challenge is Uniform sample (a, u)
- B computes dual-codex of u
- B computes K-Elimination on this
- A receives a K-Uniform sample
- A's behavior matches its K-Uniform distinguishing probability

Therefore:
```
Pr[B(RLWE) = 1] = Pr[A(K-RLWE) = 1]
Pr[B(Uniform) = 1] = Pr[A(K-Uniform) = 1]
```

Subtracting:
```
Adv_B^{RLWE} = |Pr[B(RLWE) = 1] - Pr[B(Uniform) = 1]|
             = |Pr[A(K-RLWE) = 1] - Pr[A(K-Uniform) = 1]|
             = Adv_A^{K-RLWE}
```

**Dependencies**: Step 4 construction

---

### Step 6: Runtime Analysis

**Claim**: B is PPT if A is PPT.

**Proof**:
```
Time(B) = Time(A) + O(N * polylog(q))
```

where:
- Time(A) is A's runtime (polynomial by assumption)
- O(N * polylog(q)) is for computing:
  - Dual-codex: 2 polynomial modular reductions
  - K-Elimination: 1 subtraction, 1 multiplication, 1 modulo

All additional operations are polynomial in the security parameter.

**Dependencies**: Computational complexity analysis

---

### Step 7: Conclude Security

**Final Theorem**:

By the RLWE assumption (A001), Adv_B^{RLWE} <= negl(lambda).

By Step 5, Adv_A^{K-RLWE} = Adv_B^{RLWE}.

Therefore:
```
Adv_A^{K-RLWE} <= negl(lambda)
```

for all PPT adversaries A.

This means K-RLWE samples are computationally indistinguishable from K-Uniform samples.

Q.E.D.

---

## Security Bound

**Theorem (Tight Reduction)**:
```
Adv^{K-RLWE}(A) = Adv^{RLWE}(B)
```

The reduction is TIGHT - there is no loss in the security bound.

**Implication**: If RLWE provides 128-bit security, then K-RLWE also provides
128-bit security with the same parameters.

---

## Dependency Ledger

| Step | Uses |
|------|------|
| 1 | A001 (RLWE Hardness Assumption) |
| 2 | L001 (CRT Reconstruction) |
| 3 | L003 (Information Preservation) |
| 4 | Reduction template |
| 5 | Steps 2-4 |
| 6 | Computational complexity |
| 7 | Steps 1, 5, 6 |

---

## Gap Analysis

### [GAP 1] Formal Lean 4 Verification - MEDIUM PRIORITY

**Location**: Entire proof
**Severity**: Medium
**Description**: This proof is a rigorous pen-and-paper argument, but formal
machine verification in Lean 4 would provide the highest confidence.

**Resolution Path**:
- This is covered by V001 in the blueprint
- Requires formalizing:
  - PPT adversary model
  - Computational indistinguishability
  - The reduction construction

### [GAP 2] Multi-Sample Security - LOW PRIORITY

**Location**: After Step 7
**Severity**: Low
**Description**: The proof handles single-sample security. For full FHE security,
we need to argue about security under multiple queries (IND-CPA game).

**Resolution Path**:
- Standard hybrid argument over Q queries
- Adv^{K-RLWE}_{multi} <= Q * Adv^{K-RLWE}_{single}
- This is a multiplicative loss but Q is polynomial, so security is preserved

### [NO GAP] Parameter Independence

The K-Elimination parameters (alpha_cap, beta_cap) are INDEPENDENT of RLWE security:
- alpha_cap and beta_cap are coprime factors of q (or auxiliary moduli)
- Their choice affects functionality (range of k values) not security
- Security derives entirely from RLWE hardness of the underlying samples

---

## Connection to T002 (QMNF-HE IND-CPA Security)

This theorem (T001) is a key building block for the main security theorem T002.

**Chain of Implications**:
```
A001 (RLWE Hardness)
  |
  v
L002 (K-Elimination Correctness) -----> Enables exact rescaling
  |
  v
L003 (Information Preservation) ------> No additional leakage
  |
  v
T001 (K-Enhanced RLWE Security) <------ THIS THEOREM
  |
  v
L005 (Encryption Hides Message) ------> Via RLWE indistinguishability
  |
  v
T002 (QMNF-HE IND-CPA Security) ------> Main security claim
```

---

## Comparison to Standard BFV Security

| Aspect | Standard BFV | QMNF-HE with K-Elimination |
|--------|--------------|---------------------------|
| Base assumption | RLWE | RLWE (same) |
| Reduction tightness | Tight | Tight |
| Additional assumptions | None | gcd(alpha_cap, beta_cap) = 1 |
| Security level | 128/192/256 bit | Same (inherited from RLWE params) |
| Novel attack surface | None | None (K-Elimination is deterministic) |

**Conclusion**: K-Elimination does NOT introduce any new attack surface or
weaken the security reduction. QMNF-HE inherits full RLWE-based security.

---

## References

1. A001 (RLWE Assumption): Lyubashevsky, Peikert, Regev "On Ideal Lattices and Learning with Errors over Rings" (2010)
2. L002, L003: See proof sketches in this directory
3. NINE65 Security Analysis: `/home/acid/Projects/NINE65/v5/docs/SECURITY_PROOFS.md`
4. Blueprint: `/home/acid/Projects/qmnf-security-proofs/swarm_run/state/blueprint.json`

---

## Integer-Only Arithmetic Verification

The entire security proof operates over:
- Polynomial rings R_q = Z_q[X]/(X^N + 1) with INTEGER coefficients mod q
- Dual-codex representation: integer residues mod alpha_cap and beta_cap
- K-Elimination: integer operations only

No floating-point arithmetic is used in:
- The cryptographic constructions
- The security reduction
- The advantage analysis

This is consistent with QMNF's integer-only mandate.
