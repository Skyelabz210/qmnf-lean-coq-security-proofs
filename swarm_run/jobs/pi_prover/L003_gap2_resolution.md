# GAP-2 Resolution: Completing the Reduction Argument for L003

**Node**: L003 - K-Elimination Information Preservation
**Gap ID**: GAP-2 (Issue 4.1 from κ-Critic)
**Resolved By**: π-Prover Agent (Round 2)
**Date**: 2026-02-01

---

## 1. The Gap

**Original Claim (L003 §4, Steps 3-4)**:
The reduction shows that distinguishing K_ELIM(RLWE) from K_ELIM(Uniform) is no easier than distinguishing RLWE from Uniform.

**κ-Critic Objection**:
The reduction argument is incomplete. It proves a distinguishing bound but does not explicitly connect this to the claim about information leakage about the secret s. The logical chain is valid but unstated.

**Additional Issue (L003 §5)**:
Step 4 claims H(s | K_ELIM(RLWE_s)) = H(s | RLWE_s) (equality), but the data processing inequality only gives ≥ (inequality).

---

## 2. Resolution: Explicit Logical Chain

### 2.1 Information Preservation Definition (Corrected)

**Definition (Information Preservation)**:

A deterministic function f: X → Y **preserves information about secret s** with respect to distribution D_s if:

```
H(s | f(D_s)) ≥ H(s | D_s)
```

where H(· | ·) denotes conditional entropy.

Equivalently (by data processing inequality), f preserves information if it doesn't CREATE new information about s—it can only lose or preserve information.

**Note**: We use ≥ (inequality), not = (equality). Equality would require f to be a sufficient statistic, which is a stronger condition.

### 2.2 The Missing Logical Bridge

The original proof shows:

**Computational Claim**: Adv^{K-RLWE}_A ≤ Adv^{RLWE}_B

The information preservation claim requires:

**Information-Theoretic Claim**: H(s | K_ELIM(RLWE_s)) ≥ H(s | RLWE_s)

These are connected via the following lemma:

### 2.3 Bridge Lemma

**Lemma (Computational-to-Information Bridge)**:

Let f be a deterministic function. If for all PPT distinguishers A:

```
|Pr[A(f(D_s)) = 1] - Pr[A(f(U)) = 1]| ≤ |Pr[A(D_s) = 1] - Pr[A(U) = 1]|
```

where D_s is a distribution depending on secret s and U is uniform, then:

```
H(s | f(D_s)) ≥ H(s | D_s)
```

*Proof*:

**Step 1**: By data processing inequality for entropy:
For any deterministic function f: H(s | f(X)) ≥ H(s | X, f(X))

Since f is deterministic, f(X) is determined by X, so:
H(s | X, f(X)) = H(s | X)

Therefore: H(s | f(X)) ≥ H(s | X) ✓

This proves the information-theoretic claim DIRECTLY from the determinism of f, without needing the computational reduction!

**Step 2**: The computational reduction provides additional assurance:
- If f leaked MORE distinguishing information than the input, there would exist A such that Adv^{f(D)}_A > Adv^{D}_A
- The reduction shows no such A exists
- This confirms f doesn't amplify distinguishing advantage

**Step 3**: Connection to secret recovery:
- If H(s | f(D_s)) < H(s | D_s), then f(D_s) contains more information about s
- More information about s means better distinguishing (contrapositive of semantic security)
- But we showed no better distinguishing exists
- Therefore H(s | f(D_s)) ≥ H(s | D_s)

∎

### 2.4 Complete Proof of L003

**Theorem (K-Elimination Information Preservation, Complete)**:

Let K_ELIM: (R_q, R_q) → Z_β be the K-Elimination function operating on RLWE samples.

Then K_ELIM preserves information about the secret s:

```
H(s | K_ELIM(RLWE_s)) ≥ H(s | RLWE_s)
```

*Proof*:

**Part A: K-Elimination is Deterministic**

K_ELIM is defined as:
```
K_ELIM(v_α, v_β) = ((v_β - v_α) · α_cap^(-1)) mod β_cap
```

This involves only:
- Subtraction (deterministic)
- Multiplication by precomputed constant (deterministic)
- Modular reduction (deterministic)

Therefore K_ELIM is a deterministic function. ✓

**Part B: Apply Data Processing Inequality**

For any deterministic function f and random variables X, S:
```
H(S | f(X)) ≥ H(S | X)
```

This is the data processing inequality for conditional entropy.

Setting f = K_ELIM, X = RLWE_s, S = s:
```
H(s | K_ELIM(RLWE_s)) ≥ H(s | RLWE_s)
```

✓

**Part C: Computational Confirmation (Redundant but Strengthening)**

Suppose for contradiction that K_ELIM leaks additional information. Then there exists distinguisher A such that:

```
Adv^{K-RLWE}_A > Adv^{RLWE}_A
```

Construct B as follows:
```
B(a, b):
  1. Compute v_α = b mod α_cap
  2. Compute v_β = b mod β_cap
  3. Compute k = K_ELIM(v_α, v_β)
  4. Return A(k)
```

Then:
```
Adv^{RLWE}_B = |Pr[B(RLWE) = 1] - Pr[B(U) = 1]|
            = |Pr[A(K_ELIM(RLWE)) = 1] - Pr[A(K_ELIM(U)) = 1]|
            = Adv^{K-RLWE}_A
```

So: Adv^{RLWE}_B = Adv^{K-RLWE}_A

If Adv^{K-RLWE}_A > Adv^{RLWE}_A for some A, then B has higher advantage than A against RLWE.

But this contradicts the optimality of A! If A were optimal against K-RLWE, then B would be a better RLWE distinguisher.

Therefore: Adv^{K-RLWE}_A ≤ Adv^{RLWE}_B for all A, B related by the reduction.

In particular, for the identity (no K_ELIM applied): Adv^{K-RLWE}_A ≤ Adv^{RLWE}_A

This confirms no distinguishing advantage is gained, consistent with Part B. ✓

**Part D: Explicit Statement of What L003 Claims**

K-Elimination Information Preservation means:

1. **No Additional Secret Leakage**: An adversary with access to K_ELIM(RLWE_s) learns no more about s than an adversary with access to RLWE_s directly.

2. **Quantitatively**: H(s | K_ELIM(RLWE_s)) ≥ H(s | RLWE_s)

3. **Computationally**: Adv^{K-RLWE}_A ≤ Adv^{RLWE}_B

4. **Practically**: Applying K-Elimination during FHE rescaling does not weaken security.

∎

---

## 3. Corrected Statements for L003

### Original (Incorrect):
> H(s | K_ELIM(RLWE_s)) = H(s | RLWE_s)

### Corrected:
> H(s | K_ELIM(RLWE_s)) ≥ H(s | RLWE_s)

The inequality is the correct form. Equality would hold only if K_ELIM were a sufficient statistic for s, which is a stronger (and unnecessary) claim.

### Interpretation:
- The inequality says K_ELIM **cannot increase** information about s
- K_ELIM may **decrease** information about s (some bits of the RLWE sample are discarded)
- For security, we only need to show no information is ADDED, which the inequality guarantees

---

## 4. The Complete Logical Chain

```
┌─────────────────────────────────────────────────────────────────┐
│ PREMISE: K_ELIM is deterministic                                │
│                                                                 │
│   K_ELIM(v_α, v_β) = ((v_β - v_α) · α_cap^(-1)) mod β_cap      │
│   Uses only: subtraction, multiplication, modulo               │
│   No randomness, no hidden state                                │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│ DATA PROCESSING INEQUALITY                                      │
│                                                                 │
│   For deterministic f: H(S | f(X)) ≥ H(S | X)                  │
│   "Processing data cannot create information"                   │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│ INFORMATION PRESERVATION                                        │
│                                                                 │
│   H(s | K_ELIM(RLWE_s)) ≥ H(s | RLWE_s)                        │
│   "K_ELIM reveals at most as much about s as RLWE itself"      │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│ SECURITY IMPLICATION                                            │
│                                                                 │
│   RLWE is hard ⟹ K-RLWE is hard                                │
│   No additional attack surface from K-Elimination               │
└─────────────────────────────────────────────────────────────────┘
```

---

## 5. Verification Checklist

- [x] Corrected equality to inequality (≥)
- [x] Explicitly stated the logical bridge
- [x] Proved bridge lemma from first principles
- [x] Showed determinism implies DPI applies
- [x] Confirmed computational reduction as additional evidence
- [x] Stated what L003 claims in plain language

---

## 6. GAP-2 Status

**STATUS**: RESOLVED

The reduction argument is now complete with:
1. Explicit bridge lemma connecting computational and information-theoretic claims
2. Corrected entropy statement (inequality, not equality)
3. Clear logical chain from determinism → DPI → information preservation → security

This completes the resolution of GAP-2.

---

**Resolver Signature**: π-Prover (Round 2)
**Resolution Date**: 2026-02-01
**Confidence**: HIGH
