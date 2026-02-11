# Loki-Clockwork Formal Specification v1.0

## Phase 1.1: Unified Formal Spec — Assumptions → Invariants → Definitions → Theorems → Proof Sketches → Test Obligations

**Document class:** Formal specification (Lean/Coq translation target)
**Scope:** Clockwork RNS arithmetic + Loki security substrate + composition theorems
**Status:** Draft for validation

---

# §0 — Notation and Conventions

- **ℤ** : integers
- **ℤ_m** : integers modulo m, i.e., ℤ/mℤ
- **[a, b]** : closed integer interval {a, a+1, ..., b}
- **⟨x⟩_m** : canonical representative of x mod m (context determines unsigned [0, m-1] or centered)
- **gcd(a, b)** : greatest common divisor
- **φ** : golden ratio (1 + √5)/2 ≈ 1.6180339887...
- **⊥** : failure / undefined
- **Pr[E]** : probability of event E
- **negl(λ)** : negligible function in security parameter λ
- **poly(λ)** : polynomial function in security parameter λ
- **PPT** : probabilistic polynomial time
- All logarithms are base 2 unless noted

---

# §1 — Assumptions (Axioms)

These are the non-negotiable starting points. Everything else derives from these.

## A1: RLWE Hardness

For security parameter λ, ring dimension n = n(λ), modulus q = q(λ), and error distribution χ = χ(λ):

> The Decision-RLWE_{n,q,χ} problem is hard: for all PPT adversaries A,
> |Pr[A(a, a·s + e) = 1] - Pr[A(a, u) = 1]| ≤ negl(λ)
> where a ←$ R_q, s ←$ χ, e ←$ χ, u ←$ R_q, and R_q = ℤ_q[x]/(x^n + 1).

## A2: PRF Security

Let F: {0,1}^κ × {0,1}^* → {0,1}^κ be the key evolution function.

> For all PPT distinguishers D with oracle access:
> |Pr[D^{F(K,·)} = 1] - Pr[D^{f(·)} = 1]| ≤ negl(κ)
> where K ←$ {0,1}^κ and f is a truly random function.

## A3: DDS Precision Bound

The Direct Digital Synthesis oscillator has phase accumulator width N_acc ∈ ℕ.

> All frequencies produced by the DDS are rational multiples of the reference clock f_ref:
> f_out = (Δφ / 2^{N_acc}) · f_ref
> where Δφ ∈ {0, 1, ..., 2^{N_acc} - 1} is the phase increment word.

This means: **no physical oscillator produces irrational frequencies.** All irrationality claims must be reframed as large-period claims.

## A4: Memory Zeroing

The hardware platform supports a memory zeroing primitive `zero(addr, len)` with the following property:

> After `zero(addr, len)` completes, all bytes in [addr, addr+len) read as 0x00,
> and this operation completes within T_zero(len) clock cycles,
> where T_zero is independent of the prior contents of the memory region.

In Rust: `core::ptr::write_volatile` + compiler fence, or platform `memset_s`.

## A5: Entropy Source

An entropy source ES produces output bits with min-entropy rate:

> H_∞(ES output | public state) ≥ h_min > 0
> per output bit, certified by online health tests (NIST SP 800-90B §4.4).

---

# §2 — Definitions

## §2.1 — Clockwork Core

### D1: RNS Basis

An **RNS basis** is a tuple **p** = (p_0, p_1, ..., p_k) of pairwise coprime positive integers.
The **capacity** of **p** is:

    M_k := ∏_{i=0}^{k} p_i

### D2: Residue Encoding

For X ∈ ℤ and RNS basis **p**, the **residue encoding** is:

    Enc_p(X) := (r_0, r_1, ..., r_k)  where  r_i ≡ X (mod p_i)

### D3: CRT Decode

The **CRT decode** is the unique map:

    Dec_p : ∏_{i=0}^{k} ℤ_{p_i} → ℤ_{M_k}

satisfying Dec_p(r_0, ..., r_k) ≡ r_i (mod p_i) for all i.

**Existence and uniqueness:** By CRT, this is a ring isomorphism.

### D4: Centered Lift

For modulus M and x ∈ ℤ_M, the **centered lift** is:

    Center_M(x) := the unique integer c ∈ [-⌊M/2⌋, ⌊M/2⌋] with c ≡ x (mod M)

When M is odd: the interval is [-(M-1)/2, (M-1)/2].
When M is even: the interval is [-M/2, M/2-1] (break ties toward negative — pick a convention and fix it).

### D5: Garner Mixed-Radix Digits

For RNS basis **p** = (p_0, ..., p_k), the **Garner digits** of X mod M_k are the unique tuple (d_0, d_1, ..., d_k) satisfying:

    X ≡ d_0 + d_1·p_0 + d_2·p_0·p_1 + ... + d_k·∏_{j=0}^{k-1} p_j  (mod M_k)

with d_i ∈ {0, 1, ..., p_i - 1} for all i.

### D6: K-Elimination (2-Gear Garner Step)

For coprime m, a and X with X ≡ r (mod m) and X ≡ s (mod a):

    k := (s - r) · m^{-1} (mod a)

Then X ≡ r + k·m (mod m·a), and k ∈ {0, 1, ..., a-1}.

### D7: Integer Bound Tracker

A **bound tracker** is a function H: Expressions → ℕ satisfying:

    |Center_{M_k}(X)| < 2^{H(X)}

with update rules:
- H(X + Y) ≤ max(H(X), H(Y)) + 1
- H(X · Y) ≤ H(X) + H(Y)
- H(∑_{j=1}^{L} w_j · x_j) ≤ ⌈log₂ L⌉ + max_j(H(w_j) + H(x_j))

### D8: Promotion (Basis Extension)

For RNS basis **p** = (p_0, ..., p_k) and new prime p_{k+1} coprime to M_k:

    Promote(Enc_p(X), r_{k+1}) := (r_0, ..., r_k, r_{k+1})

where r_{k+1} ≡ X (mod p_{k+1}).

This extends the representation to basis **p'** = (p_0, ..., p_k, p_{k+1}) with capacity M_{k+1} = M_k · p_{k+1}.

### D9: Decode-to-q Map

For RLWE modulus q and RNS basis **p** with M_k ≥ q:

    DecQ_p(r_0, ..., r_k) := Dec_p(r_0, ..., r_k) mod q

This is the **only** bridge from Clockwork representation space to RLWE ciphertext space.

## §2.2 — RLWE Core

### D10: Ciphertext Ring

    R_q := ℤ_q[x] / (x^n + 1)

where n is a power of 2 and q is the RLWE modulus (fixed per parameter set).

### D11: RLWE Ciphertext

An RLWE ciphertext under secret key s ∈ R is:

    ct = (a, b) ∈ R_q × R_q    where   b = a·s + e + (q/t)·m

for error e ←$ χ, plaintext m ∈ R_t, and plaintext modulus t.

### D12: Clockwork Coefficient Map (Φ)

For ct = (a, b) ∈ R_q × R_q with coefficient vectors a = (a_0, ..., a_{n-1}), b = (b_0, ..., b_{n-1}):

    Φ(ct) := (Enc_p(ã_0), ..., Enc_p(ã_{n-1}), Enc_p(b̃_0), ..., Enc_p(b̃_{n-1}))

where ã_i is the canonical integer representative of a_i ∈ ℤ_q (unsigned or centered — fix convention once).

**Φ is public and keyless.** It depends only on **p** and the lift convention.

## §2.3 — GRO Timing Model

### D13: DDS Oscillator Pair

A **DDS oscillator pair** is (Δφ_A, Δφ_B, N_acc) where:
- Δφ_A, Δφ_B ∈ {1, ..., 2^{N_acc} - 1} are phase increment words
- N_acc is the accumulator bit width
- The ratio Δφ_B / Δφ_A approximates φ (golden ratio)

The oscillator phases at discrete time step t are:

    θ_A(t) = t · Δφ_A  mod 2^{N_acc}
    θ_B(t) = t · Δφ_B  mod 2^{N_acc}

### D14: Coincidence Window

A **coincidence window** at time t is the event:

    |θ_A(t) - θ_B(t)| mod 2^{N_acc} < W

where W is the window width parameter. Operation execution is gated: crypto operations proceed only when this predicate holds.

### D15: Coincidence Period

The **coincidence period** (shortest full cycle of the coincidence pattern) is:

    T_coinc = 2^{N_acc} / gcd(Δφ_A - Δφ_B, 2^{N_acc})

Since Δφ_A - Δφ_B is odd with overwhelming probability (when approximating an irrational ratio), and 2^{N_acc} is a power of 2:

    gcd(Δφ_A - Δφ_B, 2^{N_acc}) = 1  ⟹  T_coinc = 2^{N_acc}

### D16: GRO Execution Model

A **GRO-gated execution** of function f on input x consists of:
1. **Wait** for next coincidence window W_j
2. **Execute** f(x) during W_j (must complete within window)
3. **Pad** remainder of window with constant-power dummy operations
4. **Idle** in constant-power loop until W_{j+1}

An external observer sees: uniform window-length execution blocks separated by uniform idle blocks, with the window schedule determined solely by (Δφ_A, Δφ_B, N_acc, W).

### D17: Constant-Time Function

A function f: X → Y is **constant-time** if:
- For all x₁, x₂ ∈ X: the sequence of memory access addresses is identical
- For all x₁, x₂ ∈ X: the sequence of branch decisions is identical
- The wall-clock cycle count T(f, x) satisfies T(f, x₁) = T(f, x₂)

In Rust: no secret-dependent indexing, no secret-dependent branches, use `subtle::ConditionallySelectable` for all secret-dependent selection.

## §2.4 — Key Lifecycle

### D18: Key Share Pair

For RLWE secret key s ∈ R_q, a **key share pair** is (s₁, s₂) ∈ R_q × R_q satisfying:

    s₁ + s₂ ≡ s (mod q)

### D19: Re-sharing

Given share pair (s₁, s₂), a **re-sharing** with randomness r ←$ R_q produces:

    (s₁', s₂') = (s₁ + r mod q,  s₂ - r mod q)

The new pair satisfies s₁' + s₂' ≡ s₁ + s₂ ≡ s (mod q).

### D20: Key Lifecycle State Machine

A secret key passes through states:

    KEYGEN → SPLIT → ACTIVE → RESHARE → ... → RESHARE → ZEROED

- **KEYGEN:** s computed, in plaintext memory. Duration: T_keygen (bounded).
- **SPLIT:** s₁, s₂ computed; s zeroed. Duration: T_split (bounded).
- **ACTIVE:** only (s₁, s₂) in memory. Unbounded, but resharing occurs every T_refresh ops.
- **RESHARE:** new (s₁', s₂') computed, old (s₁, s₂) zeroed within T_zero.
- **ZEROED:** all key material zeroed. Terminal state.

### D21: PRF Key Chain

The evaluation key evolution chain is:

    evk_0 = KDF(sk_master, 0)
    evk_{n+1} = KDF(sk_master, n+1)

where KDF is a key derivation function (HKDF-SHA256 or similar) satisfying A2.

## §2.5 — Integrity

### D22: Triple-Redundant State

For state value v, a **triple-redundant encoding** is:

    TR(v) = (v, v, v, CRC32(v))

stored at three independent memory locations.

### D23: Majority Vote Recovery

    MajVote(v₁, v₂, v₃, c) :=
        if v₁ = v₂ = v₃ and CRC32(v₁) = c: return v₁       (all agree)
        if v₁ = v₂ and CRC32(v₁) = c: return v₁              (v₃ corrupted)
        if v₁ = v₃ and CRC32(v₁) = c: return v₁              (v₂ corrupted)
        if v₂ = v₃ and CRC32(v₂) = c: return v₂              (v₁ corrupted)
        else: return ⊥                                         (fail-closed)

## §2.6 — Entropy Health

### D24: Entropy Health State

    EntropyState ∈ { HEALTHY, DEGRADED }

Transitions:
- HEALTHY → DEGRADED: when online health test fails (H_∞ estimate drops below h_min)
- DEGRADED → HEALTHY: after successful reseed from secondary source AND health test passes

### D25: FHE Gate

    FHE_Gate(op, entropy_state) :=
        if entropy_state = HEALTHY: execute op
        if entropy_state = DEGRADED: return ⊥ (halt, reseed, recheck)

---

# §3 — Invariants

These must hold at ALL times during system operation.

## INV-1: Fixed Cryptographic Modulus

    q is constant for the lifetime of a parameter set.
    No operation in Clockwork or Loki modifies q.

## INV-2: Representation Consistency

    ∀ coefficient c of any ciphertext in Clockwork representation:
        DecQ_p(Enc_p(c̃)) = c̃ mod q = c

    i.e., round-tripping through Clockwork residues and back to ℤ_q is the identity.

## INV-3: Bound Tracker Soundness

    ∀ expression X tracked by H:
        |Center_{M_k}(X)| < 2^{H(X)}

    and  M_k > 2^{H(X) + guard}  where guard is the safety margin.

## INV-4: GRO Window Sufficiency

    ∀ GRO-gated operations f:
        Duration(W) ≥ max_{x ∈ domain(f)} T(f, x) + T_pad

    where T_pad is the minimum padding duration for power uniformity.

## INV-5: Key Material Containment

    At any time t during ACTIVE state:
        exactly (s₁, s₂) are in memory, never s itself.
    At any time t during ZEROED state:
        no key material is in memory.

## INV-6: Entropy Gating

    No FHE operation that samples from χ (error distribution) executes
    while EntropyState = DEGRADED.

## INV-7: Public Schedule

    The operation DAG (sequence of HomAdd, HomMul, KeySwitch, Promote, Demote)
    is fixed before execution begins and does not depend on:
        (a) plaintext values
        (b) secret key values
        (c) ciphertext coefficient values
        (d) entropy state (entropy gating is halt-or-proceed, not branch)

## INV-8: Tier State Integrity

    ∀ GearStack gs with tier state ts:
        Before any DecQ operation: MajVote(ts) ≠ ⊥
        If MajVote(ts) = ⊥: abort computation (fail-closed)

---

# §4 — Theorems

## §4.1 — Clockwork Core Theorems

### T1: CRT Bijectivity

**Statement:** For RNS basis **p** = (p_0, ..., p_k) with pairwise coprime entries:

    Enc_p : ℤ_{M_k} → ∏_{i=0}^{k} ℤ_{p_i}

is a ring isomorphism. In particular, Dec_p ∘ Enc_p = id_{ℤ_{M_k}}.

**Proof:** Standard CRT. The map is well-defined (reduction mod each p_i), injective (if Enc_p(X) = Enc_p(Y) then p_i | (X-Y) for all i, hence M_k | (X-Y)), and surjective (by counting: both sets have M_k elements). Ring homomorphism follows from compatibility of mod with +, ×. ∎

### T2: K-Elimination Correctness

**Statement:** Let m, a be coprime, X ∈ ℤ with X ≡ r (mod m), X ≡ s (mod a). Define k := (s - r) · m⁻¹ (mod a). Then:

    (i)   k ∈ {0, 1, ..., a-1}
    (ii)  X ≡ r + k·m (mod m·a)
    (iii) k is the unique value in {0, ..., a-1} satisfying (ii)

**Proof sketch:**
- (i): By definition, k is reduced mod a.
- (ii): Check both congruences. mod m: r + k·m ≡ r (mod m) ✓. mod a: r + k·m ≡ r + (s-r)·m⁻¹·m ≡ r + (s-r) ≡ s (mod a) ✓.
- (iii): Uniqueness by CRT applied to the two-modulus case. ∎

### T3: Basis Extension Preservation

**Statement:** If (r_0, ..., r_k) = Enc_p(X) for X ∈ ℤ_{M_k}, and r_{k+1} ≡ X (mod p_{k+1}) where gcd(p_{k+1}, M_k) = 1, then:

    (r_0, ..., r_k, r_{k+1}) = Enc_{p'}(X)

for the extended basis **p'** = (p_0, ..., p_k, p_{k+1}), and X is the unique element of ℤ_{M_{k+1}} satisfying all k+2 congruences.

Moreover, restricting back to the first k+1 components recovers the original encoding.

**Proof:** Direct from CRT applied to **p'**. ∎

### T4: Bound Tracker Soundness

**Statement:** If H is maintained according to the update rules in D7, and all input values X satisfy |Center_{M_k}(X)| < 2^{H(X)}, then all computed values Y satisfy |Center_{M_k}(Y)| < 2^{H(Y)}.

**Proof sketch:**
- Addition: |Center(X+Y)| ≤ |Center(X)| + |Center(Y)| < 2^{H(X)} + 2^{H(Y)} ≤ 2^{max(H(X),H(Y))+1} ✓
- Multiplication: |Center(X·Y)| ≤ |Center(X)| · |Center(Y)| < 2^{H(X)} · 2^{H(Y)} = 2^{H(X)+H(Y)} ✓
- Dot product: By triangle inequality and multiplication bound, collecting L terms. ∎

### T5: Decode-to-q Correctness

**Statement:** For any coefficient c ∈ ℤ_q with canonical lift c̃:

    DecQ_p(Enc_p(c̃)) = c

provided M_k ≥ q (so that c̃ < M_k and the CRT representation is faithful).

**Proof:** c̃ < q ≤ M_k, so Enc_p(c̃) faithfully represents c̃ in ℤ_{M_k}. Dec_p recovers c̃ exactly (by T1). Reducing mod q gives c̃ mod q = c. ∎

### T6: Lane-wise Ring Homomorphism

**Statement:** For polynomials a, b ∈ R_q represented coefficient-wise in Clockwork:

    Φ(a + b mod q) can be computed by: lane-wise RNS addition, then DecQ on each coefficient.
    Φ(a · b mod (x^n+1, q)) can be computed by: lane-wise operations + NTT adaptation + DecQ.

**Caveat:** Multiplication requires care — the product coefficients may exceed M_k before reduction. The bound tracker (T4) determines when promotion is needed.

**Proof sketch:** CRT is a ring homomorphism (T1), so addition/subtraction in each lane is exact. Multiplication generates cross-terms that increase magnitude, tracked by H. After DecQ, the result is correct mod q. ∎

## §4.2 — Security Theorems

### T7: Post-Processing Security (IND-CPA Preservation)

**Statement:** Let Enc be an IND-CPA secure RLWE encryption scheme. Let Φ be the Clockwork coefficient map (D12), which is public and keyless. Then for all PPT adversaries A:

    Adv^{IND-CPA}_{Enc,Φ}(A) ≤ Adv^{IND-CPA}_{Enc}(A')

for some PPT adversary A' with comparable resources.

**Proof sketch:** Given A that distinguishes Φ(Enc(m₀)) from Φ(Enc(m₁)), construct A' that:
1. Receives ct from the IND-CPA challenger
2. Computes Φ(ct) (Φ is public, A' can compute it)
3. Runs A on Φ(ct)
4. Outputs whatever A outputs

A' has the same advantage as A, and is PPT since Φ is poly-time computable. ∎

### T8: GRO Timing Isolation

**Statement:** Let f be a constant-time function (D17) executed under GRO gating (D16). Let x₁, x₂ be any two inputs. An external observer measuring only:
- the timing of execution window starts/ends
- the power consumption during idle periods

cannot distinguish f(x₁) from f(x₂) with advantage better than:

    Adv_timing ≤ δ_power + δ_cache

where:
- δ_power is the power trace distinguishing advantage within a window (0 if padding is perfect)
- δ_cache is the cache-timing leakage (0 if f is constant-time per D17)

**Proof sketch:**
1. **Window timing is input-independent:** The GRO schedule depends only on (Δφ_A, Δφ_B, N_acc, W), which are public parameters. The schedule is identical regardless of what f computes.
2. **Within-window duration is constant:** f is constant-time (D17), and the window is padded to constant duration (INV-4). So the execution + pad duration is identical for all inputs.
3. **Idle power is constant:** By construction, the idle loop has constant power draw.
4. **Remaining leakage:** Only power variation within the execution portion of a window (δ_power) and cache-line access patterns (δ_cache) remain. Both are 0 under the stated conditions. ∎

**Critical dependency:** This theorem requires f to be constant-time (D17). GRO gating alone is insufficient for non-constant-time operations.

### T9: GRO Coincidence Period Bound

**Statement:** For DDS oscillator pair (Δφ_A, Δφ_B, N_acc) with Δφ_A - Δφ_B odd:

    T_coinc = 2^{N_acc}

An attacker performing timing correlation analysis requires at minimum T_coinc samples to identify the full coincidence pattern.

**Proof:** The coincidence function C(t) = (θ_A(t) - θ_B(t)) mod 2^{N_acc} = t·(Δφ_A - Δφ_B) mod 2^{N_acc}. Since Δφ_A - Δφ_B is odd and 2^{N_acc} is a power of 2, gcd(Δφ_A - Δφ_B, 2^{N_acc}) = 1. The sequence C(0), C(1), C(2), ... is a permutation of {0, 1, ..., 2^{N_acc} - 1} and has period exactly 2^{N_acc}. ∎

**Corollary:** For N_acc = 48 (common DDS width), T_coinc = 2^{48} ≈ 2.8 × 10^{14} clock ticks. At 1 GHz reference clock, this is ~78 hours. At 100 MHz, ~32.7 days.

### T10: Equidistribution of Coincidence Windows

**Statement:** Under the conditions of T9, the coincidence windows are equidistributed in the sense that for any subinterval I ⊆ [0, 2^{N_acc}):

    #{t ∈ [0, T) : C(t) ∈ I} / T  →  |I| / 2^{N_acc}   as T → T_coinc

More precisely, for T = T_coinc, the fraction equals |I| / 2^{N_acc} exactly (since C is a permutation).

**Consequence:** No rational-frequency sampling strategy can preferentially capture execution windows over idle periods, provided the attacker's sampling period does not divide T_coinc.

## §4.3 — Key Lifecycle Theorems

### T11: Re-sharing Correctness

**Statement:** If (s₁, s₂) is a valid key share pair for s, and (s₁', s₂') = Reshare(s₁, s₂, r), then (s₁', s₂') is also a valid key share pair for s.

**Proof:** s₁' + s₂' = (s₁ + r) + (s₂ - r) = s₁ + s₂ = s (mod q). ∎

### T12: Share Independence

**Statement:** For any fixed s, the distribution of s₁ (with s₂ = s - s₁) when s₁ ←$ R_q is uniform over R_q. In particular, knowledge of s₁ alone reveals no information about s beyond what is implied by s₁ ∈ R_q.

**Proof:** s₁ is drawn uniformly from R_q, independent of s. Given only s₁, the value s could be any element of R_q (since s₂ = s - s₁ is determined by s, but s is unknown). This is a one-time pad argument. ∎

**Caveat:** This provides security against a **single** snapshot. An attacker who observes both s₁ and s₂ at the same time recovers s. The protection model is: the attacker sees at most one share per observation.

### T13: Forward Secrecy of Key Chain

**Statement:** Under PRF security (A2), compromise of evk_n does not reveal evk_m for m ≠ n.

**Proof sketch:** Each evk_i = KDF(sk_master, i). Under PRF security, these are indistinguishable from independent random values. Knowledge of any subset does not help predict others without sk_master. ∎

**Limitation:** Compromise of sk_master breaks all evk values. This is inherent — forward secrecy is with respect to evaluation key exposure, not master key exposure.

## §4.4 — Integrity Theorems

### T14: Triple Redundancy Detection

**Statement:** MajVote (D23) detects and corrects any single-location corruption:

    If exactly one of {v₁, v₂, v₃} differs from the true value v, and CRC32(v) = c:
        MajVote returns v (correct recovery).
    If two or more locations are corrupted:
        MajVote returns ⊥ with probability ≥ 1 - 2^{-32} (CRC collision probability).

**Proof:** If one copy is corrupted, two copies agree on the true value and match the CRC. The majority vote selects the correct value. If two are corrupted to the same wrong value, CRC32 mismatch catches it with probability 1 - 2^{-32}. ∎

### T15: Fail-Closed Guarantee

**Statement:** If MajVote returns ⊥, no further FHE operations execute until the system is reinitialized.

**Proof:** By construction (INV-8). This is a design requirement, not a mathematical theorem — it must be verified by code inspection. ∎

## §4.5 — Composition Theorems

### T16: GRO-Garner Composition (Main Integration Theorem)

**Statement:** Let G be the K-Elimination operation (D6) implemented as a constant-time function (D17), executing under GRO gating (D16). Let X be a secret-dependent value (e.g., an RLWE secret key coefficient).

Then the Garner digit k = (s - r) · m⁻¹ mod a reveals no timing information about X, provided:

    (a) G is constant-time (no secret-dependent branches or memory access)
    (b) The GRO window is sufficiently long (INV-4)
    (c) The idle power is constant
    (d) The coincidence schedule is public

Formally: For all PPT timing adversaries A observing power traces and timing:

    |Pr[A(Trace(G(X₁))) = 1] - Pr[A(Trace(G(X₂))) = 1]| ≤ negl(λ)

for any X₁, X₂.

**Proof:** Combines T8 (GRO timing isolation) with D17 (constant-time guarantee). The trace consists of:
1. Window timing: independent of X (from T8 step 1)
2. Within-window power: constant (from D17 + padding)
3. Memory access pattern: constant (from D17)
4. Idle behavior: constant (from T8 step 3)

All components of the trace are X-independent, so the two distributions are identical (not just computationally indistinguishable). ∎

### T17: Full Stack Correctness

**Statement:** Let ct = Enc(m) be an RLWE ciphertext encrypting plaintext m. Let Ops be a public operation schedule (INV-7). Then:

    Dec(Execute(Φ(ct), Ops)) = m

provided:
1. Bound tracker H is sound (T4) and M_k > 2^{H+guard} at all steps
2. DecQ is applied after each arithmetic step that returns to ℤ_q semantics
3. The RLWE noise budget is not exceeded by Ops
4. Tier state integrity is maintained (INV-8)

**Proof sketch:** Correctness follows the chain:
- Φ is faithful (T5, T1)
- Lane-wise operations are correct (T6, T4 for overflow safety)
- DecQ recovers ℤ_q coefficients exactly (T5)
- RLWE decryption recovers m if noise is within budget (standard RLWE correctness)
- Tier state integrity ensures no silent corruption (T14, T15) ∎

### T18: Full Stack Security

**Statement:** Under assumptions A1 (RLWE hardness), A2 (PRF security), A3 (DDS precision), A4 (memory zeroing), A5 (entropy source):

The Loki-Clockwork system provides:
1. **IND-CPA security** for encrypted data (from A1, T7)
2. **Timing side-channel resistance** for all secret-dependent operations (from T8, T16)
3. **Forward secrecy** for evaluation keys (from A2, T13)
4. **Transient exposure resistance** for secret keys (from T12, D20)
5. **State integrity** with fail-closed recovery (from T14, T15)
6. **Entropy-gated operation** preventing low-quality error sampling (from D25, INV-6)

No single-point failure in components 2-6 compromises component 1 (IND-CPA security), since these are defense-in-depth layers operating on different threat surfaces.

---

# §5 — Proof Obligations for Formal Verification

The following are the statements that should be mechanized in Lean 4 or Coq, in priority order.

## Priority 1: Correctness Core (blocks everything else)

| ID | Statement | Target System | Dependencies |
|----|-----------|---------------|-------------|
| P1.1 | CRT bijectivity (T1) | Lean 4 | Mathlib.RingTheory.ChineseRemainder |
| P1.2 | K-Elimination correctness (T2) | Lean 4 | P1.1 |
| P1.3 | Basis extension preservation (T3) | Lean 4 | P1.1 |
| P1.4 | Bound tracker soundness (T4) | Lean 4 | Integer arithmetic |
| P1.5 | DecQ round-trip (T5) | Lean 4 | P1.1 |

## Priority 2: Security (requires crypto library)

| ID | Statement | Target System | Dependencies |
|----|-----------|---------------|-------------|
| P2.1 | IND-CPA post-processing (T7) | CryptoVerif / EasyCrypt | Game-based proof framework |
| P2.2 | GRO timing isolation (T8) | Tamarin / manual proof | Timing model formalization |
| P2.3 | Forward secrecy (T13) | CryptoVerif | PRF game |

## Priority 3: Integration (combines above)

| ID | Statement | Target System | Dependencies |
|----|-----------|---------------|-------------|
| P3.1 | GRO-Garner composition (T16) | Combined: Lean + Tamarin | P1.2, P2.2 |
| P3.2 | Full stack correctness (T17) | Lean 4 | P1.1-P1.5 |
| P3.3 | Re-sharing correctness (T11) | Lean 4 | Ring arithmetic |

---

# §6 — Test Obligations

These are executable tests that must pass before any deployment.

## §6.1 — Clockwork Arithmetic Tests

| Test ID | Description | Pass Criterion |
|---------|-------------|----------------|
| CT-01 | Round-trip Enc_p → Dec_p for all X ∈ [0, M_k) with k ∈ {2,3,4,5} | Exact equality |
| CT-02 | K-Elimination vs naive CRT decode for 10^6 random (r, s, m, a) | Exact equality |
| CT-03 | Bound tracker H vs actual |Center(X)| for 10^6 random operation chains | H(X) > ⌈log₂ |Center(X)|⌉ always |
| CT-04 | Promotion + demotion round-trip for 10^6 random values | Exact equality |
| CT-05 | DecQ(Enc_p(c̃)) = c for all c ∈ [0, q) with 5 different basis choices | Exact equality |
| CT-06 | Lane-wise add/sub matches R_q add/sub for 10^5 random polynomial pairs | Exact equality |

## §6.2 — GRO Tests

| Test ID | Description | Pass Criterion |
|---------|-------------|----------------|
| GT-01 | Coincidence period = 2^{N_acc} for 100 random DDS parameter pairs with odd difference | Exact equality |
| GT-02 | Window distribution: χ² test of coincidence times over 10^7 steps | p-value > 0.01 |
| GT-03 | Timing measurement: 10^6 GRO-gated operations with varying inputs | Timing std dev < 1 ns |
| GT-04 | Power trace correlation: 10^4 traces of GRO-gated K-Elim with random vs fixed input | Pearson |r| < 0.01 |

## §6.3 — Key Lifecycle Tests

| Test ID | Description | Pass Criterion |
|---------|-------------|----------------|
| KT-01 | Re-sharing correctness: 10^5 reshare cycles, verify s₁ + s₂ = s after each | Exact equality |
| KT-02 | Memory zeroing: inspect memory region after zero() call | All bytes 0x00 |
| KT-03 | Key evolution: verify evk_n values are PRF-consistent | Exact match with reference |
| KT-04 | Share independence: χ² test of s₁ distribution over 10^5 keygen instances | p-value > 0.01 |

## §6.4 — Integrity Tests

| Test ID | Description | Pass Criterion |
|---------|-------------|----------------|
| IT-01 | Single-bit flip in one copy → MajVote recovers correct value | 100% recovery |
| IT-02 | Two-copy corruption → MajVote returns ⊥ | ⊥ returned ≥ 99.9999% |
| IT-03 | CRC collision: 10^8 random corruption patterns | No false acceptance |
| IT-04 | Fail-closed: after MajVote returns ⊥, no FHE operation executes | Verified by state machine |

## §6.5 — Entropy Tests

| Test ID | Description | Pass Criterion |
|---------|-------------|----------------|
| ET-01 | Healthy entropy source → FHE operations proceed | Operations complete |
| ET-02 | Simulated entropy degradation → FHE operations halt | No operations during DEGRADED |
| ET-03 | Reseed + health test pass → operations resume | Operations resume |
| ET-04 | Min-entropy estimate of noise source output: 10^6 samples | H_∞ ≥ h_min |

## §6.6 — Integration Tests

| Test ID | Description | Pass Criterion |
|---------|-------------|----------------|
| FT-01 | Full round-trip: keygen → encrypt → HomAdd → HomMul → decrypt under GRO gating | Correct plaintext |
| FT-02 | Full round-trip with tier promotion/demotion during computation | Correct plaintext |
| FT-03 | Full round-trip with key resharing between operations | Correct plaintext |
| FT-04 | Full round-trip with injected tier state corruption + recovery | Correct plaintext |
| FT-05 | Full round-trip with entropy degradation mid-computation → halt → reseed → resume | Correct plaintext |
| FT-06 | Timing analysis of full round-trip: 10^4 runs with random plaintexts | No timing correlation with plaintext |

---

# §7 — Open Questions and Future Work

### Q1: Bootstrapping Protocol
The current spec covers leveled FHE (bounded depth). For arbitrary-depth FHE, a bootstrapping protocol is needed. How does GRO gating interact with bootstrapping latency? The window duration constraint (INV-4) may require very long windows during bootstrap, potentially weakening timing isolation.

**Proposed investigation:** Measure bootstrap duration variance and determine minimum GRO window width for constant-time bootstrap.

### Q2: Multi-Party Setting
If multiple parties hold key shares (threshold FHE), how does the key lifecycle protocol extend? Re-sharing requires communication, which introduces network timing.

### Q3: Hardware DDS Validation
The DDS precision model (A3) needs experimental validation on actual hardware. Specific questions: phase noise characteristics, temperature drift effects on coincidence stability, and power supply coupling.

### Q4: Formal Model for Power Leakage
T8 assumes constant power during execution. In practice, CMOS power consumption depends on Hamming weight transitions. A more detailed power model (e.g., switching activity) would tighten the security proof.

### Q5: Optimal Basis Selection
Given a target computation depth and coefficient magnitude, what is the optimal RNS basis **p** that minimizes promotion frequency while staying within the guard margin? This is an optimization problem that could be solved offline per parameter set.

---

# §8 — Document Revision History

| Version | Date | Changes |
|---------|------|---------|
| 0.1 | 2026-02-05 | Initial formal specification covering Clockwork core + Loki substrate + composition |

---

*End of formal specification.*
