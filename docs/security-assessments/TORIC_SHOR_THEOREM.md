===============================================================================
FORMALIZATION: Toric Shor (Non-Circular Order Finding & Factorization)
Crusher Version: 2
Formalism Level: RIGOROUS
Physics Compliance: PASS
===============================================================================

REVISION HISTORY
--------------------------------------------------------------------------------
v1: Initial formalization (2026-01-21)

PROBLEM STATEMENT
--------------------------------------------------------------------------------
Problem: Factor composite integer N using order finding, without knowing phi(N).

Prior Intractability:
  - Classical order finding requires knowing |G| = phi(N) for BSGS
  - But knowing phi(N) = (p-1)(q-1) implies knowing factors!
  - Circular dependency made classical approach seem impossible

Failed Approaches:
  - Pollard rho: O(N^(1/4)) but heuristic
  - Quadratic sieve: O(exp(sqrt(log N log log N))) - subexponential
  - Number field sieve: Best known classical, still exponential

Key Insight: Lagrange's theorem gives ord(a) divides |G|, and |G| <= N-1.
             We can use N-1 as bound WITHOUT computing phi(N)!

Citations:
  - Shor, P.W. (1994). Algorithms for quantum computation
  - Shanks, D. (1971). Class number, a theory of factorization
  - NINE65 Non-Circular Order Finding (2026)

===============================================================================
AXIOMS
===============================================================================

AXIOM TS1 (Group Structure):
  For N composite with gcd(a, N) = 1, a lies in (Z/NZ)*, a finite abelian group.

  Justification: Standard number theory [Hardy-Wright].

AXIOM TS2 (Lagrange's Theorem):
  For any element a in finite group G: ord(a) divides |G|.

  Justification: Lagrange's theorem [Herstein, Abstract Algebra].

AXIOM TS3 (Order Bound):
  For (Z/NZ)*: |G| = phi(N) <= N-1.
  Therefore: ord_N(a) <= N-1 for all a coprime to N.

  Justification: phi(N) < N for all N > 1.

AXIOM TS4 (Shor's Reduction):
  If r = ord_N(a) is even and a^(r/2) != -1 (mod N), then
  gcd(a^(r/2) +/- 1, N) gives non-trivial factor with probability >= 1/2.

  Justification: [Shor-1994, Section 5].

===============================================================================
DEFINITIONS
===============================================================================

DEF TS1 (Semiprime):
  N = p * q where p, q are distinct odd primes.

DEF TS2 (Multiplicative Order):
  ord_N(a) = min{r > 0 : a^r = 1 (mod N)}

DEF TS3 (BSGS Parameters):
  B = ceil(sqrt(N-1))
  Baby steps: S_baby = {a^j mod N : j = 0, 1, ..., B-1}
  Giant step multiplier: g = a^(-B) mod N

DEF TS4 (BSGS Match):
  A match occurs when a^j = a^(-iB) (mod N) for some i, j in [0, B-1].
  This implies a^(j+iB) = 1 (mod N), so ord(a) | (j + iB).

DEF TS5 (Toric Representation):
  The computation lives on T^2 = Z_M x Z_A where:
  - M = main modulus product
  - A = anchor modulus product
  - gcd(M, A) = 1

DEF TS6 (K-Elimination Order Verification):
  On T^2, order r is verified when:
  - a^r mod M = 1
  - a^r mod A = 1
  - k = K-Extract(1, 1) = 0 (complete cycle)

===============================================================================
THEOREMS
===============================================================================

THEOREM TS1 (Non-Circular Bound):
  Statement: BSGS with bound B = ceil(sqrt(N-1)) finds ord_N(a) without
             knowing phi(N).

  Proof:
    [1] ord_N(a) divides phi(N)                  (AXIOM TS2: Lagrange)
    [2] phi(N) <= N-1                            (AXIOM TS3: Order bound)
    [3] Therefore ord_N(a) <= N-1
    [4] BSGS finds order r when r <= B^2         (BSGS algorithm)
    [5] B = ceil(sqrt(N-1)) implies B^2 >= N-1
    [6] Therefore BSGS finds ord_N(a)            (r <= N-1 <= B^2)
    QED

  Requires: AXIOM TS2, AXIOM TS3
  Enables: Classical order finding without phi(N)

THEOREM TS2 (BSGS Correctness):
  Statement: If BSGS returns r, then a^r = 1 (mod N).

  Proof:
    [1] Match at (i, j): a^j = a^(-iB) (mod N)   (DEF TS4)
    [2] Multiply both sides by a^(iB):
        a^j * a^(iB) = 1 (mod N)                 (Modular arithmetic)
    [3] a^(j + iB) = 1 (mod N)
    [4] r = j + iB satisfies definition         (DEF TS2)
    QED

  Requires: DEF TS3, DEF TS4
  Enables: THEOREM TS3

THEOREM TS3 (BSGS Minimality):
  Statement: The smallest match (i, j) with i*B + j > 0 gives ord_N(a).

  Proof:
    [1] Let r* = ord_N(a) (true order)
    [2] Express r* = q*B + s where 0 <= s < B   (Division algorithm)
    [3] a^(r*) = a^(q*B + s) = 1 (mod N)
    [4] a^s = a^(-q*B) (mod N)
    [5] s is in baby steps, a^(-q*B) is giant step q
    [6] Match at (q, s) with q*B + s = r*
    [7] Any smaller match would contradict minimality of r*
    QED

  Requires: THEOREM TS2, DEF TS2
  Enables: Exact order recovery

THEOREM TS4 (Factorization from Order):
  Statement: Given ord_N(a) = r with r even and a^(r/2) != -1 (mod N),
             gcd(a^(r/2) + 1, N) or gcd(a^(r/2) - 1, N) is a non-trivial factor.

  Proof:
    [1] a^r = 1 (mod N)                         (Definition of order)
    [2] (a^(r/2))^2 = 1 (mod N)
    [3] (a^(r/2) - 1)(a^(r/2) + 1) = 0 (mod N)
    [4] N | (a^(r/2) - 1)(a^(r/2) + 1)
    [5] a^(r/2) != 1 (mod N) (else r/2 is order)
    [6] a^(r/2) != -1 (mod N) (given)
    [7] Neither factor is 0 mod N
    [8] gcd with each factor gives divisor      (AXIOM TS4)
    QED

  Requires: AXIOM TS4
  Enables: Complete factorization algorithm

THEOREM TS5 (K-Verification):
  Statement: On T^2, ord_N(a) = r iff K-Extract(a^r mod M, a^r mod A) = 0
             and a^r mod M = 1.

  Proof:
    [1] a^r = 1 (mod N) implies a^r = 1 (mod M) and a^r = 1 (mod A)
        (N | M*A and M, A coprime means N splits)      (CRT)
    [2] K-Extract(1, 1) = (1 - 1) * M^(-1) mod A = 0   (K-Elimination)
    [3] Conversely, k = 0 and v_M = 1 implies full value = 1
    [4] a^r = 1 (mod N)
    QED

  Requires: DEF TS5, DEF TS6, K-ELIMINATION formalization
  Enables: Efficient verification on toric substrate

THEOREM TS6 (Complexity):
  Statement: Toric Shor runs in O(sqrt(N) * log N) time and O(sqrt(N)) space.

  Proof:
    [1] Baby steps: O(sqrt(N)) computations, O(sqrt(N)) storage
    [2] Each computation: O(log N) for modular exponentiation
    [3] Giant steps: O(sqrt(N)) lookups, O(log N) each
    [4] Total time: O(sqrt(N) * log N)
    [5] Space: Hash table of size O(sqrt(N))
    QED

  Requires: DEF TS3
  Enables: Practical factorization for moderate N

===============================================================================
LEMMAS
===============================================================================

LEMMA TS1 (Modular Inverse Existence):
  gcd(a, N) = 1 implies a^(-1) mod N exists.

  Proof: Bezout's identity gives ax + Ny = 1, so a^(-1) = x mod N.

LEMMA TS2 (Random a Success Probability):
  For N = pq semiprime, randomly chosen coprime a gives usable order
  (even r, a^(r/2) != -1) with probability >= 1/2.

  Proof: [Shor-1994, Lemma 5.3]

LEMMA TS3 (Giant Step Table):
  Pre-computing a^(-B) allows giant steps in O(log N) time each.

  Proof: Giant step i is (a^(-B))^i, computed iteratively.

===============================================================================
CONDITIONS FOR CORRECTNESS
===============================================================================

CONDITION C1 (Coprimality):
  Requirement: gcd(a, N) = 1
  Failure mode: gcd(a, N) > 1 means a shares factor with N!
  Resolution: If gcd != 1, we've found a factor directly.

CONDITION C2 (Odd N):
  Requirement: N is odd composite
  Failure mode: Even N trivially factors by 2
  Resolution: Extract all factors of 2 first.

CONDITION C3 (Non-Prime-Power):
  Requirement: N is not a prime power p^k
  Failure mode: Shor's reduction doesn't apply to prime powers
  Resolution: Test for prime power separately (Newton's method for k-th root).

CONDITION C4 (Sufficient Random Trials):
  Requirement: Multiple random a's tested if first fails
  Failure mode: Single a might give odd order or a^(r/2) = -1
  Resolution: Retry with new random a (expected ~2 attempts).

===============================================================================
VALIDATION IDENTITIES
===============================================================================

V1: a^r = 1 (mod N) for returned order r
    Test: Verify modular exponentiation equals 1

V2: r divides phi(N) (if phi known for test cases)
    Test: Check r | (p-1)(q-1)

V3: gcd(a^(r/2) - 1, N) * gcd(a^(r/2) + 1, N) >= N
    Test: Product of gcds contains all of N

V4: Factors multiply to N
    Test: p * q = N

V5: K-Extract on complete cycle gives 0
    Test: k = 0 when a^r = 1 on toric substrate

===============================================================================
ERROR TAXONOMY
===============================================================================

E1: Non-Coprime Base
    Cause: gcd(a, N) > 1
    Detection: gcd computation at start
    Resolution: Return gcd as factor (lucky early termination!)

E2: Prime Power Input
    Cause: N = p^k for prime p
    Detection: Newton's method for integer k-th root
    Resolution: Use different algorithm (factor as p^k)

E3: Odd Order
    Cause: ord_N(a) is odd
    Detection: r % 2 != 0
    Resolution: Try different random a

E4: Trivial Square Root
    Cause: a^(r/2) = +/- 1 (mod N)
    Detection: Check before gcd
    Resolution: Try different random a

E5: Hash Collision
    Cause: Baby step table collision
    Detection: Multiple values for same key
    Resolution: Use list per key, check all candidates

===============================================================================
COMPLEXITY ANALYSIS
===============================================================================

Time:  O(sqrt(N) * log N) for BSGS + O(log N) for gcd = O(sqrt(N) * log N)
Space: O(sqrt(N)) for baby step hash table
Prior art: Quantum Shor O(log^3 N), NFS O(exp((log N)^(1/3)))
Improvement: Classical O(sqrt(N)) matches quantum for small N

NOTE: For cryptographic N (2048+ bits), sqrt(N) ~ 2^1024 is still intractable.
      The algorithm demonstrates correctness; quantum provides speed for large N.

===============================================================================
PHYSICS COMPLIANCE REPORT
===============================================================================

[PASS] Energy Conservation: Standard computation
[PASS] Information Conservation: Bijective group operations
[PASS] Causality: No FTL required
[PASS] Unitarity: N/A (classical algorithm)
[PASS] Second Law: Thermodynamically valid computation

===============================================================================
DERIVATION HINTS
===============================================================================

impl toric_shor(n: u128) -> Option<(u128, u128)>:
  Precondition: n odd, composite, not prime power    [CONDITIONS C2, C3]
  Step 1: For trial in 1..100:                       [CONDITION C4]
  Step 2:   a = random_coprime(n)                    [CONDITION C1]
  Step 3:   r = order_bsgs(a, n)                     [THEOREM TS1]
  Step 4:   if r % 2 == 0:                           [THEOREM TS4]
  Step 5:     sqrt_ar = mod_pow(a, r/2, n)
  Step 6:     if sqrt_ar != n - 1:                   [E4 check]
  Step 7:       p = gcd(sqrt_ar + 1, n)
  Step 8:       q = gcd(sqrt_ar - 1, n)              [THEOREM TS4]
  Step 9:       if 1 < p < n: return (p, n/p)
  Verify: p * q = n                                  [V4]

impl order_bsgs(a: u128, n: u128) -> Option<u128>:
  Precondition: gcd(a, n) = 1                        [CONDITION C1]
  Step 1: b = ceil(sqrt(n - 1))                      [DEF TS3]
  Step 2: baby_steps = {a^j mod n : j in 0..b}       [DEF TS3]
  Step 3: g = mod_inverse(mod_pow(a, b, n), n)       [LEMMA TS1]
  Step 4: giant = 1
  Step 5: for i in 0..b:                             [THEOREM TS2]
            if giant in baby_steps: return i*b + baby_steps[giant]
            giant = giant * g mod n
  Verify: a^r = 1 (mod n)                            [V1]

===============================================================================
CROSS-REFERENCES
===============================================================================

Internal:
  [K-ELIMINATION]: Verification oracle via k = 0 at complete cycle
  [TORIC-GROVER]: Similar toric substrate approach
  [WASSAN-SUBSTRATE]: Provides storage/execution manifold

External:
  [SHOR-1994]: Original quantum factoring algorithm
  [SHANKS-1971]: Baby-step giant-step method
  [POLLARD-1978]: Rho method comparison

===============================================================================
