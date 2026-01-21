#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Educational FROST KeyGen + Signing Experiments (Ristretto255 + SHA-512), Python 3.6.2 compatible.

This script implements an educational FROST-style flow over the Ristretto255 prime-order group:
  1) Random signer-subset selection for threshold signing (size alpha, t <= alpha <= n),
  2) A simplified, educational Schnorr-style threshold signing flow:
       - Preprocess: each signer generates nonces + commitments,
       - Sign: each signer produces a signature share using Lagrange coefficient for chosen subset,
       - Aggregate: aggregator computes binding factors, group commitment, challenge, and combines shares,
       - Verify: verify final Schnorr signature against group public key,
  3) Runtime instrumentation with time.perf_counter() (ms), per-trial and summary mean/median.

Hard constraints satisfied:
  - NO libsodium usage (no PyNaCl, no nacl.bindings, no ctypes, no indirect libsodium dependency).
  - SHA-512 is used for ALL protocol hashing.
  - Ristretto255 is used for ALL group operations with 32-byte canonical encodings.
  - Scalars are mod ℓ = 2^252 + 27742317777372353535851937790883648493 and encoded as 32-byte little-endian.

WARNING: Educational only (NOT production-grade):
  - Pure-Python big-int arithmetic is NOT constant-time.
  - Deterministic RNG mode (when --seed is used) is NOT cryptographically secure.
  - No authenticated network; broadcast/p2p are simulated with Python dicts.
  - No robust complaint/blame; failures raise.
"""

from __future__ import print_function

import argparse
import hashlib
import random
import secrets
import statistics
import time
from typing import Optional, Tuple


# =============================================================================
# Ristretto255 / Edwards25519 field + group (pure Python, educational)
# References implemented from RFC 9496 (Ristretto255 encode/decode and sqrt_ratio_m1).
# =============================================================================

# Field prime p = 2^255 - 19
P = 2**255 - 19

# Edwards25519 parameter a = -1 mod p, d = -121665/121666 mod p
EDWARDS_A = P - 1  # -1 mod p


def _fe(x: int) -> int:
    return int(x) % P


def _fe_add(x: int, y: int) -> int:
    return (int(x) + int(y)) % P


def _fe_sub(x: int, y: int) -> int:
    return (int(x) - int(y)) % P


def _fe_mul(x: int, y: int) -> int:
    return (int(x) * int(y)) % P


def _fe_neg(x: int) -> int:
    return (-int(x)) % P


def _fe_inv(x: int) -> int:
    x = int(x) % P
    if x == 0:
        raise ZeroDivisionError("No inverse for 0 mod p")
    return pow(x, P - 2, P)


def _is_negative_fe(x: int) -> bool:
    # RFC 9496: negative iff LSB of canonical little-endian encoding is 1 (i.e., integer is odd).
    return (int(x) % P) & 1 == 1


def _ct_abs_fe(x: int) -> int:
    x = int(x) % P
    return _fe_neg(x) if _is_negative_fe(x) else x


def _ct_select(cond: bool, a: int, b: int) -> int:
    return a if cond else b


def _fe_to_bytes_le(x: int) -> bytes:
    return (int(x) % P).to_bytes(32, "little")


def _fe_from_bytes_le(b: bytes) -> int:
    if not isinstance(b, (bytes, bytearray)) or len(b) != 32:
        raise ValueError("Field element encoding must be 32 bytes")
    x = int.from_bytes(bytes(b), "little")
    # RFC 9496: reject non-canonical values; no masking.
    if x >= P:
        raise ValueError("Non-canonical field element encoding")
    return x


# sqrt(-1) in F_p for p ≡ 5 (mod 8): SQRT_M1 = 2^((p-1)/4) mod p
SQRT_M1 = pow(2, (P - 1) // 4, P)


def _sqrt_mod_p(x: int) -> Optional[int]:
    """
    Return a nonnegative square root of x mod p, or None if no sqrt exists.
    For p ≡ 5 (mod 8), use the standard exponentiation method.
    """
    x = int(x) % P
    if x == 0:
        return 0
    r = pow(x, (P + 3) // 8, P)
    if (r * r - x) % P != 0:
        r = (r * SQRT_M1) % P
    if (r * r - x) % P != 0:
        return None
    return _ct_abs_fe(r)


def _sqrt_ratio_m1(u: int, v: int) -> Tuple[bool, int]:
    """
    RFC 9496 SQRT_RATIO_M1 for p = 2^255 - 19.

    Returns (was_square, r) where:
      - if was_square: r = sqrt(u/v)
      - else:         r = sqrt(i*u/v) where i = SQRT_M1
    And r is the nonnegative representative (CT_ABS).
    """
    u = int(u) % P
    v = int(v) % P

    # r = u * v^3 * (u * v^7)^((p-5)/8)
    v2 = (v * v) % P
    v3 = (v2 * v) % P
    v7 = (v3 * v3 * v) % P  # v^7

    # pow exponent: (p-5)/8
    r = (u * v3) % P
    x = (u * v7) % P
    r = (r * pow(x, (P - 5) // 8, P)) % P

    check = (v * (r * r % P)) % P
    u_neg = (-u) % P

    correct_sign_sqrt = (check == u)
    flipped_sign_sqrt = (check == u_neg)
    flipped_sign_sqrt_i = (check == (u_neg * SQRT_M1) % P)

    if flipped_sign_sqrt or flipped_sign_sqrt_i:
        r = (r * SQRT_M1) % P

    r = _ct_abs_fe(r)
    was_square = correct_sign_sqrt or flipped_sign_sqrt
    return was_square, r


# Edwards d constant
# d = -121665 / 121666 mod p
_EDWARDS_D_NUM = -121665
_EDWARDS_D_DEN = 121666
EDWARDS_D = (_EDWARDS_D_NUM * _fe_inv(_EDWARDS_D_DEN)) % P

# INVSQRT_A_MINUS_D = 1 / sqrt(a - d) (a = -1)
_a_minus_d = (EDWARDS_A - EDWARDS_D) % P
_sqrt_a_minus_d = _sqrt_mod_p(_a_minus_d)
if _sqrt_a_minus_d is None:
    raise RuntimeError("Sanity failure: sqrt(a-d) does not exist in F_p")
INVSQRT_A_MINUS_D = _fe_inv(_sqrt_a_minus_d)


class _ExtPoint:
    """
    Edwards25519 extended coordinates (X:Y:Z:T) with x=X/Z, y=Y/Z, T=XY/Z.
    """
    __slots__ = ("X", "Y", "Z", "T")

    def __init__(self, X: int, Y: int, Z: int, T: int):
        self.X = int(X) % P
        self.Y = int(Y) % P
        self.Z = int(Z) % P
        self.T = int(T) % P

    @staticmethod
    def identity() -> "_ExtPoint":
        return _ExtPoint(0, 1, 1, 0)

    def is_identity(self) -> bool:
        # In extended coords, identity has X=0, Y=Z, T=0. We keep a simple check.
        return self.X % P == 0 and self.T % P == 0 and (self.Y - self.Z) % P == 0

    def neg(self) -> "_ExtPoint":
        # (-x, y)
        return _ExtPoint(_fe_neg(self.X), self.Y, self.Z, _fe_neg(self.T))

    def add(self, Q: "_ExtPoint") -> "_ExtPoint":
        # Complete addition formulas for a = -1 (Ed25519)
        X1, Y1, Z1, T1 = self.X, self.Y, self.Z, self.T
        X2, Y2, Z2, T2 = Q.X, Q.Y, Q.Z, Q.T

        A = _fe_mul(_fe_sub(Y1, X1), _fe_sub(Y2, X2))
        B = _fe_mul(_fe_add(Y1, X1), _fe_add(Y2, X2))
        C = _fe_mul(_fe_mul(2, EDWARDS_D), _fe_mul(T1, T2))
        D = _fe_mul(2, _fe_mul(Z1, Z2))
        E = _fe_sub(B, A)
        F = _fe_sub(D, C)
        G = _fe_add(D, C)
        H = _fe_add(B, A)

        X3 = _fe_mul(E, F)
        Y3 = _fe_mul(G, H)
        T3 = _fe_mul(E, H)
        Z3 = _fe_mul(F, G)
        return _ExtPoint(X3, Y3, Z3, T3)

    def dbl(self) -> "_ExtPoint":
        X1, Y1, Z1 = self.X, self.Y, self.Z

        A = _fe_mul(X1, X1)
        B = _fe_mul(Y1, Y1)
        C = _fe_mul(2, _fe_mul(Z1, Z1))
        D = _fe_neg(A)
        E = _fe_sub(_fe_mul(_fe_add(X1, Y1), _fe_add(X1, Y1)), _fe_add(A, B))
        G = _fe_add(D, B)
        F = _fe_sub(G, C)
        H = _fe_sub(D, B)

        X3 = _fe_mul(E, F)
        Y3 = _fe_mul(G, H)
        T3 = _fe_mul(E, H)
        Z3 = _fe_mul(F, G)
        return _ExtPoint(X3, Y3, Z3, T3)

    def scalar_mul(self, k: int) -> "_ExtPoint":
        k = int(k)
        if k == 0:
            return _ExtPoint.identity()
        if k < 0:
            return self.neg().scalar_mul(-k)

        Q = _ExtPoint.identity()
        Ptmp = self
        while k > 0:
            if k & 1:
                Q = Q.add(Ptmp)
            Ptmp = Ptmp.dbl()
            k >>= 1
        return Q

    def to_internal_xyzt(self) -> Tuple[int, int, int, int]:
        # Return (x0, y0, z0, t0) in the RFC 9496 "internal representation" form.
        return self.X, self.Y, self.Z, self.T


# Edwards25519 basepoint (affine), standard constants (RFC 8032)
_ED25519_BX = 15112221349535400772501151409588531511454012693041857206046113283949847762202
_ED25519_BY = 46316835694926478169428394003475163141307993866256225615783033603165251855960
_BASEPOINT = _ExtPoint(_ED25519_BX, _ED25519_BY, 1, (_ED25519_BX * _ED25519_BY) % P)


def _ristretto_decode(s_bytes: bytes) -> _ExtPoint:
    """
    RFC 9496 §4.3.1 Decode (Ristretto255).
    Input: 32-byte encoding.
    Output: Edwards25519 extended point (prime-order group element), or raises ValueError.
    """
    s = _fe_from_bytes_le(s_bytes)

    if _is_negative_fe(s):
        raise ValueError("Decoding failed: negative field element")

    ss = (s * s) % P
    u1 = (1 - ss) % P
    u2 = (1 + ss) % P
    u2_sqr = (u2 * u2) % P

    v = (-(EDWARDS_D * (u1 * u1 % P)) - u2_sqr) % P

    was_square, invsqrt = _sqrt_ratio_m1(1, (v * u2_sqr) % P)

    den_x = (invsqrt * u2) % P
    den_y = (invsqrt * den_x % P) * v % P

    x = _ct_abs_fe((2 * s % P) * den_x % P)
    y = (u1 * den_y) % P
    t = (x * y) % P

    if (not was_square) or _is_negative_fe(t) or y == 0:
        raise ValueError("Decoding failed: invalid encoding")

    # Internal representation uses (x, y, 1, t)
    return _ExtPoint(x, y, 1, t)


def _ristretto_encode(Pt: _ExtPoint) -> bytes:
    """
    RFC 9496 §4.3.2 Encode (Ristretto255).
    Input: Edwards25519 extended point.
    Output: 32-byte canonical encoding.
    """
    x0, y0, z0, t0 = Pt.to_internal_xyzt()

    u1 = ((z0 + y0) % P) * ((z0 - y0) % P) % P
    u2 = (x0 * y0) % P

    # Ignore was_square since this is always square.
    _, invsqrt = _sqrt_ratio_m1(1, (u1 * (u2 * u2 % P)) % P)

    den1 = (invsqrt * u1) % P
    den2 = (invsqrt * u2) % P
    z_inv = (den1 * den2 % P) * t0 % P

    ix0 = (x0 * SQRT_M1) % P
    iy0 = (y0 * SQRT_M1) % P
    enchanted_denominator = (den1 * INVSQRT_A_MINUS_D) % P

    rotate = _is_negative_fe((t0 * z_inv) % P)

    # Conditionally rotate x and y.
    x = _ct_select(rotate, iy0, x0)
    y = _ct_select(rotate, ix0, y0)
    z = z0
    den_inv = _ct_select(rotate, enchanted_denominator, den2)

    y = _ct_select(_is_negative_fe((x * z_inv) % P), _fe_neg(y), y)

    s = _ct_abs_fe((den_inv * ((z - y) % P)) % P)
    return _fe_to_bytes_le(s)


# =============================================================================
# Ristretto255 scalar/point utilities (external interface mirrors baseline)
# =============================================================================

# Ed25519 / Ristretto scalar field order ℓ (prime)
L = 2**252 + 27742317777372353535851937790883648493
SCALAR_BYTES = 32
POINT_BYTES = 32

# Ristretto identity encoding is 32 zero bytes.
RISTRETTO_IDENTITY = b"\x00" * 32

# Domain separation tags (SHA-512 everywhere)
DST_KEYGEN_POK = b"FROST_KEYGEN_POK_SHA512"
DST_SIGN_RHO = b"FROST_SIGN_RHO_SHA512"
DST_SIGN_CHALLENGE = b"FROST_SIGN_CHALLENGE_SHA512"


def int_to_bytes_be(x, length):
    return int(x).to_bytes(length, "big")


def scalar_reduce(x):
    return int(x) % L


def scalar_add(a, b):
    return (int(a) + int(b)) % L


def scalar_sub(a, b):
    return (int(a) - int(b)) % L


def scalar_mul(a, b):
    return (int(a) * int(b)) % L


def scalar_inv(a):
    a = int(a) % L
    if a == 0:
        raise ZeroDivisionError("No inverse for 0 mod ℓ")
    return pow(a, L - 2, L)


def scalar_to_bytes_le(a):
    return (int(a) % L).to_bytes(SCALAR_BYTES, "little")


def scalar_from_bytes_le(b):
    if len(b) != SCALAR_BYTES:
        raise ValueError("Scalar bytes must be 32 bytes")
    return int.from_bytes(b, "little") % L


def point_is_valid(P_bytes):
    if not isinstance(P_bytes, (bytes, bytearray)) or len(P_bytes) != POINT_BYTES:
        return False
    try:
        Pt = _ristretto_decode(bytes(P_bytes))
        return _ristretto_encode(Pt) == bytes(P_bytes)
    except Exception:
        return False


def point_from_bytes(P_bytes):
    P_bytes = bytes(P_bytes)
    if len(P_bytes) != POINT_BYTES:
        raise ValueError("Point bytes must be 32 bytes")
    if not point_is_valid(P_bytes):
        raise ValueError("Invalid Ristretto255 point encoding")
    return P_bytes


def point_to_bytes(P):
    return bytes(P)


def point_eq(P, Q):
    # Ristretto encodings are canonical; byte equality is correct for group equality.
    return bytes(P) == bytes(Q)


def point_add(P, Q):
    P_i = _ristretto_decode(bytes(P))
    Q_i = _ristretto_decode(bytes(Q))
    R_i = P_i.add(Q_i)
    return _ristretto_encode(R_i)


def point_sub(P, Q):
    P_i = _ristretto_decode(bytes(P))
    Q_i = _ristretto_decode(bytes(Q))
    R_i = P_i.add(Q_i.neg())
    return _ristretto_encode(R_i)


def point_mul_base(k):
    k = int(k) % L
    if k == 0:
        return RISTRETTO_IDENTITY
    R_i = _BASEPOINT.scalar_mul(k)
    return _ristretto_encode(R_i)


def point_mul(P, k):
    k = int(k) % L
    if k == 0:
        return RISTRETTO_IDENTITY
    P_i = _ristretto_decode(bytes(P))
    R_i = P_i.scalar_mul(k)
    return _ristretto_encode(R_i)


# --- Minimal sanity checks at startup (required) ---
if not point_is_valid(RISTRETTO_IDENTITY):
    raise RuntimeError("Sanity check failed: Ristretto identity encoding is not valid.")
if not point_eq(point_mul_base(0), RISTRETTO_IDENTITY):
    raise RuntimeError("Sanity check failed: [0]B != identity.")
if not point_is_valid(point_mul_base(1)):
    raise RuntimeError("Sanity check failed: basepoint encoding invalid.")
if not point_is_valid(point_mul_base(2)):
    raise RuntimeError("Sanity check failed: [2]B encoding invalid.")


# =============================================================================
# Deterministic RNG wrapper (for reproducible experiments; NOT secure)
# =============================================================================

class ExperimentRNG(object):
    """
    A tiny wrapper that can use either:
      - secrets.SystemRandom / secrets.randbelow (default, non-deterministic), or
      - random.Random(seed) (deterministic, reproducible; NOT cryptographically secure).
    """
    def __init__(self, seed=None):
        self.seed = seed
        self._rnd = random.Random(seed) if seed is not None else None

    def randbelow(self, n):
        if self._rnd is None:
            return secrets.randbelow(n)
        return self._rnd.randrange(n)

    def sample(self, population, k):
        if self._rnd is None:
            return secrets.SystemRandom().sample(population, k)
        return self._rnd.sample(population, k)


def rand_scalar_nonzero(rng):
    # sample uniformly from Z_ℓ^* (non-zero)
    return rng.randbelow(L - 1) + 1


# =============================================================================
# SHA-512 hash-to-scalar (non-zero) in Z_ℓ
# =============================================================================

def hash_to_scalar_nonzero_sha512(domain, *parts):
    """
    c = SHA512(domain || 0x00 || ctr || (len||part)... ) mod ℓ
    retry if c == 0
    """
    ctr = 0
    while True:
        h = hashlib.sha512()
        h.update(domain)
        h.update(b"\x00")
        h.update(int_to_bytes_be(ctr, 4))
        for p in parts:
            if not isinstance(p, (bytes, bytearray)):
                raise TypeError("hash parts must be bytes")
            h.update(int_to_bytes_be(len(p), 4))
            h.update(bytes(p))
        c = int.from_bytes(h.digest(), "big") % L
        if c != 0:
            return c
        ctr += 1


# =============================================================================
# Polynomial / Shamir utilities over Z_ℓ
# =============================================================================

def eval_poly(coeffs, x):
    # f(x) = sum_{j=0..t-1} a_j * x^j mod ℓ
    acc = 0
    power = 1
    x = int(x) % L
    for a_j in coeffs:
        acc = (acc + (int(a_j) % L) * power) % L
        power = (power * x) % L
    return acc


def lagrange_coeff_at_zero(i, S):
    # λ_i = Π_{j in S, j != i} (0 - j) / (i - j) mod ℓ
    num = 1
    den = 1
    i = int(i) % L
    for j in S:
        j = int(j) % L
        if j == i:
            continue
        num = (num * (-j % L)) % L
        den = (den * ((i - j) % L)) % L
    return (num * scalar_inv(den)) % L


def shamir_reconstruct_secret_at_zero(shares):
    S = list(shares.keys())
    secret = 0
    for i, si in shares.items():
        lam = lagrange_coeff_at_zero(i, S)
        secret = (secret + lam * (int(si) % L)) % L
    return secret


# =============================================================================
# KeyGen message types
# =============================================================================

class SchnorrPoK(object):
    # σ_i = (R_i, μ_i)
    def __init__(self, R, mu):
        self.R = bytes(R)        # 32-byte Ristretto encoding
        self.mu = int(mu) % L    # scalar


class KeyGenBroadcast(object):
    # C~_i and σ_i
    def __init__(self, dealer_id, C_tilde, sigma):
        self.dealer_id = int(dealer_id)
        self.C_tilde = list(C_tilde)   # list of points φ_{i0..i,t-1} (bytes)
        self.sigma = sigma             # SchnorrPoK


# =============================================================================
# Feldman share verification over Ristretto255 points
# =============================================================================

def feldman_verify_share_point(C_tilde_dealer, receiver_id, share_value):
    """
    Check:
      Left:  [ f_dealer(receiver_id) ] B
      Right: Σ_{k=0..t-1} [ receiver_id^k ] φ_{dealer,k}
    """
    receiver_id = int(receiver_id)
    share_value = int(share_value) % L

    left = point_mul_base(share_value)

    rhs = RISTRETTO_IDENTITY
    power = 1  # receiver_id^0
    for phi_k in C_tilde_dealer:
        term = point_mul(phi_k, power)
        rhs = point_add(rhs, term)
        power = (power * receiver_id) % L

    return point_eq(left, rhs)


# =============================================================================
# Participant: KeyGen + Signing state
# =============================================================================

class Participant(object):
    """
    KeyGen state:
      - a_{i0..i,t-1} : polynomial coefficients
      - C~_i          : commitments φ_{ij} = [a_{ij}]B
      - σ_i           : PoK of a_{i0}
      - s_i           : long-lived secret share
      - Y_i           : public key share [s_i]B

    Signing (ephemeral) state per trial/signing:
      - d_i, e_i      : nonces (scalars)
      - D_i, E_i      : commitments ([d_i]B, [e_i]B)
    """

    def __init__(self, i, n, t, ctx_phi):
        self.i = int(i)
        self.n = int(n)
        self.t = int(t)
        self.ctx_phi = str(ctx_phi)

        # Round 1 internal state
        self.a = None
        self.C_tilde = None
        self.sigma = None

        # Keep own share from own polynomial
        self._self_share_from_own_poly = None

        # Outputs after Round 2
        self.s_i = None
        self.Y_i = None

        # Signing ephemeral state (set during preprocess)
        self._nonce_d = None
        self._nonce_e = None
        self.D_i = None
        self.E_i = None

    # -------- KeyGen Round 1 Step 1 + Step 3 --------
    def round1_sample_poly_and_commit(self, rng):
        self.a = [rand_scalar_nonzero(rng) for _ in range(self.t)]
        self.C_tilde = [point_mul_base(aij) for aij in self.a]

    # -------- KeyGen Round 1 Step 2 --------
    def round1_generate_pok_of_a_i0(self, rng):
        if self.a is None or self.C_tilde is None:
            raise RuntimeError("Must run round1_sample_poly_and_commit() first.")

        a_i0 = self.a[0]
        phi_i0 = self.C_tilde[0]

        k = rand_scalar_nonzero(rng)
        R = point_mul_base(k)

        # Context Φ included here (anti-replay / domain separation)
        c = hash_to_scalar_nonzero_sha512(
            DST_KEYGEN_POK,
            int_to_bytes_be(self.i, 4),
            self.ctx_phi.encode("utf-8"),
            point_to_bytes(phi_i0),
            point_to_bytes(R),
        )

        mu = scalar_add(k, scalar_mul(a_i0, c))
        self.sigma = SchnorrPoK(R=R, mu=mu)

    # -------- KeyGen Round 1 Step 4 --------
    def round1_broadcast(self):
        if self.C_tilde is None or self.sigma is None:
            raise RuntimeError("Round 1 not complete.")
        return KeyGenBroadcast(dealer_id=self.i, C_tilde=self.C_tilde, sigma=self.sigma)

    # -------- KeyGen Round 1 Step 5 --------
    def round1_verify_others_pok(self, broadcasts):
        for dealer_id, msg in broadcasts.items():
            if int(dealer_id) == self.i:
                continue

            R = msg.sigma.R
            mu = msg.sigma.mu
            phi_l0 = msg.C_tilde[0]

            c = hash_to_scalar_nonzero_sha512(
                DST_KEYGEN_POK,
                int_to_bytes_be(int(dealer_id), 4),
                self.ctx_phi.encode("utf-8"),
                point_to_bytes(phi_l0),
                point_to_bytes(R),
            )

            # Check: R ?= [μ]B - [c]φ_{ℓ0}
            g_mu = point_mul_base(mu)
            cphi = point_mul(phi_l0, c)
            right = point_sub(g_mu, cphi)

            if not point_eq(R, right):
                raise RuntimeError("PoK verification failed at P{} for dealer P{}".format(self.i, dealer_id))

    # -------- KeyGen Round 2 Step 1 --------
    def round2_send_shares(self):
        if self.a is None:
            raise RuntimeError("Round 1 polynomial not generated.")
        shares = {}
        for l_id in range(1, self.n + 1):
            shares[l_id] = eval_poly(self.a, l_id)

        self._self_share_from_own_poly = shares[self.i]
        self.a = None  # educational deletion
        return shares

    # -------- KeyGen Round 2 Step 2 + Step 3 + Step 4 --------
    def round2_receive_verify_and_finalize(self, broadcasts, shares_from_all_dealers):
        if self._self_share_from_own_poly is None:
            raise RuntimeError("Must run round2_send_shares() first.")

        # Step 2: verify all incoming shares
        for dealer_id in range(1, self.n + 1):
            C_tilde_dealer = broadcasts[dealer_id].C_tilde
            share_value = shares_from_all_dealers[dealer_id]  # f_dealer(i)
            if not feldman_verify_share_point(C_tilde_dealer, self.i, share_value):
                raise RuntimeError("Share verification failed at P{} for dealer P{}".format(self.i, dealer_id))

        # Step 3: s_i = Σ f_dealer(i) mod ℓ
        s_i = 0
        for dealer_id in range(1, self.n + 1):
            s_i = scalar_add(s_i, shares_from_all_dealers[dealer_id])

        self.s_i = s_i

        # Step 4: Y_i = [s_i]B
        self.Y_i = point_mul_base(self.s_i)

    # =============================================================================
    # Signing experiments (educational FROST-style)
    # =============================================================================

    def preprocess_nonces_and_commitments(self, rng):
        """
        Preprocess (educational):
          d_i, e_i ← Z_ℓ^*
          D_i = [d_i]B,  E_i = [e_i]B
        """
        self._nonce_d = rand_scalar_nonzero(rng)
        self._nonce_e = rand_scalar_nonzero(rng)
        self.D_i = point_mul_base(self._nonce_d)
        self.E_i = point_mul_base(self._nonce_e)
        return self.D_i, self.E_i

    def sign_share(self, rho_i, challenge_c, lambda_i):
        """
        Produce a signature share (educational Schnorr threshold share):

          z_i = d_i + rho_i*e_i + (lambda_i * s_i * c)  mod ℓ
        """
        if self._nonce_d is None or self._nonce_e is None or self.s_i is None:
            raise RuntimeError("Missing nonces or secret share; run preprocess and KeyGen first.")

        z_i = self._nonce_d
        z_i = scalar_add(z_i, scalar_mul(rho_i, self._nonce_e))
        z_i = scalar_add(z_i, scalar_mul(lambda_i, scalar_mul(self.s_i, challenge_c)))

        # Erase nonces (educational hygiene)
        self._nonce_d = None
        self._nonce_e = None

        return z_i


# =============================================================================
# KeyGen orchestrator
# =============================================================================

def frost_keygen(n, t, ctx_phi, rng):
    n = int(n)
    t = int(t)
    if not (1 <= t <= n):
        raise ValueError("Require 1 <= t <= n")

    participants = {}
    for i in range(1, n + 1):
        participants[i] = Participant(i=i, n=n, t=t, ctx_phi=ctx_phi)

    # ----- Round 1 -----
    broadcasts = {}
    for i, Pi in participants.items():
        Pi.round1_sample_poly_and_commit(rng)     # Step 1 + Step 3
        Pi.round1_generate_pok_of_a_i0(rng)       # Step 2
        broadcasts[i] = Pi.round1_broadcast()     # Step 4

    for i, Pi in participants.items():
        Pi.round1_verify_others_pok(broadcasts)   # Step 5

    # ----- Round 2 -----
    mailbox = {}
    for i in range(1, n + 1):
        mailbox[i] = {}

    for dealer_id, Pi in participants.items():
        shares = Pi.round2_send_shares()
        for receiver_id, share_val in shares.items():
            mailbox[receiver_id][dealer_id] = share_val

    for receiver_id, Pi in participants.items():
        Pi.round2_receive_verify_and_finalize(
            broadcasts=broadcasts,
            shares_from_all_dealers=mailbox[receiver_id],
        )

    # Round 2 Step 4: group public key Y = Σ φ_{j0}
    Y = RISTRETTO_IDENTITY
    for j in range(1, n + 1):
        phi_j0 = broadcasts[j].C_tilde[0]
        Y = point_add(Y, phi_j0)

    return participants, Y


# =============================================================================
# Signing helpers
# =============================================================================

def choose_signer_subset(n, t, alpha, rng):
    n = int(n)
    t = int(t)
    alpha = int(alpha)
    if not (t <= alpha <= n):
        raise ValueError("Require t <= alpha <= n")
    S = rng.sample(list(range(1, n + 1)), alpha)
    S = sorted([int(x) for x in S])
    return S


def encode_commitment_list(S, commitments):
    """
    Deterministic transcript encoding of commitments for a signer subset S.

    commitments[i] = (D_i_bytes, E_i_bytes)
    Encoding: for i in sorted(S): i(4B big-endian) || D_i(32B) || E_i(32B)
    """
    out = b""
    for i in sorted(S):
        D_i, E_i = commitments[i]
        out += int_to_bytes_be(i, 4) + point_to_bytes(D_i) + point_to_bytes(E_i)
    return out


def compute_binding_factors(ctx_phi, message_bytes, S, commitments):
    """
    Compute per-signer binding factors rho_i.

    Educational approach:
      rho_i = H_to_Zℓ*( DST_SIGN_RHO, i, Φ, m, encode_commitment_list(S, commitments) )
    """
    transcript = encode_commitment_list(S, commitments)
    rho = {}
    for i in S:
        rho[i] = hash_to_scalar_nonzero_sha512(
            DST_SIGN_RHO,
            int_to_bytes_be(i, 4),
            ctx_phi.encode("utf-8"),
            message_bytes,
            transcript,
        )
    return rho


def compute_group_commitment_R(S, commitments, rho):
    """
    Compute:
      R = Σ_{i in S} ( D_i + [rho_i] E_i )
    """
    R = RISTRETTO_IDENTITY
    for i in S:
        D_i, E_i = commitments[i]
        R_i = point_add(D_i, point_mul(E_i, rho[i]))
        R = point_add(R, R_i)
    return R


def compute_challenge(ctx_phi, Y, R, message_bytes):
    """
    Schnorr challenge:
      c = H_to_Zℓ*( DST_SIGN_CHALLENGE, Φ, Y, R, m )
    """
    return hash_to_scalar_nonzero_sha512(
        DST_SIGN_CHALLENGE,
        ctx_phi.encode("utf-8"),
        point_to_bytes(Y),
        point_to_bytes(R),
        message_bytes,
    )


def aggregate_signature_shares(S, z_shares):
    """
    Aggregate:
      z = Σ_{i in S} z_i mod ℓ
    """
    z = 0
    for i in S:
        z = scalar_add(z, z_shares[i])
    return z


def verify_schnorr_signature(Y, ctx_phi, message_bytes, signature):
    """
    Verify a Schnorr signature (R, z) against public key Y:

      [z]B ?= R + [c]Y
      c = H_to_Zℓ*( DST_SIGN_CHALLENGE, Φ, Y, R, m )
    """
    R, z = signature
    c = compute_challenge(ctx_phi, Y, R, message_bytes)
    left = point_mul_base(z)
    right = point_add(R, point_mul(Y, c))
    return point_eq(left, right)


# =============================================================================
# Runtime instrumentation helpers
# =============================================================================

def ms(dt_seconds):
    return 1000.0 * dt_seconds


def mean_median(values):
    if not values:
        return 0.0, 0.0
    return float(statistics.mean(values)), float(statistics.median(values))


# =============================================================================
# Main (CLI + trials)
# =============================================================================

def parse_args():
    p = argparse.ArgumentParser(description="Educational FROST KeyGen + signing experiments (Ristretto255 + SHA-512).")
    p.add_argument("--n", type=int, default=10, help="Number of participants (n). Default: 10.")
    p.add_argument("--t", type=int, default=5, help="Threshold (t). Default: 5.")
    p.add_argument("--alpha", type=int, default=None, help="Signer subset size (alpha), t <= alpha <= n. Default: alpha=t.")
    p.add_argument("--trials", type=int, default=10, help="Number of trials (default 10).")
    p.add_argument("--seed", type=int, default=None, help="Seed for reproducible randomness (NOT secure).")
    p.add_argument("--message", type=str, default="test", help="Message to sign (default 'test').")
    return p.parse_args()


def main():
    # --- Setup timing (argument parsing + RNG seeding) ---
    t_setup_start = time.perf_counter()

    args = parse_args()
    n = int(args.n)
    t = int(args.t)
    alpha = int(args.alpha) if args.alpha is not None else int(t)
    trials = int(args.trials)
    seed = args.seed
    msg_str = args.message
    message_bytes = msg_str.encode("utf-8")

    if not (1 <= t <= n):
        raise ValueError("Require 1 <= t <= n")
    if not (t <= alpha <= n):
        raise ValueError("Require t <= alpha <= n")
    if trials < 1:
        raise ValueError("Require --trials >= 1")

    # Setup completed
    t_setup_end = time.perf_counter()
    setup_ms = ms(t_setup_end - t_setup_start)

    # Containers for summary stats across trials (ms)
    stats = {
        "setup_ms": [],
        "keygen_ms": [],
        "preprocess_ms": [],
        "sign_ms": [],
        "aggregate_ms": [],
        "verify_ms": [],
        "total_ms": [],
        "preprocess_per_participant_ms": [],  # flattened across participants
        "sign_per_participant_ms": [],        # flattened across participants
    }

    print("=== Configuration ===")
    print("n={}, t={}, alpha={}, trials={}, seed={}, message={!r}".format(n, t, alpha, trials, seed, msg_str))
    print("Group: Ristretto255 (pure Python), Hash: SHA-512")
    print("Note: if --seed is set, RNG is deterministic for reproducibility (NOT secure).")
    print("")

    # --- Trials ---
    for trial in range(1, trials + 1):
        # Derive a per-trial deterministic seed if requested (reproducible across runs)
        trial_seed = None if seed is None else (int(seed) + int(trial))
        rng = ExperimentRNG(seed=trial_seed)

        # End-to-end trial timing (excluding setup)
        t_total_start = time.perf_counter()

        # --- KeyGen ---
        t_keygen_start = time.perf_counter()
        ctx_phi = "FROST demo context (Phi)"  # kept as in starting style; also used in signing hashes
        participants, Y = frost_keygen(n=n, t=t, ctx_phi=ctx_phi, rng=rng)
        t_keygen_end = time.perf_counter()
        keygen_ms = ms(t_keygen_end - t_keygen_start)

        # --- Random subset selection (S) ---
        S = choose_signer_subset(n=n, t=t, alpha=alpha, rng=rng)

        # --- Preprocess (per signer) ---
        commitments = {}  # commitments[i] = (D_i, E_i)
        preprocess_pp = {}  # per participant ms
        t_preprocess_start = time.perf_counter()
        for i in S:
            Pi = participants[i]
            t0 = time.perf_counter()
            D_i, E_i = Pi.preprocess_nonces_and_commitments(rng)
            t1 = time.perf_counter()
            commitments[i] = (D_i, E_i)
            preprocess_pp[i] = ms(t1 - t0)
        t_preprocess_end = time.perf_counter()
        preprocess_ms_total = ms(t_preprocess_end - t_preprocess_start)

        # --- Aggregator computations (binding factors, group commitment R, challenge c, lambdas) ---
        agg_ms_total = 0.0
        t_agg_1_start = time.perf_counter()

        rho = compute_binding_factors(ctx_phi, message_bytes, S, commitments)
        R = compute_group_commitment_R(S, commitments, rho)
        c = compute_challenge(ctx_phi, Y, R, message_bytes)

        lambdas = {}
        for i in S:
            lambdas[i] = lagrange_coeff_at_zero(i, S)

        t_agg_1_end = time.perf_counter()
        agg_ms_total += ms(t_agg_1_end - t_agg_1_start)

        # --- Sign (per signer) ---
        z_shares = {}
        sign_pp = {}  # per participant ms
        t_sign_start = time.perf_counter()
        for i in S:
            Pi = participants[i]
            t0 = time.perf_counter()
            z_i = Pi.sign_share(rho_i=rho[i], challenge_c=c, lambda_i=lambdas[i])
            t1 = time.perf_counter()
            z_shares[i] = z_i
            sign_pp[i] = ms(t1 - t0)
        t_sign_end = time.perf_counter()
        sign_ms_total = ms(t_sign_end - t_sign_start)

        # --- Aggregate (combine shares) ---
        t_agg_2_start = time.perf_counter()
        z = aggregate_signature_shares(S, z_shares)
        signature = (R, z)
        t_agg_2_end = time.perf_counter()
        agg_ms_total += ms(t_agg_2_end - t_agg_2_start)

        # --- Verify ---
        t_verify_start = time.perf_counter()
        ok = verify_schnorr_signature(Y, ctx_phi, message_bytes, signature)
        t_verify_end = time.perf_counter()
        verify_ms = ms(t_verify_end - t_verify_start)

        # --- End-to-end trial total ---
        t_total_end = time.perf_counter()
        total_ms = ms(t_total_end - t_total_start)

        # --- Print per trial ---
        print("=== Trial {}/{} ===".format(trial, trials))
        print("Trial seed: {}".format(trial_seed))
        print("Chosen signer subset S (alpha={}): {}".format(alpha, S))
        print("Verification succeeded? {}".format(ok))
        print("")
        print("Runtimes (ms):")
        print("  setup_ms       : {:.3f}".format(setup_ms))
        print("  keygen_ms      : {:.3f}".format(keygen_ms))
        print("  preprocess_ms  : {:.3f}   (per signer: {})".format(
            preprocess_ms_total,
            ", ".join(["P{}={:.3f}".format(i, preprocess_pp[i]) for i in S])
        ))
        print("  sign_ms        : {:.3f}   (per signer: {})".format(
            sign_ms_total,
            ", ".join(["P{}={:.3f}".format(i, sign_pp[i]) for i in S])
        ))
        print("  aggregate_ms   : {:.3f}".format(agg_ms_total))
        print("  verify_ms      : {:.3f}".format(verify_ms))
        print("  total_ms       : {:.3f}".format(total_ms))
        print("")

        # --- Collect stats ---
        stats["setup_ms"].append(setup_ms)
        stats["keygen_ms"].append(keygen_ms)
        stats["preprocess_ms"].append(preprocess_ms_total)
        stats["sign_ms"].append(sign_ms_total)
        stats["aggregate_ms"].append(agg_ms_total)
        stats["verify_ms"].append(verify_ms)
        stats["total_ms"].append(total_ms)

        for i in S:
            stats["preprocess_per_participant_ms"].append(preprocess_pp[i])
            stats["sign_per_participant_ms"].append(sign_pp[i])

    # --- Summary ---
    print("=== Summary (mean / median over {} trials) ===".format(trials))
    rows = [
        ("setup_ms", stats["setup_ms"]),
        ("keygen_ms", stats["keygen_ms"]),
        ("preprocess_ms", stats["preprocess_ms"]),
        ("sign_ms", stats["sign_ms"]),
        ("aggregate_ms", stats["aggregate_ms"]),
        ("verify_ms", stats["verify_ms"]),
        ("total_ms", stats["total_ms"]),
        ("preprocess_per_participant_ms", stats["preprocess_per_participant_ms"]),
        ("sign_per_participant_ms", stats["sign_per_participant_ms"]),
    ]
    for name, vals in rows:
        mu, med = mean_median(vals)
        print("  {:28s}  mean={:10.3f}   median={:10.3f}".format(name, mu, med))

    # --- Average-only summary explicitly for 10 trials ---
    if trials == 10:
        print("=== Averages over 10 trials ===")
        avg_rows = [
            ("setup_ms", stats["setup_ms"]),
            ("keygen_ms", stats["keygen_ms"]),
            ("preprocess_ms", stats["preprocess_ms"]),
            ("sign_ms", stats["sign_ms"]),
            ("aggregate_ms", stats["aggregate_ms"]),
            ("verify_ms", stats["verify_ms"]),
            ("total_ms", stats["total_ms"]),
            ("preprocess_per_participant_ms", stats["preprocess_per_participant_ms"]),
            ("sign_per_participant_ms", stats["sign_per_participant_ms"]),
        ]
        for name, vals in avg_rows:
            avg = float(statistics.mean(vals)) if vals else 0.0
            print("  {:28s}  {:10.3f}".format(name, avg))


if __name__ == "__main__":
    main()
