#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Educational FROST KeyGen + Signing Experiments (secp256k1 + SHA-256), Python 3.6.2 compatible.

This script implements an educational FROST-style flow over secp256k1:
  1) Random signer-subset selection for threshold signing (size alpha, t <= alpha <= n),
  2) A simplified, educational Schnorr-style threshold signing flow:
       - Preprocess: each signer generates nonces + commitments,
       - Sign: each signer produces a signature share using Lagrange coefficient for chosen subset,
       - Aggregate: aggregator computes binding factors, group commitment, challenge, and combines shares,
       - Verify: verify final Schnorr signature against group public key,
  3) Runtime instrumentation with time.perf_counter() (ms), per-trial and summary mean/median.

Dependencies (NEW for this refactor):
  pip install ecdsa

Notes for Python 3.6.2:
- If your pip cannot install the latest ecdsa due to Python version constraints, pip will typically select
  the newest compatible release automatically. If needed, pin an older version that still supports 3.6.

WARNING: Educational only (NOT production-grade):
- Deterministic RNG mode (when --seed is used) is NOT cryptographically secure.
- No authenticated network; broadcast/p2p are simulated with Python dicts.
- Simplified hash-to-scalar (not a ciphersuite-defined hash-to-field).
- No robust complaint/blame; failures raise.
- No side-channel protections.
"""

from __future__ import print_function

import argparse
import hashlib
import random
import secrets
import statistics
import time

try:
    from ecdsa.curves import SECP256k1
    from ecdsa.ellipticcurve import Point, INFINITY
except Exception:
    raise RuntimeError("The 'ecdsa' library is required. Install with: pip install ecdsa")


# =============================================================================
# secp256k1 scalar/point utilities (educational)
# =============================================================================

# Scalars are mod the curve subgroup order n (NOT the field prime p).
N = int(SECP256k1.order)  # group order
SCALAR_BYTES = 32

# We use compressed SEC1 point encoding (33 bytes).
POINT_BYTES = 33

# Internal identity representation: point-at-infinity object from ecdsa.
SECP256K1_IDENTITY = INFINITY

# Curve parameters for decompression / on-curve checks
_curve_fp = SECP256k1.curve
_p = int(_curve_fp.p())
_a = int(_curve_fp.a())  # should be 0
_b = int(_curve_fp.b())  # should be 7

# Use an affine generator Point for consistent internal point type.
_G_any = SECP256k1.generator
if hasattr(_G_any, "to_affine"):
    _G = _G_any.to_affine()
else:
    _G = _G_any  # already affine in some versions


# Domain separation tags (SHA-256 everywhere)
DST_KEYGEN_POK = b"FROST_KEYGEN_POK_SHA256"
DST_SIGN_RHO = b"FROST_SIGN_RHO_SHA256"
DST_SIGN_CHALLENGE = b"FROST_SIGN_CHALLENGE_SHA256"


def int_to_bytes_be(x, length):
    return int(x).to_bytes(length, "big")


def scalar_reduce(x):
    return int(x) % N


def scalar_add(a, b):
    return (int(a) + int(b)) % N


def scalar_sub(a, b):
    return (int(a) - int(b)) % N


def scalar_mul(a, b):
    return (int(a) * int(b)) % N


def scalar_inv(a):
    a = int(a) % N
    if a == 0:
        raise ZeroDivisionError("No inverse for 0 mod N")
    # N is prime for secp256k1's subgroup order, so a^(N-2) mod N is the inverse.
    return pow(a, N - 2, N)


def scalar_to_bytes_be(a):
    return (int(a) % N).to_bytes(SCALAR_BYTES, "big")


def scalar_from_bytes_be(b):
    if len(b) != SCALAR_BYTES:
        raise ValueError("Scalar bytes must be 32 bytes")
    return int.from_bytes(b, "big") % N


def _point_xy_affine(P):
    """
    Return (x, y) as Python ints for an affine point; return (None, None) for INFINITY.
    Handles both ecdsa Point and PointJacobi by converting to affine if needed.
    """
    if P is SECP256K1_IDENTITY:
        return None, None
    if hasattr(P, "to_affine"):
        P = P.to_affine()
    # ecdsa Point uses methods x(), y() in many versions; handle both method/property.
    x = P.x() if callable(getattr(P, "x", None)) else P.x
    y = P.y() if callable(getattr(P, "y", None)) else P.y
    return int(x), int(y)


def _is_on_curve_xy(x, y):
    # secp256k1: y^2 = x^3 + 7 over F_p
    if x is None or y is None:
        return False
    if not (0 <= x < _p and 0 <= y < _p):
        return False
    left = (y * y) % _p
    right = (pow(x, 3, _p) + _a * x + _b) % _p
    return left == right


def _sqrt_mod_p_secp256k1(y2):
    """
    Square root mod p for secp256k1 prime field.
    p % 4 == 3, so sqrt can be computed as y = y2^((p+1)//4) mod p.
    Returns y, or None if no square root exists.
    """
    y = pow(int(y2) % _p, (_p + 1) // 4, _p)
    if (y * y) % _p != (int(y2) % _p):
        return None
    return y


def point_is_valid(P_bytes):
    """
    Validate compressed SEC1 encoding (33 bytes) and on-curve check.
    Reject any "infinity/sentinel" encoding.
    """
    if not isinstance(P_bytes, (bytes, bytearray)) or len(P_bytes) != POINT_BYTES:
        return False
    P_bytes = bytes(P_bytes)

    # Reject sentinel used only for transcript encoding of INFINITY.
    if P_bytes == (b"\x00" * POINT_BYTES):
        return False

    prefix = P_bytes[0]
    if prefix not in (2, 3):
        return False

    x = int.from_bytes(P_bytes[1:], "big")
    if not (0 <= x < _p):
        return False

    y2 = (pow(x, 3, _p) + _a * x + _b) % _p
    y = _sqrt_mod_p_secp256k1(y2)
    if y is None:
        return False

    # Choose y with correct parity: prefix 0x02 => even y, 0x03 => odd y
    if (y & 1) != (prefix & 1):
        y = (-y) % _p

    return _is_on_curve_xy(x, y)


def point_from_bytes(P_bytes):
    """
    Decode compressed SEC1 point encoding into an affine Point.
    """
    P_bytes = bytes(P_bytes)
    if len(P_bytes) != POINT_BYTES:
        raise ValueError("Point bytes must be {} bytes".format(POINT_BYTES))
    if not point_is_valid(P_bytes):
        raise ValueError("Invalid secp256k1 point encoding")

    prefix = P_bytes[0]
    x = int.from_bytes(P_bytes[1:], "big")
    y2 = (pow(x, 3, _p) + _a * x + _b) % _p
    y = _sqrt_mod_p_secp256k1(y2)
    if y is None:
        raise ValueError("Invalid point: no square root for y^2")
    if (y & 1) != (prefix & 1):
        y = (-y) % _p

    if not _is_on_curve_xy(x, y):
        raise ValueError("Decoded point is not on curve")

    return Point(_curve_fp, x, y, N)


def point_to_bytes(P):
    """
    Encode a point to compressed SEC1 (33 bytes).
    For the internal identity (INFINITY), return a deterministic sentinel of 33 zero-bytes
    for transcript hashing only (this is NOT a valid SEC1 point encoding and is rejected by point_is_valid()).
    """
    if P is SECP256K1_IDENTITY:
        return b"\x00" * POINT_BYTES

    x, y = _point_xy_affine(P)
    if x is None or y is None:
        return b"\x00" * POINT_BYTES

    prefix = 2 if (y % 2 == 0) else 3
    return bytes([prefix]) + int_to_bytes_be(x, 32)


def point_eq(P, Q):
    if P is SECP256K1_IDENTITY and Q is SECP256K1_IDENTITY:
        return True
    if (P is SECP256K1_IDENTITY) != (Q is SECP256K1_IDENTITY):
        return False
    x1, y1 = _point_xy_affine(P)
    x2, y2 = _point_xy_affine(Q)
    return (x1 == x2) and (y1 == y2)


def point_add(P, Q):
    if P is SECP256K1_IDENTITY:
        return Q
    if Q is SECP256K1_IDENTITY:
        return P
    if hasattr(P, "to_affine"):
        P = P.to_affine()
    if hasattr(Q, "to_affine"):
        Q = Q.to_affine()
    return P + Q


def point_sub(P, Q):
    return point_add(P, point_mul(Q, N - 1))


def point_mul(P, k):
    k = int(k) % N
    if k == 0 or P is SECP256K1_IDENTITY:
        return SECP256K1_IDENTITY
    if hasattr(P, "to_affine"):
        P = P.to_affine()
    return P * k


def point_mul_base(k):
    k = int(k) % N
    if k == 0:
        return SECP256K1_IDENTITY
    return _G * k


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
    return rng.randbelow(N - 1) + 1


# =============================================================================
# SHA-256 hash-to-scalar (non-zero) in Z_N
# =============================================================================

def hash_to_scalar_nonzero_sha256(domain, *parts):
    """
    c = SHA256(domain || 0x00 || ctr || (len||part)... ) mod N
    retry if c == 0
    """
    ctr = 0
    while True:
        h = hashlib.sha256()
        h.update(domain)
        h.update(b"\x00")
        h.update(int_to_bytes_be(ctr, 4))
        for p in parts:
            if not isinstance(p, (bytes, bytearray)):
                raise TypeError("hash parts must be bytes")
            h.update(int_to_bytes_be(len(p), 4))
            h.update(bytes(p))
        c = int.from_bytes(h.digest(), "big") % N
        if c != 0:
            return c
        ctr += 1


# =============================================================================
# Polynomial / Shamir utilities over Z_N
# =============================================================================

def eval_poly(coeffs, x):
    acc = 0
    power = 1
    x = int(x) % N
    for a_j in coeffs:
        acc = (acc + (int(a_j) % N) * power) % N
        power = (power * x) % N
    return acc


def lagrange_coeff_at_zero(i, S):
    num = 1
    den = 1
    i = int(i) % N
    for j in S:
        j = int(j) % N
        if j == i:
            continue
        num = (num * (-j % N)) % N
        den = (den * ((i - j) % N)) % N
    return (num * scalar_inv(den)) % N


def shamir_reconstruct_secret_at_zero(shares):
    S = list(shares.keys())
    secret = 0
    for i, si in shares.items():
        lam = lagrange_coeff_at_zero(i, S)
        secret = (secret + lam * (int(si) % N)) % N
    return secret


# =============================================================================
# KeyGen message types (simple Python 3.6.2 classes)
# =============================================================================

class SchnorrPoK(object):
    def __init__(self, R, mu):
        self.R = R
        self.mu = int(mu) % N


class KeyGenBroadcast(object):
    def __init__(self, dealer_id, C_tilde, sigma):
        self.dealer_id = int(dealer_id)
        self.C_tilde = list(C_tilde)
        self.sigma = sigma


# =============================================================================
# Feldman share verification over secp256k1 points (KeyGen Round 2 Step 2)
# =============================================================================

def feldman_verify_share_point(C_tilde_dealer, receiver_id, share_value):
    receiver_id = int(receiver_id)
    share_value = int(share_value) % N

    left = point_mul_base(share_value)

    rhs = SECP256K1_IDENTITY
    power = 1
    for phi_k in C_tilde_dealer:
        term = point_mul(phi_k, power)
        rhs = point_add(rhs, term)
        power = (power * receiver_id) % N

    return point_eq(left, rhs)


# =============================================================================
# Participant: KeyGen + (Educational) Signing state
# =============================================================================

class Participant(object):
    def __init__(self, i, n, t, ctx_phi):
        self.i = int(i)
        self.n = int(n)
        self.t = int(t)
        self.ctx_phi = str(ctx_phi)

        self.a = None
        self.C_tilde = None
        self.sigma = None

        self._self_share_from_own_poly = None

        self.s_i = None
        self.Y_i = None

        self._nonce_d = None
        self._nonce_e = None
        self.D_i = None
        self.E_i = None

    def round1_sample_poly_and_commit(self, rng):
        self.a = [rand_scalar_nonzero(rng) for _ in range(self.t)]
        self.C_tilde = [point_mul_base(aij) for aij in self.a]

    def round1_generate_pok_of_a_i0(self, rng):
        if self.a is None or self.C_tilde is None:
            raise RuntimeError("Must run round1_sample_poly_and_commit() first.")

        a_i0 = self.a[0]
        phi_i0 = self.C_tilde[0]

        k = rand_scalar_nonzero(rng)
        R = point_mul_base(k)

        c = hash_to_scalar_nonzero_sha256(
            DST_KEYGEN_POK,
            int_to_bytes_be(self.i, 4),
            self.ctx_phi.encode("utf-8"),
            point_to_bytes(phi_i0),
            point_to_bytes(R),
        )

        mu = scalar_add(k, scalar_mul(a_i0, c))
        self.sigma = SchnorrPoK(R=R, mu=mu)

    def round1_broadcast(self):
        if self.C_tilde is None or self.sigma is None:
            raise RuntimeError("Round 1 not complete.")
        return KeyGenBroadcast(dealer_id=self.i, C_tilde=self.C_tilde, sigma=self.sigma)

    def round1_verify_others_pok(self, broadcasts):
        for dealer_id, msg in broadcasts.items():
            if int(dealer_id) == self.i:
                continue

            R = msg.sigma.R
            mu = msg.sigma.mu
            phi_l0 = msg.C_tilde[0]

            c = hash_to_scalar_nonzero_sha256(
                DST_KEYGEN_POK,
                int_to_bytes_be(int(dealer_id), 4),
                self.ctx_phi.encode("utf-8"),
                point_to_bytes(phi_l0),
                point_to_bytes(R),
            )

            g_mu = point_mul_base(mu)
            cphi = point_mul(phi_l0, c)
            right = point_sub(g_mu, cphi)

            if not point_eq(R, right):
                raise RuntimeError("PoK verification failed at P{} for dealer P{}".format(self.i, dealer_id))

    def round2_send_shares(self):
        if self.a is None:
            raise RuntimeError("Round 1 polynomial not generated.")
        shares = {}
        for l_id in range(1, self.n + 1):
            shares[l_id] = eval_poly(self.a, l_id)

        self._self_share_from_own_poly = shares[self.i]
        self.a = None
        return shares

    def round2_receive_verify_and_finalize(self, broadcasts, shares_from_all_dealers):
        if self._self_share_from_own_poly is None:
            raise RuntimeError("Must run round2_send_shares() first.")

        for dealer_id in range(1, self.n + 1):
            C_tilde_dealer = broadcasts[dealer_id].C_tilde
            share_value = shares_from_all_dealers[dealer_id]
            if not feldman_verify_share_point(C_tilde_dealer, self.i, share_value):
                raise RuntimeError("Share verification failed at P{} for dealer P{}".format(self.i, dealer_id))

        s_i = 0
        for dealer_id in range(1, self.n + 1):
            s_i = scalar_add(s_i, shares_from_all_dealers[dealer_id])

        self.s_i = s_i
        self.Y_i = point_mul_base(self.s_i)

    def preprocess_nonces_and_commitments(self, rng):
        self._nonce_d = rand_scalar_nonzero(rng)
        self._nonce_e = rand_scalar_nonzero(rng)
        self.D_i = point_mul_base(self._nonce_d)
        self.E_i = point_mul_base(self._nonce_e)
        return self.D_i, self.E_i

    def sign_share(self, rho_i, challenge_c, lambda_i):
        if self._nonce_d is None or self._nonce_e is None or self.s_i is None:
            raise RuntimeError("Missing nonces or secret share; run preprocess and KeyGen first.")

        z_i = self._nonce_d
        z_i = scalar_add(z_i, scalar_mul(rho_i, self._nonce_e))
        z_i = scalar_add(z_i, scalar_mul(lambda_i, scalar_mul(self.s_i, challenge_c)))

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

    broadcasts = {}
    for i, Pi in participants.items():
        Pi.round1_sample_poly_and_commit(rng)
        Pi.round1_generate_pok_of_a_i0(rng)
        broadcasts[i] = Pi.round1_broadcast()

    for i, Pi in participants.items():
        Pi.round1_verify_others_pok(broadcasts)

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

    Y = SECP256K1_IDENTITY
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
    out = b""
    for i in sorted(S):
        D_i, E_i = commitments[i]
        out += int_to_bytes_be(i, 4) + point_to_bytes(D_i) + point_to_bytes(E_i)
    return out


def compute_binding_factors(ctx_phi, message_bytes, S, commitments):
    transcript = encode_commitment_list(S, commitments)
    rho = {}
    for i in S:
        rho[i] = hash_to_scalar_nonzero_sha256(
            DST_SIGN_RHO,
            int_to_bytes_be(i, 4),
            ctx_phi.encode("utf-8"),
            message_bytes,
            transcript,
        )
    return rho


def compute_group_commitment_R(S, commitments, rho):
    R = SECP256K1_IDENTITY
    for i in S:
        D_i, E_i = commitments[i]
        R_i = point_add(D_i, point_mul(E_i, rho[i]))
        R = point_add(R, R_i)
    return R


def compute_challenge(ctx_phi, Y, R, message_bytes):
    return hash_to_scalar_nonzero_sha256(
        DST_SIGN_CHALLENGE,
        ctx_phi.encode("utf-8"),
        point_to_bytes(Y),
        point_to_bytes(R),
        message_bytes,
    )


def aggregate_signature_shares(S, z_shares):
    z = 0
    for i in S:
        z = scalar_add(z, z_shares[i])
    return z


def verify_schnorr_signature(Y, ctx_phi, message_bytes, signature):
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


def mean_only(values):
    if not values:
        return 0.0
    return float(statistics.mean(values))


# =============================================================================
# Main (CLI + trials)
# =============================================================================

def parse_args():
    p = argparse.ArgumentParser(description="Educational FROST KeyGen + signing experiments (secp256k1 + SHA-256).")
    p.add_argument("--n", type=int, default=10, help="Number of participants (n). Default: 10.")
    p.add_argument("--t", type=int, default=5, help="Threshold (t). Default: 5.")
    p.add_argument("--alpha", type=int, default=None, help="Signer subset size (alpha), t <= alpha <= n. Default: alpha=t.")
    # CHANGED: default trials -> 10
    p.add_argument("--trials", type=int, default=10, help="Number of trials (default 10).")
    p.add_argument("--seed", type=int, default=None, help="Seed for reproducible randomness (NOT secure).")
    p.add_argument("--message", type=str, default="test", help="Message to sign (default 'test').")
    return p.parse_args()


def main():
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

    t_setup_end = time.perf_counter()
    setup_ms = ms(t_setup_end - t_setup_start)

    stats = {
        "setup_ms": [],
        "keygen_ms": [],
        "preprocess_ms": [],
        "sign_ms": [],
        "aggregate_ms": [],
        "verify_ms": [],
        "total_ms": [],
        "preprocess_per_participant_ms": [],
        "sign_per_participant_ms": [],
    }

    print("=== Configuration ===")
    print("n={}, t={}, alpha={}, trials={}, seed={}, message={!r}".format(n, t, alpha, trials, seed, msg_str))
    print("Note: if --seed is set, RNG is deterministic for reproducibility (NOT secure).")
    print("")

    for trial in range(1, trials + 1):
        trial_seed = None if seed is None else (int(seed) + int(trial))
        rng = ExperimentRNG(seed=trial_seed)

        t_total_start = time.perf_counter()

        t_keygen_start = time.perf_counter()
        ctx_phi = "FROST demo context (Phi)"
        participants, Y = frost_keygen(n=n, t=t, ctx_phi=ctx_phi, rng=rng)
        t_keygen_end = time.perf_counter()
        keygen_ms = ms(t_keygen_end - t_keygen_start)

        S = choose_signer_subset(n=n, t=t, alpha=alpha, rng=rng)

        commitments = {}
        preprocess_pp = {}
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

        z_shares = {}
        sign_pp = {}
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

        t_agg_2_start = time.perf_counter()
        z = aggregate_signature_shares(S, z_shares)
        signature = (R, z)
        t_agg_2_end = time.perf_counter()
        agg_ms_total += ms(t_agg_2_end - t_agg_2_start)

        t_verify_start = time.perf_counter()
        ok = verify_schnorr_signature(Y, ctx_phi, message_bytes, signature)
        t_verify_end = time.perf_counter()
        verify_ms = ms(t_verify_end - t_verify_start)

        t_total_end = time.perf_counter()
        total_ms = ms(t_total_end - t_total_start)

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

    # CHANGED: average-only summary block explicitly for 10 runs (computed from existing stats arrays)
    if trials == 10:
        print("=== Averages over 10 trials ===")
        print("  setup_ms                      : {:10.3f}".format(mean_only(stats["setup_ms"])))
        print("  keygen_ms                     : {:10.3f}".format(mean_only(stats["keygen_ms"])))
        print("  preprocess_ms                 : {:10.3f}".format(mean_only(stats["preprocess_ms"])))
        print("  sign_ms                       : {:10.3f}".format(mean_only(stats["sign_ms"])))
        print("  aggregate_ms                  : {:10.3f}".format(mean_only(stats["aggregate_ms"])))
        print("  verify_ms                     : {:10.3f}".format(mean_only(stats["verify_ms"])))
        print("  total_ms                      : {:10.3f}".format(mean_only(stats["total_ms"])))
        print("  preprocess_per_participant_ms : {:10.3f}".format(mean_only(stats["preprocess_per_participant_ms"])))
        print("  sign_per_participant_ms       : {:10.3f}".format(mean_only(stats["sign_per_participant_ms"])))

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


if __name__ == "__main__":
    main()
