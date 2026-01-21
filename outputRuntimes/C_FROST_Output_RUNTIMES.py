#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Educational FROST KeyGen + Signing Experiments (NIST P-256 + SHA-256), Python 3.6.2 compatible.

This is a refactor of the authoritative Ed25519+SHA-512 script to:
  - Use NIST P-256 (short Weierstrass curve) for ALL group operations, and
  - Use SHA-256 for ALL protocol hashing (PoK challenge, binding factors, Schnorr challenge).

Curve: secp256r1 / NIST P-256
  y^2 = x^3 + a*x + b  over F_p
  subgroup order is prime (N), cofactor h=1.

Point encoding for hashing transcripts:
  SEC1 uncompressed encoding:
    0x04 || x(32B big-endian) || y(32B big-endian)

WARNING: Educational only (NOT production-grade):
  - Pure-Python EC arithmetic is NOT constant-time and not hardened.
  - Deterministic RNG mode (when --seed is used) is NOT cryptographically secure.
  - No authenticated network; broadcast/p2p are simulated with Python dicts.
  - Simplified hash-to-scalar (not a ciphersuite-defined hash-to-field).
  - No robust complaint/blame; failures raise.
"""

from __future__ import print_function

import argparse
import hashlib
import os
import random
import secrets
import statistics
import time


# =============================================================================
# NIST P-256 parameters and field/scalar utilities (educational)
# =============================================================================

# Field prime p
P = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

# Curve parameters: y^2 = x^3 + a*x + b over F_p
# For P-256: a = -3 mod p
A = (P - 3) % P
B = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

# Base point G (generator) and subgroup order N
Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
G = (Gx, Gy)

# Subgroup order (prime), cofactor h=1
N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

SCALAR_BYTES = 32
POINT_BYTES = 65  # SEC1 uncompressed point length for non-infinity points

# Identity element (point at infinity) represented as None
P256_IDENTITY = None

# Domain separation tags (SHA-256 everywhere)
DST_KEYGEN_POK = b"FROST_KEYGEN_POK_SHA256"
DST_SIGN_RHO = b"FROST_SIGN_RHO_SHA256"
DST_SIGN_CHALLENGE = b"FROST_SIGN_CHALLENGE_SHA256"


def int_to_bytes_be(x, length):
    return int(x).to_bytes(length, "big")


def fe(x):
    return int(x) % P


def fe_add(x, y):
    return (int(x) + int(y)) % P


def fe_sub(x, y):
    return (int(x) - int(y)) % P


def fe_mul(x, y):
    return (int(x) * int(y)) % P


def fe_inv(x):
    x = int(x) % P
    if x == 0:
        raise ZeroDivisionError("No inverse for 0 mod p")
    return pow(x, P - 2, P)


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
    # N is prime for P-256
    return pow(a, N - 2, N)


def scalar_to_bytes_be(a):
    return (int(a) % N).to_bytes(SCALAR_BYTES, "big")


def scalar_from_bytes_be(b):
    if len(b) != SCALAR_BYTES:
        raise ValueError("Scalar bytes must be 32 bytes")
    return int.from_bytes(b, "big") % N


# =============================================================================
# P-256 point operations (educational, pure Python; NOT constant-time)
# =============================================================================

def point_is_infinity(Pt):
    return Pt is None


def point_is_valid(Pt):
    if Pt is None:
        return True
    if (not isinstance(Pt, tuple)) or len(Pt) != 2:
        return False
    x, y = Pt
    if not (0 <= int(x) < P and 0 <= int(y) < P):
        return False
    left = fe_mul(y, y)
    right = fe_add(fe_add(fe_mul(fe_mul(x, x), x), fe_mul(A, x)), B)
    return left == right


def point_eq(P, Q):
    return P == Q


def point_neg(Pt):
    if Pt is None:
        return None
    x, y = Pt
    return (int(x) % P, (-int(y)) % P)


def point_sub(P, Q):
    return point_add(P, point_neg(Q))


def _affine_to_jacobian(Pt):
    if Pt is None:
        return (1, 1, 0)  # Z=0 indicates infinity
    x, y = Pt
    return (int(x) % P, int(y) % P, 1)


def _jacobian_to_affine(X, Y, Z):
    if Z == 0:
        return None
    Zinv = fe_inv(Z)
    Zinv2 = fe_mul(Zinv, Zinv)
    x = fe_mul(X, Zinv2)
    y = fe_mul(Y, fe_mul(Zinv2, Zinv))
    return (x, y)


def _jacobian_double(X1, Y1, Z1):
    if Z1 == 0 or Y1 == 0:
        return (1, 1, 0)

    Y1_sq = fe_mul(Y1, Y1)
    S = fe_mul(4, fe_mul(X1, Y1_sq))

    Z1_sq = fe_mul(Z1, Z1)
    M = fe_mul(3, fe_mul(fe_sub(X1, Z1_sq), fe_add(X1, Z1_sq)))

    X3 = fe_sub(fe_mul(M, M), fe_mul(2, S))

    Y1_4 = fe_mul(Y1_sq, Y1_sq)
    Y3 = fe_sub(fe_mul(M, fe_sub(S, X3)), fe_mul(8, Y1_4))

    Z3 = fe_mul(2, fe_mul(Y1, Z1))

    return (X3, Y3, Z3)


def _jacobian_add(X1, Y1, Z1, X2, Y2, Z2):
    if Z1 == 0:
        return (X2, Y2, Z2)
    if Z2 == 0:
        return (X1, Y1, Z1)

    Z1Z1 = fe_mul(Z1, Z1)
    Z2Z2 = fe_mul(Z2, Z2)

    U1 = fe_mul(X1, Z2Z2)
    U2 = fe_mul(X2, Z1Z1)

    Z1_cub = fe_mul(Z1Z1, Z1)
    Z2_cub = fe_mul(Z2Z2, Z2)

    S1 = fe_mul(Y1, Z2_cub)
    S2 = fe_mul(Y2, Z1_cub)

    H = fe_sub(U2, U1)
    r = fe_sub(S2, S1)

    if H == 0:
        if r == 0:
            return _jacobian_double(X1, Y1, Z1)
        return (1, 1, 0)

    HH = fe_mul(H, H)
    HHH = fe_mul(H, HH)
    V = fe_mul(U1, HH)

    X3 = fe_sub(fe_sub(fe_mul(r, r), HHH), fe_mul(2, V))
    Y3 = fe_sub(fe_mul(r, fe_sub(V, X3)), fe_mul(S1, HHH))
    Z3 = fe_mul(H, fe_mul(Z1, Z2))

    return (X3, Y3, Z3)


def point_add(P1, P2):
    X1, Y1, Z1 = _affine_to_jacobian(P1)
    X2, Y2, Z2 = _affine_to_jacobian(P2)
    X3, Y3, Z3 = _jacobian_add(X1, Y1, Z1, X2, Y2, Z2)
    return _jacobian_to_affine(X3, Y3, Z3)


def point_mul(Pt, k):
    k = int(k) % N
    if k == 0 or Pt is None:
        return None

    X, Y, Z = _affine_to_jacobian(Pt)
    Qx, Qy, Qz = (1, 1, 0)

    while k > 0:
        if k & 1:
            Qx, Qy, Qz = _jacobian_add(Qx, Qy, Qz, X, Y, Z)
        X, Y, Z = _jacobian_double(X, Y, Z)
        k >>= 1

    return _jacobian_to_affine(Qx, Qy, Qz)


def point_mul_base(k):
    return point_mul(G, k)


def point_to_bytes(Pt):
    if Pt is None:
        return b"\x00"
    x, y = Pt
    return b"\x04" + int_to_bytes_be(x, 32) + int_to_bytes_be(y, 32)


def point_from_bytes(b):
    if not isinstance(b, (bytes, bytearray)):
        raise ValueError("Point encoding must be bytes")
    b = bytes(b)
    if b == b"\x00":
        return None
    if len(b) != 65 or b[0:1] != b"\x04":
        raise ValueError("Invalid SEC1 uncompressed encoding")
    x = int.from_bytes(b[1:33], "big")
    y = int.from_bytes(b[33:65], "big")
    Pt = (x, y)
    if not point_is_valid(Pt):
        raise ValueError("Invalid point (not on curve)")
    return Pt


if not point_is_valid(G):
    raise RuntimeError("Generator G is not on the curve; check P-256 parameters.")
if point_mul_base(N) is not None:
    raise RuntimeError("Subgroup order check failed: [N]G != infinity (scalar mul / params bug).")


# =============================================================================
# Deterministic RNG wrapper (for reproducible experiments; NOT secure)
# =============================================================================

class ExperimentRNG(object):
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
# Feldman share verification over EC points (KeyGen Round 2 Step 2)
# =============================================================================

def feldman_verify_share_point(C_tilde_dealer, receiver_id, share_value):
    receiver_id = int(receiver_id)
    share_value = int(share_value) % N

    left = point_mul_base(share_value)

    rhs = P256_IDENTITY
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

    Y = P256_IDENTITY
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
    R = P256_IDENTITY
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


def _fmt3(x):
    return "{:.3f}".format(float(x))


def _tsv_sanitize(s):
    if s is None:
        return ""
    s = str(s)
    s = s.replace("\t", " ")
    s = s.replace("\r", " ")
    s = s.replace("\n", " ")
    return s


# =============================================================================
# Main (CLI + trials)
# =============================================================================

def parse_args():
    p = argparse.ArgumentParser(description="Educational FROST KeyGen + signing experiments (P-256 + SHA-256).")
    p.add_argument("--n", type=int, default=10, help="Number of participants (n). Default: 10.")
    p.add_argument("--t", type=int, default=5, help="Threshold (t). Default: 5.")
    p.add_argument("--alpha", type=int, default=None,
                   help="Signer subset size (alpha), t <= alpha <= n. Default: alpha=t.")
    # CHANGED: default trials -> 10
    p.add_argument("--trials", type=int, default=10, help="Number of trials (default 10).")
    p.add_argument("--seed", type=int, default=None, help="Seed for reproducible randomness (NOT secure).")
    p.add_argument("--message", type=str, default="test", help="Message to sign (default 'test').")

    # NEW: per-trial runtime TSV output
    p.add_argument("--out", type=str, default="runtimes.tsv",
                   help="TSV output path for per-trial runtimes (default: runtimes.tsv).")
    p.add_argument("--append", action="store_true",
                   help="Append to --out instead of overwriting. If the file does not exist, a header is written.")
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

    out_path = args.out
    append = bool(args.append)

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
    print("Curve: NIST P-256, Hash: SHA-256")
    print("Note: if --seed is set, RNG is deterministic for reproducibility (NOT secure).")
    print("")

    # --- TSV output setup (overwrite by default) ---
    write_header = (not append)
    if append:
        if not os.path.exists(out_path):
            write_header = True
        else:
            try:
                write_header = (os.path.getsize(out_path) == 0)
            except OSError:
                write_header = True

    mode = "a" if append else "w"

    header_cols = [
        "trial",
        "trial_seed",
        "n",
        "t",
        "alpha",
        "message",
        "ok",
        "setup_ms",
        "keygen_ms",
        "preprocess_ms",
        "sign_ms",
        "aggregate_ms",
        "verify_ms",
        "total_ms",
        "preprocess_per_participant_ms_mean",
        "sign_per_participant_ms_mean",
    ]

    with open(out_path, mode, newline="") as f_out:
        if write_header:
            f_out.write("\t".join(header_cols) + "\n")

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

            # Per-trial means over this trial's signer subset S (NOT flattened across trials)
            preprocess_pp_mean = mean_only(list(preprocess_pp.values()))
            sign_pp_mean = mean_only(list(sign_pp.values()))

            # Write ONE TSV row per trial (Excel-friendly)
            row = [
                str(trial),
                "" if trial_seed is None else str(trial_seed),
                str(n),
                str(t),
                str(alpha),
                _tsv_sanitize(msg_str),
                str(bool(ok)),
                _fmt3(setup_ms),
                _fmt3(keygen_ms),
                _fmt3(preprocess_ms_total),
                _fmt3(sign_ms_total),
                _fmt3(agg_ms_total),
                _fmt3(verify_ms),
                _fmt3(total_ms),
                _fmt3(preprocess_pp_mean),
                _fmt3(sign_pp_mean),
            ]
            f_out.write("\t".join(row) + "\n")

            # Existing console output (UNCHANGED)
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

    # CHANGED: average-only summary block explicitly for 10 runs
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
