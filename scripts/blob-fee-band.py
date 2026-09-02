#!/usr/bin/env python3
"""Reproduce the MM-15 numbers (docs/mismatches.md).

Both specifications compute the same recurrence for the blob base fee:

    acc = factor * den, out = 0, i = 1
    while acc > 0:  out += acc;  acc = acc * num // (den * i);  i += 1
    price = out // den

with factor = BLOB_MIN_GASPRICE = 1 and num = excess_blob_gas. The
extraction (`fake_exponential_word`) additionally fatal-errors as soon as
the accumulator or the running sum reaches `scaled_limit = den * 2**256`;
SpecRef (`taylor_exponential`) has no such guard and pushes the result
unreduced.

This script finds where those two behaviours part, and compares that
point to the ceiling the extraction's own profile admits.
"""

DEN = 11684671        # bpo2_blob_fee_update_fraction == BLOB_BASE_FEE_UPDATE_FRACTION
TARGET, MAXIMUM = 14, 21   # bpo2 blob counts
GAS_PER_BLOB = 2 ** 17
SCALED_LIMIT = DEN * 2 ** 256
EXCESS_LIMIT = 256 * DEN + (MAXIMUM - TARGET) * GAS_PER_BLOB


def extraction(num):
    """(status, iterations, sum) — status 'ok' or which guard tripped."""
    acc, out, i, steps = DEN, 0, 1, 0
    while acc > 0:
        if acc >= SCALED_LIMIT:
            return "fatal (accumulator)", steps, out
        if out + acc >= SCALED_LIMIT:
            return "fatal (running sum)", steps, out
        out, acc, i, steps = out + acc, acc * num // (DEN * i), i + 1, steps + 1
    return "ok", steps, out


def specref(num):
    """(price, iterations, fuel, terminated) — no overflow guard."""
    fuel = 4 * (num // DEN) + (DEN + 2).bit_length() - 1 + 8
    acc, out, i, steps = DEN, 0, 1, 0
    while acc > 0 and steps < fuel:
        out, acc, i, steps = out + acc, acc * num // (DEN * i), i + 1, steps + 1
    return out // DEN, steps, fuel, acc == 0


def first_divergence():
    lo, hi = 0, EXCESS_LIMIT
    while lo < hi:
        mid = (lo + hi) // 2
        if extraction(mid)[0] == "ok":
            lo = mid + 1
        else:
            hi = mid
    return lo


if __name__ == "__main__":
    thr = first_divergence()
    print(f"denominator                     {DEN}")
    print(f"profile excess_blob_gas_limit   {EXCESS_LIMIT}  (= 256*den + {MAXIMUM-TARGET}*2^17)")
    print(f"first diverging excess_blob_gas {thr}  (= {thr/DEN:.4f} * den)")
    print(f"divergent band width            {EXCESS_LIMIT - thr}")
    print(f"blocks to reach it from zero    {thr / ((MAXIMUM - TARGET) * GAS_PER_BLOB):.0f}")
    for num, label in ((thr - 1, "below"), (thr, "threshold"), (EXCESS_LIMIT, "limit")):
        status, steps, _ = extraction(num)
        price, sspeps, fuel, done = specref(num)
        print(f"\nexcess = {num} ({label})")
        print(f"  Evm      : {status} after {steps} iterations")
        print(f"  SpecRef  : price of {price.bit_length()} bits after {sspeps} "
              f"iterations (fuel {fuel}, terminated: {done})")
