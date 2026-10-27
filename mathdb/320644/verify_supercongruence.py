"""Exact, low-memory checks accompanying the proof of MathDB #320644.

This is a regression/certificate script, not a substitute for the proof.
It uses only Python integer arithmetic and retains no large tables.
"""

from __future__ import annotations


def primes_up_to(limit: int) -> list[int]:
    out: list[int] = []
    for value in range(2, limit + 1):
        if all(value % q for q in out if q * q <= value):
            out.append(value)
    return out


def prime_divisors(value: int) -> list[int]:
    divisors: list[int] = []
    trial = 2
    while trial * trial <= value:
        if value % trial == 0:
            divisors.append(trial)
            while value % trial == 0:
                value //= trial
        trial += 1
    if value > 1:
        divisors.append(value)
    return divisors


def power_sum_mod(n: int, length: int, modulus: int) -> int:
    return sum(pow(j, n, modulus) for j in range(1, length + 1)) % modulus


def check_block_identity() -> int:
    checks = 0
    for p in primes_up_to(31):
        modulus = p**3
        for a in range(1, 18):
            a1 = a * (a - 1) // 2
            a2 = a * (a - 1) * (2 * a - 1) // 6
            for n in range(2, 25):
                lhs = (
                    power_sum_mod(n, a * p, modulus)
                    - a * power_sum_mod(n, p, modulus)
                ) % modulus
                rhs = (
                    n * p * a1 * power_sum_mod(n - 1, p, modulus)
                    + n * (n - 1) // 2
                    * p**2
                    * a2
                    * power_sum_mod(n - 2, p, modulus)
                ) % modulus
                assert lhs == rhs, (p, a, n, lhs, rhs)
                checks += 1
    return checks


def check_three_adic_table() -> int:
    expected = {
        0: (2, 5, 2, 1, 0, 0),
        2: (5, 8, 1, 1, 2, 1),
        4: (8, 2, 0, 1, 1, 0),
    }
    checks = 0
    for n in range(4, 220, 2):
        residue = n % 6
        sn = power_sum_mod(n, 3, 9)
        admissible = [
            a
            for a in range(9)
            if a * sn % 9 == (1 + 3 * a * n) % 9
        ]
        assert len(admissible) == 1
        a = admissible[0]
        q = (power_sum_mod(n - 1, 3, 9) // 3) % 3
        a1 = a * (a - 1) // 2 % 3
        a2 = a * (a - 1) * (2 * a - 1) // 6 % 3
        choose2 = n * (n - 1) // 2 % 3
        assert (sn, a, q, a1, a2, choose2) == expected[residue]
        correction = (
            n * a1 * q
            + choose2 * a2 * power_sum_mod(n - 2, 3, 3)
        ) % 3
        assert correction == 0
        checks += 1
    return checks


def check_bounded_premises(max_k: int = 500, max_n: int = 60) -> tuple[int, int]:
    premise_count = 0
    target_checks = 0
    for k in range(1, max_k + 1):
        modulus = k * k
        running = [0] * (max_n + 1)
        for j in range(1, k + 1):
            for n in range(1, max_n + 1):
                running[n] = (running[n] + pow(j, n, modulus)) % modulus
        for n in range(1, max_n + 1):
            if running[n] != pow(k + 1, n, modulus):
                continue
            premise_count += 1
            for p in prime_divisors(k):
                target_modulus = p**3
                target = (
                    power_sum_mod(n, k, target_modulus)
                    - (k // p) * power_sum_mod(n, p, target_modulus)
                ) % target_modulus
                assert target == 0, (n, k, p, target)
                target_checks += 1
    return premise_count, target_checks


def main() -> None:
    block_checks = check_block_identity()
    table_checks = check_three_adic_table()
    premise_count, target_checks = check_bounded_premises()
    print(f"block identity checks: {block_checks}")
    print(f"3-adic table/cancellation checks: {table_checks}")
    print(f"bounded premise instances: {premise_count}")
    print(f"bounded prime-target checks: {target_checks}")
    print("PASS")


if __name__ == "__main__":
    main()
