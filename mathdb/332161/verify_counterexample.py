"""Exact verifier for the F_2 counterexample to MathDB #332161."""

from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
from typing import Any


CERTIFICATE_SHA256 = (
    "22ac2cae24fb3bff91d041fac457ffb97685ec1319f33da969b837efd6a25577"
)


def require(condition: bool, message: str) -> None:
    """Raise an informative error; unlike assert, this remains active under -O."""
    if not condition:
        raise RuntimeError(message)


def check_elements(value: Any, label: str) -> list[int]:
    require(type(value) is list and value, f"{label} must be a nonempty list")
    require(all(type(x) is int for x in value), f"{label} must contain integers")
    require(len(value) == len(set(value)), f"{label} contains a duplicate")
    return value


def check_table(value: Any, elements: list[int], label: str) -> list[list[int]]:
    n = len(elements)
    require(type(value) is list and len(value) == n, f"{label} has wrong row count")
    for row in value:
        require(type(row) is list and len(row) == n, f"{label} has wrong shape")
        require(all(type(x) is int and x in elements for x in row),
                f"{label} is not closed")
    return value


def main() -> None:
    path = Path(__file__).with_name("certificate.json")
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == CERTIFICATE_SHA256,
            f"certificate hash mismatch: expected {CERTIFICATE_SHA256}, got {digest}")
    data = json.loads(raw)

    require(type(data) is dict, "certificate root must be an object")
    require(set(data) == {
        "format",
        "problem",
        "semiring",
        "semimodule",
        "partition",
        "finite_subset_F",
        "expected_cell_failures",
    }, "unexpected certificate fields")
    require(data["format"] == "mathdb-332161-f2-counterexample-v1",
            "wrong certificate format")
    require(type(data["problem"]) is int and data["problem"] == 332161,
            "wrong problem number")

    ring = data["semiring"]
    require(type(ring) is dict and set(ring) == {
        "elements", "zero", "one", "addition", "multiplication"
    }, "wrong semiring fields")
    r_elements = check_elements(ring["elements"], "semiring elements")
    require(r_elements == [0, 1], "certificate is required to encode F_2")
    r_index = {x: i for i, x in enumerate(r_elements)}
    zero = ring["zero"]
    one = ring["one"]
    require(type(zero) is int and zero in r_index, "invalid semiring zero")
    require(type(one) is int and one in r_index and one != zero,
            "invalid semiring unit")
    r_add = check_table(ring["addition"], r_elements, "semiring addition")
    r_mul = check_table(ring["multiplication"], r_elements, "semiring multiplication")

    def ra(x: int, y: int) -> int:
        return r_add[r_index[x]][r_index[y]]

    def rm(x: int, y: int) -> int:
        return r_mul[r_index[x]][r_index[y]]

    for x in r_elements:
        require(ra(x, zero) == x and ra(zero, x) == x,
                "semiring additive-zero axiom failed")
        require(rm(one, x) == x and rm(x, one) == x,
                "semiring multiplicative-unit axiom failed")
        require(rm(zero, x) == zero,
                "source's left absorbing-zero axiom failed")
        require(rm(x, zero) == zero,
                "right absorbing-zero axiom failed")
    for x, y in itertools.product(r_elements, repeat=2):
        require(ra(x, y) == ra(y, x), "semiring addition is not commutative")
    for x, y, z in itertools.product(r_elements, repeat=3):
        require(ra(ra(x, y), z) == ra(x, ra(y, z)),
                "semiring addition is not associative")
        require(rm(rm(x, y), z) == rm(x, rm(y, z)),
                "semiring multiplication is not associative")
        require(rm(ra(x, y), z) == ra(rm(x, z), rm(y, z)),
                "right distributivity failed")
        require(rm(z, ra(x, y)) == ra(rm(z, x), rm(z, y)),
                "left distributivity failed")

    module = data["semimodule"]
    require(type(module) is dict and set(module) == {
        "elements", "zero", "addition", "scalar_action"
    }, "wrong semimodule fields")
    m_elements = check_elements(module["elements"], "semimodule elements")
    require(m_elements == [0, 1], "certificate is required to encode the regular F_2-module")
    m_index = {x: i for i, x in enumerate(m_elements)}
    m_zero = module["zero"]
    require(type(m_zero) is int and m_zero in m_index, "invalid semimodule zero")
    m_add = check_table(module["addition"], m_elements, "semimodule addition")
    action = module["scalar_action"]
    require(type(action) is list and len(action) == len(r_elements),
            "scalar action has wrong row count")
    for row in action:
        require(type(row) is list and len(row) == len(m_elements),
                "scalar action has wrong shape")
        require(all(type(x) is int and x in m_index for x in row),
                "scalar action is not closed")

    def ma(x: int, y: int) -> int:
        return m_add[m_index[x]][m_index[y]]

    def act(r: int, x: int) -> int:
        return action[r_index[r]][m_index[x]]

    for x in m_elements:
        require(ma(x, m_zero) == x and ma(m_zero, x) == x,
                "semimodule additive-zero axiom failed")
        require(act(one, x) == x, "unit scalar axiom failed")
        require(act(zero, x) == m_zero, "zero scalar axiom failed")
    for x, y in itertools.product(m_elements, repeat=2):
        require(ma(x, y) == ma(y, x), "semimodule addition is not commutative")
    for x, y, z in itertools.product(m_elements, repeat=3):
        require(ma(ma(x, y), z) == ma(x, ma(y, z)),
                "semimodule addition is not associative")
    for r, t, x in itertools.product(r_elements, r_elements, m_elements):
        require(act(ra(r, t), x) == ma(act(r, x), act(t, x)),
                "(r+t)g = rg+tg failed")
        require(act(rm(r, t), x) == act(r, act(t, x)),
                "usual scalar-associativity axiom failed")
    for r, x, y in itertools.product(r_elements, m_elements, m_elements):
        require(act(r, ma(x, y)) == ma(act(r, x), act(r, y)),
                "r(g+h) = rg+rh failed")

    partition = data["partition"]
    require(type(partition) is list and partition, "partition must be nonempty")
    seen: set[int] = set()
    cells: list[set[int]] = []
    for cell_data in partition:
        require(type(cell_data) is list and cell_data, "partition cells must be nonempty")
        require(all(type(x) is int and x in m_index for x in cell_data),
                "partition contains an invalid element")
        cell = set(cell_data)
        require(len(cell) == len(cell_data), "partition cell contains a duplicate")
        require(seen.isdisjoint(cell), "partition cells overlap")
        seen.update(cell)
        cells.append(cell)
    require(seen == set(m_elements), "partition does not cover the semimodule")

    f_data = data["finite_subset_F"]
    require(type(f_data) is list and f_data, "F must be a nonempty finite list")
    require(all(type(f) is int and f in r_index for f in f_data),
            "F is not a subset of the semiring")
    require(len(f_data) == len(set(f_data)), "F contains a duplicate")
    f_set = set(f_data)
    require(f_set == set(r_elements), "the certificate's F must equal F_2")

    expected = data["expected_cell_failures"]
    require(type(expected) is list and len(expected) == len(cells),
            "wrong expected-failure list")
    require(expected == [
        {"cell_index": 0, "reason": "no_nonzero_b"},
        {"cell_index": 1, "reason": "no_a_b_pair"},
    ], "unexpected expected-failure data")

    candidates_checked = 0
    cell_witnesses: list[list[tuple[int, int]]] = []
    for cell in cells:
        witnesses: list[tuple[int, int]] = []
        for a in m_elements:
            for b in sorted(cell - {m_zero}):
                candidates_checked += 1
                image = {ma(a, act(f, b)) for f in f_set}
                if image <= cell:
                    witnesses.append((a, b))
        cell_witnesses.append(witnesses)

    require(all(not witnesses for witnesses in cell_witnesses),
            "some color cell satisfies the conjectured property for the chosen F")
    require(not (cells[0] - {m_zero}), "first cell should have no permitted b")
    require(cells[1] == {1}, "second cell should be {1}")
    require(all({ma(a, act(f, 1)) for f in f_set} == set(m_elements)
                for a in m_elements),
            "for b=1, a+Fb should be the whole module")

    print("PASS: exact F_2 counterexample to MathDB #332161")
    print(f"certificate_sha256={digest}")
    print("semiring_order=2 semimodule_order=2 cells=2 F_size=2")
    print(f"candidate_(a,b)_pairs_checked={candidates_checked}")
    print("cell_witness_counts=" + ",".join(str(len(x)) for x in cell_witnesses))
    print("all source semiring/semimodule axioms and the quantifier failure verified")


if __name__ == "__main__":
    main()
