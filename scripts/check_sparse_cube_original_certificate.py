"""Check the original Taylor generators exactly and evaluate the rational cofactor circuit.

Run from any directory with python -B path/to/check_sparse_cube_original_certificate.py.
The polynomial generator comparisons are symbolic. The checks of the full circuit
are exact evaluations at finitely many points, including points on the boundary.
"""

import argparse
from collections import Counter
from fractions import Fraction
import gzip
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
import random
import re

from sympy import QQ
from sympy.polys.rings import ring


ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / "certificates/original-nine.json.gz"
GENERATORS = ROOT / "certificates/integer-input.ms"
VARIABLES = ("p", "v1", "v2", "v3", "s1", "s2", "s3", "u")


def parse_polynomial(text, algebra):
    """Read the expanded integer polynomial syntax used in the msolve input."""
    names = dict(zip(VARIABLES, algebra.gens))
    result = algebra.zero
    for token in re.split(r"(?=[+-])", text):
        if not token:
            continue
        monomial = -algebra.one if token.startswith("-") else algebra.one
        for factor in token.lstrip("+-").split("*"):
            if factor.isdecimal():
                monomial *= int(factor)
            else:
                name, caret, power = factor.partition("^")
                if name not in names or (caret and not power.isdecimal()):
                    raise ValueError(f"Invalid polynomial factor {factor!r}")
                monomial *= names[name]**(int(power) if caret else 1)
        result += monomial
    return result


def cube_moments(cube_mean, variance, skew):
    """Use the four frequencies of the cube of a normalized binomial."""
    x = cube_mean * QQ(1, 3)
    # Original binomial frequencies a,h have sum and product as follows.
    freq_sum = 2*x + skew
    freq_product = x**2 + x*skew - variance
    # Pairs (3a,3h) and (2a+h,a+2h) have the same sum.
    pair_sum = 3*freq_sum
    outer = 9*freq_product
    inner = 2*freq_sum**2 + freq_product
    recurrence = (2*pair_sum, -(pair_sum**2 + outer + inner),
                  pair_sum*(outer + inner), -outer*inner)
    moments = [x.ring.one, 3*x, 9*x**2 + 3*variance,
               27*x**3 + 27*x*variance + 3*variance*skew]
    for n in range(4, 10):
        moments.append(sum(a*moments[n-i] for i, a in enumerate(recurrence, 1)))
    return moments


def check_generators(path):
    lines = path.read_text(encoding="ascii").splitlines()
    if len(lines) != 11 or tuple(lines[0].split(",")) != VARIABLES or lines[1] != "0":
        raise ValueError("Expected nine characteristic-zero msolve generators")
    algebra, p, v1, v2, v3, s1, s2, s3, u = ring(",".join(VARIABLES), QQ)
    actual = [parse_polynomial(line.removesuffix(","), algebra) for line in lines[2:]]
    moments = [cube_moments(a, v, s) for a, v, s in (
        (algebra.one, v1, s1), (algebra.zero, v2, s2), (p, v3, s3))]
    expected = [p*a + (1-p)*b - c for a, b, c in zip(*moments)]
    if expected[:2] != [algebra.zero, algebra.zero]:
        raise ValueError("The zeroth and first mixed moments must vanish identically")
    expected = expected[2:] + [u*p*(1-p)*v1*v2*v3 - 1]
    for i, (f, g) in enumerate(zip(actual, expected)):
        if f != g:
            raise ValueError(f"Input generator {i+1} differs from the frequency recurrence")
    return [[(int(coeff), [(i, n) for i, n in enumerate(exp) if n])
             for exp, coeff in poly.items()] for poly in actual]


def read_circuit(path):
    payload = path.read_bytes()
    data = json.loads(gzip.decompress(payload))
    expected_names = [f"F{i}" for i in range(2, 10)] + ["u*p*(1-p)*v1*v2*v3-1"]
    if tuple(data["variables"]) != VARIABLES or data["generators"] != expected_names:
        raise ValueError("Unexpected circuit variable or generator order")
    nodes = []
    outputs = data["outputs"]
    for i, (op, *args) in enumerate(data["nodes"]):
        def is_child(k):
            return type(k) is int and 0 <= k < i

        if op == "const":
            if len(args) != 2 or any(not isinstance(v, str) or
                                     not re.fullmatch(r"-?[0-9]+", v) for v in args):
                raise ValueError(f"Invalid rational constant at node {i}")
            numerator, denominator = map(int, args)
            valid = denominator > 0 and gcd(numerator, denominator) == 1
            args = [numerator, denominator]
        elif op == "var":
            valid = len(args) == 1 and args[0] in VARIABLES
            if valid:
                args = [VARIABLES.index(args[0])]
        elif op in ("add", "mul"):
            valid = len(args) == 2 and all(is_child(k) for k in args)
        elif op == "pow":
            child, power = args
            valid = is_child(child) and type(power) is int and power >= 0
        else:
            valid = False
        if not valid:
            raise ValueError(f"Invalid polynomial circuit node {i}")
        nodes.append((op, *args))
    if (len(outputs) != 9 or len(set(outputs)) != 9 or
            any(type(i) is not int or not 0 <= i < len(nodes) for i in outputs)):
        raise ValueError("Expected nine valid circuit outputs")
    print("Circuit SHA256", sha256(payload).hexdigest())
    print("Division-free circuit nodes", len(nodes))
    return nodes, outputs


def evaluate(point, prime, generators, nodes, outputs):
    generator_values = []
    for polynomial in generators:
        value = 0
        for coeff, powers in polynomial:
            term = coeff
            for var, power in powers:
                term *= point[var]**power
            value += term
        generator_values.append(value)
    values = []
    for op, *args in nodes:
        if op == "const":
            a, b = args
            value = Fraction(a, b) if prime is None else a*pow(b, -1, prime)
        elif op == "var":
            value = point[args[0]]
        elif op == "add":
            value = values[args[0]] + values[args[1]]
        elif op == "mul":
            value = values[args[0]] * values[args[1]]
        else:
            base, power = values[args[0]], args[1]
            value = base**power if prime is None else pow(base, power, prime)
        values.append(value if prime is None else value % prime)
    cofactors = [values[i] for i in outputs]
    terms = [g*c for g, c in zip(generator_values, cofactors)]
    if prime is not None:
        terms = [t % prime for t in terms]
    total = sum(terms)
    if (total if prime is None else total % prime) != 1:
        raise ValueError(f"Identity failed at {point} in characteristic {prime or 0}")
    return terms, cofactors


def verify(certificate, input_file):
    generators = check_generators(input_file)
    print("Nine original generators verified by exact symbolic comparison.")
    nodes, outputs = read_circuit(certificate)
    half, third = Fraction(1, 2), Fraction(1, 3)
    rational_points = [
        (0, 2, -1, 3, -2, 1, 4, -2), (1, 2, -1, 3, -2, 1, 4, -2),
        (2, -1, 2, 1, -1, 3, -2, 1), (half, 1, 2, -2, 3, 1, -1, -1),
        (third, 2, 1, 3, -2, -3, 1, Fraction(3, 4)), (2, 0, 1, 3, 1, 4, -2, 12),
        (2, 1, -1, 2, 2, 5, 11, 0), (half, 2, 1, 2, -1, 4, 3, 1),
    ]
    for point in rational_points:
        evaluate(point, None, generators, nodes, outputs)
    rng = random.Random(0x8BFC)
    omissions = Counter()
    for prime in (65521, 1000003, 2147483647):
        for mode in list(range(8))*4:
            point = [rng.randrange(prime) for _ in VARIABLES]
            if mode in (0, 1):
                point[0] = mode
            elif mode in (2, 3, 4):
                point[mode-1] = 0
            elif mode == 5:
                point[-1] = 0
            elif mode == 6:
                point = [v or 2 for v in point]
                if point[0] == 1:
                    point[0] = 2
                p, v1, v2, v3 = point[:4]
                point[-1] = pow(p*(1-p)*v1*v2*v3, -1, prime)
            terms, cofactors = evaluate(point, prime, generators, nodes, outputs)
            if mode < 6 and cofactors != [0]*8 + [prime-1]:
                raise ValueError("Incorrect cofactors on the saturation boundary")
            if mode == 6 and (terms[-1] != 0 or not all(cofactors[:8])):
                raise ValueError("Unexpected cofactors on the saturation hypersurface")
            if mode == 7:
                omissions.update(i for i in range(9) if (sum(terms)-terms[i]) % prime != 1)
    if omissions != Counter({i: 12 for i in range(9)}):
        raise ValueError("One or more omitted-generator controls escaped detection")
    print("Identity holds at 8 points over Q and 96 points over three prime fields.")
    print("Omitting any one cofactor failed at each of the 12 generic control points.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=CERTIFICATE)
    parser.add_argument("--generators", type=Path, default=GENERATORS)
    args = parser.parse_args()
    verify(args.certificate, args.generators)
