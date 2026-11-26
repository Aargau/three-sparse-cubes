"""Verify the rational cofactor identity directly from the four cube frequencies."""

import argparse
import gzip
import json
from pathlib import Path

from sympy import ZZ
from sympy.polys.rings import ring


def cube_equations(curvature, target_name):
    """Derive the primitive order 4 through 9 equations with w = curvature."""
    algebra, x, b, c, d, e, j = ring("x,b,c,d,e,j", ZZ)
    mean_cubic = x**3 - b*x - c

    def reduce_mean(poly):
        return poly.rem([mean_cubic])

    # The centered two-point distribution has mean zero, variance v, and
    # frequencies with sum s and product -v. Translate each frequency by x.
    v = 3*(b + d + e*x - x**2)
    s = curvature*(d + x**2) + e*(j+9) + j*x
    freq_sum = 2*x + s
    freq_product = x**2 + x*s - v

    # For translated frequencies a, h, the cube has frequencies 3a, 3h,
    # 2a+h, a+2h. The first pair and the last pair each sum to 3(a+h).
    # Their products are 9ah and 2(a+h)^2 + ah. Multiplying these two
    # quadratic annihilators gives the following four recurrence coefficients.
    pair_sum = 3*freq_sum
    product_outer = 9*freq_product
    product_inner = 2*freq_sum**2 + freq_product
    recurrence = [reduce_mean(poly) for poly in (
        2*pair_sum, -pair_sum**2 - product_outer - product_inner,
        pair_sum*(product_outer + product_inner), -product_outer*product_inner,
    )]
    moments = [algebra.one, 3*x, reduce_mean(9*x**2 + 3*v),
               reduce_mean(27*x**3 + 27*x*v + 3*v*s)]
    for n in range(4, 10):
        moments.append(reduce_mean(sum(a*moments[n-i] for i, a in enumerate(recurrence, 1))))

    # Res(P,v/3) is the product of the three scaled variances. The second
    # factor is the discriminant of P. Both are computed in the x-free ring.
    norm = mean_cubic.resultant(v.exquo(3*algebra.one))
    disc = -mean_cubic.resultant(mean_cubic.diff(x))
    target = {"H": disc*norm, "D2": disc**2}[target_name]
    equations = []
    for n, moment in enumerate(moments):
        quadratic = norm.ring.from_dict({exp[1:]: coeff for exp, coeff in moment.items()
                                         if exp[0] == 2})
        if n < 4:
            if quadratic:
                raise ValueError(f"The interpolation constraint failed at order {n}")
        else:
            equations.append(quadratic.primitive()[1])
    return equations, target


def parse_integer(value):
    if type(value) is int:
        return value
    if isinstance(value, str):
        digits = value.removeprefix("-")
        if digits.isascii() and digits.isdigit():
            return int(value)
    raise ValueError("Expected an integer or a decimal integer string")


def verify(certificate):
    """Expand the supplied integer cofactors in the independently derived ring."""
    open_file = gzip.open if certificate.suffix == ".gz" else open
    with open_file(certificate, "rt", encoding="utf8") as stream:
        data = json.load(stream)
    if "rows" in data:
        curvature = 1
        target_name = "H"
        denominator = parse_integer(data["denominator"])
        rows = data["rows"]
    else:
        target_name = data["target"]
        if (target_name not in ("H", "D2") or data["variables"] != list("bcdej")
                or len(data["multipliers"]) != 6):
            raise ValueError("Unexpected affine-chart certificate format")
        curvature = 0
        denominator = parse_integer(data["target_multiplier"])
        rows = ((slot, *powers, coeff) for slot, table in enumerate(data["multipliers"])
                for coeff, *powers in table)
    equations, target = cube_equations(curvature, target_name)
    if denominator <= 0:
        raise ValueError("Expected a positive common denominator")
    tables = [{} for _ in equations]
    for slot, *powers, numerator in rows:
        if (type(slot) is not int or not 0 <= slot < len(equations) or len(powers) != 5
                or any(type(k) is not int or k < 0 for k in powers)):
            raise ValueError("Invalid cofactor term")
        exponent = tuple(powers)
        if exponent in tables[slot]:
            raise ValueError("Repeated cofactor monomial")
        tables[slot][exponent] = parse_integer(numerator)

    left = sum((f*target.ring.from_dict(table) for f, table in zip(equations, tables)),
               target.ring.zero)
    if left != denominator*target:
        difference = left - denominator*target
        raise ValueError(f"Identity fails at {len(difference)} monomials")
    print(f"Verified the w={curvature} identity for {target_name} by expansion over ZZ.")
    print("Generator terms", [len(f) for f in equations])
    print("Cofactor terms", [len(t) for t in tables])
    print("Target terms", len(target))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    verify(parser.parse_args().certificate)
