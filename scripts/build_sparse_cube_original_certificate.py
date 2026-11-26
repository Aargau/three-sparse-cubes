"""Build nine division-free rational cofactor circuits for the original Taylor equations.

The only symbolic denominator used during construction is p*(1-p). Each value
tracks its denominator exponent until the final saturation step clears it.
"""
import argparse
from fractions import Fraction
from functools import lru_cache
import gzip
from hashlib import sha256
import json
from math import comb, prod
from pathlib import Path

from sympy import ZZ
from sympy.polys.rings import ring


ROOT = Path(__file__).resolve().parents[1]
W1 = ROOT / "certificates/w1.json.gz"
W0 = ROOT / "certificates/w0-rational-H.json.gz"


class Circuit:
    def __init__(self):
        self.nodes = []
        self.ids = {}
        self.zero = self.number(0)
        self.one = self.number(1)
        self.base = None

    def node(self, *op):
        if op not in self.ids:
            self.ids[op] = len(self.nodes)
            self.nodes.append(op)
        return self.ids[op]

    def number(self, value):
        q = Fraction(value)
        return self.node("const", str(q.numerator), str(q.denominator))

    def add(self, a, b):
        if a == self.zero:
            return b
        if b == self.zero:
            return a
        return self.node("add", min(a, b), max(a, b))

    def mul(self, a, b):
        if self.zero in (a, b):
            return self.zero
        if a == self.one:
            return b
        if b == self.one:
            return a
        return self.node("mul", min(a, b), max(a, b))

    def power(self, a, n):
        if n < 0:
            raise ValueError("negative polynomial exponent")
        if n == 0 or a == self.one:
            return self.one
        if n == 1 or a == self.zero:
            return a
        return self.node("pow", a, n)

    def compact(self, outputs):
        keep = set(outputs)
        for idx in range(len(self.nodes)-1, -1, -1):
            if idx in keep:
                op, *args = self.nodes[idx]
                if op in ("add", "mul"):
                    keep.update(args)
                elif op == "pow":
                    keep.add(args[0])
        renumber = {idx: i for i, idx in enumerate(sorted(keep))}
        result = []
        for idx in sorted(keep):
            op, *args = self.nodes[idx]
            if op in ("add", "mul"):
                args = [renumber[t] for t in args]
            elif op == "pow":
                args[0] = renumber[args[0]]
            result.append([op, *args])
        return result, [renumber[t] for t in outputs]


class FractionNode:
    """A polynomial numerator node divided by (p*q)**den."""
    def __init__(self, graph, num, den=0):
        self.g, self.num = graph, num
        self.den = 0 if num == graph.zero else den

    def convert(self, other):
        if isinstance(other, FractionNode):
            if self.g is not other.g:
                raise ValueError("mixed circuits")
            return other
        return FractionNode(self.g, self.g.number(other))

    def clear(self, degree):
        return self.g.mul(self.num, self.g.power(self.g.base, degree-self.den))

    def __add__(self, other):
        other = self.convert(other)
        if other.num == self.g.zero:
            return self
        if self.num == self.g.zero:
            return other
        k = max(self.den, other.den)
        return FractionNode(self.g, self.g.add(self.clear(k), other.clear(k)), k)

    __radd__ = __add__

    def __neg__(self):
        return self * (-1)

    def __sub__(self, other):
        return self + (-self.convert(other))

    def __rsub__(self, other):
        return self.convert(other) + (-self)

    def __mul__(self, other):
        other = self.convert(other)
        return FractionNode(self.g, self.g.mul(self.num, other.num), self.den+other.den)

    __rmul__ = __mul__

    def __pow__(self, n):
        return FractionNode(self.g, self.g.power(self.num, n), self.den*n)


def geom(a, b, n):
    """Return (a**n-b**n)/(a-b) as a polynomial, including on a=b."""
    return sum(a**(n-1-i) * b**i for i in range(n))


def raw_cube_moments():
    r, x, v, s = ring("x,v,s", ZZ)
    f = [r.one, x]
    for _ in range(2, 10):
        f.append((2*x+s)*f[-1] + (v-x*x-x*s)*f[-2])
    def convolve(left, right):
        return [sum(comb(n, i)*left[i]*right[n-i] for i in range(n+1))
                for n in range(10)]
    return convolve(convolve(f, f), f)


def differences(moment, x, v, vstar, s, sstar, sflat):
    """Two successive divided differences and the one for w-specialization."""
    dv, ds, flat = 0, 0, 0
    for (i, k, j), coeff in moment.items():
        common = int(coeff)*x**i
        if k:
            dv += common*s**j*geom(v, vstar, k)
        if j:
            scale = common*vstar**k
            ds += scale*geom(s, sstar, j)
            flat += scale*geom(sstar, sflat, j)
    return dv, ds, flat


def make_certificate():
    g = Circuit()
    variables = ["p", "v1", "v2", "v3", "s1", "s2", "s3", "u"]
    p, *rest = [FractionNode(g, g.node("var", name)) for name in variables]
    v, s, u = rest[:3], rest[3:6], rest[-1]
    q = 1-p
    g.base = (p*q).num
    inv_l = FractionNode(g, g.number(9), 1)
    def mass(values):
        return p*values[0] + q*values[1] - values[2]

    # Shift all three cube means by -mu. Their binomial means sum to zero.
    mu = (1+p)*Fraction(1, 3)
    x = [(a-mu)*Fraction(1, 3) for a in (1, 0, p)]
    b = -(x[0]*x[1] + x[0]*x[2] + x[1]*x[2])
    c = prod(x)
    k = [t*t-b for t in x]
    one_ninth = p.convert(Fraction(1, 9))
    disc = (p*q)**2 * Fraction(1, 729)
    actual_h = disc*prod(v)*Fraction(1, 27)

    # Each vector is a cofactor row in the original eight Taylor generators.
    def shifted(n):
        return [comb(n, i)*(-mu)**(n-i) if 2 <= i <= n else 0 for i in range(2,10)]
    delta_row = [a*inv_l*Fraction(1, 3) for a in shifted(2)]
    delta = 3 + mass(v)*inv_l
    vs = [a-delta*t for a, t in zip(v,k)]
    # x1-x2=1/3. Interpolate (v*/3+K) as d+eX and s as s0+jX+wK.
    e = vs[0]+3*k[0]-vs[1]-3*k[1]
    d = vs[1]*Fraction(1, 3)+k[1]-e*x[1]
    w = mass(s)*inv_l
    j = 3*(s[0]-s[1]-w*(k[0]-k[1]))
    flat = [e*(j+9)+j*t for t in x]
    ss = [a+w*(d+b+ki) for a,ki in zip(flat,k)]
    vpart = mass([ki*(27*xi+3*si) for ki,xi,si in zip(k,x,s)])
    eta_row = [(a*vpart-t)*inv_l*one_ninth for a,t in zip(delta_row,shifted(3))]
    h = disc*prod(vs)*Fraction(1, 27)

    with gzip.open(W0, "rt", encoding="utf8") as stream:
        z0 = json.load(stream)
    # This first witness uses a positional schema without target/variable metadata.
    # Bind it to the exact archived product checked in (b,c,d,e,j) with target H.
    packed_w1 = W1.read_bytes()
    if sha256(packed_w1).hexdigest() != "ecd96da2cb100caa4f571b684a197a74de1ceb53e6572bba7f1dc1ca96d54f34":
        raise ValueError("unrecognized nonzero-curvature chart witness")
    z1 = json.loads(gzip.decompress(packed_w1))
    if set(z1) != {"denominator", "rows"} or int(z1["denominator"]) <= 0:
        raise ValueError("incorrect nonzero-curvature witness schema")
    if z0["target"] != "H" or z0["variables"] != ["b","c","d","e","j"]:
        raise ValueError("incorrect zero-curvature witness")
    chart_vars = [b,c,d,e,j]
    @lru_cache(None)
    def monomial(powers):
        return prod(a**n for a,n in zip(chart_vars,powers))
    def weight(powers):
        return sum(a*b for a,b in zip((2,3,2,1,0),powers))
    # Raw moment coefficients E_n in each chart equal nine times the archived G_n.
    c0 = [sum(int(a)*monomial(tuple(m)) for a,*m in table) *
          Fraction(1,9*int(z0["target_multiplier"])) for table in z0["multipliers"]]
    shift = min(row[0]+2+weight(row[1:6]) for row in z1["rows"])
    if not 0 <= shift < 12:
        raise ValueError("unexpected homogenization shift")
    m = 12-shift
    c1 = [0]*6
    for slot,*powers,a in z1["rows"]:
        exp = slot+2+weight(powers)-shift
        c1[slot] += int(a)*monomial(tuple(powers))*w**exp
    c1 = [a*Fraction(1,9*int(z1["denominator"])) for a in c1]

    chart_rows = []
    bridge = 0
    for slot,moment in enumerate(raw_cube_moments()[4:]):
        dvd, dsd, flatd = zip(*(differences(moment,*args) for args in zip(x,v,vs,s,ss,flat)))
        va = mass([t*a for t,a in zip(k,dvd)])
        sa = mass(dsd)
        chart_rows.append([(tn-a*va-y*sa)*inv_l for tn,a,y in
                           zip(shifted(slot+4),delta_row,eta_row)])
        # (E_n(0)-E_n(w))/w, evaluated with a polynomial divided difference.
        bridge -= c0[slot]*inv_l*mass([(d+b+t)*a for t,a in zip(k,flatd)])
    co_chart = [a*h*geom(h,w*bridge,m)+z*bridge**m for a,z in zip(c0,c1)]
    change_h = disc*Fraction(1,27)*sum(ki*prod(v[:i])*prod(vs[i+1:]) for i,ki in enumerate(k))
    h_correction = change_h*geom(actual_h,h,m+1)
    rows = [a*h_correction + sum(co*row[i] for co,row in zip(co_chart,chart_rows))
            for i,a in enumerate(delta_row)]
    clear = max(a.den for a in rows)
    power = clear+2*(m+1)
    factor = 19683**(m+1)*u**power*prod(v)**(power-m-1)
    outputs = [g.mul(a.clear(clear), factor.num) for a in rows]
    sat_value = u*p*q*prod(v)
    outputs.append((-geom(sat_value,p.convert(1),power)).num)
    nodes, outputs = g.compact(outputs)
    return {"variables":variables, "generators":["F"+str(i) for i in range(2,10)]+["u*p*(1-p)*v1*v2*v3-1"],
            "nodes":nodes,"outputs":outputs,"chart_power":m+1,"clearing_power":clear,
            "saturation_power":power}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("output", nargs="?", type=Path, help="write a new compressed circuit")
    modes.add_argument("--check", type=Path, help="compare the rebuilt JSON to a compressed circuit")
    args = parser.parse_args()
    certificate = make_certificate()
    encoded = json.dumps(certificate,separators=(",",":")).encode("ascii")
    if args.check:
        if encoded != gzip.decompress(args.check.read_bytes()):
            raise ValueError("The rebuilt arithmetic circuit differs from the supplied JSON")
        print("Rebuilt circuit JSON matches byte for byte.")
    else:
        args.output.write_bytes(gzip.compress(encoded, compresslevel=9, mtime=0))
    print("Nodes",len(certificate["nodes"]),"chart power",certificate["chart_power"],
          "denominator clearing power",certificate["clearing_power"],
          "saturation power",certificate["saturation_power"])
