# Rational certificates for the Taylor equations

The eight Taylor equations for three normalized cubes with distinct means and nonzero variances have an explicit rational certificate of inconsistency after saturation. In the variable order `p,v1,v2,v3,s1,s2,s3,u`, put $q=1-p$ and $V=v_1v_2v_3$. The nine cofactor polynomials satisfy

$$
\sum_{n=2}^9 h_n F_n + h_{\mathrm{sat}}(upqV-1)=1.
$$

Here $F_n$ is the order-$n$ moment of the signed sum of the three normalized cubes, with weights $p,q,-1$ and means $1,0,p$. At a common zero, $u$ is the inverse of $pqV$. The input lists all nine integer polynomials in the order of the circuit outputs. [Integer inputs](integer-input.ms) · [Original-coordinate circuit](original-nine.json.gz)

## The two chart products

Let $P(X)=X^3-bX-c$, $K=X^2-b$, and work in the quotient by $P$. The three centered binomial means are the roots of $P$. At each mean, the variance is $3(d+eX-K)$, and the sum of the two centered frequencies is $(d+b)w+e(j+9)+jX+wK$. Let $E_n(w)$ be the coefficient of $K$ in the order-$n$ cube moment on the basis $1,X,K$. The six primitive generators are $G_n(w)=E_n(w)/9$ for $4\le n\le9$. Their common target is

$$
H=(4b^3-27c^2)\operatorname{Res}_X\!\left(P(X),d+eX-K\right).
$$

For each chart $w\in\{0,1\}$, the file supplies a positive integer $D$ and six integer polynomials $C_n$ with $D H=\sum_{n=4}^9 C_n G_n(w)$. The checker independently constructs cube moments using their four frequencies, computes the norm and discriminant by resultants, and checks every coefficient of this identity over the integers.

| Chart | Terms in $C_4,C_5,C_6,C_7,C_8,C_9$ | Digits in $D$ |
| --- | --- | ---: |
| [Zero curvature](w0-rational-H.json.gz) | 308, 119, 68, 37, 19, 0 | 76 |
| [Unit curvature](w1.json.gz) | 3,119, 1,291, 666, 372, 214, 88 | 520 |

The exponent order is `b,c,d,e,j` in both files. In the zero chart, `target_multiplier` is $D$, and each row of a multiplier is `[coefficient,b,c,d,e,j]`, with the last five entries denoting exponents. In the unit chart, `denominator` is $D$, and rows are `[slot,b,c,d,e,j,coefficient]`, with `slot` running from zero for $G_4$ through five for $G_9$.

## Reconstruction in the original variables

Scaling $(b,c,d,e,j)$ to $(w^2b,w^3c,w^2d,we,j)$ in the $w=1$ witness yields a polynomial identity for $w^7H$ after cancellation. The $w=0$ witness supplies an identity for $H-wB$, where $B$ is obtained by polynomial divided differences in $w$. The difference-of-powers formula combines the two identities to express $H^8$ in the general chart ideal.

The builder translates the Taylor equations to centered means, projects the variance and centered frequency sum to the chart, and accounts for the projection errors with cofactor rows in $F_2,F_3$. It clears a denominator power of 213 in $pq$ and uses a difference of powers of degree 229 in $upqV$ to obtain the displayed identity for 1. The resulting JSON stores nine outputs of a shared circuit with 36,948 nodes. Its operations are rational constants, variables, addition, multiplication, and nonnegative integer powers. [Circuit builder](../scripts/build_sparse_cube_original_certificate.py)

## Reproduce the checks

Run from the repository root with Python and SymPy. The commands below were checked with Python 3.14.7 and SymPy 1.14.0. Install that dependency with `python -m pip install sympy==1.14.0`.

```sh
python -B scripts/check_sparse_cube_independent_identity.py certificates/w0-rational-H.json.gz
python -B scripts/check_sparse_cube_independent_identity.py certificates/w1.json.gz
python -B scripts/check_sparse_cube_certificate_lifts.py
python -B scripts/check_sparse_cube_original_bridge.py
python -B scripts/build_sparse_cube_original_certificate.py --check certificates/original-nine.json.gz
python -B scripts/check_sparse_cube_original_certificate.py
```

The first two commands expand the chart products in full. The next two compare the general-curvature scaling, moment recurrences, divided differences, norm correction, coordinate projection, and saturation identities symbolically. The rebuild compares the complete uncompressed circuit JSON byte for byte.

The final command regenerates the nine original input polynomials independently and compares every coefficient, then checks the circuit topology and evaluates the factored identity at eight rational points and 96 points over three prime fields. Removing any one cofactor makes the identity fail at each of the twelve generic control points. These evaluations are finite checks. The symbolic justification of the original identity uses the two chart products and the algebraic reconstruction above. [Independent circuit checker](../scripts/check_sparse_cube_original_certificate.py)
