"""Exact, independent algebra for section 2.3; does not execute Lean kernels.

Compares differentiation of -F0.Q/2 and -Q.Q/4 (the source densities) with
closed three- and four-gauge-field tensors. Cubic momenta are independent;
all 12 momentum coefficients are tested. Quartic tests cover all color and
Lorentz components for each chosen alternating color tensor. Also checks
finite-matrix Wilson plaquettes with affine, noncommuting link fields.
"""
import itertools as it
import json
import math
from pathlib import Path
from fractions import Fraction as Q

def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1,len(p)))

def alternating(dim):
    triples=list(it.combinations(range(dim),3))
    table={t:(1 if dim==3 else (i+1)*(-1)**i) for i,t in enumerate(triples)}
    def f(a,b,c):
        t=(a,b,c)
        if len(set(t))<3:return 0
        return sign(t)*table[tuple(sorted(t))]
    return f

def cubic(colors,axes,f):
    # Twice the coefficient after stripping i*g.
    raw=[0]*12
    for a,b,c in it.permutations(range(3)):
        fac=f(colors[b],colors[c],colors[a])
        if axes[a]==axes[c]:raw[4*a+axes[b]]-=fac
        if axes[a]==axes[b]:raw[4*a+axes[c]]+=fac
    expected=[0]*12
    fac=f(*colors)
    for a,b,c in [(0,1,2),(1,2,0),(2,0,1)]:
        if axes[a]==axes[b]:
            expected[4*a+axes[c]]+=fac
            expected[4*b+axes[c]]-=fac
    assert raw==[2*x for x in expected],(colors,axes,raw,expected)
    if any(expected):
        assert raw != [-2*x for x in expected]
        assert [math.factorial(3)*x for x in raw] != [2*x for x in expected]
    return any(expected)

def quartic(colors,axes,f,dim):
    # Four times the coefficient after stripping g^2.
    raw=0
    for a,b,c,d in it.permutations(range(4)):
        if axes[a]==axes[c] and axes[b]==axes[d]:
            raw-=sum(f(colors[a],colors[b],e)*f(colors[c],colors[d],e) for e in range(dim))
    a,b,c,d=colors; mu,nu,rho,sigma=axes
    delta=lambda a,b:int(a==b)
    expected=-sum(
        f(a,b,e)*f(c,d,e)*(delta(mu,rho)*delta(nu,sigma)-delta(mu,sigma)*delta(nu,rho))
        + f(a,c,e)*f(b,d,e)*(delta(mu,nu)*delta(rho,sigma)-delta(mu,sigma)*delta(nu,rho))
        + f(a,d,e)*f(b,c,e)*(delta(mu,nu)*delta(rho,sigma)-delta(mu,rho)*delta(nu,sigma))
        for e in range(dim))
    assert raw==4*expected,(colors,axes,raw,expected)
    if expected:
        assert raw != -4*expected
        assert math.factorial(4)*raw != 4*expected
    return expected!=0

rows=[]
for dim in [3,4]:
    f=alternating(dim); c3=c4=n3=n4=0
    for colors in it.product(range(dim),repeat=3):
        for axes in it.product(range(4),repeat=3):
            n3+=cubic(colors,axes,f);c3+=1
    for colors in it.product(range(dim),repeat=4):
        for axes in it.product(range(4),repeat=4):
            n4+=quartic(colors,axes,f,dim);c4+=1
    assert n3 and n4
    rows.append(dict(color_dimension=dim,cubic_tensor_entries=c3,
        cubic_momentum_coefficients=12*c3,cubic_nonzero_entries=n3,
        quartic_tensor_entries=c4,quartic_nonzero_entries=n4))

# Exact Pauli/quaternion algebra: E_i E_j=-delta_ij+epsilon_ijk E_k.
Z=(Q(0),)*4;eye=(Q(1),Q(0),Q(0),Q(0))
def qa(a,b):return tuple(x+y for x,y in zip(a,b))
def qs(a,c):return tuple(c*x for x in a)
def qm(a,b):
    return (a[0]*b[0]-sum(a[i]*b[i] for i in range(1,4)),
        a[0]*b[1]+a[1]*b[0]+a[2]*b[3]-a[3]*b[2],
        a[0]*b[2]+a[2]*b[0]+a[3]*b[1]-a[1]*b[3],
        a[0]*b[3]+a[3]*b[0]+a[1]*b[2]-a[2]*b[1])
def qsum(xs):
    out=Z
    for x in xs:out=qa(out,x)
    return out

def mat(v):return (Q(0),)+tuple(Q(x) for x in v)
def mul(a,b):return [qsum(qm(a[j],b[k-j]) for j in range(k+1)) for k in range(5)]
def exp_link(A,B):
    x=[Z,A,B,Z,Z];power=[eye,Z,Z,Z,Z];res=[eye,Z,Z,Z,Z]
    for j in range(1,5):
        power=mul(power,x)
        res=[qa(res[k],qs(power[k],Q(1,math.factorial(j)))) for k in range(5)]
    return res
plaquettes=[]
samples=[((1,0,0),(0,1,0),(0,0,0),(0,0,0)),
         ((1,2,0),(-1,0,1),(2,-1,3),(1,3,-2)),
         ((0,0,0),(0,0,0),(1,2,3),(-2,1,1)),
         ((2,-1,1),(1,2,-2),(3,0,-1),(-1,2,2))]
for av,bv,dibv,djav in samples:
    A,B,diB,djA=map(mat,[av,bv,dibv,djav])
    # Nonzero transverse derivatives; own-direction derivatives zero.
    # Midpoint link sampling then gives these four exponents.
    P=mul(mul(mul(exp_link(A,Z),exp_link(B,diB)),exp_link(qs(A,-1),qs(djA,-1))),exp_link(qs(B,-1),Z))
    coeff=[(1 if k==0 else 0)-P[k][0] for k in range(5)]
    F=qsum([diB,qs(djA,-1),qm(A,B),qs(qm(B,A),-1)])
    expected=-qm(F,F)[0]/2
    assert coeff[:4]==[0,0,0,0] and coeff[4]==expected
    plaquettes.append(dict(input=[av,bv,dibv,djav],a4_coefficient=str(expected)))

record=dict(status='passed',scope='Exact finite tests and independently differentiated tensors; not a new Lean proof of every tensor component or a continuum-limit theorem.',
    vertex_tests=rows,tests_impose_momentum_conservation=False,
    all_arithmetic='integer/rational and exact imaginary unit',
    negative_controls=dict(cubic_sign_and_extra_factorial_detected=True,quartic_sign_and_extra_factorial_detected=True),
    wilson_affine_SU2_plaquettes=plaquettes)
# Explicit negative controls on nonzero entries, not just an assertion that
# some component exists: changing sign or adding a factorial changes it.
f=alternating(3)
assert cubic((0,1,2),(0,0,1),f)
assert quartic((0,0,1,1),(0,0,1,1),f,3)
(Path(__file__).resolve().parents[1]/'evidence/matching/section23-algebra.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
