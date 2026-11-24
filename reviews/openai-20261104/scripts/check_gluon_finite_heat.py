#!/usr/bin/env python3
"""Exact heat-kernel calculation for the finite gluon-bubble review.

No master-integral or expected finite value defines the heat density. The
script derives the force, the regulated Taylor coefficient and a primitive
from the Gaussian contraction. Source-to-integral identification is an
analytic argument in the companion note; this is not a Lean acceptance test.
"""
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, math

class P:
    def __init__(self, value=0):
        self.v = ({(0,)*5:F(value)} if value else {}) if not isinstance(value,dict) else {k:F(v) for k,v in value.items() if v}
    def __add__(self,o):
        o=asP(o); v=defaultdict(F,self.v)
        for k,c in o.v.items(): v[k]+=c
        return P(dict(v))
    __radd__=__add__
    def __neg__(self): return P({k:-v for k,v in self.v.items()})
    def __sub__(self,o): return self+-asP(o)
    def __rsub__(self,o): return asP(o)+-self
    def __mul__(self,o):
        o=asP(o); v=defaultdict(F)
        for a,b in self.v.items():
            for c,e in o.v.items(): v[tuple(x+y for x,y in zip(a,c))]+=b*e
        return P(dict(v))
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0:
            assert len(self.v)==1
            k,c=next(iter(self.v.items())); return P({tuple(n*x for x in k):c**n})
        r=P(1)
        for _ in range(n): r=r*self
        return r
    def __truediv__(self,o): return self*asP(o)**-1
    def __eq__(self,o): return self.v==asP(o).v
    def subs(self,i,o):
        o=asP(o); result=P()
        for k,c in self.v.items():
            kk=list(k); n=kk[i]; kk[i]=0
            result+=P({tuple(kk):c})*o**n
        return result
    def val(self,*xs):
        return sum(c*prod(F(x)**n for x,n in zip(xs,k)) for k,c in self.v.items())
    def __repr__(self):
        return ' + '.join(str(c)+''.join('*'+s+('^'+str(n) if n!=1 else '') for s,n in zip(['A','B','t','h','d'],k) if n) for k,c in sorted(self.v.items())) or '0'
def asP(x): return x if isinstance(x,P) else P(x)
def prod(xs):
    r=1
    for x in xs:r*=x
    return r
def sym(i):
    k=[0]*5;k[i]=1;return P({tuple(k):1})
def deriv(poly,i):
    out={}
    for k,c in poly.v.items():
        if k[i]:
            kk=list(k);kk[i]-=1;out[tuple(kk)]=c*k[i]
    return P(out)

D,u,X,s,H=map(sym,range(5))
a=-u;b=1-u;c=a+b
ab=a*b
AB=D*(D+2)*s**2+(D*(a*a+b*b)+4*ab)*X*s+ab**2*X**2
ABt=(D+2)*(D+4)*s**3+((D+2)*(a*a+b*b)+4*ab)*X*s**2+ab**2*X**2*s
ABl=(D+2)*(D+4)*s**3+((D+2)*(a*a+b*b)+12*ab)*X*s**2+ab**2*X**2*s
M_T=4*(X*((2*D*D+D-5)*s**2+(a*a+b*b)*X*(D-1)*s)+(H-1)*ABt)
M_L=(H-1)*(4*ABl+8*c*c*(D+2)*X*s**2+8*ab*c*c*X**2*s+c*c*X*AB)-X*(4*(D-1)*s**2+c*c*X*(D-1)*s)
radialT=4*(X*(13*s+(a*a+b*b)*X)+(H-1)*(12*s**2+(a*a+b*b)*X*s))
fourthT=4*(2*X+(H-1)*s)
radialL=(H-1)*(48*s**2+(16*c*c+4*(a*a+b*b))*X*s+c*c*(a*a+b*b)*X**2)-X*(4*s+c*c*X)
fourthL=(H-1)*(4*s+c*c*X)

def coeff(poly,i,n):
    out={}
    for k,v in poly.v.items():
        if k[i]==n:
            kk=list(k);kk[i]=0;out[tuple(kk)]=v
    return P(out)
def show(poly):
    return ' + '.join(str(c)+''.join('*'+s+('^'+str(n) if n!=1 else '') for s,n in zip(['D','u','X','s','H'],k) if n) for k,c in sorted(poly.v.items())) or '0'
def integral(poly,i,lo=F(0),hi=F(1,2)):
    out=P()
    for k,c in poly.v.items():
        assert k[i]>=0
        kk=list(k);n=kk[i];kk[i]=0
        out+=P({tuple(kk):c*(hi**(n+1)-lo**(n+1))/(n+1)})
    return out
def divide_one_minus_u(poly):
    # Exact polynomial division, used only when the numerator is divisible.
    q=P();r=poly
    while r.v:
        degree=max(k[1] for k in r.v)
        assert degree>0,show(r)
        top=coeff(r,1,degree)*u**(degree-1)
        q-=top;r+=top*(1-u)
    return q

def log_integral(poly):
    # Returns rational and log(2) coefficients of int_0^.5 poly(u)log(1-u)du.
    q=poly.subs(1,1-u)
    rational=P();logtwo=P()
    for k,c0 in q.v.items():
        n=k[1];kk=list(k);kk[1]=0;c=P({tuple(kk):c0})
        rational+=c*(F(1,2)**(n+1)-1)/((n+1)**2)
        logtwo+=c*F(1,2)**(n+1)/(n+1)
    return rational,logtwo

def laplace(poly):
    # int_0^.5 exp(-X u)poly(u,X)du = U(X)+exp(-X/2)V(X).
    import math
    U=P();V=P()
    for k,c0 in poly.v.items():
        n=k[1];kk=list(k);kk[1]=0
        c=P({tuple(kk):c0})*F(math.factorial(n))*X**(-n-1)
        U+=c
        V-=c*sum(X**j*F(1,2)**j/F(math.factorial(j)) for j in range(n+1))
    return U,V

def primitive(U,V):
    # int f(X)/(2 X^2) dX = R(X)+exp(-X/2)S(X)+k E1(X/2).
    r=U/(2*X**2);v=V/(2*X**2);R=P();S=P()
    for kk,c in r.v.items():
        kk=list(kk);n=kk[2];assert n != -1
        kk[2]+=1;R+=P({tuple(kk):c/(n+1)})
    while v.v and min(k[2] for k in v.v)<-1:
        n=min(k[2] for k in v.v)
        term=coeff(v,2,n)*X**(n+1)/(n+1)
        S+=term;v-=deriv(term,2)-term/2
    # Any nonnegative powers are solved in descending order.
    while v.v and max(k[2] for k in v.v)>=0:
        n=max(k[2] for k in v.v)
        term=-2*coeff(v,2,n)*X**n
        S+=term;v-=deriv(term,2)-term/2
    assert all(k[2]==-1 for k in v.v)
    K=-v*X
    assert deriv(R,2)==U/(2*X**2)
    assert deriv(S,2)-S/2-K/X==V/(2*X**2)
    return R,S,K


def run():
    result={}
    for label,M in [('transverse',M_T),('longitudinal',M_L)]:
        radial,fourth=(radialT,fourthT) if label=='transverse' else (radialL,fourthL)
        assert M.subs(0,4+2*D)==M.subs(0,4)+2*D*s*radial+4*D*(D+1)*s**2*fourth
        trace_h=2*u*divide_one_minus_u((2*deriv(M,4)).subs(3,(1-u)/2).subs(0,4).subs(4,4))
        trace_j=coeff(trace_h,2,1)-u*coeff(trace_h,2,0)
        trace_delta=-integral(trace_j,1)/2
        assert trace_delta==(F(1,3) if label=='transverse' else F(0))
        heat=2*u*divide_one_minus_u(M.subs(3,(1-u)/2).subs(4,D))
        physical=heat.subs(0,4)
        j=coeff(heat,2,1)-u*coeff(heat,2,0)
        a0=integral(coeff(physical,2,0),1)
        a1=integral(j.subs(0,4),1)
        assert a0==F(33,4)
        assert a1==(F(25,6) if label=='transverse' else F(-1,2))
        jr,jl=log_integral(j.subs(0,4))
        jr+=integral((2*deriv(j,0)).subs(0,4),1)
        U,V=laplace(physical)
        R,S,K=primitive(U,V)
        exp_series=sum((-X/2)**n/F(math.factorial(n)) for n in range(8))
        small=R+S*exp_series
        cr=coeff(small,2,0)
        assert coeff(small,2,-3)==0 and coeff(small,2,-2)==0
        assert coeff(small,2,-1)==-a0/2
        assert K==-a1/2 and K+jl/2==0
        finite=-cr-jr/2
        assert finite==(F(89,36) if label=='transverse' else F(-1,2))
        # Independent power-series integration of the compact heat integral.
        # Use rational X and compare to the elementary force, with Decimal exp.
        from decimal import Decimal, localcontext
        numerical=[]
        for x in [F(1,10),F(1),F(3),F(10)]:
            h=physical.subs(2,x)
            series=sum(integral(h*(-x*u)**n/F(math.factorial(n)),1).val(0,0,0,0,0) for n in range(140))
            with localcontext() as context:
                context.prec=70
                dec=lambda q:Decimal(q.numerator)/Decimal(q.denominator)
                closed=dec(U.val(0,0,x,0,0))+(-dec(x)/2).exp()*dec(V.val(0,0,x,0,0))
                error=abs(closed-dec(series))
                assert error<Decimal('1e-55')
                numerical.append({'X':str(x),'absolute_error':str(error)})
        result[label]={
            'heat_polynomial':show(physical),'force_constant':show(a0),'force_X_coefficient':show(a1),
            'jet_integrand_at_zero':show(j.subs(0,4)),
            'jet_integrand_dimension_derivative':show((2*deriv(j,0)).subs(0,4)),
            'jet_integral_rational':show(jr),'jet_integral_log2_coefficient':show(jl),
            'force_nonexponential':show(U),'force_exponential_coefficient':show(V),
            'primitive_nonexponential':show(R),'primitive_exponential_coefficient':show(S),
            'primitive_E1_coefficient':show(K),'primitive_constant_rational':show(cr),
            'finite_constant':show(finite),'extra_vector_trace_finite_contribution':show(trace_delta),
            'independent_heat_series_checks':numerical}
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    channels=run()
    record={'status':'passed','checked_utc':datetime.now(timezone.utc).isoformat(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Exact rational heat-density, regulator-jet and primitive calculation; independent heat-series checks. The source identification is an analytic derivation, not a completed Lean theorem.',
        'conventions':{'gauge':'Landau','sign':'Euclidean log density','regulator':'D=Ds=4+2z','mu_bar':'y=log(mu_bar)+(EulerGamma-log(4pi))/2','external_squared_momentum':'1 for calculation; restored by source scale law','coupling':'g^2 stripped'},
        'channels':channels,
        'verified_identities':['split radial Gaussian moments, with independent spin dimension H','heat parameter Jacobian and polynomial coefficients','regulator jet including vector-dimension derivative','elementary heat integral','primitive derivative','small-X cancellations and constant','finite constant with subtraction normalization','negative control with frozen vector trace'],
        'limits_not_numerically_inferred':'Endpoint limits of the explicit primitive are proved in GluonLoopFinite.lean.',
        'unproved_lean_target':'YMReview.NovemberMatching.GluonLoop.SubmittedFinitePartTest',
        'formal_gaps':['actual noninteger innerTrace/yeast to the stated contracted Gaussian moment','source regulated Taylor coefficient to the explicit jet','assembly with source ultraviolet boundary and tensor/scale laws']}
    output=json.dumps(record,indent=2)+'\n'
    if args.output:args.output.write_text(output)
    print(output,end='')

if __name__=='__main__':main()
