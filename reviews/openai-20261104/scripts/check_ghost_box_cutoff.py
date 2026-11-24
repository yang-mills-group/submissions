#!/usr/bin/env python3
"""Independent direct momentum quadrature of the source heat-cutoff formula.

Subtracts a massive reference with known zero finite part at m=mu_bar=1.
Does not use the simplex or bubble reduction in the integrand. No certified
quadrature error bound, Lean evaluation, or lattice comparison is claimed.
"""
import argparse, json
from pathlib import Path
from datetime import datetime, timezone
import numpy as np
from numpy.polynomial.legendre import leggauss
import math

def cutoff(t):
    # Stable 1-(1+t) exp(-t), including the small-t cancellation.
    return -np.expm1(-t)-t*np.exp(-t)

def integrate(n,R):
    u,w=leggauss(n)
    # Center at -3p/2 to make the large momentum cancellation even.
    # rho=tan(pi v/2). Subdivide x at each soft point.
    rho=np.tan(np.pi*(u+1)/4)[None,:]
    wr=(w*np.pi/4*(1+rho[0]**2))[None,:]
    total=0.
    # rational map on each outer half-line, ordinary intervals inside
    panels=[(-np.inf,-3.),(-3.,-2.),(-2.,-1.),(-1.,0.),(0.,np.inf)]
    for a,b in panels:
        if math.isinf(a):
            x=(b-(1+u)/(1-u))[:,None]; wx=(w*2/(1-u)**2)[:,None]
        elif math.isinf(b):
            x=(a+(1+u)/(1-u))[:,None]; wx=(w*2/(1-u)**2)[:,None]
        else:
            x=(a+(b-a)*(u+1)/2)[:,None]; wx=(w*(b-a)/2)[:,None]
        den=[(x+j)**2+rho**2 for j in range(4)]
        product=np.prod(den,axis=0)
        base=((x+1.5)**2+rho**2+1)**4
        # The massive reference is centered at -3p/2; its MSbar finite
        # value at m=mu_bar=1 is zero by translation invariance.
        # Use a common numerator instead of subtracting two reciprocals.
        value=(base-product)/(base*product)
        if R is not None:
            h=np.prod([cutoff(R*R*d) for d in den],axis=0)
            value += (h-1)/product
        total += float(np.sum(wx*wr*rho**6*value))
    # 4pi/(5*(2pi)^4) times 128pi^2 = 32/(5pi)
    return total*32/(5*math.pi)

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    target=46/15+32/15*math.log(2)-81/20*math.log(3)
    rows=[]
    for n in (192,320,512,768):
        for R in (1,2,4,8,16,32,None):
            value=integrate(n,R)
            rows.append({'nodes_per_panel_axis':n,'infrared_length':R,
                'normalized_finite_value':value,'difference_from_infinite_length_formula':value-target})
    assert abs(rows[-1]['difference_from_infinite_length_formula']) < 1e-9
    assert abs(rows[-2]['difference_from_infinite_length_formula']) < 5e-9
    result={'checked_utc':datetime.now(timezone.utc).isoformat(),
        'scope':'Direct convergent four-dimensional momentum integral with source H(u)=(1+u)exp(-u). Numerical corroboration of the written analytic comparison, without a certified error bound or Lean finite-value theorem.',
        'normalization':'128 pi^2 I_R^MSbar, p^2=mu_bar^2=1',
        'reference_integrand':'(e.k)^4 / ((k+3p/2)^2+1)^4',
        'reference_finite_part':0,'c_box':target,'quadrature':rows}
    output=json.dumps(result,indent=2)+'\n'
    if args.output: args.output.write_text(output)
    print(output,end='')
