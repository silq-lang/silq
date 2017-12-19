// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import dexpr;

DExpr differentiate(DVar v,DExpr e){
	if(v == e) return one;
	if(cast(Dℚ)e) return zero;
	if(cast(DFloat)e) return zero;
	if(auto p=cast(DPlus)e){
		DExprSet r;
		foreach(s;p.summands)
			DPlus.insert(r,dDiff(v,s));
		return dPlus(r);
	}
	if(auto m=cast(DMult)e){
		DExprSet r;
		foreach(f;m.factors)
			DPlus.insert(r,dDiff(v,f)*m.withoutFactor(f));
		return dPlus(r);
	}
	if(auto p=cast(DPow)e)
		return p.operands[0]^^(p.operands[1]+mone)*
			(dDiff(v,p.operands[0])*p.operands[1]+
			 p.operands[0]*dLog(p.operands[0])*dDiff(v,p.operands[1]));
	if(auto l=cast(DLog)e)
		return dDiff(v,l.e)/l.e;
	if(auto s=cast(DSin)e)
		return dDiff(v,s.e)*dSin(s.e+dΠ/2);
	if(auto f=cast(DFloor)e)
		return dDiff(v,f.e)*dDelta(dSin(dΠ*e)/dΠ); // TODO: this delta function should be skewed!
	if(auto f=cast(DCeil)e)
		return dDiff(v,f.e)*dDelta(dSin(dΠ*e)/dΠ); // TODO: this delta function should be skewed!
	if(auto g=cast(DGaussInt)e)
		return dDiff(v,g.x)*dE^^(-g.x^^2);
	if(auto g=cast(DGaussIntInv)e)
		return dDiff(v,g.x)*dE^^(e^^2);
	if(!e.hasFreeVar(v)) return zero;
	return null;
}
