import dexpr, util;

DExpr getPoly(double[] coeff,DExpr x){
	DExpr r=zero;
	foreach(c;coeff) r=x*r+c;
	return r;
}

DExpr approxPowEmX2(DExpr e){
	// e^-x²
	auto arg=dAbs(e);
	// range [0, 3]
	auto poly=[0.0422,-0.4013, 1.3594, -1.7601, 0.1268, 1.0000].getPoly(e);
	return dIvr(DIvr.Type.leZ,arg-3)*poly;
}

DExpr approxLog(DExpr e){
	// TODO: what about ranges [0, 0.1] and [10, ∞]?
	// range [0.1, 1]
	auto poly1=[629.189738585664, -2557.47417049932, 4210.10819766748,
			   -3594.79066567300, 1694.98719011315, -436.987965205420,
				60.1321271299536, -5.16445211851018].getPoly(e);
	// range [1, 10]
	auto poly2=[-0.000711707042556582, 0.0204319245831799,
				-0.220870997847981, 1.20818665998564, -1.00703587967828].getPoly(e);
	return dBounded!"[]"(e,one/10,one)*poly1+dBounded!"[]"(e,one,10.dℕ)*poly2;
}

DExpr approximate(DExpr e){
	static DExpr doIt(DExpr e, bool necessary){
		if(auto p=cast(DPlus)e){
			DExprSet summands=p.summands.dup;
			foreach(s;p.summands){
				if(auto k=doIt(s,necessary)){
					summands.remove(s);
					DPlus.insert(summands,k);
					return dPlus(summands);
				}
			}
		}
		if(auto m=cast(DMult)e){
			DExprSet factors=m.factors.dup;
			foreach(f;m.factors){
				if(auto k=doIt(f,necessary)){
					factors.remove(f);
					DMult.insert(factors,k);
					return dMult(factors);
				}
			}			
		}
		if(auto p=cast(DPow)e){
			if(auto k=doIt(p.operands[0],necessary))
				return k^^p.operands[1];
			if(auto k=doIt(p.operands[1],necessary))
				return p.operands[0]^^p.operands[1];
		}
		if(auto intg=cast(DInt)e){
			auto tmpvar=new DVar("tmp"); // TODO: get rid of this!
			auto intExpr=intg.getExpr(tmpvar);
			if(auto r=doIt(intExpr,true))
				return dInt(tmpvar,r);
		}
		if(necessary){
			if(auto l=cast(DLog)e){
				return approxLog(l.e);
			}
		}
		return null;
	}
	return doIt(e,false);
}

bool hasIntegrals(DExpr e){ return hasAny!DInt(e); }

DExpr killIntegrals(DExpr e){
	while(hasIntegrals(e)){
		if(auto r=e.approximate())
			e=r.simplify(one);
		else break;
	}
	return e;
}
