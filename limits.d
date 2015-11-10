import dexpr, util;

bool isInfinite(DExpr e){
	return e is dInf || e is -dInf;
}

bool hasLimits(DExpr e){ return hasAny!DLim(e); }

DExpr getLimit(DVar v,DExpr e,DExpr x,DExpr facts=one){
	e=e.simplify(facts);
	x=x.simplify(facts);
	DExpr doIt(DVar v,DExpr e,DExpr x){
		if(!x.hasFreeVar(v)) return x;
		if(x is v) return e;
		if(auto p=cast(DPlus)x){
			bool simplified=false;
			DExpr finite=zero;
			DExprSet unsupported;
			DExprSet inf;
			DExprSet minf;
			foreach(s;p.summands){
				auto l=doIt(v,e,s);
				if(!l){ unsupported.insert(s); continue; }
				l=l.simplify(facts);
				if(l is dInf){ inf.insert(s); continue; }
				if(l is -dInf){ minf.insert(s); continue; }
				if(l.hasLimits()){ unsupported.insert(s); continue; }
				finite = finite+l;
				simplified = true;
			}
			if(!unsupported.length){
				if(inf.length && !minf.length) return dInf;
				if(minf.length && !inf.length) return -dInf;
			}
			// TODO: figure out which function grows faster
			if(!simplified) return null;
			foreach(x;inf) unsupported.insert(x);
			foreach(x;minf) unsupported.insert(x);
			return finite+dLimSmp(v,e,dPlus(unsupported)); // TODO: repeated simplification ugly, how to do without?
		}
		if(auto m=cast(DMult)x){
			bool simplified=false;
			DExpr finite=one;
			DExprSet unsupported;
			DExprSet inf;
			int sign=0;
			DExprSet zro;
			foreach(f;m.factors){
				auto l=doIt(v,e,f);
				if(!l){ unsupported.insert(f); continue; }
				l=l.simplify(facts);
				if(l.isInfinite()){
					sign ^= l is -dInf;
					inf.insert(f);
					continue;
				}
				if(l is zero){
					zro.insert(f);
					continue;
				}
				if(l.hasLimits()){ unsupported.insert(f); continue; }
				finite=finite*l;
				simplified=true;
			}
			if(dIvr(DIvr.Type.leZ,finite).simplify(facts) is zero){
				// sign is correct
			}else if(dIvr(DIvr.Type.leZ,-finite).simplify(facts) is zero){
				sign = !sign;
			}
			if(!unsupported.length){
				if(inf.length && !zro.length) return sign?-dInf:dInf;
				if(zro.length && !inf.length) return zero;
			}
			// TODO: Bernoulli-De l'Hôpital (?)
			// auto f=dMult(inf), g=1/dMult(zro);
			if(!simplified) return null;		
			foreach(x;inf) unsupported.insert(x);
			foreach(x;zro) unsupported.insert(x);
			return finite*dLimSmp(v,e,dMult(unsupported));// TODO: repeated simplification ugly, how to do without?
		}
		if(auto p=cast(DPow)x){
			auto l0=doIt(v,e,p.operands[0]);
			auto l1=doIt(v,e,p.operands[1]);
			if(!l0 || !l1) return null;
			l0=l0.simplify(facts);
			l1=l1.simplify(facts);
			if(l0.isInfinite()&&l1.isInfinite()){
				if(l1 is -dInf||l0 is -dInf) return null;
				return dInf;
			}
			if(l0.hasLimits()||l1.hasLimits()) return null;
			if(l1 is -dInf) return zero;
			// TODO: fix those cases
			if(l1 is dInf){
				if(dIvr(DIvr.Type.leZ,-l0).simplify(facts) is zero){
					if(dIvr(DIvr.Type.leZ,l0-one).simplify(facts) is zero)
						return dInf;
					if(dIvr(DIvr.Type.leZ,one-l0).simplify(facts) is zero)
						return zero;
				}
				return null;
			}
			if(l0 is -dInf) return null;
			if(l0 is dInf){
				if(dIvr(DIvr.Type.leZ,l1).simplify(facts) is zero)
					return dInf;
				if(dIvr(DIvr.Type.leZ,-l1).simplify(facts) is zero)
					return zero;
				return null;
			}
			return l0^^l1;
		}
		if(auto g=cast(DGaussInt)x){
			auto l=doIt(v,e,g.x);
			if(!l) return null;
			if(l.hasLimits()) return null;
			if(l is -dInf) return zero;
			if(l is dInf) return one;
			return dGaussInt(g.x.substitute(v,l));
		}
		return null;
	}
	return doIt(v,e,x);
}
