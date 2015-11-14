import dexpr, util;
import std.algorithm, std.array;
import asymptotics;

static struct ExpLim{
	DExpr expression;
	DExpr limit;
}
static struct Case(T){
	DExpr condition;
	T expression;
	auto map(alias a)(){ return Case!(typeof(a(expression)))(a(expression),condition,limit); }
	auto addCondition(DExpr c){ return Case!T(condition*c,expression); }
}
auto expandMap(alias a)(Case!ExpLim[][] r){
	alias T=typeof(a(ExpLim[].init));
	Case!T[] result;
	void go(int i,DExpr cond,ExpLim[] explims){ // TODO: this seems inefficient
		if(i==r.length){
			result~=Case!T(cond,a(explims));
			return;
		}
		foreach(k;r[i]) go(i+1,cond*k.condition,explims~k.expression);
	}
	go(0,one,[]);
	return result;
}
auto expandFlatMap(alias a)(Case!ExpLim[][] r){
	Case!ExpLim[] result;
	void go(int i,DExpr cond,ExpLim[] explims){ // TODO: this seems inefficient
		if(i==r.length){
			result~=a(explims).map!(a=>a.addCondition(cond)).array;
			return;
		}
		foreach(k;r[i]) go(i+1,cond*k.condition,explims~k.expression);
	}
	go(0,one,[]);
	return result;
}


DExpr getLimit(DVar v,DExpr e,DExpr x,DExpr facts=one)in{assert(isInfinite(e));}body{
	e=e.simplify(facts);
	x=x.simplify(facts);
	Case!ExpLim[] doIt(DVar v,DExpr e,DExpr x){
		if(!x.hasFreeVar(v)) return [Case!ExpLim(one,ExpLim(x,x))];
		if(x is v) return [Case!ExpLim(one,ExpLim(x,e))];
		if(auto p=cast(DPlus)x.polyNormalize(v).simplify(facts)){
			DExpr handlePlusImpl(ExpLim[] c){
				bool simplified=false;
				DExpr finite=zero;
				DExprSet unsupported;
				DExprSet inf;
				DExprSet minf;
				foreach(s;c){
					auto l=s.limit;
					if(!l){ unsupported.insert(s.expression); continue; }
					l=l.simplify(facts);
					if(l is dInf){ inf.insert(s.expression); continue; }
					if(l is -dInf){ minf.insert(s.expression); continue; }
					if(l.hasLimits()){ unsupported.insert(l); continue; }
					finite = finite+l;
					simplified = true;
				}
				//dw(v," ",inf," ",minf," ",finite," ",unsupported);
				if(!unsupported.length){
					if(inf.length && !minf.length) return dInf;
					if(minf.length && !inf.length) return -dInf;

					auto infAsymp=asymptoticNormalize(v,dPlus(inf));
					auto minfAsymp=asymptoticNormalize(v,dPlus(minf));
					if(growsFasterThanNormalized(v,infAsymp,minfAsymp))
						return dInf;
					if(growsFasterThanNormalized(v,minfAsymp,infAsymp))
						return -dInf;
				}
			
				if(!simplified) return null;
				foreach(x;inf) unsupported.insert(x);
				foreach(x;minf) unsupported.insert(x);
				return finite+dLimSmp(v,e,dPlus(unsupported)); // TODO: repeated simplification ugly, how to do without?			
			}
			ExpLim handlePlus(ExpLim[] c){ return ExpLim(p,handlePlusImpl(c)); }
			Case!ExpLim[][] r;
			foreach(s;p.summands){
				r~=doIt(v,e,s);
				if(!r[$-1].length) return [];
			}
			return expandMap!handlePlus(r);
		}
		if(auto m=cast(DMult)x){
			Case!ExpLim[] handleMult(ExpLim[] c){
				bool simplified=false;
				DExpr finite=one;
				DExprSet unsupported;
				DExprSet inf;
				bool sign=0;
				DExprSet zro;
				foreach(f;c){
					auto l=f.limit;
					if(!l){ unsupported.insert(f.expression); continue; }
					l=l.simplify(facts);
					if(l.isInfinite()){
						sign ^= l is -dInf;
						inf.insert(f.expression);
						continue;
					}
					if(l is zero){
						zro.insert(f.expression);
						continue;
					}
					if(l.hasLimits()){ unsupported.insert(l); continue; }
					finite=finite*l;
					simplified=true;
				}
				//dw(v," ",inf," ",zro," ",finite," ",unsupported);
				if(!unsupported.length){
					if(inf.length && !zro.length){
						auto leZ=dIvr(DIvr.Type.leZ,finite).simplify(facts);
						auto geZ=dIvr(DIvr.Type.leZ,-finite).simplify(facts);
						Case!ExpLim[] r;
						if(leZ !is zero)
							r~=Case!ExpLim(leZ,ExpLim(m,sign?dInf:-dInf));
						if(geZ !is zero)
							r~=Case!ExpLim(geZ,ExpLim(m,sign?-dInf:dInf));
						return r;
					}
					if(zro.length && !inf.length) return [Case!ExpLim(one,ExpLim(m,zero))];
				}
				// TODO: Bernoulli-De l'Hôpital (?)
				// auto f=dMult(inf), g=1/dMult(zro);
				if(!simplified) return null;		
				foreach(x;inf) unsupported.insert(x);
				foreach(x;zro) unsupported.insert(x);
				return [Case!ExpLim(one,ExpLim(m,finite*dLimSmp(v,e,dMult(unsupported))))];
				// TODO: repeated simplification ugly, how to do without?
			}
			Case!ExpLim[][] r;
			foreach(s;m.factors){
				r~=doIt(v,e,s);
				if(!r[$-1].length) return [];
			}
			return expandFlatMap!handleMult(r);
		}
		if(auto p=cast(DPow)x){
			DExpr handlePow(DExpr l0,DExpr l1){
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
				if(l0 is -dInf){
					if(auto c=cast(Dℕ)l1)
						return c.c%2?-dInf:dInf;
					return null;
				}
				if(l0 is dInf){
					if(dIvr(DIvr.Type.leZ,l1).simplify(facts) is zero)
						return dInf;
					if(dIvr(DIvr.Type.leZ,-l1).simplify(facts) is zero)
						return zero;
					return null;
				}
				return l0^^l1;
			}
			auto l0=doIt(v,e,p.operands[0]);
			auto l1=doIt(v,e,p.operands[1]);
			Case!ExpLim[] r;
			foreach(el0;l0)
				foreach(el1;l1)
					r~=Case!ExpLim(el0.condition*el1.condition,
							ExpLim(p,handlePow(el0.expression.limit,el1.expression.limit)));
			return r;
		}
		if(auto g=cast(DGaussInt)x){
			DExpr handleGaussInt(DExpr l){
				if(!l) return null;
				if(l.hasLimits()) return null;
				if(l is -dInf) return zero;
				if(l is dInf) return one;
				return dGaussInt(g.x.substitute(v,l));
			}
			auto l=doIt(v,e,g.x);
			Case!ExpLim[] r;
			foreach(el;l){
				r~=Case!ExpLim(el.condition,ExpLim(g,handleGaussInt(el.expression.limit)));
			}
			return r;
		}
		return [];
	}
	auto k=doIt(v,e,x);
	if(!k.length) return null;
	foreach(c;k) if(!c.expression.limit) return null;
	DExpr r=zero;
	foreach(c;k) r=r+c.condition*c.expression.limit;
	return r.simplify(facts);
}
