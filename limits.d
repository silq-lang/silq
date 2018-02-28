// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

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
auto compress(Case!ExpLim[] explims){
	foreach(ref el;explims){
		el.condition=el.condition.simplify(one);
		el.expression.limit=el.expression.limit.maybe!(e=>e.simplify(one));
	}
	Case!ExpLim[][DExpr] byLimit;
	Case!ExpLim[] result;
	foreach(el;explims) byLimit[el.expression.limit]~=el;
	foreach(k,v;byLimit){
		auto condition=zero, expression=zero, limit=zero;
		if(k&&k.isInfinite()){
			// TODO: improve
			result~=v;
		}else{
			foreach(el;v){
				assert(el.expression.limit == k);
				condition=condition+el.condition;
				expression=expression+el.condition*el.expression.expression;
				if(el.expression.limit !is null) limit=limit+el.condition*el.expression.limit;
				else limit=null;
			}
			result~=Case!ExpLim(condition,ExpLim(expression,limit));
		}
	}
	return result;
}
auto expandMap(alias a)(Case!ExpLim[][] r){
	alias T=typeof(a(ExpLim[].init));
	Case!T[] result;
	void go(int i,DExpr cond,ExpLim[] explims){ // TODO: this seems inefficient
		if(i==r.length){
			result~=Case!T(cond,a(explims));
			return;
		}
		r[i]=compress(r[i]);
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
		r[i]=compress(r[i]);
		foreach(k;r[i]) go(i+1,cond*k.condition,explims~k.expression);
	}
	go(0,one,[]);
	return result;
}


DExpr getLimit(DVar v,DExpr e,DExpr x,DExpr facts=one)in{assert(isInfinite(e));}body{ // TODO: handle iverson brackets in some way
	e=e.simplify(facts);
	x=x.simplify(facts);
	Case!ExpLim[] doIt(DVar v,DExpr e,DExpr x){
		if(!x.hasFreeVar(v)) return [Case!ExpLim(one,ExpLim(x,x))];
		if(x == v) return [Case!ExpLim(one,ExpLim(x,e))];
		x=x.polyNormalize(v).simplify(facts);
		if(auto p=cast(DPlus)x){
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
					if(l == dInf){ inf.insert(s.expression); continue; }
					if(l == -dInf){ minf.insert(s.expression); continue; }
					if(l.hasLimits()){ unsupported.insert(l); continue; }
					finite = finite+l;
					simplified = true;
				}
				if(!unsupported.length){
					if(!inf.length && !minf.length) return finite;
					if(inf.length && !minf.length) return dInf;
					if(minf.length && !inf.length) return -dInf;

					auto infAsymp=asymptoticNormalize(v,dPlus(inf));
					auto minfAsymp=asymptoticNormalize(v,dPlus(minf));
					if(growsFasterThanNormalized(v,infAsymp,minfAsymp))
						return dInf;
					if(growsFasterThanNormalized(v,minfAsymp,infAsymp))
						return -dInf;
				}
				if(simplified) return finite+dLim(v,e,dPlus(unsupported)+dPlus(inf)+dPlus(minf));
				return null;
			}
			ExpLim handlePlus(ExpLim[] c){ return ExpLim(p,handlePlusImpl(c)); }
			Case!ExpLim[][] r;
			foreach(s;p.summands){
				auto cur=doIt(v,e,s);
				if(!cur.length) return [];
				r~=cur;
			}
			return expandMap!handlePlus(r);
		}
		if(auto m=cast(DMult)x){
			Case!ExpLim[][] r;
			auto ow=m.splitMultAtVar(v);
			foreach(s;ow[1].factors){
				r~=doIt(v,e,s);
				if(!r[$-1].length) return [];
			}
			DExpr replaceDeltasByIvrs(DExpr e){
				auto h=e.getHoles!(x=>cast(DDelta)x,DDelta);
				auto r=h.expr;
				foreach(hole;h.holes){
					r=r.substitute(hole.var,dEqZ(hole.expr.var).simplify(facts));
				}
				return r;
			}
			// TODO: this is a hack and not generally correct:
			// (It might be fine for the cases that this is actually called with though. This should still be fixed.)
			auto owZNoDeltas=replaceDeltasByIvrs(ow[0]);
			auto owZneqZ=dNeqZ(owZNoDeltas).simplify(facts);
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
						sign ^= l == -dInf;
						inf.insert(f.expression);
						continue;
					}
					if(l == zero){
						zro.insert(f.expression);
						continue;
					}
					if(l.hasLimits()){ unsupported.insert(l); continue; }
					finite=finite*l;
					simplified=true;
				}
				//dw(v," ",inf," ",zro," ",finite," ",unsupported);
				if(!unsupported.length){
					if(!inf.length && !zro.length) return [Case!ExpLim(one,ExpLim(m,finite*ow[0]))];
					if(inf.length && !zro.length){
						auto lZ=dLtZ(finite*owZNoDeltas).simplify(facts);
						auto eqZ=dEqZ(finite*owZNoDeltas).simplify(facts);
						auto gZ=dGtZ(finite*owZNoDeltas).simplify(facts);
						Case!ExpLim[] r;
						if(lZ != zero)
							r~=Case!ExpLim(lZ,ExpLim(m,sign?dInf:-dInf));
						if(eqZ != zero)
							r~=Case!ExpLim(eqZ,ExpLim(m,zero));
						if(gZ != zero)
							r~=Case!ExpLim(gZ,ExpLim(m,sign?-dInf:dInf));
						return r;
					}
					if(zro.length && !inf.length) return [Case!ExpLim(one,ExpLim(m,zero))];
					// Bernoulli-De l'Hôpital.
					/+static int nesting = 0;
					  enum nestingLimit=5; // TODO: probably something like this is necessary.
					  ++nesting; scope(exit) --nesting;
					  if(nesting>nestingLimit) return null;+/
					if(inf.length && zro.length){
						auto f=dMult(inf), g=1/dMult(zro);
						return doIt(v,e,finite*dDiff(v,f)/dDiff(v,g));
					}
				}
				return [Case!ExpLim(owZneqZ,ExpLim(m,null))];
				// TODO: repeated simplification ugly, how to do without?
			}
			auto res=expandFlatMap!handleMult(r);
			return res;
		}
		if(auto p=cast(DPow)x){
			DExpr handlePow(DExpr l0,DExpr l1){
				if(!l0 || !l1) return null;
				l0=l0.simplify(facts);
				l1=l1.simplify(facts);
				if(l0.isInfinite()&&l1.isInfinite()){
					if(l1 == -dInf||l0 == -dInf) return null;
					return dInf;
				}
				if(l0.hasLimits()||l1.hasLimits()) return null;
				if(l0 == dE && l1 == -dInf) return zero;
				if(l1 == dInf||l1 == -dInf){
					if(l1 == dInf && dBounded!"()"(l0,mone,one).simplify(facts) == one)
						return zero;
					if(l1 == -dInf && dBounded!"[]"(l0,mone,one).simplify(facts) == zero)
						return zero;
					return null;
				}
				if(l0 == -dInf){
					if(dGeZ(l1).simplify(facts) == zero)
						return zero;
					if(auto c=l1.isInteger()){
						assert(c.c>=0 && c.c.den==1);
						if(c.c.num==0) return one;
						return c.c.num%2?-dInf:dInf;
					}
					return null;
				}
				if(l0 == dInf){
					if(dLeZ(l1).simplify(facts) == zero)
						return dInf;
					if(dGeZ(l1).simplify(facts) == zero)
						return zero;
					return null;
				}
				// pow is discontinuous at (0,0).
				auto bad=(dEqZ(l0)*dEqZ(l1)).simplify(facts);
				if(bad != zero) return null; // TODO!
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
				if(l == -dInf) return zero;
				if(l == dInf) return dΠ^^(one/2);
				return dGaussInt(l);
			}
			auto l=doIt(v,e,g.x);
			Case!ExpLim[] r;
			foreach(el;l){
				r~=Case!ExpLim(el.condition,ExpLim(g,handleGaussInt(el.expression.limit)));
			}
			return r;
		}
		if(auto g=cast(DGaussIntInv)x){
			DExpr handleGaussIntInv(DExpr l){
				if(!l) return null;
				if(l.hasLimits()) return null;
				if(l == -dInf||l == dInf) return null;
				if(l == zero) return -dInf;
				if(l == (dΠ^^(one/2)).simplify(one)) return dInf;
				return dGaussIntInv(l);
			}
			auto l=doIt(v,e,g.x);
			Case!ExpLim[] r;
			foreach(el;l){
				r~=Case!ExpLim(el.condition,ExpLim(g,handleGaussIntInv(el.expression.limit)));
			}
			return r;
		}
		if(auto ivr=cast(DIvr)x){
			DExpr handleIvr(DExpr l){
				if(!l) return null;
				if(l.hasLimits()) return null;
				if(l == -dInf||l==dInf){
					with(DIvr.Type){
						if(ivr.type==neqZ) return one;
						if(ivr.type==eqZ) return zero;
						else{
							assert(ivr.type==leZ);
							return l==-dInf?one:zero;
						}
					}
				}
				auto bad=dEqZ(l).simplify(one);
				if(bad != zero) return null; // TODO?
				return dIvr(ivr.type,l);
			}
			auto l=doIt(v,e,ivr.e);
			Case!ExpLim[] r;
			foreach(el;l){
				r~=Case!ExpLim(el.condition,ExpLim(ivr,handleIvr(el.expression.limit)));
			}
			return r;
		}
		return [];
	}
	auto k=doIt(v,e,x);
	if(!k.length) return null;
	foreach(c;k) if(c.condition!=zero && !c.expression.limit) return null;
	DExprSet summands;
	foreach(c;k){
		if(c.condition==zero||c.expression.limit==zero) continue;
		DPlus.insert(summands,c.condition*c.expression.limit);
	}
	return dPlus(summands).simplify(facts);
}
