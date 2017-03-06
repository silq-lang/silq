// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import options, dexpr, util;
import std.conv;


MapX!(Q!(DExpr,DExpr),DExpr) definiteIntegralMemo;

DExpr definiteIntegral(DExpr expr,DExpr facts=one){
	auto t=q(expr,facts);
	if(t in definiteIntegralMemo) return definiteIntegralMemo[t];
	auto r=definiteIntegralImpl(t.expand);
	definiteIntegralMemo[t]=r;
	return r;
}

private DExpr definiteIntegralImpl(DExpr expr,DExpr facts=one){
	auto var=dDeBruijnVar(1);
	auto nexpr=expr.simplify(facts.incDeBruijnVar(1,0));
	if(expr != nexpr) expr=nexpr;
	if(expr == zero) return zero;
	// TODO: move (most of) the following into the implementation of definiteIntegral
	auto ow=expr.splitMultAtVar(var);
	ow[0]=ow[0].incDeBruijnVar(-1,0).simplify(facts);
	if(ow[0] != one){
		if(auto r=definiteIntegral(ow[1],facts)){
			return (ow[0]*r).simplify(facts);
		}
		return null;
	}
	DExpr discDeltaSubstitution(){
		foreach(f;expr.factors){
			if(!f.hasFreeVar(var)) continue;
			if(auto d=cast(DDiscDelta)f){
				if(d.var == var && !d.e.hasFreeVar(var))
					return expr.withoutFactor(f).substitute(var,d.e).incDeBruijnVar(-1,0).simplify(facts);
				if(d.e == var) // TODO: more complex "inversions"?
					return expr.withoutFactor(f).substitute(var,d.var).incDeBruijnVar(-1,0).simplify(facts);
			}
		}
		return null;
	}
	if(auto r=discDeltaSubstitution())
		return r;
	DExpr deltaSubstitution(){
		// TODO: detect when to give up early?
		foreach(f;expr.factors){
			if(!f.hasFreeVar(var)) continue;
			if(auto d=cast(DDelta)f){
				if(auto r=DDelta.performSubstitution(d,expr.withoutFactor(f),false))
					return r.simplify(facts);
			}
		}
		return null;
	}
	if(auto r=deltaSubstitution()) return r;
	foreach(T;Seq!(DDiscDelta,DDelta,DIvr)){ // TODO: need to split on DIvr?
		foreach(f;expr.factors){
			if(auto p=cast(DPlus)f){
				bool check(){
					foreach(d;p.allOf!T(true))
						if(d.hasFreeVar(var))
							return true;
					return false;
				}
				if(check()){
					DExprSet works;
					DExprSet doesNotWork;
					bool simpler=false;
					foreach(k;distributeMult(p,expr.withoutFactor(f))){
						k=k.simplify(facts.incDeBruijnVar(1,0));
						auto ow=k.splitMultAtVar(var);
						ow[0]=ow[0].incDeBruijnVar(-1,0).simplify(facts);
						if(ow[0] == zero){ simpler=true; continue; }
						auto r=definiteIntegral(ow[1],facts);
						if(r){
							DPlus.insert(works,ow[0]*r);
							simpler=true;
						}else DPlus.insert(doesNotWork,k);
					}
					if(simpler){
						auto r=dPlus(works).simplify(facts);
						if(doesNotWork.length) r = r + dInt(dPlus(doesNotWork));
						return r;
					}
				}
			}
		}
	}
	nexpr=expr.linearizeConstraints!(x=>!!cast(DDelta)x)(var).simplify(facts.incDeBruijnVar(1,0)); // TODO: only linearize the first feasible delta.
	if(nexpr != expr) return definiteIntegral(nexpr,facts);
	/+if(auto r=deltaSubstitution(true))
	 return r;+/

	if(expr == one) return null; // (infinite integral)

	if(opt.integrationLevel!=IntegrationLevel.deltas){
		nexpr=expr.linearizeConstraints!(x=>!!cast(DIvr)x)(var).simplify(facts.incDeBruijnVar(1,0));
		if(nexpr != expr) return definiteIntegral(nexpr,facts);
		if(auto r=definiteIntegralContinuous(expr,facts))
			return r;
	}
	
	// pull sums out (TODO: ok?)
	/+foreach(f;expr.factors){ // TODO: fix this
		if(auto sum=cast(DSum)f){
			auto tmp1=freshVar(); // TODO: get rid of this!
			auto tmp2=freshVar(); // TODO: get rid of this!
			auto expr=sum.getExpr(tmp1)*expr.withoutFactor(f);
			return dSum(tmp1,dInt(tmp2,unbind(expr,tmp2))).simplify(facts);
		}
	}+/
	// Fubini
	DExpr fubini(){
		bool hasInt=false;
		Q!(DExpr,int) fubiRec(DExpr cur){
			// TODO: execute incDeBruijnVar only once for each subexpression
			// (such that the running time is linear in the expression size)
			DExpr r=one;
			foreach(f;cur.factors)
				if(!cast(DInt)f)
					r=r*f;
			int numVars=0;
			foreach(f;cur.factors){
				if(auto other=cast(DInt)f){
					hasInt=true;
					auto en=fubiRec(other.expr);
					r=r.incDeBruijnVar(en[1],0);
					r=r*en[0].incDeBruijnVar(numVars,en[1]);
					numVars+=en[1];
				}
			}
			return q(r,numVars+1);
		}
		auto fubiExprNumVars=fubiRec(expr);
		if(!hasInt) return null;
		auto fubiExpr=fubiExprNumVars[0], numFubiVars=fubiExprNumVars[1];
		fubiExpr=fubiExpr.incDeBruijnVar(1,0).substitute(dDeBruijnVar(numFubiVars+1),dDeBruijnVar(1)).incDeBruijnVar(-1,numFubiVars);
		auto r=definiteIntegral(fubiExpr,facts.incDeBruijnVar(numFubiVars-1,0));
		if(!r) return null;
		foreach_reverse(v;0..numFubiVars-1) r=dInt(r);
		return r.simplify(facts);
	}
	assert(var == dDeBruijnVar(1));
	if(auto r=fubini()) return r;
	if(!expr.hasFreeVar(var)) return expr.incDeBruijnVar(-1,0)*dInt(one); // (infinite integral)
	return null;
}

private DExpr definiteIntegralContinuous(DExpr expr,DExpr facts)out(res){
	version(INTEGRATION_STATS){
		integrations++;
		if(res) successfulIntegrations++;
	}
}body{
	auto var=dDeBruijnVar(1);
	// ensure integral is continuous
	foreach(f;expr.allOf!DDistApply(true))
		if(f.hasFreeVar(var)) return null;
	foreach(d;expr.allOf!DDelta(true))
		if(d.hasFreeVar(var)) return null;
	foreach(d;expr.allOf!DDiscDelta(true))
		if(d.hasFreeVar(var)) return null;

	assert(expr.factors.all!(x=>x.hasFreeVar(var)));
	assert(expr.factors.all!(x=>!cast(DDelta)x));
	auto ivrsNonIvrs=splitIvrs(expr), ivrs=ivrsNonIvrs[0], nonIvrs=ivrsNonIvrs[1];
	ivrs=ivrs.simplify(facts.incDeBruijnVar(1,0));
	nonIvrs=nonIvrs.simplify(facts.incDeBruijnVar(1,0));
	DExpr lower=null;
	DExpr upper=null;
	foreach(f;ivrs.factors){
		if(f == one) break;
		auto ivr=cast(DIvr)f;
		assert(!!ivr);
		//if(ivr.type==DIvr.Type.eqZ) return null; // TODO: eliminate eqZ early
		if(ivr.type==DIvr.Type.eqZ||ivr.type==DIvr.Type.neqZ){
			bool mustHaveZerosOfMeasureZero(){
				auto e=ivr.e;
				if(e != e.linearizeConstraints(var)) return false; // TODO: guarantee this condition
				if(e.hasAny!DIvr) return false; // TODO: make sure this cannot actually happen
				if(e.hasAny!DFloor||e.hasAny!DCeil) return false;
				if(e.hasAny!DDistApply) return false; // TODO: some proofs still possible
				return true;
			}
			if(mustHaveZerosOfMeasureZero()){
				if(ivr.type==DIvr.Type.eqZ) return zero;
				if(ivr.type==DIvr.Type.neqZ) continue;
			}else return null;
		}
		assert(ivr.type!=DIvr.Type.lZ);
		DExpr bound;
		auto status=ivr.getBoundForVar(var,bound);
		if(bound) bound=bound.incDeBruijnVar(-1,0);
		final switch(status) with(BoundStatus){
			case fail:
				SolutionInfo info;
				SolUse usage={caseSplit:true,bound:true};
				bound=solveFor(ivr.e,var,zero,usage,info);
				if(!bound) return null;
				foreach(ref x;info.caseSplits) x.constraint=x.constraint.incDeBruijnVar(-1,0);
				import std.conv: text;
				// TODO: fuse some of this with DDelta.performSubstitution?
				auto constraints=one;
				foreach(ref x;info.caseSplits)
					constraints=constraints*dIvr(DIvr.Type.neqZ,x.constraint);
				//constraints=constraints.simplify(one);
				auto rest=expr.withoutFactor(ivr);
				auto r=constraints == zero?zero:
					constraints*(dIntSmp(dIvr(DIvr.Type.leZ,var-bound)*
					                     dIvr(DIvr.type.leZ,info.bound.isLower)*rest,one)
					             +dIntSmp(dIvr(DIvr.Type.lZ,bound-var)*
					                      dIvr(DIvr.type.leZ,-info.bound.isLower)*rest,one));
				foreach(ref x;info.caseSplits){
					auto curConstr=constraints.withoutFactor(dIvr(DIvr.Type.neqZ,x.constraint));
					r=r+curConstr*dIvr(DIvr.Type.eqZ,x.constraint)*
						dIntSmp(rest*dIvr(DIvr.Type.leZ,x.expression),one);
				}
				return r.simplify(facts);
			case lowerBound:
				if(lower) lower=dMax(lower,bound);
				else lower=bound;
				lower=lower.simplify(facts);
				break;
			case upperBound:
				if(upper) upper=dMin(upper,bound);
				else upper=bound;
				upper=upper.simplify(facts);
				break;
			case equal: assert(0);
			}
	}
	if(auto r=tryIntegrate(nonIvrs,lower,upper,ivrs))
		return r.simplify(facts);
	return null;
}

struct AntiD{ // TODO: is this even worth the hassle?
	DExpr antiderivative;
	DExpr atMinusInfinity;
	DExpr atInfinity;
	T opCast(T:bool)(){ return !!antiderivative; }
	AntiD opBinary(string op)(DExpr e){
		return AntiD(antiderivative.maybe!(a=>mixin(`a `~op~` e`)),
		             atMinusInfinity.maybe!(a=>mixin(`a `~op~` e`)),
		             atInfinity.maybe!(a=>mixin(`a `~op~` e`)));
	}
	AntiD opBinaryRight(string op)(DExpr e){
		return AntiD(antiderivative.maybe!(a=>mixin(`e `~op~` a`)),
		             atMinusInfinity.maybe!(a=>mixin(`e `~op~` a`)),
		             atInfinity.maybe!(a=>mixin(`e `~op~` a`)));
	}
	AntiD opBinary(string op)(AntiD e){
		DExpr f(DExpr x,DExpr y){
			return x.maybe!(a=>y.maybe!(b=>mixin(`a `~op~` b`)));
		}
		return AntiD(f(antiderivative,e.antiderivative));
	}
}


AntiD tryGetAntiderivative(DExpr nonIvrs,DExpr ivrs){
	auto var=dDeBruijnVar(1);
	auto ow=nonIvrs.splitMultAtVar(var);
	ow[0]=ow[0].simplify(one);
	if(ow[0] != one){
		return ow[0]*tryGetAntiderivative(ow[1].simplify(one),ivrs);
	}

	static DExpr safeLog(DExpr e){ // TODO: integrating 1/x over 0 diverges (not a problem for integrals occurring in the analysis)
		return dLog(e)*dIvr(DIvr.Type.lZ,-e)
			+ dLog(-e)*dIvr(DIvr.Type.lZ,e);
	}
	if(auto p=cast(DPow)nonIvrs){
		if(!p.operands[1].hasFreeVar(var)){
			if(p.operands[0] == var){
				// constraint: lower && upper
				return AntiD((safeLog(var)*
							  dIvr(DIvr.Type.eqZ,p.operands[1]+1)
							  +(var^^(p.operands[1]+1))/(p.operands[1]+1)*
							  dIvr(DIvr.Type.neqZ,p.operands[1]+1)).simplify(one));
			}
			auto ba=p.operands[0].asLinearFunctionIn(var);
			auto b=ba[0],a=ba[1];
			if(a && b){
				return AntiD(((safeLog(p.operands[0])*
				               dIvr(DIvr.Type.eqZ,p.operands[1]+1)
				              +(p.operands[0]^^(p.operands[1]+1))/(p.operands[1]+1)*
				               dIvr(DIvr.Type.neqZ,p.operands[1]+1))/a).simplify(one));
			}
		}
		if(!p.operands[0].hasFreeVar(var)){
			auto k=safeLog(p.operands[0])*p.operands[1];
			// need to integrate e^^(k(x)).
			auto dk=dDiff(var,k);
			if(!dk.hasFreeVar(var)){
				DExpr lo=null,up=null;
				if(dIvr(DIvr.Type.leZ,k).simplify(one) == one){
					up=zero;
				}
				return dIvr(DIvr.Type.neqZ,dk)*AntiD(dE^^k/dk,lo,up);
				// + dIvr(DIvr.Type.eqZ,dk)*var*dE^^(k-var*dk);
				// TODO: BUG: this is necessary. Need to fix limit code such that it can handle this.
			}
		}
	}
	if(nonIvrs == one) return AntiD(var); // constraint: lower && upper
	if(auto poly=nonIvrs.asPolynomialIn(var)){
		DExprSet s;
		foreach(i,coeff;poly.coefficients){
			assert(i<size_t.max);
			DPlus.insert(s,coeff*var^^(i+1)/(i+1));
		}
		// constraint: lower && upper
		return AntiD(dPlus(s));
	}
	if(auto p=cast(DLog)nonIvrs){
		auto ba=p.e.asLinearFunctionIn(var);
		auto b=ba[0],a=ba[1];
		if(a && b){
			static DExpr logIntegral(DVar x,DExpr a, DExpr b){
				return (x+b/a)*safeLog(a*x+b)-x;
			}
			return AntiD(dIvr(DIvr.Type.neqZ,a)*logIntegral(var,a,b)+
			             dIvr(DIvr.Type.eqZ,a)*var*dLog(b));
		}
	}
	// integrate log(x)ʸ/x to log(x)ʸ⁺¹/(y+1)
	if(auto p=cast(DMult)nonIvrs){
		auto inv=1/var;
		if(p.hasFactor(inv)){
			auto without=p.withoutFactor(inv);
			DExpr y=null;
			// TODO: linear functions of var
			if(auto l=cast(DLog)without){
				if(l.e == var) y=one;
			}else if(auto pw=cast(DPow)without){
				if(auto l=cast(DLog)pw.operands[0])
					if(l.e == var) y=pw.operands[1];
			}
			if(y !is null && !y.hasFreeVar(var)){
				return AntiD(
					dIvr(DIvr.Type.eqZ,y+1)*safeLog(safeLog(var))+
					dIvr(DIvr.Type.neqZ,y+1)*safeLog(var)^^(y+1)/(y+1));
			}
		}
	}
	// integrate log to some positive integer power
	if(auto p=cast(DPow)nonIvrs){
		if(auto l=cast(DLog)p.operands[0]){
			auto ba=l.e.asLinearFunctionIn(var);
			auto b=ba[0],a=ba[1];
			if(a && b){
				if(auto n=p.operands[1].isInteger()){
					DExpr dInGamma(DExpr a,DExpr z){
						a=a.incDeBruijnVar(1,0), z=z.incDeBruijnVar(1,0);
						auto t=dDeBruijnVar(1);
						return dIntSmp(t^^(a-1)*dE^^(-t)*dIvr(DIvr.type.leZ,z-t),one);
					}
					if(n.c>0)
						return AntiD(dIvr(DIvr.Type.neqZ,a*var+b)*mone^^n*dInGamma(n+1,-dLog(a*var+b))/a);
				}
			}
		}
	}
	AntiD gaussianIntegral(DVar v,DExpr e){
		// detect e^^(-a*x^^2+b*x+c), and integrate to e^^(b^^2/4a+c)*(pi/a)^^(1/2).
		// TODO: this currently assumes that a≥0. (The produced expressions are still formally correct if √(-1)=i)
		auto p=cast(DPow)e;
		if(!p) return AntiD();
		if(!cast(DE)p.operands[0]) return AntiD();
		auto q=p.operands[1].asPolynomialIn(v,2);
		if(!q.initialized) return AntiD();
		if(q.degree!=2) return AntiD();
		auto qc=q.coefficients;
		auto a=-qc.get(2,zero),b=qc.get(1,zero),c=qc.get(0,zero);
		// -a(x-b/2a)²=-ax²+bx-b²/4a
		// -ax²+bx+c =-a(x-b/2a)²+b²/4a+c
		// -ax²+bx+c =-(√(a)x-b/2√a)²+b²/4a+c
		// e^(-ax²+bx+c) = e^(b²/4a+c)·e^-(√(a)x-b/2√a)²
		// ∫dx e^(-ax²+bx+c)[l≤x≤r] = e^(b²/4a+c)·∫dx(e^-(√(a)x-b/(2√a))²[l≤x≤r]
		// = e^(b²/4a+c)·⅟√a∫dx(e^-x²)[l≤x/√(a)+b/(2a)≤r]
		// = e^(b²/4a+c)·⅟√a∫dx(e^-x²)[l*(√(a))-b/(2√(a))≤x≤r*(√(a))-b/(2√(a))]
		auto fac=dE^^(b^^2/(4*a)+c)*(one/a)^^(one/2);
		DExpr transform(DExpr x){
			if(x == dInf || x == -dInf) return x;
			auto sqrta=a^^(one/2);
			return sqrta*x-b/(2*sqrta);
		}
		// constraints: none!
		return dIvr(DIvr.Type.neqZ,a)*AntiD(fac*dGaussInt(transform(v)),zero,fac*dΠ^^(one/2));
			//+ dIvr(DIvr.Type.eqZ,a)*tryGetAntiderivative(v,dE^^(b*v+c),ivrs);
			// TODO: BUG: this is necessary. Need to fix limit code such that it can handle this.
	}
	auto gauss=gaussianIntegral(var,nonIvrs);
	if(gauss.antiderivative) return gauss;
	// TODO: this is just a list of special cases. Generalize!
	AntiD doubleGaussIntegral(DVar var,DExpr e){
		auto gi=cast(DGaussInt)e;
		if(!gi) return AntiD();
		auto q=gi.x.asPolynomialIn(var,1);
		if(!q.initialized) return AntiD();
		auto a=q.coefficients.get(1,zero),b=q.coefficients.get(0,zero);
		if(a == zero) return AntiD(); // TODO: make "dynamic"
		static DExpr primitive(DExpr e){
			if(e == -dInf) return zero;
			return dGaussInt(e)*e+dE^^(-e^^2)/2;
		}
		auto fac=one/a;
		// constraints: upper
		return AntiD(fac*primitive(gi.x),zero);
	}
	auto dgauss=doubleGaussIntegral(var,nonIvrs);
	if(dgauss.antiderivative) return dgauss;
	AntiD gaussIntTimesGauss(DVar var,DExpr e){
		//∫dx (d/dx)⁻¹[e^(-x²)](g(x))·f(x) = (d/dx)⁻¹[e^(-x²)](g(x))·∫dx f(x) - ∫dx (g'(x)e^(-g(x)²)·∫dx f(x))
		auto m=cast(DMult)e;
		if(!m) return AntiD();
		DGaussInt gaussFact=null;
		foreach(f;m.factors){
			if(auto g=cast(DGaussInt)f){
				gaussFact=g;
				break;
			}
		}
		if(!gaussFact) return AntiD();
		auto rest=m.withoutFactor(gaussFact);
		auto gauss=dDiff(var,gaussFact).simplify(one);
		auto intRest=tryGetAntiderivative(rest,ivrs);
		if(!intRest.antiderivative) return AntiD();
		if(e == (gauss*intRest.antiderivative).simplify(one)){ // TODO: handle all cases
			return AntiD(gaussFact*intRest.antiderivative/2);
		}
		return AntiD();
	}
	auto dgaussTG=gaussIntTimesGauss(var,nonIvrs);
	if(dgaussTG.antiderivative) return dgaussTG;
	// partial integration for polynomials
	AntiD partiallyIntegratePolynomials(DVar var,DExpr e){ // TODO: is this well founded?
		static MapX!(Q!(DVar,DExpr),AntiD) memo;
		if(q(var,e) in memo) return memo[q(var,e)];
		auto token=freshVar("τ"); // TODO: make sure this does not create a GC issue.
		memo[q(var,e)]=AntiD(token); // TODO :get rid of AntiD
		auto fail(){
			memo[q(var,e)]=AntiD();
			return AntiD();
		}
		
		auto m=cast(DMult)e;
		if(!m) return fail();
		DExpr polyFact=null;
		foreach(f;m.factors){
			if(auto p=cast(DPow)f){
				if(p.operands[0] == var){
					if(auto c=p.operands[1].isInteger()){
						if(c.c>0){ polyFact=p; break; }
					}
				}
			}
			if(f == var){ polyFact=f; break; }
		}
		if(!polyFact) return fail();
		auto rest=m.withoutFactor(polyFact);
		auto intRest=tryGetAntiderivative(rest,ivrs).antiderivative;
		if(!intRest) return fail();
		auto diffPoly=dDiff(var,polyFact);
		auto diffRest=(diffPoly*intRest).polyNormalize(var).simplify(one);
		auto intDiffPolyIntRest=tryGetAntiderivative(diffRest,ivrs).antiderivative;
		if(!intDiffPolyIntRest) return fail();
		auto r=AntiD(polyFact*intRest-intDiffPolyIntRest);
		if(!r.antiderivative.hasFreeVar(token)){ memo[q(var,e)]=r; return r; }
		if(auto s=(r.antiderivative-token).simplify(one).solveFor(token)){
			r=AntiD(s);
			memo[q(var,e)]=r;
			return r;
		}
		return fail();
	}
	auto partPoly=partiallyIntegratePolynomials(var,nonIvrs);
	if(partPoly.antiderivative) return partPoly;

	// x = ∫ u'v
	// (uv)' = uv'+u'v
	// ∫(uv)' = ∫uv'+∫u'v
	// uv+C = ∫uv'+∫u'v
	// 
	//auto factors=splitIntegrableFactor(nonIvrs);
	//dw(factors[1]);
	//dw("!! ",dDiff(var,factors[1]));

	if(auto p=cast(DPlus)nonIvrs.polyNormalize(var)){
		AntiD r=AntiD(zero,zero,zero);
		foreach(s;p.summands){
			r=r+tryGetAntiderivative(s,ivrs);
			if(!r) return AntiD();
		}
		return r;
	}

	return AntiD(); // no simpler expression available
}

MapX!(Q!(DExpr,DExpr,DExpr,DExpr),DExpr) tryIntegrateMemo;

DExpr tryIntegrate(DExpr nonIvrs,DExpr lower,DExpr upper,DExpr ivrs){
	auto t=q(nonIvrs,lower,upper,ivrs);
	if(t in tryIntegrateMemo) return tryIntegrateMemo[t];
	auto r=tryIntegrateImpl(t.expand);
	tryIntegrateMemo[t]=r;
	return r;
}

private DExpr tryIntegrateImpl(DExpr nonIvrs,DExpr lower,DExpr upper,DExpr ivrs){
	auto var=dDeBruijnVar(1);
	// TODO: add better approach for antiderivatives	
	auto antid=tryGetAntiderivative(nonIvrs,ivrs);
	//dw(var," ",nonIvrs," ",ivrs);
	//dw(antid.antiderivative);
	//dw(dDiff(var,antid.antiderivative.simplify(one)).simplify(one));
	if(auto anti=antid.antiderivative){
		//dw(anti.substitute(var,lower).simplify(one)," ",lower," ",upper);
		auto lo=lower?unbind(anti,lower):
			antid.atMinusInfinity.maybe!(x=>x.incDeBruijnVar(-1,0));
		auto up=upper?unbind(anti,upper):
			antid.atInfinity.maybe!(x=>x.incDeBruijnVar(-1,0));
		if(lower&&upper){
			//dw("??! ",dDiff(var,anti).simplify(one));
			//dw(anti.substitute(var,upper).simplify(one));
			//dw(anti.substitute(var,lower).simplify(one));
			return dIvr(DIvr.Type.leZ,lower-upper)*(up-lo);
		}
		if(!lo) lo=dLimSmp(var,-dInf,anti,one).incDeBruijnVar(-1,0);
		if(!up) up=dLimSmp(var,dInf,anti,one).incDeBruijnVar(-1,0);
		if(lo.isInfinite() || up.isInfinite()) return null;
		if(lo.hasLimits() || up.hasLimits()) return null;
		return up-lo;
	}
	if(auto p=cast(DPlus)nonIvrs.polyNormalize(var)){
		DExprSet works;
		DExprSet doesNotWork;
		bool ok=true;
		foreach(s;p.summands){
			auto ow=s.splitMultAtVar(var);
			ow[0]=ow[0].incDeBruijnVar(-1,0).simplify(one);
			auto t=tryIntegrate(ow[1],lower,upper,ivrs);
			if(t) DPlus.insert(works,ow[0]*t);
			else DPlus.insert(doesNotWork,s);
		}
		if(works.length) return dPlus(works)+dInt((dPlus(doesNotWork)*ivrs));
	}//else dw("fail: ","Integrate[",nonIvrs.toString(Format.mathematica),",",var.toString(Format.mathematica),"]");
	return null; // no simpler expression available
}
