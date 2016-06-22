import dexpr, util;


MapX!(Q!(DVar,DExpr,DExpr),DExpr) definiteIntegralMemo;

DExpr definiteIntegral(DVar var,DExpr expr,DExpr facts=one){
	auto t=q(var,expr,facts);
	if(t in definiteIntegralMemo) return definiteIntegralMemo[t];
	auto r=definiteIntegralImpl(t.expand);
	definiteIntegralMemo[t]=r;
	return r;
}

private DExpr definiteIntegralImpl(DVar var,DExpr expr,DExpr facts=one){
	auto nexpr=expr.simplify(facts);
	if(expr !is nexpr) expr=nexpr;
	if(expr is zero) return zero;
	if(cast(DContextVars)var) return null;
	// TODO: move (most of) the following into the implementation of definiteIntegral
	auto ow=expr.splitMultAtVar(var);
	ow[0]=ow[0].simplify(facts);
	if(ow[0] !is one){
		if(auto r=definiteIntegral(var,ow[1],facts))
			return (ow[0]*r).simplify(facts);
		return null;
	}
	DExpr discDeltaSubstitution(){
		foreach(f;expr.factors){
			if(!f.hasFreeVar(var)) continue;
			if(auto d=cast(DDiscDelta)f){
				if(d.var !is var) continue;
				return expr.withoutFactor(f).substitute(var,d.e).simplify(facts);
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
				if(auto r=DDelta.performSubstitution(var,d,expr.withoutFactor(f),false))
					return r.simplify(facts);
			}
		}
		return null;
	}
	if(auto r=deltaSubstitution())
		return r;
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
						k=k.simplify(facts);
						auto ow=k.splitMultAtVar(var);
						auto r=definiteIntegral(var,ow[1],facts);
						if(r){
							DPlus.insert(works,ow[0]*r);
							simpler=true;
						}else DPlus.insert(doesNotWork,k);
					}
					if(simpler){
						auto r=dPlus(works).simplify(facts);
						if(doesNotWork.length) r = r + dInt(var,dPlus(doesNotWork));
						return r;
					}
				}
			}
		}
	}
	nexpr=expr.linearizeConstraints!(x=>!!cast(DDelta)x)(var).simplify(facts); // TODO: only linearize the first feasible delta.
	if(nexpr !is expr) return definiteIntegral(var,nexpr,facts);
	/+if(auto r=deltaSubstitution(true))
	 return r;+/

	if(expr is one) return null; // (infinite integral)

	if(simplification!=Simpl.deltas){
		nexpr=expr.linearizeConstraints!(x=>!!cast(DIvr)x)(var).simplify(facts);
		if(nexpr !is expr) return definiteIntegral(var,nexpr,facts);
		if(auto r=definiteIntegralContinuous(var,expr,facts))
			return r;
	}
	
	// pull sums out (TODO: ok?)
	foreach(f;expr.factors){
		if(auto sum=cast(DSum)f){
			auto tmp1=freshVar(); // TODO: get rid of this!
			auto tmp2=freshVar(); // TODO: get rid of this!
			auto expr=sum.getExpr(tmp1)*expr.withoutFactor(f);
			return dSumSmp(tmp1,dIntSmp(tmp2,expr.substitute(var,tmp2),one),one);
		}
	}
	// Fubini
	DExpr fubini(){
		foreach(f;expr.allOf!DFun(true)) // TODO: constrain less
			return null;
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
		auto fubiExpr=fubiExprNumVars[0], numFubiVars=fubiExprNumVars[1];
		fubiExpr=fubiExpr.incDeBruijnVar(1,0).substitute(dDeBruijnVar(numFubiVars+1),dDeBruijnVar(1));
		if(hasInt) if(auto r=definiteIntegral(var,fubiExpr)){
			r=r.simplify(facts);
			foreach_reverse(v;0..numFubiVars-1) r=dInt(r);
			return r.simplify(facts);
		}
		return null;
	}
	assert(var is dDeBruijnVar(1));
	if(auto r=fubini()) return r;
	if(!expr.hasFreeVar(var)) return expr*dInt(var,one); // (infinite integral)
	return null;
}

private DExpr definiteIntegralContinuous(DVar var,DExpr expr,DExpr facts)out(res){
	version(INTEGRATION_STATS){
		integrations++;
		if(res) successfulIntegrations++;
	}
}body{
	// ensure integral is continuous
	foreach(f;expr.allOf!DFun(true))
		if(f.hasFreeVar(var)) return null;
	foreach(d;expr.allOf!DDelta(true))
		if(d.hasFreeVar(var)) return null;
	foreach(d;expr.allOf!DDiscDelta(true))
		if(d.hasFreeVar(var)) return null;

	// TODO: keep ivrs and nonIvrs separate in DMult
	DExpr ivrs=one;
	DExpr nonIvrs=one;
	foreach(f;expr.factors){
		assert(f.hasFreeVar(var));
		assert(!cast(DDelta)f);
		if(cast(DIvr)f) ivrs=ivrs*f;
		else nonIvrs=nonIvrs*f;
	}
	ivrs=ivrs.simplify(facts);
	nonIvrs=nonIvrs.simplify(facts);
	DExpr lower=null;
	DExpr upper=null;
	foreach(f;ivrs.factors){
		if(f is one) break;
		auto ivr=cast(DIvr)f;
		assert(!!ivr);
		//if(ivr.type==DIvr.Type.eqZ) return null; // TODO: eliminate eqZ early
		if(ivr.type==DIvr.Type.eqZ||ivr.type==DIvr.Type.neqZ){
			bool mustHaveZerosOfMeasureZero(){
				auto e=ivr.e;
				if(e !is e.linearizeConstraints(var)) return false; // TODO: guarantee this condition
				if(e.hasAny!DIvr) return false; // TODO: make sure this cannot actually happen
				if(e.hasAny!DFun) return false; // TODO: some proofs still possible
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
		final switch(status) with(BoundStatus){
			case fail:
				SolutionInfo info;
				SolUse usage={caseSplit:true,bound:true};
				bound=solveFor(ivr.e,var,zero,usage,info);
				if(!bound) return null;
				import std.conv: text;
				// TODO: fuse some of this with DDelta.performSubstitution?
				auto constraints=one;
				foreach(ref x;info.caseSplits)
					constraints=constraints*dIvr(DIvr.Type.neqZ,x.constraint);
				//constraints=constraints.simplify(one);
				auto rest=expr.withoutFactor(ivr);
				auto r=constraints is zero?zero:
					constraints*(dIntSmp(var,dIvr(DIvr.Type.leZ,var-bound)*
										 dIvr(DIvr.type.leZ,info.bound.isLower)*rest,one)
								 +dIntSmp(var,dIvr(DIvr.Type.lZ,bound-var)*
										  dIvr(DIvr.type.leZ,-info.bound.isLower)*rest,one));
				foreach(ref x;info.caseSplits){
					auto curConstr=constraints.withoutFactor(dIvr(DIvr.Type.neqZ,x.constraint));
					r=r+curConstr*dIvr(DIvr.Type.eqZ,x.constraint)*
						dIntSmp(var,rest*dIvr(DIvr.Type.leZ,x.expression),one);
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
	if(auto r=tryIntegrate(var,nonIvrs,lower,upper,ivrs))
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


AntiD tryGetAntiderivative(DVar var,DExpr nonIvrs,DExpr ivrs){
	auto ow=nonIvrs.splitMultAtVar(var);
	ow[0]=ow[0].simplify(one);
	if(ow[0] !is one){
		return ow[0]*tryGetAntiderivative(var,ow[1].simplify(one),ivrs);
	}

	static DExpr safeLog(DExpr e){ // TODO: integrating 1/x over 0 diverges (not a problem for integrals occurring in the analysis)
		return dLog(e)*dIvr(DIvr.Type.lZ,-e)
			+ dLog(-e)*dIvr(DIvr.Type.lZ,e);
	}
	if(auto p=cast(DPow)nonIvrs){
		if(p.operands[0] is var && !p.operands[1].hasFreeVar(var)){
			// constraint: lower && upper
			return AntiD((safeLog(var)*
				 dIvr(DIvr.Type.eqZ,p.operands[1]+1)
				 +(var^^(p.operands[1]+1))/(p.operands[1]+1)*
						  dIvr(DIvr.Type.neqZ,p.operands[1]+1)).simplify(one));
		}
		if(!p.operands[0].hasFreeVar(var)){
			auto k=safeLog(p.operands[0])*p.operands[1];
			// need to integrate e^^(k(x)).
			auto dk=dDiff(var,k);
			if(!dk.hasFreeVar(var)){
				DExpr lo=null,up=null;
				if(dIvr(DIvr.Type.leZ,k).simplify(one) is one){
					up=zero;
				}
				return dIvr(DIvr.Type.neqZ,dk)*AntiD(dE^^k/dk,lo,up);
					// + dIvr(DIvr.Type.eqZ,dk)*var*dE^^(k-var*dk);
					// TODO: BUG: this is necessary. Need to fix limit code such that it can handle this.
			}
		}
	}
	if(nonIvrs is one) return AntiD(var); // constraint: lower && upper
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
				if(l.e is var) y=one;
			}else if(auto pw=cast(DPow)without){
				if(auto l=cast(DLog)pw.operands[0])
					if(l.e is var) y=pw.operands[1];
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
				if(auto n=cast(Dℕ)p.operands[1]){
					DExpr dInGamma(DExpr a,DExpr z){
						auto t=freshVar(); // TODO: get rid of this
						return dIntSmp(t,t^^(a-1)*dE^^(-t)*dIvr(DIvr.type.leZ,z-t),one);
					}
					if(n.c>0)
						return AntiD(dIvr(DIvr.Type.neqZ,a*var+b)*(-mone)^^n*dInGamma(n+1,-dLog(a*var+b))/a);
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
			if(x is dInf || x is -dInf) return x;
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
		if(a is zero) return AntiD(); // TODO: make "dynamic"
		static DExpr primitive(DExpr e){
			if(e is -dInf) return zero;
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
		auto intRest=tryGetAntiderivative(var,rest,ivrs);
		if(!intRest.antiderivative) return AntiD();
		if(e is (gauss*intRest.antiderivative).simplify(one)){ // TODO: handle all cases
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
				if(p.operands[0] is var){
					if(auto c=cast(Dℕ)p.operands[1]){
						if(c.c>0){ polyFact=p; break; }
					}
				}
			}
			if(f is var){ polyFact=f; break; }
		}
		if(!polyFact) return fail();
		auto rest=m.withoutFactor(polyFact);
		auto intRest=tryGetAntiderivative(var,rest,ivrs).antiderivative;
		if(!intRest) return fail();
		auto diffPoly=dDiff(var,polyFact);
		auto diffRest=(diffPoly*intRest).polyNormalize(var).simplify(one);
		auto intDiffPolyIntRest=tryGetAntiderivative(var,diffRest,ivrs).antiderivative;
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
			r=r+tryGetAntiderivative(var,s,ivrs);
			if(!r) return AntiD();
		}
		return r;
	}

	return AntiD(); // no simpler expression available
}

MapX!(Q!(DVar,DExpr,DExpr,DExpr,DExpr),DExpr) tryIntegrateMemo;

DExpr tryIntegrate(DVar var,DExpr nonIvrs,DExpr lower,DExpr upper,DExpr ivrs){
	auto t=q(var,nonIvrs,lower,upper,ivrs);
	if(t in tryIntegrateMemo) return tryIntegrateMemo[t];
	auto r=tryIntegrateImpl(t.expand);
	tryIntegrateMemo[t]=r;
	return r;
}

private DExpr tryIntegrateImpl(DVar var,DExpr nonIvrs,DExpr lower,DExpr upper,DExpr ivrs){
	// TODO: add better approach for antiderivatives	
	auto lowLeUp(){ return lower&&upper?dIvr(DIvr.Type.leZ,lower-upper):one; }
	auto antid=tryGetAntiderivative(var,nonIvrs,ivrs);
	//dw(var," ",nonIvrs," ",ivrs);
	//dw(antid.antiderivative);
	//dw(dDiff(var,antid.antiderivative.simplify(one)).simplify(one));
	if(auto anti=antid.antiderivative){
		//dw(anti.substitute(var,lower).simplify(one)," ",lower," ",upper);
		if(lower&&upper){
			//dw("??! ",dDiff(var,anti).simplify(one));
			//dw(anti.substitute(var,upper).simplify(one));
			//dw(anti.substitute(var,lower).simplify(one));
			return lowLeUp()*(anti.substitute(var,upper)
							  -anti.substitute(var,lower));
		}
		auto lo=lower?anti.substitute(var,lower):antid.atMinusInfinity;
		auto up=upper?anti.substitute(var,upper):antid.atInfinity;
		if(!lo) lo=dLimSmp(var,-dInf,anti,one);
		if(!up) up=dLimSmp(var,dInf,anti,one);
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
			ow[0]=ow[0].simplify(one);
			auto t=tryIntegrate(var,ow[1],lower,upper,ivrs);
			if(t) DPlus.insert(works,ow[0]*t);
			else DPlus.insert(doesNotWork,s);
		}
		if(works.length) return dPlus(works)+dInt(var,(dPlus(doesNotWork)*ivrs));
	}//else dw("fail: ","Integrate[",nonIvrs.toString(Format.mathematica),",",var.toString(Format.mathematica),"]");
	return null; // no simpler expression available
}
