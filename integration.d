import dexpr, util;

DExpr definiteIntegral(DVar var,DExpr expr)out(res){
	version(INTEGRATION_STATS){
		integrations++;
		if(res) successfulIntegrations++;
	}
}body{
	// TODO: explicit antiderivative (d/dx)⁻¹
	// eg. the full antiderivative e^^(-a*x^^2+b*x) is given by:
	// e^^(b^^2/4a)*(d/dx)⁻¹(e^^(-x^^2))[(b-2*a*x)/2*a^^(1/2)]/a^^(1/2)
	// TODO: keep ivrs and nonIvrs separate in DMult
	DExpr ivrs=one;
	DExpr nonIvrs=one;
	if(expr.hasAny!DFun) return null;
	foreach(f;expr.factors){
		assert(f.hasFreeVar(var));
		if(cast(DIvr)f) ivrs=ivrs*f;
		else if(cast(DDelta)f) return null;
		else nonIvrs=nonIvrs*f;
	}
	DExpr lower=null;
	DExpr upper=null;
	foreach(f;ivrs.factors){
		if(f is one) break;
		auto ivr=cast(DIvr)f;
		assert(!!ivr);
		//if(ivr.type==DIvr.Type.eqZ) return null; // TODO: eliminate eqZ early
		if(ivr.type==DIvr.Type.eqZ||ivr.type==DIvr.Type.neqZ){
			if(ivr.e.hasZerosOfMeasureZero()){
				if(ivr.type==DIvr.Type.eqZ) return zero;
				if(ivr.type==DIvr.Type.neqZ) continue;
			}
		}
		assert(ivr.type!=DIvr.Type.lZ);
		DExpr bound;
		auto status=ivr.getBoundForVar(var,bound);
		final switch(status) with(BoundStatus){
		case fail:
			 // TODO: non-linear bounds
			SolutionInfo info;
			SolUse usage={caseSplit:true,bound:true};
			bound=solveFor(ivr.e,var,zero,usage,info);
			if(!bound) return null;
			assert(info.caseSplits.length||info.bound.isLower!is mone&&info.bound.isLower!is one);
			// TODO: fuse some of this with DDelta.performSubstitution?
			auto constraints=one;
			foreach(ref x;info.caseSplits)
				constraints=constraints*dIvr(DIvr.Type.neqZ,x.constraint);
			auto rest=expr.withoutFactor(ivr);
			auto r=constraints is zero?zero:
				constraints*(dIntSmp(var,dIvr(DIvr.Type.leZ,var-bound)*
								  dIvr(DIvr.type.leZ,info.bound.isLower)*rest)
							 +dIntSmp(var,dIvr(DIvr.Type.lZ,bound-var)*
								   dIvr(DIvr.type.leZ,-info.bound.isLower)*rest));
			foreach(ref x;info.caseSplits){
				auto curConstr=constraints.withoutFactor(dIvr(DIvr.Type.neqZ,x.constraint));
				r=r+curConstr*dIvr(DIvr.Type.eqZ,x.constraint)*
					dIntSmp(var,rest*dIvr(DIvr.Type.leZ,x.expression));
			}
			return r;
		case lowerBound:
			if(lower) lower=dMax(lower,bound);
			else lower=bound;
			break;
		case upperBound:
			if(upper) upper=dMin(upper,bound);
			else upper=bound;
			break;
		}
	}
	return tryIntegrate(var,nonIvrs,lower,upper,ivrs);
}

struct AntiD{
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
	if(ow[0] !is one){
		return ow[0]*tryGetAntiderivative(var,ow[1],ivrs);
	}

	static DExpr safeLog(DExpr e){ // TODO: ok?
		return dLog(e)*dIvr(DIvr.Type.neqZ,e);
	}
	if(auto p=cast(DPow)nonIvrs){
		if(p.operands[0] is var && !p.operands[1].hasFreeVar(var)){
			// constraint: lower && upper
			return AntiD((safeLog(var)*
				 dIvr(DIvr.Type.eqZ,p.operands[1]+1)
				 +(var^^(p.operands[1]+1))/(p.operands[1]+1)*
						  dIvr(DIvr.Type.neqZ,p.operands[1]+1)));
		}
		if(!p.operands[0].hasFreeVar(var)){
			auto k=dLog(p.operands[0])*p.operands[1];
			// need to integrate e^^(k(x)).
			auto dk=dDiff(var,k);
			if(dk!is zero && !dk.hasFreeVar(var)){
				DExpr lo=null,up=null;
				if(dIvr(DIvr.Type.leZ,k).simplify(ivrs) is one){
					up=zero;
				}
				return AntiD(dE^^k/dk,lo,up);
			}
		}
	}
	if(nonIvrs is one) return AntiD(var); // constraint: lower && upper
	if(auto poly=nonIvrs.asPolynomialIn(var)){ // TODO: this can be wasteful sometimes
		DExprSet s;
		foreach(i,coeff;poly.coefficients){
			assert(i<size_t.max);
			DPlus.insert(s,coeff*var^^(i+1)/(i+1));
		}
		// constraint: lower && upper
		return AntiD(dPlus(s));
	}
	if(auto p=cast(DLog)nonIvrs){
		if(p.e is var){
			static DExpr logIntegral(DExpr e){
				return e*safeLog(e)-e;
			}
			// constraint: lower && upper
			return AntiD(logIntegral(var));
		}
	}
	AntiD gaussianIntegral(DVar v,DExpr e){
		// detect e^^(-a*x^^2+b*x+c), and integrate to e^^(b^^2/4a+c)*(pi/a)^^(1/2).
		// TODO: this assumes that a≥0!
		auto p=cast(DPow)e;
		if(!p) return AntiD();
		if(!cast(DE)p.operands[0]) return AntiD();
		auto q=p.operands[1].asPolynomialIn(v,2);
		if(!q.initialized) return AntiD();
		if(q.coefficients.length!=3) return AntiD();
		auto qc=q.coefficients;
		auto a=-qc[2],b=qc[1],c=qc[0];
		// if(couldBeZero(a)) return null; // TODO: this is what should be done!
		if(a is null) return AntiD(); // TODO: it could still be zero!
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
		return AntiD(fac*dGaussInt(transform(var)),zero,fac*dΠ^^(one/2));
	}
	auto gauss=gaussianIntegral(var,nonIvrs);
	if(gauss.antiderivative) return gauss;
	// TODO: this is just a list of special cases. Generalize!
	AntiD doubleGaussIntegral(DVar var,DExpr e){
		auto gi=cast(DGaussInt)e;
		if(!gi) return AntiD();
		auto q=gi.x.asPolynomialIn(var,1);
		if(!q.initialized) return AntiD();
		auto a=q.coefficients[1],b=q.coefficients[0];
		if(a is zero) return AntiD();
		static DExpr primitive(DExpr e){
			if(e is -dInf) return zero;
			return dGaussInt(e)*e-dE^^(-e^^2);
		}
		DExpr transform(DExpr x){
			return x/a-b;
		}
		auto fac=one/a;
		// constraints: upper
		// TODO: what if a<0?!
		return AntiD(fac*primitive(transform(var)),zero);
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
	AntiD partiallyIntegratePolynomials(DVar var,DExpr e){
		auto m=cast(DMult)e;
		if(!m) return AntiD();
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
		if(!polyFact) return AntiD();
		auto rest=m.withoutFactor(polyFact);
		auto intRest=tryGetAntiderivative(var,rest,ivrs).antiderivative;
		if(!intRest) return AntiD();
		auto diffPoly=dDiff(var,polyFact);
		auto intDiffPolyIntRest=tryGetAntiderivative(var,(diffPoly*intRest).simplify(one),ivrs).antiderivative;
		if(!intDiffPolyIntRest) return AntiD();
		return AntiD(polyFact*intRest-intDiffPolyIntRest);
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
	return AntiD(); // no simpler expression available
}

DExpr tryIntegrate(DVar var,DExpr nonIvrs,DExpr lower,DExpr upper,DExpr ivrs){
	// TODO: add better approach for antiderivatives	
	auto lowLeUp(){ return lower&&upper?dIvr(DIvr.Type.leZ,lower-upper):one; }
	auto antid=tryGetAntiderivative(var,nonIvrs,ivrs);
	if(auto anti=antid.antiderivative){
		if(lower&&upper)
			return lowLeUp()*(anti.substitute(var,upper)
							  -anti.substitute(var,lower));
		auto lo=lower?anti.substitute(var,lower):antid.atMinusInfinity;
		auto up=upper?anti.substitute(var,upper):antid.atInfinity;
		if(!lo) lo=dLimSmp(var,-dInf,anti);
		if(!up) up=dLimSmp(var,dInf,anti);
		// dw(anti," ",lo," ",up);
		if(lo.isInfinite() || up.isInfinite()) return null;
		return up-lo;
	}
	if(auto p=cast(DPlus)nonIvrs.polyNormalize(var)){
		DExprSet works;
		DExprSet doesNotWork;
		bool ok=true;
		foreach(s;p.summands){
			auto ow=s.splitMultAtVar(var);
			auto t=tryIntegrate(var,ow[1],lower,upper,ivrs);
			if(t) DPlus.insert(works,ow[0]*t);
			else DPlus.insert(doesNotWork,s);
		}
		if(works.length) return dPlus(works)+dInt(var,dPlus(doesNotWork)*ivrs);
	}
	return null; // no simpler expression available
}
