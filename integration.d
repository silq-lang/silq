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
				constraints*(dInt(var,dIvr(DIvr.Type.leZ,var-bound)*
								  dIvr(DIvr.type.leZ,info.bound.isLower)*rest)
							 +dInt(var,dIvr(DIvr.Type.lZ,bound-var)*
								   dIvr(DIvr.type.leZ,-info.bound.isLower)*rest));
			foreach(ref x;info.caseSplits){
				auto curConstr=constraints.withoutFactor(dIvr(DIvr.Type.neqZ,x.constraint));
				r=r+curConstr*dIvr(DIvr.Type.eqZ,x.constraint)*
					dInt(var,rest*dIvr(DIvr.Type.leZ,x.expression));
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


static DExpr tryIntegrate(DVar var,DExpr nonIvrs,DExpr lower,DExpr upper,DExpr ivrs){
	// TODO: add better approach for antiderivatives	
	auto lowLeUp(){ return dIvr(DIvr.Type.leZ,lower-upper); }
	static DExpr safeLog(DExpr e){ // TODO: ok?
		return dLog(e)*dIvr(DIvr.Type.neqZ,e);
	}
	if(auto p=cast(DPow)nonIvrs){
		if(upper && lower){
			if(p.operands[0] is var && !p.operands[1].hasFreeVar(var)){
				return lowLeUp()*
					((safeLog(upper)-safeLog(lower))*
					 dIvr(DIvr.Type.eqZ,p.operands[1]+1)
					 +(upper^^(p.operands[1]+1)-lower^^(p.operands[1]+1))/(p.operands[1]+1)*
					 dIvr(DIvr.Type.neqZ,p.operands[1]+1));
			}
		}
		if(!p.operands[0].hasFreeVar(var)){
			auto k=dLog(p.operands[0])*p.operands[1];
			if(upper&&lower||dIvr(DIvr.Type.leZ,k).simplify(ivrs) is one){
				// need to integrate e^^(k(x)).
				auto dk=dDiff(var,k);
				if(dk!is zero && !dk.hasFreeVar(var)){
					return (upper&&lower?lowLeUp():one)*
						((upper?dE^^k.substitute(var,upper):zero)
						 -(lower?dE^^k.substitute(var,lower):zero))/dk;
				}
			}
		}
	}
	if(upper&&lower){
		//writeln(lower," ",upper);
		//writeln(lowLeUp());
		if(nonIvrs is one) return lowLeUp()*(upper-lower);
		if(auto poly=nonIvrs.asPolynomialIn(var)){ // TODO: this can be wasteful sometimes
			DExprSet s;
			foreach(i,coeff;poly.coefficients){
				assert(i<size_t.max);
				DPlus.insert(s,coeff*(upper^^(i+1)-lower^^(i+1))/(i+1));
			}
			return lowLeUp()*dPlus(s);
		}
		//if(1/nonIvrs is var){ return lowLeUp()*(safeLog(upper)-safeLog(lower)); }
	}
	if(upper&&lower){
		if(auto p=cast(DLog)nonIvrs){
			if(p.e is var){
				static DExpr logIntegral(DExpr e){
					return e*safeLog(e)-e;
				}
				return lowLeUp()*(logIntegral(upper)-logIntegral(lower));
			}
		}
	}
	DExpr gaussianIntegral(DVar v,DExpr e){
		// detect e^^(-a*x^^2+b*x+c), and integrate to e^^(b^^2/4a+c)*(pi/a)^^(1/2).
		// TODO: this assumes that a≥0!
		auto p=cast(DPow)e;
		if(!p) return null;
		if(!cast(DE)p.operands[0]) return null;
		auto q=p.operands[1].asPolynomialIn(v,2);
		if(!q.initialized) return null;
		if(q.coefficients.length!=3) return null;
		auto qc=q.coefficients;
		auto a=-qc[2],b=qc[1],c=qc[0];
		// if(couldBeZero(a)) return null; // TODO: this is what should be done!
		if(a is null) return null; // TODO: it could still be zero!
		// -a(x-b/2a)²=-ax²+bx-b²/4a
		// -ax²+bx+c =-a(x-b/2a)²+b²/4a+c
		// -ax²+bx+c =-(√(a)x-b/2√a)²+b²/4a+c
		// e^(-ax²+bx+c) = e^(b²/4a+c)·e^-(√(a)x-b/2√a)²
		// ∫dx e^(-ax²+bx+c)[l≤x≤r] = e^(b²/4a+c)·∫dx(e^-(√(a)x-b/(2√a))²[l≤x≤r]
		// = e^(b²/4a+c)·⅟√a∫dx(e^-x²)[l≤x/√(a)+b/(2a)≤r]
		// = e^(b²/4a+c)·⅟√a∫dx(e^-x²)[l*(√(a))-b/(2√(a))≤x≤r*(√(a))-b/(2√(a))]
		auto fac=dE^^(b^^2/(4*a)+c)*(one/a)^^(one/2);
		if(!upper&&!lower){
			return fac*dΠ^^(one/2);
		}else{
			auto up=upper?upper:dInf, lo=lower?lower:-dInf;
			auto lowLeUp(){
				if(!upper||!lower) return one;
				return dIvr(DIvr.Type.leZ,lo-up);
			}
			DExpr transform(DExpr x){
				if(x is dInf || x is -dInf) return x;
				auto sqrta=a^^(one/2);
				return sqrta*x-b/(2*sqrta);
			}
			return fac*lowLeUp()*(dGaussInt(transform(up))-dGaussInt(transform(lo)));
		}
	}
	if(auto r=gaussianIntegral(var,nonIvrs)) return r;
	// TODO: this is just a list of special cases. Generalize!
	DExpr doubleGaussIntegral(DVar var,DExpr e){
		if(!upper) return null;
		auto up=upper,lo=lower?lower:-dInf;
		auto gi=cast(DGaussInt)e;
		if(!gi) return null;
		auto q=gi.x.asPolynomialIn(var,1);
		if(!q.initialized) return null;
		auto a=q.coefficients[1],b=q.coefficients[0];
		if(a is zero) return null;
		static DExpr primitive(DExpr e){
			if(e is -dInf) return zero;
			return dGaussInt(e)*e-dE^^(-e^^2);
		}
		DExpr transform(DExpr x){
			return x/a-b;
		}
		auto fac=one/a;
		return fac*lowLeUp()*(primitive(transform(up))-primitive(transform(lo)));
		return null;
	}
	if(auto r=doubleGaussIntegral(var,nonIvrs)) return r;
	DExpr gaussIntTimesFunction(DVar var,DExpr e){ // TODO: support other functions
		auto m=cast(DMult)e;
		if(!m) return null;
		DGaussInt gaussFact=null;
		foreach(f;m.factors){
			if(auto g=cast(DGaussInt)f){
				gaussFact=g;
				break;
			}
		}
		if(!gaussFact) return null;
		auto rest=m.withoutFactor(gaussFact);
		dw(gaussFact," ",rest);
		return null;
	}
	if(auto r=gaussIntTimesFunction(var,nonIvrs)) return r;
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
		if(works.length) return dPlus(works)+dInt(var,dPlus(doesNotWork)*ivrs);// TODO: don't try to integrate this again!
	}
	// partial integration: TODO: this is not well founded!
	/+if(!lower&&!upper){
	 // x = ∫ u'v
	 // (uv)' = uv'+u'v
	 // ∫(uv)' = ∫uv'+∫u'v
	 // uv+C = ∫uv'+∫u'v
	 // 
	 auto factors=splitIntegrableFactor(nonIvrs);
	 //dw(factors[1]);
	 //dw("!! ",dDiff(var,factors[1]));
	 // TODO
		
	 }+/
	return null; // no simpler expression available
}
