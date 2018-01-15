// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.algorithm;

import dexpr, util;

DExpr computeSum(DExpr expr,DExpr facts=one){
	auto var=db1;
	auto newFacts=(facts.incDeBruijnVar(1,0)*dIsℤ(db1)).simplify(one);
	auto nexpr=expr.simplify(newFacts);
	if(nexpr !is expr) expr=nexpr;
	if(expr is zero) return zero;
	auto ow=expr.splitMultAtVar(var); // not a good strategy without modification, due to deltas
	ow[0]=ow[0].incDeBruijnVar(-1,0).simplify(facts);
	if(ow[0] !is one){
		if(auto r=computeSum(ow[1],facts))
			return (ow[0]*r).simplify(facts);
		return null;
	}
	if(expr is one) return null; // (infinite sum)
	foreach(f;expr.factors){
		if(auto p=cast(DPlus)f){
			bool check(){ // TODO: deltas?
				foreach(d;p.allOf!DIvr(true))
					if(d.hasFreeVar(var))
						return true;
				return false;
			}
			if(check()){
				DExprSet works;
				DExprSet doesNotWork;
				bool simpler=false;
				foreach(k;distributeMult(p,expr.withoutFactor(f))){
					k=k.simplify(newFacts);
					auto ow=k.splitMultAtVar(var);
					auto r=computeSum(ow[1],facts);
					if(r){
						ow[0]=ow[0].incDeBruijnVar(-1,0);
						DPlus.insert(works,ow[0]*r);
						simpler=true;
					}else DPlus.insert(doesNotWork,k);
				}
				if(simpler){
					auto r=dPlus(works).simplify(facts);
					if(doesNotWork.length) r = r + dSum(dPlus(doesNotWork));
					return r;
				}
			}
		}
	}
	nexpr=expr.linearizeConstraints!(x=>!!cast(DIvr)x)(var).simplify(newFacts);
	if(nexpr != expr) return computeSum(nexpr,facts);

	Q!(DVar,DExpr) factSubsts;
	DVar[] factSubstVars;
	DExpr[] factSubstExprs;
	foreach(f;expr.factors){
		auto ivr=cast(DIvr)f;
		if(ivr&&ivr.type==DIvr.Type.eqZ){
			DExpr bound;
			auto status=getBoundForVar(ivr,var,bound);
			if(status==BoundStatus.equal)
				return dIsℤ(bound)*unbind(expr,bound);
			else return null;
		}
		if(auto d=cast(DDelta)f){
			auto fv=d.freeVars.setx;
			assert(var in fv);
			fv.remove(var);
			auto svar=getCanonicalVar(d.var.freeVars); // TODO: more clever choice?
			SolutionInfo info;
			SolUse usage={caseSplit:false,bound:false};
			auto sol=d.var.solveFor(svar,zero,usage,info);
			if(sol&&!info.needCaseSplit){
				factSubstVars~=svar;
				factSubstExprs~=sol;
			}
		}
	}
	DExpr newIvrs=one;
	foreach(fact;newFacts.factors){
		auto ivr=cast(DIvr)fact;
		if(ivr&&util.among(ivr.type,DIvr.Type.leZ,DIvr.Type.eqZ)&&factSubstVars.any!(x=>fact.hasFreeVar(x))){
			auto nivr=cast(DIvr)ivr.substituteAll(factSubstVars,factSubstExprs).simplify(one);
			assert(!!nivr);
			if(nivr.type==DIvr.Type.leZ){
				newIvrs=newIvrs*nivr;
			}else{
				if(!expr.hasAny!DDelta&&!expr.hasAny!DDistApply){ // TODO: improve IR to enable less conservative rules (trouble with e.g. (∑ᵢδ(i)[x])·δ(x)(y), as the rewrite to [x=⌊x⌋]·(δ(y)(x))² is not valid.)
					assert(nivr.type==DIvr.Type.eqZ);
					DExpr bound; // TODO: get rid of code duplication?
					auto status=getBoundForVar(nivr,var,bound);
					if(status==BoundStatus.equal)
						return dIsℤ(bound)*unbind(expr,bound);
					else return null;
				}
			}
		}
	}
	// TODO: keep ivrs and nonIvrs separate in DMult
	DExpr ivrs=one;
	DExpr nonIvrs=one;
	foreach(f;expr.factors){
		assert(f.hasFreeVar(var));
		auto ivr=cast(DIvr)f;
		if(ivr&&ivr.type==DIvr.Type.leZ) ivrs=ivrs*f;
		else nonIvrs=nonIvrs*f;
	}
	ivrs=ivrs.simplify(newFacts);
	nonIvrs=nonIvrs.simplify(newFacts);
	auto loup=(ivrs*newIvrs).simplify(one).getBoundsForVar(var,newFacts);
	// TODO: allow ivrs that do not contribute to bound.
	// TODO: only use external facts if local facts insufficient?
	if(!loup[0]) return null;
	DExpr lower=loup[1][0].maybe!(x=>x.incDeBruijnVar(-1,0)),upper=loup[1][1].maybe!(x=>x.incDeBruijnVar(-1,0));
	//dw("!! ",nonIvrs," ",lower," ",upper);
	// TODO: symbolic summation. TODO: use the fact that the loop index is an integer in simplifications.
	if(nonIvrs==one && lower && upper) return (dLe(dCeil(lower),dFloor(upper))*(dFloor(upper)+1-dCeil(lower))).simplify(facts);
	// TODO: use more clever summation strategies first
	auto lq=cast(Dℚ)lower, uq=cast(Dℚ)upper;
	import std.format: format;
	import std.math: ceil, floor;
	bool isFloat=false;
	if(!lq && !uq){
		if(auto f=cast(DFloat)lower){ lq = ℤ(format("%.0f",ceil(f.c))).dℚ; isFloat=true; }
		if(auto f=cast(DFloat)upper){ uq = ℤ(format("%.0f",floor(f.c))).dℚ; isFloat=true; }
	}
	if(lower && upper && lq && uq){
		import util: ceil, floor;
		auto low=ceil(lq.c), up=floor(uq.c);
		DExprSet s;
		if(low<=up) foreach(i;low..up+1){ // TODO: report bug in std.bigint (the if condition should not be necessary)
			import std.conv: text, to;
			DPlus.insert(s,unbind(nonIvrs,isFloat?dFloat(text(i).to!real):dℚ(i)).simplify(facts));
		}
		return dPlus(s);
	}
	return null;
}
