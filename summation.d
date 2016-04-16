import dexpr, util;

DExpr computeSum(DVar var,DExpr expr,DExpr facts=one){
	auto nexpr=expr.simplify(facts);
	if(nexpr !is expr) expr=nexpr;
	if(expr is zero) return zero;
	auto ow=expr.splitMultAtVar(var); // not a good strategy without modification, due to deltas
	if(ow[0] !is one){
		if(auto r=computeSum(var,ow[1]))
			return ow[0]*r;
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
					auto ow=k.splitMultAtVar(var);
					auto r=computeSum(var,ow[1],facts);
					if(r){
						DPlus.insert(works,ow[0]*r);
						simpler=true;
					}else DPlus.insert(doesNotWork,k);
				}
				if(simpler){
					auto r=dPlus(works).simplify(facts);
					if(doesNotWork.length) r = r + dSum(var,dPlus(doesNotWork));
					return r;
				}
			}
		}
	}
	nexpr=expr.linearizeConstraints!(x=>!!cast(DIvr)x)(var).simplify(facts);
	if(nexpr !is expr) return computeSum(var,nexpr);

	// TODO: keep ivrs and nonIvrs separate in DMult
	DExpr ivrs=one;
	DExpr nonIvrs=one;
	foreach(f;expr.factors){
		assert(f.hasFreeVar(var));
		if(cast(DIvr)f) ivrs=ivrs*f;
		else nonIvrs=nonIvrs*f;
	}

	DExpr lower,upper;
	foreach(f;ivrs.factors){
		if(f is one) break;
		auto ivr=cast(DIvr)f;
		assert(!!ivr);
		if(ivr.type==DIvr.Type.neqZ) continue; // TODO: ok?
		DExpr bound;
		auto status=ivr.getBoundForVar(var,bound);
		final switch(status) with(BoundStatus){
		case fail:
			return null;
		case lowerBound:
			if(lower) lower=dMax(lower,bound);
			else lower=bound;
			break;
		case upperBound:
			if(upper) upper=dMin(upper,bound);
			else upper=bound;
			break;
		case equal:
			if(lower) lower=dMax(lower,bound);
			else lower=bound;
			if(upper) upper=dMin(upper,bound);
			else upper=bound;
		}
	}
	
	//dw("!! ",nonIvrs," ",lower," ",upper);
	// TODO: use more clever summation strategies first
	if(lower && upper && lower.isFraction() && upper.isFraction()){
		auto ndl=lower.getFraction();
		auto ndu=upper.getFraction();
		auto low=ceildiv(ndl[0],ndl[1]);
		auto up=floordiv(ndu[0],ndu[1]);
		DExprSet s;
		foreach(i;low..up+1)
			DPlus.insert(s,expr.substitute(var,dℕ(i)).simplify(one));
		return dPlus(s);
	}
	return null;
}
