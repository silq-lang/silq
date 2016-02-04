import dexpr, util;

DExpr computeSum(DVar var,DExpr expr){
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
		if(ivr.type==DIvr.Type.eqZ||ivr.type==DIvr.Type.neqZ){
			return null; // TODO
		}
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
		}
	}
	//dw("!! ",nonIvrs," ",lower," ",upper);
	// TODO: use more clever summation strategies first
	// TODO: don't use this one at all?
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
