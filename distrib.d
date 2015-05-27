import dexpr, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	return one / (2*dΠ*σsq)^^(one/2) * dE^^-((var-μ)^^2/σsq);
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	return /*dInd((a<=var).and(var<=b))* */one/(b-a);
}

class Distribution{
	int[string] vbl;
	this(){ distribution=1.dℕ; }
	SetX!DVar freeVars;
	DExpr distribution;
	DVar getVar(string name){
		int suffix=++vbl[name];
		auto v=dVar(name~suffix.lowNumber);
		freeVars.insert(v);
		return v;
	}
	void distribute(DVar var,DExpr pdf){
		distribution=distribution*pdf;
	}
	void assign(DVar var,DExpr exp){
		// distribution=distribution*dDelta(exp-var); // TODO
	}
	void marginalize(DVar var)in{assert(var in freeVars); }body{
		distribution=dInt(var,distribution);
		freeVars.remove(var);
	}
	override string toString(){
		return distribution.toString();
	}
}

