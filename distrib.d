import dexpr, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	return one / (2*dΠ*σsq)^^(one/2) * dE^^((var-μ)^^2/σsq);
}

/*DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	return dInd((a<=var).and(var<=b))*one/(b-a);
}*/

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
		distribution=distribution.dMult(pdf);
	}
	void marginalize(DVar var){
		distribution=dInt(var,distribution);
	}
	override string toString(){
		return distribution.toString();
	}
}

