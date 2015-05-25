import dexpr, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	return 1.dℕ .dDiv(dPow(2.dℕ .dMult(dΠ).dMult(σsq),1.dℕ.dDiv(2.dℕ))).dMult(dE.dPow((var.dMinus(μ).dPow(2.dℕ).dDiv(σsq))));
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
		distribution=distribution.dMult(pdf);
	}
	void marginalize(DVar var){
		distribution=dInt(var,distribution);
	}
	override string toString(){
		return distribution.toString();
	}
}

