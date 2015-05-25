import dexpr, util;

class Distribution{
	int[string] vbl;
	this(){}
	DExpr distribution;
	DVar addVariable(string name){
		int suffix=++vbl[name];
		return dVar(name~suffix.lowNumber);
	}
}

