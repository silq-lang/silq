import std.algorithm, std.array, std.conv;

import dexpr, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	return one / (2*dΠ*σsq)^^(one/2) * dE^^-((var-μ)^^2/(2*σsq));
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	return /*dInd((a<=var).and(var<=b))* */one/(b-a);
}

DExpr bernoulliPDF(DVar var,DExpr p){
	return dDelta(var)*(1-p)+dDelta(1-var)*p;
}

class Distribution{
	int[string] vbl;
	this(){ distribution=1.dℕ; }
	SetX!DVar freeVars;
	DExpr distribution;
	DVar declareVar(string name){
		if(name in symtab) return null;
		auto v=dVar(name);
		symtab[name]=v;
		freeVars.insert(v);
		return v;
	}
	DVar[string] symtab;
	DVar lookupVar(string name){
		return symtab.get(name,null);
	}
	DVar getVar(string name){
		int suffix=++vbl[name];
		string nn=name~suffix.lowNum;
		auto v=declareVar(nn);
		assert(v);
		return v;
	}
	void distribute(DVar var,DExpr pdf){
		distribution=distribution*pdf;
	}
	void assign(DVar var,DExpr exp){
		distribution=distribution*dDelta(exp-var);
	}
	void marginalize(DVar var)in{assert(var in freeVars); }body{
		distribution=dInt(var,distribution);
		freeVars.remove(var);
	}
	override string toString(){
		string r="p(";
		auto vars=freeVars.array.map!(a=>a.name).array;
		sort(vars);
		foreach(v;vars) r~=v~",";
		if(vars.length) r=r[0..$-1];
		r~=") = "~distribution.toString();
		return r;
	}
}

