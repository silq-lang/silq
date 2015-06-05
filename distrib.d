import std.algorithm, std.array, std.conv;

import dexpr, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	return one / (2*dΠ*σsq)^^(one/2) * dE^^-((var-μ)^^2/(2*σsq));
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	return dIvr(DIvr.Type.lZ,a-var)*dIvr(DIvr.Type.lZ,var-b)*one/(b-a);
}

DExpr bernoulliPDF(DVar var,DExpr p){
	return dDelta(var)*(1-p)+dDelta(1-var)*p;
}

class Distribution{
	int[string] vbl;
	DVar[string] symtab;
	this(){ distribution=1.dℕ; }
	SetX!DVar freeVars;
	DExpr distribution;

	Distribution dup(){
		auto r=new Distribution();
		r.vbl=vbl.dup();
		r.symtab=symtab.dup();
		r.freeVars=freeVars.dup();
		r.distribution=distribution;
		return r;
	}

	// TODO: elegance
	Distribution join(int[string] vbl,DVar[string] symtab,SetX!DVar freeVars,Distribution b,DExpr constraint){
		auto r=new Distribution();
		auto d1=distribution;
		auto d2=b.distribution;
		// TODO: this should be unnecessary with dead variable analysis
		foreach(x;this.freeVars) if(x !in freeVars) d1=dInt(x,d1);
		foreach(x;b.freeVars) if(x !in freeVars) d2=dInt(x,d2);
		//// /// // /
		r.vbl=vbl;
		r.symtab=symtab;
		r.freeVars=freeVars;
		r.distribution=constraint*d1+(1-constraint)*d2;
		return r;
	}

	DVar declareVar(string name){
		if(name in symtab) return null;
		auto v=dVar(name);
		symtab[name]=v;
		freeVars.insert(v);
		return v;
	}
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
	void initialize(DVar var,DExpr exp){
		distribution=distribution*dDelta(exp-var);
	}
	void assign(DVar var,DExpr exp){
		auto nvar=getVar(var.name);
		distribution=distribution.substitute(var,nvar);
		exp=exp.substitute(var,nvar);		
		distribution=distribution*dDelta(exp-var);
		marginalize(nvar);
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

