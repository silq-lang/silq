import std.algorithm, std.array, std.conv;

import dexpr, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	return one / (2*dΠ*σsq)^^(one/2) * dE^^-((var-μ)^^2/(2*σsq));
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	return dIvr(DIvr.Type.leZ,a-var)*dIvr(DIvr.Type.leZ,var-b)*one/(b-a);
}

DExpr bernoulliPDF(DVar var,DExpr p){
	return dDelta(var)*(1-p)+dDelta(1-var)*p;
}

DExpr uniformIntPDF(DVar var,DExpr a,DExpr b){
	// TODO: remove this hack!
	if(auto ca=cast(Dℕ)a) if(auto cb=cast(Dℕ)b){
		DExprSet r;
		for(ℕ x=ca.c;x<=cb.c;x++)
			DPlus.insert(r,dDelta(var-x));
		return dPlus(r)/(b-a+1);
	}
	auto nnorm=dIvr(DIvr.Type.leZ,a-var)*dIvr(DIvr.Type.leZ,var-b)*dDelta(dSin(dΠ*var)/dΠ);
	return nnorm/dInt(var,nnorm);
}

class Distribution{
	int[string] vbl;
	DVar[string] symtab;
	this(){ distribution=1.dℕ; vbl["__dummy"]=0; }
	SetX!DVar freeVars;
	DExpr distribution;
	Distribution[] parents;

	SetX!DVar tmp;
	void marginalizeTemporaries(){
		foreach(v;tmp) marginalize(v);
		tmp.clear();
	}

	Distribution dup(){
		auto r=new Distribution();
		r.vbl=vbl;
		r.symtab=symtab.dup();
		r.freeVars=freeVars.dup();
		r.distribution=distribution;
		r.parents=parents~this; // TODO: elegance
		return r;
	}

	// TODO: elegance
	Distribution join(int[string] vbl,DVar[string] symtab,SetX!DVar freeVars,Distribution b,DExpr constraint){
		auto r=new Distribution();
		auto d1=distribution;
		auto d2=b.distribution;
		// TODO: this should be unnecessary with dead variable analysis
		foreach(x;this.freeVars) if(x !in freeVars){ assert(d1.hasFreeVar(x)); d1=dInt(x,d1); }
		foreach(x;b.freeVars) if(x !in freeVars){ assert(d2.hasFreeVar(x)); d2=dInt(x,d2); }
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
		DVar v;
		while(!v){ // TODO: fix more elegantly!
			int suffix=++vbl[name];
			string nn=name~suffix.lowNum;
			v=declareVar(nn);
		}
		return v;
	}
	DVar getTmpVar(string name){
		auto v=getVar(name);
		tmp.insert(v);
		return v;
	}
	void distribute(DExpr pdf){ distribution=distribution*pdf; }
	void initialize(DVar var,DExpr exp){
		assert(!distribution.hasFreeVar(var));
		distribute(dDelta(exp-var));
		marginalizeTemporaries();
	}
	void assign(DVar var,DExpr exp){
		assert(distribution.hasFreeVar(var));
		auto nvar=getVar(var.name);
		distribution=distribution.substitute(var,nvar);
		exp=exp.substitute(var,nvar);		
		distribute(dDelta(exp-var));
		marginalizeTemporaries();
		marginalize(nvar);
	}
	void marginalize(DVar var)in{assert(var in freeVars); }body{
		//assert(distribution.hasFreeVar(var),text(distribution," ",var));
		//writeln("marginalizing: ",var,"\ndistribution: ",distribution,"\nmarginalized: ",dInt(var,distribution));
		distribution=dInt(var,distribution);
		freeVars.remove(var);
		assert(!distribution.hasFreeVar(var));
	}
	void observe(DExpr e){ // e's domain must be 0 or 1.
		auto nDist=distribution*e;
		auto intNDist=nDist;
		foreach(v;freeVars) intNDist=dInt(v,intNDist);
		distribution=nDist/intNDist;
	}
	override string toString(){
		string r="p(";
		string[] vars;
		foreach(a;freeVars) vars~=a.name;
		sort(vars);
		foreach(v;vars) r~=v~",";
		if(vars.length) r=r[0..$-1];
		r~=") = "~distribution.toString();
		return r;
	}
}

