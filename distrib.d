import std.algorithm, std.array, std.conv;

import dexpr, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	auto dist=one/(2*dΠ*σsq)^^(one/2)*dE^^-((var-μ)^^2/(2*σsq));
	return dIvr(DIvr.Type.neqZ,σsq)*dist+dIvr(DIvr.Type.eqZ,σsq)*dDelta(var-μ);
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	auto diff=b-a, dist=dBounded!"[]"(var,a,b)/diff;
	return dIvr(DIvr.Type.neqZ,diff)*dist+dIvr(DIvr.Type.eqZ,diff)*dDelta(var-a);
}

DExpr bernoulliPDF(DVar var,DExpr p){
	return dDelta(var)*(1-p)+dDelta(1-var)*p;
}

DExpr uniformIntPDFNnorm(DVar var,DExpr a,DExpr b){
	// TODO: remove this hack!
	if(auto ca=cast(Dℕ)a) if(auto cb=cast(Dℕ)b){
		DExprSet r;
		for(ℕ x=ca.c;x<=cb.c;x++)
			DPlus.insert(r,dDelta(var-x));
		return dPlus(r)/(b-a+1);
	}
	return dIvr(DIvr.Type.leZ,a-var)*dIvr(DIvr.Type.leZ,var-b)*dDelta(dSin(dΠ*var)/dΠ);
	//auto tmp=new DVar("tmp"); // TODO: get rid of this!
	//return dSumSmp(tmp,dBounded!"[]"(tmp,a,b)*dDelta(tmp-var));
}

DExpr uniformIntPDF(DVar var,DExpr a,DExpr b){
	auto nnorm=uniformIntPDFNnorm(var,a,b);
	return nnorm/dIntSmp(var,nnorm);
}

/+ TODO:
DExpr poissonPDF(DVar var,DExpr λ){
	
}+/

DExpr betaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=var^^(α-1)*(1-var)^^(β-1)*dBounded!"[]"(var,zero,one);
	return nnorm/dIntSmp(var,nnorm);
}
DExpr gammaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=var^^(α-1)*dE^^(-β*var)*dBounded!"[]"(var,zero,one);
	return nnorm/dIntSmp(var,nnorm);
}

DExpr expPDF(DVar var,DExpr λ){
	return λ*dE^^(-λ*var)*dIvr(DIvr.Type.leZ,-var);
}

DExpr studentTPDF(DVar var,DExpr ν){ // this has a mean only if ν>1. how to treat this?
	auto nnorm=(1+var^^2/ν)^^(-(ν+1)/2);
	return nnorm/dIntSmp(var,nnorm);
}

DExpr weibullPDF(DVar var,DExpr λ,DExpr k){
	return dIvr(DIvr.Type.leZ,-var)*k/λ*(var/λ)^^(k-1)*dE^^(-(var/λ)^^k);
}


class Distribution{
	int[string] vbl;
	DVar[string] symtab;
	this(){ distribution=one; error=zero; vbl["__dummy"]=0; }
	SetX!DVar freeVars;
	DExpr distribution;
	DExpr error;
	Distribution[] parents;

	SetX!DVar tmpVars;
	void marginalizeTemporaries(){
		foreach(v;tmpVars.dup) marginalize(v);
	}
	void marginalizeLocals(Distribution enclosing,scope void delegate(DVar) hook=null){
		foreach(x;this.freeVars.dup){
			if(x in enclosing.freeVars) continue;
			if(hook) hook(x);
			marginalize(x);
			symtab.remove(x.name);
		}
	}	

	Distribution dup(){
		auto r=new Distribution();
		r.vbl=vbl;
		r.symtab=symtab.dup();
		r.freeVars=freeVars.dup();
		r.distribution=distribution;
		r.error=error;
		r.parents=parents~this; // TODO: elegance
		r.context=context;
		return r;
	}

	Distribution dupNoErr(){
		auto r=dup();
		r.error=zero;
		return r;
	}

	Distribution join(Distribution orig,Distribution b){
		auto r=new Distribution();
		auto d1=distribution;
		auto d2=b.distribution;
		// TODO: this should be unnecessary with dead variable analysis
		foreach(x;this.freeVars) if(x !in orig.freeVars){ assert(d1 is zero || d1.hasFreeVar(x)); d1=dIntSmp(x,d1); }
		foreach(x;b.freeVars) if(x !in orig.freeVars){ assert(d2 is zero || d2.hasFreeVar(x)); d2=dIntSmp(x,d2); }
		//// /// // /
		r.vbl=orig.vbl;
		r.symtab=orig.symtab;
		r.freeVars=orig.freeVars;
		r.tmpVars=orig.tmpVars;
		r.distribution=d1+d2;
		r.error=orig.error;
		if(error !is zero || b.error !is zero)
			r.error=(orig.error+error+b.error).simplify(one);
		return r;
	}

	DContextVars context=null;
	DContextVars getContext(string name,DFunVar fun)in{assert(!context);}body{
		return context=dContextVars(name,fun);
	}

	DVar declareVar(string name,bool addtosymtab=true){
		if(name in symtab) return null;
		auto v=dVar(name);
		if(v in freeVars) return null;
		if(addtosymtab) symtab[name]=v;
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
			v=declareVar(nn,false);
		}
		return v;
	}
	DVar getTmpVar(string name){
		auto v=getVar(name);
		tmpVars.insert(v);
		return v;
	}

	DExpr computeProbability(DExpr cond){
		auto tdist=distribution*cond;
		foreach(v;freeVars) tdist=dIntSmp(v,tdist);
		return tdist;		
	}

	void assertTrue(DExpr cond,lazy string msg){
		error=(error+computeProbability(dIvr(DIvr.Type.eqZ,cond))).simplify(one);
		distribution=distribution*cond;
	}
	void distribute(DExpr pdf){ distribution=distribution*pdf; }
	void initialize(DVar var,DExpr exp){
		assert(!distribution.hasFreeVar(var));
		distribute(dDelta(exp-var));
		marginalizeTemporaries();
	}
	void assign(DVar var,DExpr exp){
		if(distribution is zero) return;
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
		distribution=dIntSmp(var,distribution);
		freeVars.remove(var);
		tmpVars.remove(var);
		assert(!distribution.hasFreeVar(var));
	}
	void observe(DExpr e){ // e's domain must be {0,1}
		distribution=distribution*e;
	}
	void renormalize(){
		auto factor=distribution;
		foreach(v;freeVars)
			factor=dIntSmp(v,factor);
		if(context) factor=dInt(context,factor);
		factor=factor+error;
		distribution=(dIvr(DIvr.Type.neqZ,factor)*(distribution/factor)).simplify(one);
		error=(dIvr(DIvr.Type.eqZ,factor)+dIvr(DIvr.Type.neqZ,factor)*(error/factor)).simplify(one);
	}
	DExpr call(Distribution q,DExpr[] args){
		DExpr rdist=q.distribution;
		DExpr rerr=q.error;
		assert(q.freeVars.length==1,"TODO!");
		import hashtable;
		auto context=freeVars.dup;
		auto r=getTmpVar("__r");
		rdist=rdist.substitute(q.freeVars.element,r);
		rerr=rerr.substitute(q.freeVars.element,r);
		DVar[] vars;
		auto oldDist=distribution;
		foreach(a;args){
			auto var=getTmpVar("__arg");
			vars~=var;
			oldDist=oldDist*dDelta(var-a);
		}
		distribution = rdist.substituteFun("q".dFunVar,oldDist,vars,context);
		auto nerror = rerr.substituteFun("q".dFunVar,oldDist,vars,context);
		foreach(v;vars){
			tmpVars.remove(v);
			freeVars.remove(v);
		}
		foreach(v;freeVars.without(r)) nerror=dIntSmp(v,nerror);
		error = error + nerror;
		return r;
	}
	void simplify(){
		distribution=distribution.simplify(one); // TODO: this shouldn't be necessary!
		error=error.simplify(one);
	}
	override string toString(){
		return toString(Format.default_);
	}
	string toString(Format formatting){
		string r="p(";
		string[] vars;
		foreach(a;freeVars) vars~=a.name;
		sort(vars);
		foreach(v;vars) r~=v~",";
		if(vars.length) r=r[0..$-1];
		r~=") = "~distribution.toString(formatting);
		if(error !is zero) r~="\nPr[error] = "~error.toString(formatting);
		return r;
	}
}

