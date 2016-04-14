import std.algorithm, std.range, std.array, std.conv;

import dexpr, type, util;

DExpr gaussianPDF(DVar var,DExpr μ,DExpr σsq){
	auto dist=one/(2*dΠ*σsq)^^(one/2)*dE^^-((var-μ)^^2/(2*σsq));
	return dIvr(DIvr.Type.neqZ,σsq)*dist+dIvr(DIvr.Type.eqZ,σsq)*dDelta(var-μ);
}

DExpr rayleighPDF(DVar var,DExpr σsq){
	auto dist=var/(σsq)*dE^^-((var)^^2/(2*σsq)) * dIvr(DIvr.Type.leZ,-var);
	return dIvr(DIvr.Type.neqZ,σsq)*dist+dIvr(DIvr.Type.eqZ,σsq)*dDelta(var);
}

DExpr exponentialPDF(DVar var, DExpr lambda) {
      auto dist=lambda*dE^^-(lambda*var)*dIvr(DIvr.Type.lZ,-var);
      return dIvr(DIvr.Type.leZ,-lambda)*dist;
}


DExpr truncGaussianPDF(DVar var,DExpr μ,DExpr σsq, DExpr a, DExpr b){
	auto gdist=one/(2*dΠ)^^(one/2)*dE^^-((var-μ)^^2/(2*σsq));
	auto dist = gdist/(σsq)/(dGaussInt((b-μ)/σsq^^(one/2))-dGaussInt((a-μ)/(σsq)^^(one/2)))*dBounded!"[]"(var,a,b);
	return dIvr(DIvr.Type.neqZ,σsq)*dist+dIvr(DIvr.Type.eqZ,σsq)*dDelta(var-μ);
}

DExpr paretoPDF(DVar var, DExpr a, DExpr b) {
        auto dist = a * b^^a / var^^(a+one);
	return dist * dIvr(DIvr.Type.leZ, b-var);
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
	/+auto tmp=new DVar("tmp"); // TODO: get rid of this!
	return dSumSmp(tmp,dBounded!"[]"(tmp,a,b)*dDelta(tmp-var));+/
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
	auto nnorm=var^^(α-1)*dE^^(-β*var)*dIvr(DIvr.Type.leZ,-var);
	return nnorm/dIntSmp(var,nnorm);
}

DExpr laplacePDF(DVar var, DExpr μ, DExpr b) {
      auto positive = dE^^(-(var-μ)/b)/(2*b);
      auto negative = dE^^((var-μ)/b)/(2*b);
      auto dif = var - μ;
      return positive * dIvr(DIvr.Type.leZ,-dif) + negative * dIvr(DIvr.Type.leZ,var);
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
		r.freeVarsOrdered=freeVarsOrdered;
		r.orderedFreeVars=orderedFreeVars.dup;
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
	void addArgsWithContext(DExpr[] args)in{assert(!context);}body{
		context=dContextVars("γ","q".dFunVar);
		auto q="q".dFunVar;
		args~=context;
		distribute(dFun(q,args)); // TODO: constant name sufficient?
	}
	
	void deleteContext(size_t nParams){
		auto vars=iota(0,nParams).map!(x=>dVar("__p"~lowNum(x))).array;
		auto fun=dFun("q".dFunVar,cast(DExpr[])vars); // TODO: get rid of cast
		distribution=distribution.substituteFun("q".dFunVar,fun,vars,SetX!DVar.init).simplify(one);
		error=error.substituteFun("q".dFunVar,fun,vars,SetX!DVar.init).simplify(one);
		context=null;
	}

	void assumeInputNormalized(size_t nParams){
		auto vars=iota(0,nParams).map!(x=>dVar("__p"~lowNum(x))).array;
		auto fun=dFun("q".dFunVar,cast(DExpr[])vars); // TODO: get rid of cast
		DExpr tdist=fun;
		foreach(v;vars) tdist=dIntSmp(v,tdist);
		if(context) tdist=dInt(context,tdist);
		DExpr doIt(DExpr e){
			auto h=e.getHoles!(x=>x is tdist?x:null);
			e=h.expr;
			foreach(hole;h.holes){
				assert(hole.expr is tdist);
				e=e.substitute(hole.var,one);
			}
			return e;
		}
		distribution=doIt(distribution).simplify(one);
		error=doIt(error).simplify(one);
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
		if(context) tdist=dInt(context,tdist);
		return tdist;
	}

	void assertTrue(DExpr cond,lazy string msg){
		error=(error+computeProbability(dIvr(DIvr.Type.eqZ,cond))).simplify(one);
		distribution=distribution*cond;
	}
	void distribute(DExpr pdf){ distribution=distribution*pdf; }
	void initialize(DVar var,DExpr exp,Type ty){
		assert(!distribution.hasFreeVar(var));
		distribute(dDelta(var,exp,ty));
		marginalizeTemporaries();
	}
	void assign(DVar var,DExpr exp,Type ty){
		if(distribution is zero) return;
		assert(distribution.hasFreeVar(var),text(var));
		auto nvar=getVar(var.name);
		distribution=distribution.substitute(var,nvar);
		exp=exp.substitute(var,nvar);
		distribute(dDelta(var,exp,ty));
		marginalizeTemporaries();
		//marginalize(nvar);
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
		import hashtable;
		auto context=freeVars.dup;
		DVar[] r;
		foreach(v;q.orderedFreeVars){
			r~=getTmpVar("__r");
			rdist=rdist.substitute(v,r[$-1]);
			rerr=rerr.substitute(v,r[$-1]);
		}
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
		error = error + nerror;
		return r.length==1?r[0]:dTuple(cast(DExpr[])r);
	}
	void simplify(){
		distribution=distribution.simplify(one); // TODO: this shouldn't be necessary!
		error=error.simplify(one);
	}
	override string toString(){
		return toString(Format.default_);
	}

	bool freeVarsOrdered=false;
	DVar[] orderedFreeVars;
	void orderFreeVars(DVar[] orderedFreeVars)in{
		assert(!freeVarsOrdered);
		assert(orderedFreeVars.length==freeVars.length);
		foreach(v;orderedFreeVars)
			assert(v in freeVars);
		// TODO: this does not check that variables occur at most once in orderedFreeVars
	}body{
		freeVarsOrdered=true;
		this.orderedFreeVars=orderedFreeVars;
	}

	string toString(Format formatting){
		auto initial="p(";
		auto middle=") = ";
		auto errstr="Pr[error] = ";
		if(formatting==Format.mathematica){
			initial="p[";
			middle="] := ";
			errstr="Pr_error := ";
		}
		string r=initial;
		DVar[] vars;
		if(freeVarsOrdered) vars=orderedFreeVars;
		else vars=freeVars.array;
		foreach(v;orderedFreeVars) r~=(formatting==Format.mathematica?v.name~"_":v.name)~",";
		if(orderedFreeVars.length) r=r[0..$-1];
		r~=middle~distribution.toString(formatting);
		if(error !is zero) r~="\n"~errstr~error.toString(formatting);
		return r;
	}
}

