// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.algorithm, std.range, std.array, std.conv;

import options, dexpr, type, util;

DExpr gaussPDF(DVar var,DExpr μ,DExpr ν){
	auto dist=one/(2*dΠ*ν)^^(one/2)*dE^^-((var-μ)^^2/(2*ν));
	return dIvr(DIvr.Type.neqZ,ν)*dist+dIvr(DIvr.Type.eqZ,ν)*dDelta(var-μ);
}
DExpr gaussCond(DExpr μ,DExpr ν){
	return dIvr(DIvr.Type.leZ,-ν);
}

DExpr rayleighPDF(DVar var,DExpr ν){
	auto dist=var/(ν)*dE^^-((var)^^2/(2*ν)) * dIvr(DIvr.Type.leZ,-var);
	return dIvr(DIvr.Type.neqZ,ν)*dist+dIvr(DIvr.Type.eqZ,ν)*dDelta(var);
}
DExpr rayleighCond(DExpr ν){
	return dIvr(DIvr.Type.leZ,-ν);
}

DExpr truncatedGaussPDF(DVar var,DExpr μ,DExpr ν,DExpr a,DExpr b){
	auto gdist=one/(2*dΠ)^^(one/2)*dE^^-((var-μ)^^2/(2*ν));
	auto dist = gdist/(ν)/(dGaussInt((b-μ)/ν^^(one/2))-dGaussInt((a-μ)/(ν)^^(one/2)))*dBounded!"[]"(var,a,b);
	return dIvr(DIvr.Type.neqZ,ν)*dist+dIvr(DIvr.Type.eqZ,ν)*dDelta(var-μ);
}
DExpr truncatedGaussCond(DExpr μ,DExpr ν,DExpr a,DExpr b){
	return dIvr(DIvr.Type.leZ,-ν); // TODO: add a<b condition.
}

DExpr paretoPDF(DVar var, DExpr a, DExpr b) {
	auto dist = a * b^^a / var^^(a+one);
	return dist * dIvr(DIvr.Type.leZ, b-var);
}
DExpr paretoCond(DExpr a, DExpr b){
	return dIvr(DIvr.Type.leZ,-a)*dIvr(DIvr.Type.leZ,-b);
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	auto diff=b-a, dist=dBounded!"[]"(var,a,b)/diff;
	return dIvr(DIvr.Type.neqZ,diff)*dist+dIvr(DIvr.Type.eqZ,diff)*dDelta(var-a);
}
DExpr uniformCond(DExpr a,DExpr b){
	return dIvr(DIvr.Type.leZ,a-b);
}

DExpr bernoulliPDF(DVar var,DExpr p){
	return dDelta(var)*(1-p)+dDelta(1-var)*p;
}
DExpr bernoulliCond(DExpr p){
	return dIvr(DIvr.Type.leZ,-p)*dIvr(DIvr.Type.leZ,p-1);
}

DExpr uniformIntPDFNnorm(DVar var,DExpr a,DExpr b){
	auto tmp=freshVar(); // TODO: get rid of this!
	return dSumSmp(tmp,dBounded!"[]"(tmp,a,b)*dDelta(var-tmp),one);
}

DExpr uniformIntPDF(DVar var,DExpr a,DExpr b){
	auto nnorm=uniformIntPDFNnorm(var,a,b);
	return nnorm/dIntSmp(var,nnorm,one);
}
DExpr uniformIntCond(DExpr a,DExpr b){
	auto tmp=freshVar(); // TODO: get rid of this!
	auto nnorm=uniformIntPDFNnorm(tmp,a,b);
	auto norm=dIntSmp(tmp,nnorm,one);
	return dIvr(DIvr.Type.neqZ,norm);
}

DExpr poissonPDF(DVar var,DExpr λ){
	auto tmp=freshVar();
	return dE^^-λ*dSumSmp(tmp,dIvr(DIvr.Type.leZ,-tmp)*dDelta(var-tmp)*λ^^tmp/dGamma(tmp+1),one);
}
DExpr poissonCond(DExpr λ){
	return dIvr(DIvr.Type.lZ,-λ);
}

DExpr betaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=var^^(α-1)*(1-var)^^(β-1)*dBounded!"[]"(var,zero,one);
	return nnorm/dIntSmp(var,nnorm,one);
}
DExpr betaCond(DExpr α,DExpr β){
	return dIvr(DIvr.Type.lZ,-α)*dIvr(DIvr.Type.lZ,-β);
}

DExpr gammaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=var^^(α-1)*dE^^(-β*var)*dIvr(DIvr.Type.leZ,-var);
	return nnorm/dIntSmp(var,nnorm,one);
}
DExpr gammaCond(DExpr α,DExpr β){
	return dIvr(DIvr.Type.lZ,-α)*dIvr(DIvr.Type.lZ,-β);
}

DExpr laplacePDF(DVar var, DExpr μ, DExpr b){
      auto positive = dE^^(-(var-μ)/b)/(2*b);
      auto negative = dE^^((var-μ)/b)/(2*b);
      auto dif = var - μ;
      return positive * dIvr(DIvr.Type.leZ,-dif) + negative * dIvr(DIvr.Type.leZ,var);
}
DExpr laplaceCond(DExpr μ,DExpr b){
	return dIvr(DIvr.Type.lZ,-b);
}


DExpr exponentialPDF(DVar var,DExpr λ){
	return λ*dE^^(-λ*var)*dIvr(DIvr.Type.leZ,-var);
}
DExpr exponentialCond(DExpr λ){
	return dIvr(DIvr.Type.lZ,-λ);
}


DExpr studentTPDF(DVar var,DExpr ν){ // this has a mean only if ν>1. how to treat this?
	auto nnorm=(1+var^^2/ν)^^(-(ν+1)/2);
	return nnorm/dIntSmp(var,nnorm,one);
}
DExpr studentTCond(DExpr ν){
	return dIvr(DIvr.Type.lZ,-ν);
}

DExpr weibullPDF(DVar var,DExpr λ,DExpr k){
	return dIvr(DIvr.Type.leZ,-var)*k/λ*(var/λ)^^(k-1)*dE^^(-(var/λ)^^k);
}
DExpr weibullCond(DExpr λ,DExpr k){
	return dIvr(DIvr.Type.lZ,-λ)*dIvr(DIvr.Type.lZ,-k);
}

DExpr categoricalPDF(DVar var,DExpr p){
	auto dbv=dDeBruijnVar(1);
	auto nnorm=dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv]*dDelta(var-dbv));
	return nnorm;///dIntSmp(tmp,nnorm);
}
DExpr categoricalCond(DExpr p){
	auto dbv=dDeBruijnVar(1);
	return dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length")*dIvr(DIvr.Type.lZ,p[dbv]))))
		*dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv])-1);
}


class Distribution{
	int[string] vbl;
	this(){ distribution=one; error=zero; vbl["__dummy"]=0; }
	SetX!DVar freeVars;
	DExpr distribution;
	DExpr error;

	SetX!DVar tmpVars;
	void marginalizeTemporaries(){
		foreach(v;tmpVars.dup) marginalize(v);
	}
	void marginalizeLocals(Distribution enclosing,scope void delegate(DVar) hook=null){
		foreach(x;this.freeVars.dup){
			if(x in enclosing.freeVars) continue;
			if(hook) hook(x);
			marginalize(x);
		}
	}	

	Distribution dup(){
		auto r=new Distribution();
		r.vbl=vbl;
		r.freeVars=freeVars.dup();
		r.distribution=distribution;
		r.error=error;
		r.q=q;
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

	Distribution orderedJoin(Distribution b)in{assert(freeVarsOrdered && b.freeVarsOrdered);}body{
		auto r=dup();
		auto bdist = b.distribution.substituteAll(b.orderedFreeVars,cast(DExpr[])orderedFreeVars);
		r.distribution=r.distribution+bdist;
		r.error=r.error+b.error;
		assert(r.context is b.context);
		return r;
	}
	
	Distribution join(Distribution orig,Distribution b){
		auto r=new Distribution();
		auto d1=distribution;
		auto d2=b.distribution;
		// TODO: this should be unnecessary with dead variable analysis
		foreach(x;this.freeVars) if(x !in orig.freeVars){ assert(d1 is zero || d1.hasFreeVar(x)); d1=dIntSmp(x,d1,one); }
		foreach(x;b.freeVars) if(x !in orig.freeVars){ assert(d2 is zero || d2.hasFreeVar(x)); d2=dIntSmp(x,d2,one); }
		//// /// // /
		r.vbl=orig.vbl;
		r.freeVars=orig.freeVars;
		r.tmpVars=orig.tmpVars;
		r.distribution=d1+d2;
		r.error=orig.error;
		r.q=q;
		r.context=context;
		assert(q is b.q);
		assert(context is b.context);
		assert(!freeVarsOrdered && !b.freeVarsOrdered);
		if(error !is zero || b.error !is zero)
			r.error=(orig.error+error+b.error).simplify(one);
		return r;
	}

	DVar q;
	DContextVars context=null;

	void addArgsWithContext(DExpr[] args)in{assert(!context&&!q);}body{
		q=dVar("`q");
		assert(!!q);
		context=dContextVars("γ",q);
		args~=context;
		distribute(dFun(q,args)); // TODO: constant name sufficient?
	}
	
	void deleteContext(size_t nParams)in{ assert(!!q); }body{
		auto vars=iota(0,nParams).map!(x=>dVar("__p"~lowNum(x))).array;
		auto fun=dFun(q,cast(DExpr[])vars); // TODO: get rid of cast
		distribution=distribution.substituteFun(q,fun,vars,SetX!DVar.init).simplify(one);
		error=error.substituteFun(q,fun,vars,SetX!DVar.init).simplify(one);
		context=null;
		q=null;
	}

	void assumeInputNormalized(size_t nParams){
		auto vars=iota(0,nParams).map!(x=>dVar("__p"~lowNum(x))).array;
		auto fun=dFun(q,cast(DExpr[])vars); // TODO: get rid of cast
		DExpr tdist=fun;
		foreach(v;vars) tdist=dIntSmp(v,tdist,one);
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
	
	DVar declareVar(string name){
		auto v=dVar(name);
		if(v in freeVars) return null;
		freeVars.insert(v);
		return v;
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
	void freeVar(string name){
		while(name in vbl&&vbl[name]!=0&&dVar(name~vbl[name].lowNum)!in freeVars)
			--vbl[name];
	}
	DVar getTmpVar(string name){
		auto v=getVar(name);
		tmpVars.insert(v);
		return v;
	}

	DExpr computeProbability(DExpr cond){
		auto tdist=distribution*cond.simplify(one);
		foreach(v;freeVars) tdist=dIntSmp(v,tdist,one);
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
	}
	void assign(DVar var,DExpr exp,Type ty){
		if(distribution is zero) return;
		// assert(distribution.hasFreeVar(var)); // ∫dx0
		auto nvar=getVar(var.name);
		distribution=distribution.substitute(var,nvar);
		exp=exp.substitute(var,nvar);
		distribute(dDelta(var,exp,ty));
		marginalize(nvar);
	}
	void marginalize(DVar var)in{assert(var in freeVars); }body{
		//assert(distribution.hasFreeVar(var),text(distribution," ",var));
		//writeln("marginalizing: ",var,"\ndistribution: ",distribution,"\nmarginalized: ",dInt(var,distribution));
		distribution=dIntSmp(var,distribution,one);
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
			factor=dIntSmp(v,factor,one);
		if(context) factor=dInt(context,factor);
		factor=factor+error;
		distribution=(dIvr(DIvr.Type.neqZ,factor)*(distribution/factor)).simplify(one);
		error=(dIvr(DIvr.Type.eqZ,factor)+dIvr(DIvr.Type.neqZ,factor)*(error/factor)).simplify(one);
	}
	DExpr call(Distribution q,DExpr[] args,Type[] ty)in{assert(!!q.q);}body{
		DExpr rdist=q.distribution;
		DExpr rerr=q.error;
		import hashtable;
		auto context=freeVars.dup;
		if(this.context) context.insert(this.context);
		DVar[] r;
		foreach(v;q.orderedFreeVars){
			r~=getTmpVar("__r");
			rdist=rdist.substitute(v,r[$-1]);
			rerr=rerr.substitute(v,r[$-1]);
		}
		DVar[] vars;
		auto oldDist=distribution;
		foreach(i,a;args){
			auto var=getTmpVar("__arg");
			vars~=var;
			oldDist=oldDist*dDelta(var,a,ty[i]);
		}
		distribution = rdist.substituteFun(q.q,oldDist,vars,context);
		auto nerror = rerr.substituteFun(q.q,oldDist,vars,context);
		//dw("+--\n",oldDist,"\n",rdist,"\n",distribution,"\n--+");
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

	DExpr toDExpr()in{assert(freeVarsOrdered);}body{
		auto db1=dDeBruijnVar(1);
		auto r=dDiscDelta(db1,dRecord(["tag":one,"values":dTuple(cast(DExpr[])orderedFreeVars)]))*distribution.incDeBruijnVar(1,0);
		foreach(v;orderedFreeVars) r=dInt(v,r);
		r=r+dDiscDelta(db1,dRecord(["tag":zero]))*error;
		return dLambda(r);
	}

	static Distribution fromDExpr(DExpr dexpr,DVar[] orderedFreeVars,Type[] types){
		auto r=new Distribution();
		auto db1=dDeBruijnVar(1);
		dexpr=dexpr.incDeBruijnVar(1,0);
		foreach(i,v;orderedFreeVars){
			r.freeVars.insert(v);
			r.initialize(v,dIndex(dField(db1,"values"),dℤ(i)),types[i]);
		}
		r.distribution=dInt(r.distribution*dIvr(DIvr.Type.eqZ,dField(db1,"tag")-one)*dApply(dexpr,db1));
		r.error=dInt(dIvr(DIvr.Type.eqZ,dField(db1,"tag"))*dApply(dexpr,db1));
		r.orderFreeVars(orderedFreeVars);
		return r;
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
		foreach(v;vars) r~=(formatting==Format.mathematica?v.toString(formatting)~"_":v.toString(formatting))~",";
		if(vars.length) r=r[0..$-1];
		r~=middle~distribution.toString(formatting);
		if(error !is zero) r~="\n"~errstr~error.toString(formatting);
		return r;
	}
}

