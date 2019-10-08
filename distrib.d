// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.algorithm, std.range, std.array, std.conv;

import options, dexpr, ast.expression, util;

struct Cond{
	DExpr cond;
	string error;
}
DExpr extractConditions(Cond[] conds){
	DExpr r=one;
	foreach(x;conds) r=r*x.cond;
	return r;
}
enum distribNames=[__traits(allMembers,distrib)].filter!(x=>x.endsWith("PDF")).map!(x=>x[0..$-"PDF".length]).array;

import std.traits: ParameterIdentifierTuple;
enum paramNames(string name)=[ParameterIdentifierTuple!(mixin(name~"PDF"))[1..$]];

DExpr pdf(string name)(DVar var,DExpr[] args)in{assert(args.length==paramNames!name.length);}body{
	return mixin(text(name,"PDF(var,",iota(paramNames!name.length).map!(i=>text("args[",i,"]")).join(","),")"));
}

Cond[] cond(string name)(DExpr[] args)in{assert(args.length==paramNames!name.length);}body{
	return mixin(text(name,"Cond(",iota(paramNames!name.length).map!(i=>text("args[",i,"]")).join(","),")"));
}

DExpr gaussPDF(DVar var,DExpr μ,DExpr ν){
	auto dist=one/(2*dΠ*ν)^^(one/2)*dE^^-((var-μ)^^2/(2*ν));
	return dNeqZ(ν)*dist+dEqZ(ν)*dDelta(var-μ);
}
Cond[] gaussCond(DExpr μ,DExpr ν){
	return [Cond(dGeZ(ν),"negative variance")];
}

DExpr chiSquaredPDF(DVar var,DExpr k){
	return dNeqZ(k)*dGeZ(var)/(2^^(k/2)*dGamma(k/2))*var^^(k/2-1)*dE^^(-var/2)+
		dEqZ(k)*dDelta(var);
}
Cond[] chiSquaredCond(DExpr k){
	return [Cond(dIsℤ(k),"k must be an integer"),
	        Cond(dGeZ(k),"k must be non-negative")];
}

DExpr rayleighPDF(DVar var,DExpr ν){
	auto dist=var/(ν)*dE^^-((var)^^2/(2*ν)) * dGeZ(var);
	return dNeqZ(ν)*dist+dEqZ(ν)*dDelta(var);
}
Cond[] rayleighCond(DExpr ν){
	return [Cond(dGeZ(ν),"negative scale")];
}

DExpr truncatedGaussPDF(DVar var,DExpr μ,DExpr ν,DExpr a,DExpr b){
	auto gdist=one/(2*dΠ)^^(one/2)*dE^^-((var-μ)^^2/(2*ν));
	auto dist = gdist/(ν)/(dGaussInt((b-μ)/ν^^(one/2))-dGaussInt((a-μ)/(ν)^^(one/2)));
	return (dNeqZ(ν)*dist+dEqZ(ν)*dDelta(var-μ))*dBounded!"[]"(var,a,b);
}
Cond[] truncatedGaussCond(DExpr μ,DExpr ν,DExpr a,DExpr b){
	return [Cond(dGeZ(ν),"negative variance"),
	        Cond(dLt(a,b),"empty range")];
}

DExpr paretoPDF(DVar var, DExpr a, DExpr b) {
	auto dist = a * b^^a / var^^(a+one);
	return dist * dLe(b,var);
}
Cond[] paretoCond(DExpr a, DExpr b){
	return [Cond(dGeZ(a),"negative scale"),
	        Cond(dGeZ(b),"negative shape")];
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	auto diff=b-a, dist=dBounded!"[]"(var,a,b)/diff;
	return dNeqZ(diff)*dist+dEqZ(diff)*dDelta(var-a);
}
Cond[] uniformCond(DExpr a,DExpr b){
	return [Cond(dLe(a,b),"empty range")];
}

DExpr flipPDF(DVar var,DExpr p){
	return dDelta(var)*(1-p)+dDelta(1-var)*p;
}
Cond[] flipCond(DExpr p){
	return [Cond(dBounded!"[]"(p,zero,one),"parameter ouside range [0..1]")];
}

DExpr uniformIntPDFNnorm(DVar var,DExpr a,DExpr b){
	var=var.incDeBruijnVar(1,0);
	a=a.incDeBruijnVar(1,0), b=b.incDeBruijnVar(1,0);
	auto x=db1;
	return dSumSmp(dBounded!"[]"(x,a,b)*dDelta(var-x),one);
}

DExpr uniformIntPDF(DVar var,DExpr a,DExpr b){
	auto nnorm=uniformIntPDFNnorm(var,a,b);
	return nnorm/dIntSmp(var,nnorm,one);
}
Cond[] uniformIntCond(DExpr a,DExpr b){
	a=a.incDeBruijnVar(1,0), b=b.incDeBruijnVar(1,0);
	auto x=db1; // TODO: get rid of this!
	auto nnorm=uniformIntPDFNnorm(x,a,b);
	auto norm=dIntSmp(nnorm,one);
	return [Cond(dNeqZ(norm),"no integers in range")];
}

DExpr binomialPDF(DVar var,DExpr n,DExpr p){
	n=n.incDeBruijnVar(1,0), p=p.incDeBruijnVar(1,0);
	auto k=db1;
	return dSumSmp(dNChooseK(n,k)*p^^k*(1-p)^^(n-k)*dDelta(k-var),one);
}
Cond[] binomialCond(DExpr n,DExpr p){
	return [Cond(dIsℤ(n),"n must be an integer"),
	        Cond(dGeZ(n),"n must be non-negative"),
	        Cond(dBounded!"[]"(p,zero,one),"parameter p out of range [0..1]")];
}

DExpr negBinomialPDF(DVar var,DExpr r,DExpr p){
	r=r.incDeBruijnVar(1,0), p=p.incDeBruijnVar(1,0);
	auto k=db1;
	return dSumSmp(dGeZ(k)*(dGamma(r+k)/(dGamma(r)*dGamma(k+1)))*p^^r*(1-p)^^k*dDelta(k-var),one);
}
Cond[] negBinomialCond(DExpr r,DExpr p){
	return [Cond(dGtZ(r),"r must be positive"),
	        Cond(dBounded!"[]"(p,zero,one),"parameter ouside range [0..1]")];
}


DExpr geometricPDF(DVar var,DExpr p){
	p=p.incDeBruijnVar(1,0);
	auto i=db1;
	return dSumSmp(dGeZ(i)*p*(1-p)^^i*dDelta(i-var),one);
}
Cond[] geometricCond(DExpr p){
	return [Cond(dBounded!"[]"(p,zero,one),"parameter ouside range [0..1]")];
}

DExpr poissonPDF(DVar var,DExpr λ){
	var=var.incDeBruijnVar(1,0), λ=λ.incDeBruijnVar(1,0);
	auto x=db1;
	return dE^^-λ*dSumSmp(dGeZ(x)*dDelta(var-x)*λ^^x/dGamma(x+1),one);
}
Cond[] poissonCond(DExpr λ){
	return [Cond(dGeZ(λ),"λ must be non-negative")];
}

DExpr betaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=dNeqZ(α)*dNeqZ(β)*
		var^^(α-1)*(1-var)^^(β-1)*dBounded!"[]"(var,zero,one)+
		dEqZ(α)*dDelta(var)+
		dEqZ(β)*dDelta(1-var);
	return nnorm/dIntSmp(var,nnorm,one);
}
Cond[] betaCond(DExpr α,DExpr β){
	return [Cond(dGeZ(α),"α must be non-negative"),
	        Cond(dGeZ(β),"β must be non-negative")];
}

DExpr gammaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=dNeqZ(α)*var^^(α-1)*dE^^(-β*var)*dGeZ(var)+dEqZ(α)*dDelta(var);
	return nnorm/dIntSmp(var,nnorm,one);
}
Cond[] gammaCond(DExpr α,DExpr β){
	return [Cond(dGeZ(α),"α must be non-negative"),
	        Cond(dGtZ(β),"β must be positive")];
}

DExpr laplacePDF(DVar var, DExpr μ, DExpr b){
	return dNeqZ(b)*dE^^(-dAbs(var-μ)/b)/(2*b)+
		dEqZ(b)*dDelta(μ-var);
}
Cond[] laplaceCond(DExpr μ,DExpr b){
	return [Cond(dGeZ(b),"b must be non-negative")];
}

DExpr cauchyPDF(DVar var,DExpr x0,DExpr γ){
	return dNeqZ(γ)/(dΠ*γ*(1+((var-x0)/γ)^^2))+
		dEqZ(γ)*dDelta(x0-var);
}
Cond[] cauchyCond(DExpr x0,DExpr γ){
	return [Cond(dGeZ(γ),"γ must be non-negative")];
}

DExpr exponentialPDF(DVar var,DExpr λ){
	return λ*dE^^(-λ*var)*dGeZ(var);
}
Cond[] exponentialCond(DExpr λ){
	return [Cond(dGtZ(λ),"λ must be positive")];
}


DExpr studentTPDF(DVar var,DExpr ν){ // this has a mean only if ν>1. how to treat this?
	auto nnorm=(1+var^^2/ν)^^(-(ν+1)/2);
	return dNeqZ(ν)*nnorm/dIntSmp(var,nnorm,one)+dEqZ(ν)*dDelta(var);
}
Cond[] studentTCond(DExpr ν){
	return [Cond(dGeZ(ν),"ν must be non-negative")];
}

DExpr weibullPDF(DVar var,DExpr λ,DExpr k){
	return dNeqZ(λ)*dNeqZ(k)*
		dGeZ(var)*k/λ*(var/λ)^^(k-1)*dE^^(-(var/λ)^^k)+
		dNeqZ(dEqZ(λ)+dEqZ(k))*dDelta(var);
}
Cond[] weibullCond(DExpr λ,DExpr k){
	return [Cond(dGeZ(λ),"λ must be non-negative"),
	        Cond(dGeZ(k),"k must be non-negative")];
}

DExpr categoricalPDF(DVar var,DExpr p){
	var=var.incDeBruijnVar(1,0), p=p.incDeBruijnVar(1,0);
	auto dbv=db1;
	auto nnorm=dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv]*dDelta(var-dbv));
	return nnorm;///dIntSmp(nnorm);
}
Cond[] categoricalCond(DExpr p){
	p=p.incDeBruijnVar(1,0);
	auto dbv=db1;
	return [Cond(dEqZ(dSum(dBounded!"[)"(dbv,zero,dField(p,"length")*dLtZ(p[dbv])))),"probability of category should be non-negative"),
	        Cond(dEqZ(dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv])-1),"probabilities should sum up to 1")];
}

DExpr diracPDF(DVar var,DExpr e){
	import ast.type;
	return dDelta(e,var,varTy("a",typeTy));
}
Cond[] diracCond(DExpr e){
	return [];
}


class Distribution{
	int[string] vbl;
	this(){ distribution=one; error=zero; vbl["__dummy"]=0; }
	SetX!DNVar freeVars;
	DExpr distribution;
	DExpr error;


	bool hasArgs=false;
	DNVar[] args;
	bool argsIsTuple=true;
	DNVar context;
	
	void addArgs(DNVar[] args,bool isTuple,DNVar ctx)in{
		assert(!hasArgs);
		assert(!context);
		assert(isTuple||args.length==1);
		foreach(v;args) assert(v in freeVars);
		assert(!ctx||ctx in freeVars);
	}body{
		hasArgs=true;
		this.args=args;
		argsIsTuple=isTuple;
		context=ctx;
		foreach(v;args) freeVars.remove(v);
		if(context) freeVars.remove(context);
	}
	void addArgs(size_t nargs,bool isTuple,DNVar ctx){
		DNVar[] args=[];
		foreach(i;0..nargs) args~=getVar("__a");
		addArgs(args,isTuple,ctx);
	}

	bool hasArg(DNVar v){
		 // TODO: use more efficient search?
		return args.canFind(v) || context&&v==context;
	}
	
	bool freeVarsOrdered=false;
	DNVar[] orderedFreeVars;
	bool isTuple=true;
	void orderFreeVars(DNVar[] orderedFreeVars,bool isTuple)in{
		assert(!freeVarsOrdered);
	   /+assert(orderedFreeVars.length==freeVars.length);
		foreach(v;orderedFreeVars)
			assert(v in freeVars);
		// TODO: this does not check that variables occur at most once in orderedFreeVars
		assert(isTuple||orderedFreeVars.length==1);+/
	}body{
		freeVarsOrdered=true;
		this.orderedFreeVars=orderedFreeVars;
		this.isTuple=isTuple;
	}
	
	SetX!DNVar tmpVars;
	void marginalizeTemporaries(){
		foreach(v;tmpVars.dup) marginalize(v);
	}
	void marginalizeLocals(Distribution enclosing,scope void delegate(DNVar) hook=null){
		foreach(x;this.freeVars.dup){
			if(x in enclosing.freeVars) continue;
			if(hook) hook(x);
			marginalize(x);
		}
	}	

	Distribution dup(){
		auto r=new Distribution();
		r.vbl=vbl.dup;
		r.freeVars=freeVars.dup();
		r.distribution=distribution;
		r.error=error;
		r.freeVarsOrdered=freeVarsOrdered;
		r.hasArgs=hasArgs;
		r.args=args.dup;
		r.argsIsTuple=argsIsTuple;
		r.context=context;
		r.orderedFreeVars=orderedFreeVars.dup;
		r.isTuple=isTuple;
		return r;
	}

	Distribution dupNoErr(){
		auto r=dup();
		r.error=zero;
		return r;
	}

	Distribution orderedJoin(Distribution b)in{assert(freeVarsOrdered && b.freeVarsOrdered);}body{
		auto r=dup();
		auto bdist = b.distribution.substituteAll(cast(DVar[])b.orderedFreeVars,cast(DExpr[])orderedFreeVars);
		r.distribution=r.distribution+bdist;
		r.error=r.error+b.error;
		assert(r.args == b.args);
		return r;
	}
	
	Distribution join(Distribution orig,Distribution b){
		auto r=new Distribution();
		auto d1=distribution;
		auto d2=b.distribution;
		// TODO: this should be unnecessary with dead variable analysis
		foreach(x;this.freeVars) if(x !in orig.freeVars){ assert(d1 == zero || d1.hasFreeVar(x)); d1=dIntSmp(x,d1,one); }
		foreach(x;b.freeVars) if(x !in orig.freeVars){ assert(d2 == zero || d2.hasFreeVar(x)); d2=dIntSmp(x,d2,one); }
		//// /// // /
		r.vbl=orig.vbl;
		r.freeVars=orig.freeVars;
		r.tmpVars=orig.tmpVars;
		r.distribution=d1+d2;
		r.error=orig.error;
		r.hasArgs=orig.hasArgs;
		r.args=orig.args;
		r.argsIsTuple=orig.argsIsTuple;
		r.context=orig.context;
		r.orderedFreeVars=orig.orderedFreeVars;
		r.isTuple=isTuple;
		assert(hasArgs==b.hasArgs && args == b.args);
		assert(!freeVarsOrdered && !b.freeVarsOrdered);
		if(error != zero || b.error != zero)
			r.error=orig.error+error+b.error;
		return r;
	}
	
	DNVar declareVar(string name){
		auto v=dVar(name);
		if(v in freeVars) return null;
		if(hasArg(v)) return null;
		freeVars.insert(v);
		return v;
	}
	DNVar getVar(string name){
		DNVar v;
		while(!v){ // TODO: fix more elegantly!
			int suffix=++vbl[name];
			string nn=name~suffix.lowNum;
			v=declareVar(nn);
		}
		return v;
	}
	DNVar getPrimedVar(string name){
		DNVar v;
		for(string nn=name;!v;nn~="'")
			v=declareVar(nn);
		return v;
	}
	void freeVar(string name){
		while(name in vbl&&vbl[name]!=0&&dVar(name~vbl[name].lowNum)!in freeVars)
			--vbl[name];
	}
	DNVar getTmpVar(string name){
		auto v=getVar(name);
		tmpVars.insert(v);
		return v;
	}

	DExpr computeProbability(DExpr cond){
		auto tdist=distribution*cond.simplify(one);
		foreach(v;freeVars) tdist=dIntSmp(v,tdist,one);
		return tdist;
	}

	void assertTrue(DExpr cond,lazy string msg){
		if(opt.noCheck) return;
		error=(error+computeProbability(dEqZ(cond))).simplify(one);
		distribution=distribution*cond;
	}
	void distribute(DExpr pdf){ distribution=distribution*pdf; }
	void initialize(DNVar var,DExpr exp,Expression ty)in{
		assert(var&&exp&&ty);
	}body{
		assert(!distribution.hasFreeVar(var));
		distribute(dDelta(exp,var,ty));
	}
	void assign(DNVar var,DExpr exp,Expression ty){
		if(distribution is zero) return;
		// assert(distribution.hasFreeVar(var)); // ∫dx0
		auto nvar=getVar(var.name);
		distribution=distribution.substitute(var,nvar);
		exp=exp.substitute(var,nvar);
		distribute(dDelta(exp,var,ty));
		marginalize(nvar);
	}
	void marginalize(DNVar var)in{assert(var in freeVars,text(var)); }body{
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
		foreach(v;freeVars) factor=dIntSmp(v,factor,one);
		factor=factor+error;
		distribution=distribution/factor;
		if(!opt.noCheck) distribution=dNeqZ(factor)*distribution;
		distribution=distribution.simplify(one);
		if(!opt.noCheck) error=(dEqZ(factor)+dNeqZ(factor)*(error/factor)).simplify(one);
		/+import type;
		Distribution r=fromDExpr(dLambda(dNormalize(dApply(toDExpr().incDeBruijnVar(1,0),db1))),args.length,argsIsTuple,orderedFreeVars,isTuple,orderedFreeVars.map!(x=>cast(Expression)contextTy).array);
		r.simplify();
		distribution=r.distribution;
		if(!opt.noCheck) error=r.error;+/
	}
	DExpr call(DExpr q,DExpr arg){
		auto vars=freeVars.dup;
		auto r=getTmpVar("__r");
		if(!opt.noCheck){
			auto ndist=dDistApply(dApply(q,arg),db1);
			auto nerror=distribution*dInt(dMCase(db1,zero,one)*ndist);
			distribution=distribution*dInt(dMCase(db1,dDiscDelta(db1,r),zero)*ndist);
			foreach(v;vars) nerror=dInt(v,nerror);
			error=error+nerror;
		}else distribution=distribution*dDistApply(dApply(q,arg),r);
		return r;
	}
	DExpr call(Distribution q,DExpr arg,Expression ty){
		return call(q.toDExpr(),arg);
	}
	void simplify(){
		distribution=distribution.simplify(one); // TODO: this shouldn't be necessary!
		error=error.simplify(one);
	}

	private DExpr toDExprLambdaBody(bool stripContext=false)in{
		assert(!stripContext||isTuple&&orderedFreeVars.length==2);
	}body{
		auto vars=orderedFreeVars;
		assert(isTuple||vars.length==1);
		auto values=(isTuple&&!stripContext?dTuple(cast(DExpr[])vars):vars[0]).incDeBruijnVar(1,0);
		auto dist=distribution.incDeBruijnVar(2,0);
		auto allVars=cast(DVar[])args;
		DExpr[] allVals;
		if(context){
			allVars~=context;
			allVals=iota(0,args.length).map!(i=>argsIsTuple?db2[0.dℚ][i.dℚ]:db2[0.dℚ]).array~db2[1.dℚ];
		}else{
			allVals=iota(0,args.length).map!(i=>argsIsTuple?db2[i.dℚ]:db2).array;
		}
		dist=dist.substituteAll(allVars,allVals);
		if(!opt.noCheck){
			auto r=dist*dDiscDelta(dVal(values),db1);
			foreach(v;vars) r=dInt(v,r);
			r=r+dDiscDelta(dErr,db1)*error.substituteAll(allVars,allVals);
			return dDistLambda(r);
		}else{
			auto r=dist*dDiscDelta(values,db1);
			foreach(v;vars) r=dInt(v,r);
			return dDistLambda(r);
		}
	}
	
	DExpr toDExpr()in{assert(freeVarsOrdered&&hasArgs);}body{
		return dLambda(toDExprLambdaBody());
	}

	DExpr toDExprWithContext(DExpr context,bool stripContext=false)in{
		assert(!!this.context);
		assert(freeVarsOrdered&&hasArgs);
	}body{
		auto bdy=toDExprLambdaBody(stripContext);
		context=context.incDeBruijnVar(1,0);
		bdy=bdy.substitute(db1,dTuple([db1,context]));
		return dLambda(bdy);
	}
	
	static Distribution fromDExpr(DExpr dexpr,size_t nargs,bool argsIsTuple,DNVar[] orderedFreeVars,bool isTuple,Expression[] types)in{
		assert(argsIsTuple||nargs==1);
		assert(isTuple||orderedFreeVars.length==1);
	}body{
		auto r=new Distribution();
		dexpr=dexpr.incDeBruijnVar(1,0);
		auto values=db1;
		foreach(i,v;orderedFreeVars){
			r.freeVars.insert(v);
			auto value=isTuple?dIndex(values,dℚ(i)):values;
			r.initialize(v,value,types[i]);
		}
		r.addArgs(nargs,argsIsTuple,null);
		auto args=argsIsTuple?dTuple(cast(DExpr[])r.args):r.args[0];
		auto ndist=dDistApply(dApply(dexpr,args),db1);
		if(!opt.noCheck){
			r.distribution=dInt(r.distribution*dInt(dMCase(db1,dDiscDelta(db1,db3),zero)*ndist));
			r.error=dInt(dMCase(db1,zero,one)*ndist);
		}else r.distribution=dInt(r.distribution*ndist);
		r.orderFreeVars(orderedFreeVars,isTuple);
		return r;
	}

	override string toString(){
		return toString(Format.default_);
	}
	
	string argsToString(Format formatting){
		if(formatting==Format.mathematica)
			return args.length?(freeVars.length?", ":"")~args.map!(a=>a.toString(formatting)~"_").join(","):"";
		return args.map!(a=>a.toString(formatting)).join(",");
	}

	string varsToString(Format formatting){
		DNVar[] vars;
		if(freeVarsOrdered) vars=orderedFreeVars;
		else vars=freeVars.array;
		string r;
		foreach(v;vars) r~=(formatting==Format.mathematica?v.toString(formatting)~"_":v.toString(formatting))~",";
		if(vars.length) r=r[0..$-1];
		return r;
	}
	
	string toString(Format formatting){
		string initial,middle,errstr;
		auto astr=argsToString(formatting);
		if(formatting==Format.mathematica){
			initial="p[";
			middle=text(astr,"] := ");
			errstr=text("Pr_error[",astr.length?astr:"","] := ");
		}else{
			initial="p(";
			middle=text(astr.length?"|":"",astr,") = ");
			errstr=text("Pr[error",astr.length?"|":"",astr,"] = ");
		}
		string r=initial~varsToString(formatting);
		r~=middle~distribution.toString(formatting);
		if(error != zero) r~="\n"~errstr~error.toString(formatting);
		return r;
	}
}

