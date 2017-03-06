// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.algorithm, std.range, std.array, std.conv;

import options, dexpr, expression, util;

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
	return dIvr(DIvr.Type.neqZ,ν)*dist+dIvr(DIvr.Type.eqZ,ν)*dDelta(var-μ);
}
Cond[] gaussCond(DExpr μ,DExpr ν){
	return [Cond(dIvr(DIvr.Type.leZ,-ν),"negative variance")];
}

DExpr rayleighPDF(DVar var,DExpr ν){
	auto dist=var/(ν)*dE^^-((var)^^2/(2*ν)) * dIvr(DIvr.Type.leZ,-var);
	return dIvr(DIvr.Type.neqZ,ν)*dist+dIvr(DIvr.Type.eqZ,ν)*dDelta(var);
}
Cond[] rayleighCond(DExpr ν){
	return [Cond(dIvr(DIvr.Type.leZ,-ν),"negative scale")];
}

DExpr truncatedGaussPDF(DVar var,DExpr μ,DExpr ν,DExpr a,DExpr b){
	auto gdist=one/(2*dΠ)^^(one/2)*dE^^-((var-μ)^^2/(2*ν));
	auto dist = gdist/(ν)/(dGaussInt((b-μ)/ν^^(one/2))-dGaussInt((a-μ)/(ν)^^(one/2)))*dBounded!"[]"(var,a,b);
	return dIvr(DIvr.Type.neqZ,ν)*dist+dIvr(DIvr.Type.eqZ,ν)*dDelta(var-μ);
}
Cond[] truncatedGaussCond(DExpr μ,DExpr ν,DExpr a,DExpr b){
	return [Cond(dIvr(DIvr.Type.leZ,-ν),"negative variance"),
	        Cond(dIvr(DIvr.Type.lZ,a-b),"empty range")];
}

DExpr paretoPDF(DVar var, DExpr a, DExpr b) {
	auto dist = a * b^^a / var^^(a+one);
	return dist * dIvr(DIvr.Type.leZ, b-var);
}
Cond[] paretoCond(DExpr a, DExpr b){
	return [Cond(dIvr(DIvr.Type.leZ,-a),"negative scale"),
	        Cond(dIvr(DIvr.Type.leZ,-b),"negative shape")];
}

DExpr uniformPDF(DVar var,DExpr a,DExpr b){
	auto diff=b-a, dist=dBounded!"[]"(var,a,b)/diff;
	return dIvr(DIvr.Type.neqZ,diff)*dist+dIvr(DIvr.Type.eqZ,diff)*dDelta(var-a);
}
Cond[] uniformCond(DExpr a,DExpr b){
	return [Cond(dIvr(DIvr.Type.leZ,a-b),"empty range")];
}

DExpr flipPDF(DVar var,DExpr p){
	return dDelta(var)*(1-p)+dDelta(1-var)*p;
}
Cond[] flipCond(DExpr p){
	return [Cond(dIvr(DIvr.Type.leZ,-p)*dIvr(DIvr.Type.leZ,p-1),"parameter ouside range [0..1]")];
}

DExpr uniformIntPDFNnorm(DVar var,DExpr a,DExpr b){
	var=var.incDeBruijnVar(1,0);
	a=a.incDeBruijnVar(1,0), b=b.incDeBruijnVar(1,0);
	auto x=dDeBruijnVar(1);
	return dSumSmp(dBounded!"[]"(x,a,b)*dDelta(var-x),one);
}

DExpr uniformIntPDF(DVar var,DExpr a,DExpr b){
	auto nnorm=uniformIntPDFNnorm(var,a,b);
	return nnorm/dIntSmp(var,nnorm,one);
}
Cond[] uniformIntCond(DExpr a,DExpr b){
	a=a.incDeBruijnVar(1,0), b=b.incDeBruijnVar(1,0);
	auto x=dDeBruijnVar(1); // TODO: get rid of this!
	auto nnorm=uniformIntPDFNnorm(x,a,b);
	auto norm=dIntSmp(nnorm,one);
	return [Cond(dIvr(DIvr.Type.neqZ,norm),"no integers in range")];
}

DExpr poissonPDF(DVar var,DExpr λ){
	var=var.incDeBruijnVar(1,0), λ=λ.incDeBruijnVar(1,0);
	auto x=dDeBruijnVar(1);
	return dE^^-λ*dSumSmp(dIvr(DIvr.Type.leZ,-x)*dDelta(var-x)*λ^^x/dGamma(x+1),one);
}
Cond[] poissonCond(DExpr λ){
	return [Cond(dIvr(DIvr.Type.lZ,-λ),"λ must be positive")];
}

DExpr betaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=var^^(α-1)*(1-var)^^(β-1)*dBounded!"[]"(var,zero,one);
	return nnorm/dIntSmp(var,nnorm,one);
}
Cond[] betaCond(DExpr α,DExpr β){
	return [Cond(dIvr(DIvr.Type.lZ,-α),"α must be positive"),
	        Cond(dIvr(DIvr.Type.lZ,-β),"β must be positive")];
}

DExpr gammaPDF(DVar var,DExpr α,DExpr β){
	auto nnorm=var^^(α-1)*dE^^(-β*var)*dIvr(DIvr.Type.leZ,-var);
	return nnorm/dIntSmp(var,nnorm,one);
}
Cond[] gammaCond(DExpr α,DExpr β){
	return [Cond(dIvr(DIvr.Type.lZ,-α),"α must be positive"),
	        Cond(dIvr(DIvr.Type.lZ,-β),"β must be positive")];
}

DExpr laplacePDF(DVar var, DExpr μ, DExpr b){
      auto positive = dE^^(-(var-μ)/b)/(2*b);
      auto negative = dE^^((var-μ)/b)/(2*b);
      auto dif = var - μ;
      return positive * dIvr(DIvr.Type.leZ,-dif) + negative * dIvr(DIvr.Type.leZ,var);
}
Cond[] laplaceCond(DExpr μ,DExpr b){
	return [Cond(dIvr(DIvr.Type.lZ,-b),"b must be positive")];
}


DExpr exponentialPDF(DVar var,DExpr λ){
	return λ*dE^^(-λ*var)*dIvr(DIvr.Type.leZ,-var);
}
Cond[] exponentialCond(DExpr λ){
	return [Cond(dIvr(DIvr.Type.lZ,-λ),"λ must be positive")];
}


DExpr studentTPDF(DVar var,DExpr ν){ // this has a mean only if ν>1. how to treat this?
	auto nnorm=(1+var^^2/ν)^^(-(ν+1)/2);
	return nnorm/dIntSmp(var,nnorm,one);
}
Cond[] studentTCond(DExpr ν){
	return [Cond(dIvr(DIvr.Type.lZ,-ν),"ν must be positive")];
}

DExpr weibullPDF(DVar var,DExpr λ,DExpr k){
	return dIvr(DIvr.Type.leZ,-var)*k/λ*(var/λ)^^(k-1)*dE^^(-(var/λ)^^k);
}
Cond[] weibullCond(DExpr λ,DExpr k){
	return [Cond(dIvr(DIvr.Type.lZ,-λ),"λ must be positive"),
	        Cond(dIvr(DIvr.Type.lZ,-k),"k must be positive")];
}

DExpr categoricalPDF(DVar var,DExpr p){
	var=var.incDeBruijnVar(1,0), p=p.incDeBruijnVar(1,0);
	auto dbv=dDeBruijnVar(1);
	auto nnorm=dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv]*dDelta(var-dbv));
	return nnorm;///dIntSmp(nnorm);
}
Cond[] categoricalCond(DExpr p){
	p=p.incDeBruijnVar(1,0);
	auto dbv=dDeBruijnVar(1);
	return [Cond(dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length")*dIvr(DIvr.Type.lZ,p[dbv])))),"probability of category should be non-negative"),
	        Cond(dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv])-1),"probabilities should sum up to 1")];
}

DExpr diracPDF(DVar var,DExpr e){
	import type;
	return dDelta(var,e,varTy("a",typeTy));
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
		r.vbl=vbl;
		r.freeVars=freeVars.dup();
		r.distribution=distribution;
		r.error=error;
		r.q=q;
		r.nargs=nargs;
		r.freeVarsOrdered=freeVarsOrdered;
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
		assert(r.q == b.q && r.nargs == b.nargs);
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
		r.q=q;
		r.nargs=nargs;
		assert(q == b.q && nargs == b.nargs);
		assert(!freeVarsOrdered && !b.freeVarsOrdered);
		if(error != zero || b.error != zero)
			r.error=(orig.error+error+b.error).simplify(one);
		return r;
	}

	DNVar q;
	size_t nargs;

	void addArgs(DExpr[] args,bool isTuple,DExpr ctx)in{assert(!q);}body{
		q=dVar("`q");
		assert(!!q);
		nargs=args.length;
		assert(isTuple||args.length==1);
		auto arg=isTuple?dTuple(args):args[0];
		if(ctx){
			nargs=2;
			arg=dTuple([arg,ctx]);
		}
		distribute(dDistApply(q,arg)); // TODO: constant name sufficient?
	}
	
	void assumeInputNormalized(size_t nParams,bool isTuple){
		auto vars=iota(0,nParams).map!(x=>dVar("__p"~lowNum(x))).array;
		auto fun=dDistApply(q,isTuple?dTuple(cast(DExpr[])vars):vars[0]); // TODO: get rid of cast
		DExpr tdist=fun;
		foreach(v;vars) tdist=dIntSmp(v,tdist,one);
		DExpr doIt(DExpr e){
			auto h=e.getHoles!(x=>x == tdist?x:null);
			e=h.expr;
			foreach(hole;h.holes){
				assert(hole.expr == tdist);
				e=e.substitute(hole.var,one);
			}
			return e;
		}
		distribution=doIt(distribution).simplify(one);
		error=doIt(error).simplify(one);
	}
	
	DNVar declareVar(string name){
		auto v=dVar(name);
		if(v in freeVars) return null;
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
		error=(error+computeProbability(dIvr(DIvr.Type.eqZ,cond))).simplify(one);
		distribution=distribution*cond;
	}
	void distribute(DExpr pdf){ distribution=distribution*pdf; }
	void initialize(DNVar var,DExpr exp,Expression ty){
		assert(!distribution.hasFreeVar(var));
		distribute(dDelta(var,exp,ty));
	}
	void assign(DNVar var,DExpr exp,Expression ty){
		if(distribution is zero) return;
		// assert(distribution.hasFreeVar(var)); // ∫dx0
		auto nvar=getVar(var.name);
		distribution=distribution.substitute(var,nvar);
		exp=exp.substitute(var,nvar);
		distribute(dDelta(var,exp,ty));
		marginalize(nvar);
	}
	void marginalize(DNVar var)in{assert(var in freeVars); }body{
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
		factor=factor+error;
		distribution=(dIvr(DIvr.Type.neqZ,factor)*(distribution/factor)).simplify(one);
		error=(dIvr(DIvr.Type.eqZ,factor)+dIvr(DIvr.Type.neqZ,factor)*(error/factor)).simplify(one);
	}
	DExpr call(Distribution q,DExpr arg,Expression ty)in{assert(!!q.q);}body{ // TODO: get rid of 'ty'
		DExpr rdist=q.distribution;
		DExpr rerr=q.error;
		auto context=freeVars.dup;
		DNVar[] r;
		foreach(_;q.orderedFreeVars)
			r~=getTmpVar("__r");
		rdist=rdist.substituteAll(cast(DVar[])q.orderedFreeVars,cast(DExpr[])r);
		rerr=rerr.substituteAll(cast(DVar[])q.orderedFreeVars,cast(DExpr[])r);
		auto oldDist=distribution;
		auto db1=dDeBruijnVar(1);
		auto argDist=dLambda(dDelta(db1,arg.incDeBruijnVar(1,0),ty));
		distribution = rdist.substitute(q.q,argDist)*oldDist;
		auto nerror = rerr.substitute(q.q,argDist)*oldDist;
		//dw("+--\n",oldDist,"\n",rdist,"\n",distribution,"\n--+");
		foreach(v;context) nerror=dInt(v,nerror);
		error = error + nerror;
		return q.isTuple?dTuple(cast(DExpr[])r):r[0];
	}
	void simplify(){
		distribution=distribution.simplify(one); // TODO: this shouldn't be necessary!
		error=error.simplify(one);
	}
	override string toString(){
		return toString(Format.default_);
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

	private DExpr toDExprLambdaBody(bool stripContext=false)in{
		assert(!stripContext||isTuple&&orderedFreeVars.length==2);
	}body{
		auto db1=dDeBruijnVar(1);
		auto vars=orderedFreeVars;
		assert(isTuple||vars.length==1);
		auto values=(isTuple&&!stripContext?dTuple(cast(DExpr[])vars):vars[0]).incDeBruijnVar(1,0);
		auto r=dDiscDelta(db1,dRecord(["tag":one,"val":values]))*distribution.incDeBruijnVar(1,0);
		foreach(v;vars) r=dInt(v,r);
		r=r+dDiscDelta(db1,dRecord(["tag":zero]))*error;
		return dLambda(r).substitute(q,db1);
	}
	
	DExpr toDExpr()in{assert(freeVarsOrdered&&q);}body{
		return dLambda(toDExprLambdaBody());
	}

	DExpr toDExprWithContext(DExpr context,bool stripContext=false)in{
		assert(freeVarsOrdered&&q&&nargs==2);
	}body{
		auto db1=dDeBruijnVar(1),db2=dDeBruijnVar(2);
		auto bdy=toDExprLambdaBody(stripContext);
		context=context.incDeBruijnVar(1,0);
		bdy=bdy.substitute(db1,dLambda(dDistApply(db2,db1[0.dℚ])*dDiscDelta(db1[dℚ(1)],context)));
		return dLambda(bdy);
	}
	
	static Distribution fromDExpr(DExpr dexpr,size_t nargs,DNVar[] orderedFreeVars,bool isTuple,Expression[] types){
		auto r=new Distribution();
		auto db1=dDeBruijnVar(1);
		dexpr=dexpr.incDeBruijnVar(1,0);
		auto values=dField(db1,"val");
		foreach(i,v;orderedFreeVars){
			r.freeVars.insert(v);
			auto value=isTuple?dIndex(values,dℚ(i)):values;
			r.initialize(v,value,types[i]);
		}
		r.q=dVar("`q");
		r.nargs=nargs;
		auto ndist=dDistApply(dApply(dexpr,r.q),db1);
		r.distribution=dInt(r.distribution*dIvr(DIvr.Type.eqZ,dField(db1,"tag")-one)*ndist);
		r.error=dInt(dIvr(DIvr.Type.eqZ,dField(db1,"tag"))*ndist);
		r.orderFreeVars(orderedFreeVars,isTuple);
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
		DNVar[] vars;
		if(freeVarsOrdered) vars=orderedFreeVars;
		else vars=freeVars.array;
		foreach(v;vars) r~=(formatting==Format.mathematica?v.toString(formatting)~"_":v.toString(formatting))~",";
		if(vars.length) r=r[0..$-1];
		r~=middle~distribution.toString(formatting);
		if(error != zero) r~="\n"~errstr~error.toString(formatting);
		return r;
	}
}

