// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

// TODO: the caches should use weak references

import std.conv;
import options, util.hashtable, util;

alias Q=TupleX, q=tuplex;
static import std.typecons;

import std.algorithm, std.array;

import std.datetime.stopwatch;

struct RecursiveStopWatch{
	StopWatch sw;
	int started=0;
	void stop(){
		if(--started==0) sw.stop();
	}
	void start(){
		if(++started==1) sw.start();
	}
	auto peek(){ return sw.peek(); }
}

/+RecursiveStopWatch sw;
int swCount=0;
static ~this(){
	writeln("time: ",sw.peek().total!"hnsecs"/1e7);
	writeln("freq: ",swCount);
}
enum measure="swCount++;sw.start();scope(exit)sw.stop();";+/

//version=DISABLE_INTEGRATION;

enum Precedence{
	none,
	lambda,
	bind,
	bitOr,
	bitXor,
	bitAnd,
	plus,
	uminus,
	lim,
	intg,
	mult,
	div,
	diff,
	pow,
	apply,
	index,
	field=index,
	subscript,
	invalid,
}
hash_t g_hash=0;
abstract class DExpr{
	hash_t hash;
	this(){ hash = ++g_hash; }
	final override hash_t toHash()@trusted{ return hash; }
	final override bool opEquals(Object r){ return this is r; }

	final override string toString(){ return toString(Format.default_); }

	string toString(Format formatting){
		auto r=toStringImpl(formatting,Precedence.none,0);
		if(formatting==Format.sympy) r=text("limit(",r,",pZ,0,'+')"); // pZ: positive zero
		else if(formatting==Format.maple) r=text("limit(",r,",pZ=0,right)");
		return r;
	}
	abstract string toStringImpl(Format formatting,Precedence prec,int binders);

	abstract int forEachSubExpr(scope int delegate(DExpr) dg);

	abstract DExpr simplifyImpl(DExpr facts);

	/+static RecursiveStopWatch[DExpr] simplificationTimer;
	static ~this(){
		Q!(double,DExpr)[] x;
		foreach(k,v;simplificationTimer) x~=q(v.peek().to!("seconds",double),k);
		sort!"a[0]>b[0]"(x);
		double tot=0;
		foreach(k;x){
			writeln(k[1],": ",k[0]);
			writeln(k[1].simplify(one));
			writeln();
			writeln();
			// if(k[0]<0.01) break;
			tot+=k[0];
		}
		writeln("tot: ",tot);
	}+/

	static MapX!(Q!(DExpr,DExpr),DExpr) simplifyCache;
	final DExpr simplify(string file=__FILE__,int line=__LINE__)(DExpr facts){
		/+static int nested=0;nested++; scope(exit) nested--;
		if(nested==1){
			if(this !in simplificationTimer){
				simplificationTimer[this]=RecursiveStopWatch();
			}
			simplificationTimer[this].start();
		}
		scope(exit) if(nested==1) simplificationTimer[this].stop();+/
		assert(!cast(DPlus)facts,text(facts));
		if(q(this,facts) in simplifyCache) return simplifyCache[q(this,facts)];
		if(facts==zero) return zero;
		auto r=simplifyImpl(facts);
		assert(!!r,text(typeid(this)));
		simplifyCache[q(this,facts)]=r;
		simplifyCache[q(r,facts)]=r;
		/+foreach(ivr;r.allOf!DIvr){ // TODO: remove?
			assert(ivr == ivr.simplify(facts),text(this," ",r," ",facts));
			assert(ivr.type != DIvr.Type.lZ);
		}+/
		return r;
	}

	// TODO: implement in terms of 'forEachSubExpr'?
	static MapX!(Q!(DExpr,DVar,DExpr),DExpr) substituteCache;
	final DExpr substitute(DVar var,DExpr e){
		auto t=q(this,var,e);
		if(t in substituteCache) return substituteCache[t];
		auto r=substituteImpl(var,e);
		substituteCache[t]=r;
		return r;
	}
	abstract DExpr substituteImpl(DVar var,DExpr e);
	static MapX!(Q!(DExpr,int,int),DExpr) incDeBruijnVarCache;
	final DExpr incDeBruijnVar(int di,int bound){
		auto t=q(this,di,bound);
		if(t in incDeBruijnVarCache) return incDeBruijnVarCache[t];
		auto r=incDeBruijnVarImpl(di,bound);
		incDeBruijnVarCache[t]=r;
		return r;
	}
	abstract DExpr incDeBruijnVarImpl(int di,int bound);
	abstract int freeVarsImpl(scope int delegate(DVar),ref DExprSet visited);
	final freeVars(){
		static struct FreeVars{ // TODO: move to util?
			DExpr self;
			DExprSet visited;
			@disable this(this);
			int opApply(scope int delegate(DVar) dg){
				visited=DExprSet.init;
				return self.freeVarsImpl(dg,visited);
			}
		}
		return FreeVars(this);
	}
	final bool hasFreeVar(DVar var){
		foreach(v;freeVars) if(v == var) return true;
		return false;
	}

	final Dℚ isFractional(){
		auto q=cast(Dℚ)this;
		if(q&&q.c.den!=1) return q;
		return null;
	}
	final Dℚ isInteger(){
		auto q=cast(Dℚ)this;
		if(q&&q.c.den==1) return q;
		if(auto f=cast(DFloat)this){
			import std.math: floor;
			import std.format: format;
			if(f.c==floor(f.c)) return ℤ(format("%.0f",floor(f.c))).dℚ;
		}
		return null;
	}

	// helpers for construction of DExprs:
	enum ValidUnary(string s)=s=="-";
	enum ValidBinary(string s)=["+","-","*","/","%","^^","~"].canFind(s);
	template UnaryCons(string s)if(ValidUnary!s){
		static assert(s=="-");
		alias UnaryCons=dUMinus;
	}
	template BinaryCons(string s)if(ValidBinary!s){
		static if(s=="+") alias BinaryCons=dPlus;
		else static if(s=="-") alias BinaryCons=dMinus;
		else static if(s=="*") alias BinaryCons=dMult;
		else static if(s=="/") alias BinaryCons=dDiv;
		else static if(s=="%") alias BinaryCons=dMod;
		else static if(s=="^^") alias BinaryCons=dPow;
		else static if(s=="~") alias BinaryCons=dCat;
		else static assert(0);
	}
	final opUnary(string op)()if(op=="-"){
		return UnaryCons!op(this);
	}
	final DExpr opBinary(string op)(DExpr e)if(ValidBinary!op){
		return BinaryCons!op(this,e);
	}
	final DExpr opBinary(string op)(long e)if(ValidBinary!op){
		return mixin("this "~op~" e.dℚ");
	}
	final DExpr opBinaryRight(string op)(long e)if(ValidBinary!op){
		return mixin("e.dℚ "~op~" this");
	}
	final DExpr opBinary(string op)(ℤ e)if(ValidBinary!op&&op!="~"){
		return mixin("this "~op~" e.dℚ");
	}
	final DExpr opBinary(string op)(ℚ e)if(ValidBinary!op&&op!="~"){
		return mixin("this "~op~" e.dℚ");
	}
	final DExpr opBinaryRight(string op)(ℤ e)if(ValidBinary!op&&op!="~"){
		return mixin("e.dℚ "~op~" this");
	}
	final DExpr opBinaryRight(string op)(ℚ e)if(ValidBinary!op&&op!="~"){
		return mixin("e.dℚ "~op~" this");
	}

	final DExpr opBinary(string op)(real e)if(ValidBinary!op&&op!="~"){
		return mixin("this "~op~" e.dFloat");
	}
	final DExpr opBinaryRight(string op)(real e)if(ValidBinary!op&&op!="~"){
		return mixin("e.dFloat "~op~" this");
	}

	final DExpr opIndex(DExpr rhs){ return dIndex(this,rhs); }


	mixin template Constant(){
		static if(!is(subExprs==Seq!()))
			this(typeof(subExprs) args){ subExprs=args; }
		override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
		override int freeVarsImpl(scope int delegate(DVar) dg,ref DExprSet visited){ return 0; }
		override DExpr substituteImpl(DVar var,DExpr e){ assert(var != this); return this; }
		override DExpr incDeBruijnVarImpl(int di,int bound){ return this; }
		override DExpr simplifyImpl(DExpr facts){ return this; }
	}
}

// attributes
struct binder{} struct even{} struct conditionallyEven(alias cond){ } struct isAbstract{}
enum forEachSubExprImpl(string code)=mixin(X!q{
	foreach(i,se;subExprs){
		//import dp: Dist;
		static if(is(typeof(se):DExpr)/+||is(typeof(se)==Dist)+/){
			alias x=se;
			@(code)
		}else static if(is(typeof(se)==SetX!DExpr)||is(typeof(se)==DExpr[])||is(typeof(se)==DExpr[2])){
			foreach(x;se) @(code)
		}else static if(is(typeof(se)==DExpr[string])){
			foreach(k,x;values) @(code)
		}else{
			import ast.type: Type;
			import ast.declaration: FunctionDef;
			static assert(is(typeof(se)==string)||is(typeof(se)==int)||is(typeof(se)==DIvr.Type)||is(typeof(se)==Type)||is(typeof(se)==FunctionDef)||is(typeof(se)==Dist), "foreachSubExprImpl is not exhaustive.");
		}
	}
});
template IncDeBruijnVarType(T){
	static if(is(T:DVar)||is(T==DLambda)||is(T==DDistLambda)) alias IncDeBruijnVarType=T;
	else alias IncDeBruijnVarType=DExpr;
}
template SubstituteType(T){
	static if(is(T==DLambda)||is(T==DDistLambda)) alias SubstituteType=T;
	else alias SubstituteType=DExpr;
}
import std.traits: hasUDA;
enum IsAbstract(T) = hasUDA!(T,isAbstract);
mixin template Visitors(){
	this(typeof(subExprs) args)in{
		static if(is(typeof(this)==DDeBruijnVar))
			assert(args[0]>=0);
		static if(is(typeof(this):DAssocOp)||is(typeof(this):DCommutAssocOp))
			assert(args[0].length>1);
		static if(is(typeof(this)==DIvr)){
			foreach(d;args[1].allOf!DDelta) assert(0,text(args[1]));
		}
	}body{
		subExprs=args;
	}
	static if(is(typeof(subExprs)==Seq!(DExpr[2])))
		this(DExpr e1,DExpr e2){ this([e1,e2]); }
	static if(!IsAbstract!(typeof(this))):
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		// TODO: fix this.
		//import dp: DDPDist;
		static if(!(/+is(typeof(this)==DDPDist)||+/is(typeof(this)==DLambda)||is(typeof(this)==DDistLambda)||is(typeof(this)==DInt)||is(typeof(this)==DSum)||is(typeof(this)==DLim)||is(typeof(this)==DDiff)||is(typeof(this)==DDelta)||is(typeof(this)==DDiscDelta)))
			mixin(forEachSubExprImpl!"if(auto r=dg(x)) return r;");
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg,ref DExprSet visited){
		// TODO: improve performance (this method uses ~10% of total running time)
		if(this in visited) return 0;
		visited.insert(this);
		static if(is(typeof(this):DVar)) return dg(this);
		else{
			mixin(forEachSubExprImpl!q{{
				import std.traits: hasUDA;
				static if(hasUDA!(subExprs[i],binder)){
					foreach(v;x.freeVars())
						if(v!=db1)
							if(auto r=dg(v.incDeBruijnVar(-1,0)))
								return r;
				}else{ if(auto r=x.freeVarsImpl(dg,visited)) return r; }
			}});
			return 0;
		}
	}
	override SubstituteType!(typeof(this)) substituteImpl(DVar var,DExpr e){
		static if(is(typeof(this):DVar)) return this==var?e:this;
		else{
			Q!(typeof(subExprs)) nsubs;
			//import dp: Dist;
			foreach(i,sub;subExprs){
				auto cvar=var,ce=e;
				import std.traits: hasUDA;
				static if(hasUDA!(subExprs[i],binder)){
					cvar=cvar.incDeBruijnVar(1,0);
					ce=ce.incDeBruijnVar(1,0);
				}
				static if(is(typeof(sub):DExpr)/+||is(typeof(sub)==Dist)+/){
					nsubs[i]=sub.substitute(cvar,ce);
				}else static if(is(typeof(sub)==DExprSet)){
					if(auto evar=cast(DVar)e){ // TODO: make this unnecessary, this is a hack to improve performance
						if(!hasFreeVar(evar)){
							foreach(f;sub) nsubs[i].insert(f.substitute(cvar,ce));
							continue;
						}
					}
					foreach(f;sub) typeof(this).insert(nsubs[i],f.substitute(cvar,ce));
				}else static if(is(typeof(sub)==DExpr[])||is(typeof(sub)==DExpr[2])){
					nsubs[i]=sub.dup;
					foreach(ref x;nsubs[i]) x=x.substitute(cvar,ce);
				}else static if(is(typeof(sub)==DExpr[string])){
					foreach(k,v;sub) nsubs[i][k]=v.substitute(cvar,ce);
				}else{
					import ast.type: Type;
					import ast.declaration: FunctionDef;
					static assert(is(typeof(sub)==string)||is(typeof(sub)==int)||is(typeof(sub)==DIvr.Type)||is(typeof(sub)==Type)||is(typeof(sub)==FunctionDef));
					nsubs[i]=sub;
				}
			}
			if(nsubs==q(subExprs)) return this;
			return mixin(lowerf(typeof(this).stringof))(nsubs.expand);
		}
	}
	override IncDeBruijnVarType!(typeof(this)) incDeBruijnVarImpl(int di,int bound){
		static if(is(typeof(this)==DDeBruijnVar)){
			if(i<=bound) return this;
			assert((i<=bound) == (i+di <= bound)); // (otherwise bound variables can be captured);
			return dDeBruijnVar(i+di);
		}else{
			Q!(typeof(subExprs)) nsubs;
			alias subs=subExprs;
			foreach(i,sub;subExprs){
				auto cdi=di,cbound=bound;
				import std.traits: hasUDA;
				static if(hasUDA!(subExprs[i],binder)){
					cbound++;
				}
				static if(is(typeof(sub):DExpr)){
					nsubs[i]=cast(typeof(nsubs[i]))sub.incDeBruijnVar(cdi,cbound);
				}else static if(is(typeof(sub)==SetX!DExpr)){
					foreach(f;sub) nsubs[i].insert(f.incDeBruijnVar(cdi,cbound));
				}else static if(is(typeof(sub)==DExpr[])||is(typeof(sub)==DExpr[2])){
					nsubs[i]=sub.dup;
					foreach(ref x;nsubs[i]) x=x.incDeBruijnVar(cdi,cbound);
				}else static if(is(typeof(sub)==DExpr[string])){
					foreach(k,v;sub) nsubs[i][k]=v.incDeBruijnVar(cdi,cbound);
				}else nsubs[i]=sub;
			}
			if(nsubs==q(subExprs)) return this;
			return mixin(lowerf(typeof(this).stringof))(nsubs.expand);
		}
	}
}

mixin template FactoryFunction(T){
	static if(is(T==DIvr)){
		DExpr dIvr(DIvr.Type type,DExpr e){
			static MapX!(DExpr,DExpr)[DIvr.Type.max+1] cache;
			if(e in cache[type]) return cache[type][e];
			auto r=new DIvr(type,e);
			cache[type][e]=r;
			return r;
		}
		DExpr dEqZ(DExpr e){ return dIvr(DIvr.Type.eqZ,e); }
		DExpr dNeqZ(DExpr e){ return dIvr(DIvr.Type.neqZ,e); }
		DExpr dLeZ(DExpr e){ return dIvr(DIvr.Type.leZ,e); }
		DExpr dGeZ(DExpr e){ return dIvr(DIvr.Type.leZ,-e); }
		DExpr dLtZ(DExpr e){ return dIvr(DIvr.Type.lZ,e); }
		DExpr dGtZ(DExpr e){ return dIvr(DIvr.Type.lZ,-e); }
		DExpr dEq(DExpr e1,DExpr e2){ return dEqZ(e1-e2); }
		DExpr dNeq(DExpr e1,DExpr e2){ return dNeqZ(e1-e2); }
		DExpr dLe(DExpr e1,DExpr e2){ return dLeZ(e1-e2); }
		DExpr dGe(DExpr e1,DExpr e2){ return dLeZ(e2-e1); }
		DExpr dLt(DExpr e1,DExpr e2){ return dLtZ(e1-e2); }
		DExpr dGt(DExpr e1,DExpr e2){ return dLtZ(e2-e1); }
	}else:

	static if(is(T==DDelta)){
		import ast.expression; // TODO: remove this import
		DExpr dDelta(DExpr e,DExpr var,Expression ty){ // TODO: dexpr shouldn't know about expression/type, but this is most convenient for overloading
			import ast.type;
			if(isSubtype(ty,ℝ(true))) return dDelta(e-var);
			assert(cast(TupleTy)ty||cast(ArrayTy)ty||cast(AggregateTy)ty||cast(ContextTy)ty||cast(FunTy)ty||cast(TypeTy)ty||cast(Identifier)ty||cast(CallExp)ty,text(ty)); // TODO: add more supported types
			return dDiscDelta(e,var);
		}
	}else static if(is(T==DInt)){ // TODO: generalize over DInt, DSum, DLim, DLambda, (DDiff)
		@disable DExpr dIntSmp(DVar var,DExpr expr);
		DExpr dIntSmp(DExpr expr,DExpr facts){
			return dInt(expr).simplify(facts);
		}
		DExpr dIntSmp(DVar var,DExpr expr,DExpr facts){
			return dInt(var,expr).simplify(facts);
		}
		DExpr dInt(DVar var,DExpr expr)in{assert(var&&expr&&!cast(DDeBruijnVar)var);}body{
			return dInt(expr.incDeBruijnVar(1,0).substitute(var,db1));
		}
	}else static if(is(T==DSum)){
		@disable DExpr dSumSmp(DVar var,DExpr expr);
		DExpr dSumSmp(DExpr expr,DExpr facts){
			return dSum(expr).simplify(facts);
		}
		DExpr dSumSmp(DVar var,DExpr expr,DExpr facts){
			return dSum(var,expr).simplify(facts);
		}
		DExpr dSum(DVar var,DExpr expr)in{assert(var&&expr&&!cast(DDeBruijnVar)var);}body{
			return dSum(expr.incDeBruijnVar(1,0).substitute(var,db1));
		}
	}else static if(is(T==DLim)){
		@disable DExpr dLimSmp(DVar var,DExpr e,DExpr x);
		DExpr dLimSmp(DExpr e,DExpr x,DExpr facts){
			return dLim(e,x).simplify(facts);
		}
		DExpr dLimSmp(DVar v,DExpr e,DExpr x,DExpr facts){
			return dLim(v,e,x).simplify(facts);
		}
		DExpr dLim(DVar v,DExpr e,DExpr x)in{assert(v&&e&&x&&(!cast(DDeBruijnVar)v||v==db1));}body{
			if(v==db1) return dLim(e,x.incDeBruijnVar(1,1));
			return dLim(e,x.incDeBruijnVar(1,0).substitute(v,db1));
		}
	}else static if(is(T==DDiff)){
		DExpr dDiff(DVar v,DExpr e,DExpr x)in{assert(v&&e&&x&&(!cast(DDeBruijnVar)v||v==db1));}body{
			if(v==db1) return dDiff(e.incDeBruijnVar(1,1),x);
			return dDiff(e.incDeBruijnVar(1,0).substitute(v,db1),x);
		}
		DExpr dDiff(DVar v,DExpr e){ return dDiff(v,e,v); }
	}else static if(is(T==DLambda)){
		@disable DExpr dLambdaSmp(DVar var,DExpr expr);
		DLambda dLambdaSmp(DExpr expr,DExpr facts)in{assert(expr);}body{
			auto r=dLambda(expr).simplify(facts);
			assert(!!cast(DLambda)r);
			return cast(DLambda)cast(void*)r;
		}
		DLambda dLambdaSmp(DVar var,DExpr expr,DExpr facts)in{assert(var&&expr);}body{
			auto r=dLambda(var,expr).simplify(facts);
			assert(!!cast(DLambda)r);
			return cast(DLambda)cast(void*)r;
		}
		DLambda dLambda(DVar var,DExpr expr)in{assert(var&&expr&&(!cast(DDeBruijnVar)var||var==db1));}body{
			if(var==db1) return dLambda(expr);
			return dLambda(expr.incDeBruijnVar(1,0).substitute(var,db1));
		}
	}else static if(is(T==DDistLambda)){
		@disable DExpr dDistLambdaSmp(DVar var,DExpr expr);
		DDistLambda dDistLambdaSmp(DExpr expr,DExpr facts)in{assert(expr);}body{
			auto r=dDistLambda(expr).simplify(facts);
			assert(!!cast(DDistLambda)r);
			return cast(DDistLambda)cast(void*)r;
		}
		DDistLambda dDistLambdaSmp(DVar var,DExpr expr,DExpr facts)in{assert(var&&expr);}body{
			auto r=dDistLambda(var,expr).simplify(facts);
			assert(!!cast(DDistLambda)r);
			return cast(DDistLambda)cast(void*)r;
		}
		DDistLambda dDistLambda(DVar var,DExpr expr)in{assert(var&&expr&&(!cast(DDeBruijnVar)var||var==db1));}body{
			if(var==db1) return dDistLambda(expr);
			return dDistLambda(expr.incDeBruijnVar(1,0).substitute(var,db1));
		}
	}else static if(is(T==DRecord)){
		auto dRecord(){ return dRecord((DExpr[string]).init); }
	}else static if(is(T==DArray)){
		auto dArray(DExpr length){ return dArray(length,dLambda(zero)); }
		auto dConstArray(DExpr length,DExpr default_){
			assert(!cast(DLambda)default_);
			return dArray(length,dLambda(default_.incDeBruijnVar(1,0)));
		}
		auto dArray(DExpr[] entries){
			auto dbv=db1;
			// TODO: not necessarily very clean for types that are not real numbers, but can be interpreted in terms of linear algebra
			DExpr body_=zero;
			foreach(i,e;entries) body_=body_+dEq(dbv,i.dℚ)*entries[i].incDeBruijnVar(1,0);
			return dArray(dℚ(ℤ(entries.length)),dLambda(body_));
		}
	}else static if(is(T==Dℚ)){
		DExpr dℚ(long c){ return dℚ(ℚ(c)); }
		Dℚ dℚ(ℤ c){ return dℚ(ℚ(c)); }
	}
	static if(is(T.subExprs==Seq!())){
		mixin(mixin(X!q{
			auto @(lowerf(T.stringof))(){
				static T cache=null;
				if(cache) return cache;
				cache=new T();
				return cache;
			}
		}));
	}else:
	mixin(mixin(X!q{
		auto @(lowerf(T.stringof))(typeof(T.subExprs) args){
			static if(is(T:DCommutAssocOp)){
				static assert(is(typeof(args)==Seq!DExprSet));
				if(args[0].length==1) return args[0].element;
			}
			static if(is(T:DAssocOp)){
				static assert(is(typeof(args)==Seq!(DExpr[])));
				if(args[0].length==1) return args[0][0];
			}
			static if(__traits(hasMember,T,"constructHook"))
				if(auto r=T.constructHook(args)) return r;
			static if(is(T==DFloat)) if(args[0]==0) return zero;
			static MapX!(TupleX!(typeof(T.subExprs)),T) cache;
			auto t=tuplex(args);
			if(t in cache) return cache[t];
			auto r=new T(args);
			cache[t]=r;
			return r;
		}
	}));
	static if(is(T:DBinaryOp)||is(T:DAssocOp)){
		mixin(mixin(X!q{
			auto @(lowerf(T.stringof))(DExpr e1,DExpr e2){
				return @(lowerf(T.stringof))([e1,e2]);
			}
		}));
	}
	static if(is(T:DCommutAssocOp)){
		mixin(mixin(X!q{
			auto @(lowerf(T.stringof))(DExpr e1,DExpr e2){
				DExprSet a;
				T.insert(a,e1);
				T.insert(a,e2);
				return @(lowerf(T.stringof))(a);
			}
		}));
	}
}
mixin template FactoryFunction(string name,string value){
	mixin(mixin(X!q{
		auto @(name)(){
			static typeof(@(value)) cache=null;
			if(cache) return cache;
			cache=@(value);
			return cache;
		}
	}));
}


alias DExprSet=SetX!DExpr;
abstract class DVar: DExpr{
	static string fixName(string name,Format formatting){
		if(formatting==Format.gnuplot||formatting==Format.python||formatting==Format.sympy||formatting==Format.matlab||formatting==Format.mathematica){
			return asciify(name);
			auto nname=name.to!dstring; // TODO: why necessary? Phobos bug?
			nname=nname.replace("ξ"d,"xi"d);
			//pragma(msg, cast(dchar)('₀'+1));
			foreach(x;0..10)
				nname=nname.replace(""d~cast(dchar)('₀'+x),""d~cast(dchar)('0'+x));
			return nname.to!string;
		}
		return name;
	}
	override abstract DVar incDeBruijnVarImpl(int di,int bound);
	final DVar incDeBruijnVar(int di,int bound){
		auto r=cast(DVar)super.incDeBruijnVar(di,bound); // TODO: get rid of cast?
		assert(!!r);
		return r;
	}
	override DExpr simplifyImpl(DExpr facts){
		// TODO: make more efficient! (e.g. keep hash table in product expressions)
		foreach(f;facts.factors){
			if(auto ivr=cast(DIvr)f){
				if(ivr.type!=DIvr.Type.eqZ) continue;
				if(ivr.e.getCanonicalFreeVar()!=this) continue; // TODO: make canonical var smart
				SolutionInfo info;
				SolUse usage={caseSplit:false,bound:false};
				auto sol=ivr.e.solveFor(this,zero,usage,info);
				if(!sol||info.needCaseSplit) continue; // TODO: make more efficient!
				// TODO: we probably want to do a case split here.
				// TODO: allow this simplification to be disabled temporarily (for delta expressions)
				return sol.simplify(facts);
			}
		}
		return this;
	}
}
class DNVar: DVar{ // named variables
	string name;
	alias subExprs=Seq!(name);
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		return fixName(name,formatting);
	}
	mixin Visitors;
}

DNVar[string] dVarCache; // TODO: caching desirable? (also need to update parser if not)
DNVar dNVar(string name){
	if(name in dVarCache) return dVarCache[name];
	return dVarCache[name]=new DNVar(name);
}
alias dVar=dNVar;

class DDeBruijnVar: DVar{
	int i;
	alias subExprs=Seq!i;
	static string displayName(int i,Format formatting,int binders){
		return DVar.fixName("ξ"~lowNum(1+binders-i),formatting);
	}
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		return displayName(i,formatting,binders);
	}
	mixin Visitors;
}
mixin FactoryFunction!DDeBruijnVar;
@property db1(){ return dDeBruijnVar(1); }
@property db2(){ return dDeBruijnVar(2); }
@property db3(){ return dDeBruijnVar(3); }

// substitute all variables from 'from' by the respective expressions in 'to' at the same time (avoiding capture)
DExpr substituteAll(DExpr e,DVar[] from, DExpr[] to)in{assert(from.length==to.length);}body{
	assert(from.length<int.max);
	auto ne=e;
	auto vars=from.map!(a=>freshVar).array; // TODO: get rid of this!
	foreach(i,v;from) ne=ne.substitute(v,vars[i]);
	foreach(i,t;to) ne=ne.substitute(vars[i],t);
	return ne;
}


class DTmpDeBruijnVar: DNVar{
	int i;
	static int curi=0;
	this(string name){ super(name); i=curi++; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(name=="tmp") // Can be convenient for debugging. TODO: get rid of "tmp" vars
			return name~(cast(void*)this).to!string;
		return super.toStringImpl(formatting,prec,binders);
	}
	override DExpr simplifyImpl(DExpr facts){
		return this;
	}
} // TODO: get rid of this!

DNVar freshVar(string name="tmp"){ return new DTmpDeBruijnVar(name); } // TODO: get rid of this!

DVar theDε;
DVar dε(){ return theDε?theDε:(theDε=new DNVar("ε")); }

class Dℚ: DExpr{
	ℚ c;
	alias subExprs=Seq!c;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		string r;
		if(c.den==1){
			r=text(c.num);
		}else{
			if(formatting==Format.matlab||formatting==Format.gnuplot)
				r=text(c.num,"./",c.den);
			else if(formatting==Format.lisp){
				return text("(/ ",c.num," ",c.den,")");
			}else r=text(c.num,"/",c.den);
		}
		if(formatting==Format.maple && c<0){
			r="("~r~")";
		}else if(c.den!=1&&prec>Precedence.div||prec>Precedence.uminus&&c<0)
			r="("~r~")";
		return r;
	}

	mixin Constant;
}
mixin FactoryFunction!Dℚ;

Dℚ nthRoot(ℤ x,ℤ n){ // TODO: return Maybe!ℤ or something.
	ℤ k=1,r=0;
	while(k<x) k*=2;
	for(;k;k/=2){
		ℤ c=r+k;
		if(pow(c,n)<=x)
			r=c;
	}
	return pow(r,n)==x?dℚ(r):null;
}

Dℚ nthRoot(ℚ x,ℤ n){
	if(auto rnum=nthRoot(x.num,n))
		if(auto rden=nthRoot(x.den,n)){
			assert(rnum.c.den==1 && rden.c.den==1);
			return dℚ(ℚ(rnum.c.num,rden.c.num));
		}
	return null;
}

ℤ ceilLog2(ℤ x)in{assert(x>=1);}body{
	ℤ r=0;
	for(ℤ y=1;y<x;y*=2) ++r;
	return r;
}

Dℚ[2] isPower(ℤ x,size_t bound=-1)in{assert(x>=0);}body{ // TODO: return Maybe!(ℤ[2])
	if(x<4) return [null,null];
	ℤ i = ceilLog2(x);
	if(bound!=-1) if(i>bound) return [null,null];
	for(;i>1;--i)
		if(auto r=nthRoot(x,i))
			return [r,dℚ(i)];
	return [null,null];
}

Dℚ integerLog(ℤ x,ℤ b)in{assert(x>0);}body{ // TODO: return Maybe!ℤ
	if(x==1) return cast(Dℚ)zero;
	if(x%b) return null;
	ℤ r=0,d=1;
	ℤ[] p=[b];
	while(!(x%p[$-1])){
		p~=p[$-1]*p[$-1];
		d*=2;
	}
	ℤ c=x;
	for(size_t i=p.length;i--;d/=2){
		if(!(c%p[i])){
			c/=p[i];
			r+=d;
		}
	}
	return c==1?dℚ(r):null;
}

class DFloat: DExpr{
	real c;
	alias subExprs=Seq!c;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		import std.format;
		string r=format("%.16e",c);
		assert(all!(c=>'0'<=c&&c<='9'||c=='-'||c=='+'||c=='.'||c=='e')(r),r);
		if(formatting==Format.mathematica){
			if(r.canFind("e"))
				r="("~r.replace("e","*10^")~")";
		}else if(formatting==Format.maple){
			if(c<0) r="("~r~")";
		}else if(formatting==Format.lisp){
			long e=0;
			if(r.canFind("e")){
				auto x=r.split("e");
				assert(x.length==2);
				e=to!long(x[1]);
				r=x[0];
			}
			if(r.canFind(".")){
				auto y=r.split('.');
				while(!y[1].empty && y[1][$-1]=='0') y[1].popBack();
				assert(y[1].length<=long.max);
				auto exp="(^ 10 "~text(e-cast(long)y[1].length)~")";
				e-=cast(long)y[1].length;
				r=y[0]~y[1];
			}
			//if(e!=0) r="(* "~r~" (^ 10 "~text(e)~"))";
			if(e!=0){
				import std.range: repeat;
				r="("~(e<0?"/":"*")~" "~r~" 1"~'0'.repeat(e<0?-e:e).to!string~")";
			}
		}else if(prec>Precedence.uminus&&c<0)
			r="("~r~")";
		return r;
	}

	mixin Constant;
}
mixin FactoryFunction!DFloat;

class DE: DExpr{
	alias subExprs=Seq!();
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.gnuplot) return "exp(1)";
		if(formatting==Format.maple) return "exp(1)";
		if(formatting==Format.mathematica) return "E";
		if(formatting==Format.sympy) return "E";
		return "e";
	} // TODO: maple
	mixin Constant;
}
mixin FactoryFunction!DE;

class DΠ: DExpr{
	alias subExprs=Seq!();
	override string toStringImpl(Format formatting,Precedence prec,int binders){ // TODO: maple
		if(formatting==Format.gnuplot) return "pi";
		if(formatting==Format.matlab) return "pi";
		if(formatting==Format.maple) return "Pi";
		if(formatting==Format.mathematica) return "Pi";
		if(formatting==Format.sympy) return "pi";
		else return "π";
	}
	mixin Constant;
}
mixin FactoryFunction!DΠ;
mixin FactoryFunction!("one","dℚ(1)");
mixin FactoryFunction!("mone","dℚ(-1)");
mixin FactoryFunction!("zero","dℚ(0)");

abstract class DOp: DExpr{
	abstract @property string symbol(Format formatting,int binders);
	bool rightAssociative(){ return false; }
	abstract @property Precedence precedence();
	/+protected+/ final string addp(Precedence prec, string s, Precedence myPrec=Precedence.invalid){ // TODO: add protected
		if(myPrec==Precedence.invalid) myPrec=precedence;
		return prec > myPrec||rightAssociative&&prec==precedence? "(" ~ s ~ ")":s;
	}
}


@isAbstract
abstract class DAssocOp: DOp{
	DExpr[] operands;
	alias subExprs=Seq!operands;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		string r;
		if(formatting==Format.lisp){
			r~="(";
			r~=symbol(formatting,binders);
			foreach(o;operands){
				r~=" ";
				r~=o.toStringImpl(formatting,prec,binders);
			}
			r~=")";
			return r;
		}
		foreach(o;operands) r~=symbol(formatting,binders)~o.toStringImpl(formatting,prec,binders);
		return addp(prec, r[symbol(formatting,binders).length..$]);
	}
}


abstract class DCommutAssocOp: DOp{
	/+protected+/ final string toStringImplImpl(DExprSet operands,Format formatting,Precedence prec,int binders){
		string r;
		if(formatting==Format.lisp){
			r~="(";
			r~=symbol(formatting,binders);
			foreach(o;operands){
				r~=" ";
				r~=o.toStringImpl(formatting,prec,binders);
			}
			r~=")";
			return r;
		}
		auto ops=operands.array.map!(a=>a.toStringImpl(formatting,precedence,binders)).array;
		sort(ops);
		foreach(o;ops) r~=symbol(formatting,binders)~o;
		return addp(prec, r[symbol(formatting,binders).length..$]);
	}
	mixin template ToString(){
		override string toStringImpl(Format formatting,Precedence prec,int binders){
			return toStringImplImpl(operands,formatting,prec,binders);
		}
	}
}

class DPlus: DCommutAssocOp{
	DExprSet operands;
	alias subExprs=Seq!operands;
	mixin ToString;
	override @property Precedence precedence(){ return Precedence.plus; }
	override @property string symbol(Format formatting,int binders){ return "+"; }
	mixin Visitors;

	static void insert(ref DExprSet summands,DExpr summand)in{assert(!!summand);}body{
		if(summand==zero) return;
		if(summand in summands){
			summands.remove(summand);
			insert(summands,2*summand);
		}else{
			summands.insert(summand);
		}
	}
	static void insertAndSimplify(ref DExprSet summands,DExpr summand,DExpr facts){
		// swCount++;sw.start(); scope(exit) sw.stop();
		foreach(i;0..2){
			if(auto dp=cast(DPlus)summand){
				foreach(s;dp.summands)
					insertAndSimplify(summands,s,facts);
				return;
			}
			if(!i) summand=summand.simplify(facts);
		}

		if(auto p=cast(DPow)summand){
			if(cast(DPlus)p.operands[0]){
				auto expanded=expandPow(p);
				if(expanded != p){
					insertAndSimplify(summands,expanded,facts);
					return;
				}
			}
		}

		DExpr combine(DExpr e1,DExpr e2,DExpr facts){
			if(e1==zero) return e2;
			if(e2==zero) return e1;
			if(e1==e2) return (2*e1).simplify(facts);

			static DExpr combineFractions(DExpr e1,DExpr e2){
				if(auto q1=cast(Dℚ)e1)
					if(auto q2=cast(Dℚ)e2)
						return dℚ(q1.c+q2.c);
				return null;
			}

			if(auto r=combineFractions(e1,e2)) return r.simplify(facts);

			static DExpr combineWithFloat(DExpr e1,DExpr e2){
				if(auto f=cast(DFloat)e1){
					if(auto g=cast(DFloat)e2)
						return (f.c+g.c).dFloat;
					if(auto q2=cast(Dℚ)e2)
						return (f.c+toReal(q2.c)).dFloat;
				}
				return null;
			}
			static DExpr combineFloat(DExpr e1,DExpr e2){
				if(auto r=combineWithFloat(e1,e2)) return r;
				if(auto r=combineWithFloat(e2,e1)) return r;
				return null;
			}

			if(auto p1=cast(DPow)e1){
				if(p1.operands[0]==mone){
					if(auto p2=cast(DPow)e2){
						if(p2.operands[0]==mone){
							auto diff=(p1.operands[1]-p2.operands[1]).simplify(facts);
							if(auto z=diff.isInteger()){
								assert(z.c.den==1);
								if(z.c.num&1) return zero;
								return (2*e1).simplify(facts);
							}
						}
					}
				}
			}

			if(auto r=combineFloat(e1,e2)) return r;

			if(auto r=recursiveCombine(e1,e2,facts))
				return r;

			static DExpr combineIvr(DExpr e1,DExpr e2,DExpr facts){
				if(auto ivr1=cast(DIvr)e1){
					if(ivr1.type==DIvr.Type.eqZ){
						if(e2==dLtZ(ivr1.e).simplify(facts))
							return dLeZ(ivr1.e);
						if(e2==dGtZ(ivr1.e).simplify(facts))
							return dGeZ(ivr1.e);
						if(e2==dNeqZ(ivr1.e).simplify(facts))
							return one;
					}else if(ivr1.type==DIvr.Type.leZ){
						if(e2==dGeZ(ivr1.e).simplify(facts))
							return 2*dEqZ(ivr1.e)+dNeqZ(ivr1.e);
						if(e2==dGtZ(ivr1.e).simplify(facts))
							return one;
					}
				}
				return null;
			}
			if(auto r=combineIvr(e1,e2,facts)) return r.simplify(facts);
			if(auto r=combineIvr(e2,e1,facts)) return r.simplify(facts);

			static DExpr combineIvr2(DExpr e1,DExpr e2,DExpr facts){
				// If B → A and B ⇔  ¬C: [A∧ C] + [B] = [A]
				if(cast(DIvr)e1 && cast(DIvr)e2) return null;
				foreach(f;e1.factors) if(!cast(DIvr)f) return null;
				foreach(f;e2.factors) if(!cast(DIvr)f) return null;
				auto implied=one, notImplied=one;
				foreach(f;e1.factors){
					if(f.simplify(e2)==one) implied=implied*f;
					else notImplied=notImplied*f;
				}
				if(implied != one){
					notImplied=notImplied.simplify(facts); // C
					static DExprSet active;
					if(notImplied in active) return null; // detect cycles (TODO: can this be avoided?)
					active.insert(notImplied); scope(exit) active.remove(notImplied);
					if(dEqZ(notImplied).simplify(facts)==e2) // B ⇔ ¬ C
						return implied.simplify(facts);
				}
				return null;
			}
			if(auto r=combineIvr2(e1,e2,facts)) return r.simplify(facts);
			if(auto r=combineIvr2(e2,e1,facts)) return r.simplify(facts);

			if(auto c1=cast(DMCase)e1)
				if(auto c2=cast(DMCase)e2)
					if(c1.e==c2.e)
						return dMCase(c1.e,c1.val+c2.val,c1.err+c2.err).simplify(facts);

			return null;
		}
		// TODO: use suitable data structures
		foreach(s;summands){
			if(auto nws=combine(s,summand,facts)){
				assert(s in summands);
				summands.remove(s);
				insertAndSimplify(summands,nws,facts);
				return;
			}
		}
		assert(summand !in summands);
		summands.insert(summand);
	}

	static DExpr integralSimplify(DExprSet summands,DExpr facts){
		DExprSet integralSummands;
		DExprSet integrals;
		static void recursiveInsert(ref DExprSet set,DExpr e){
			if(auto p=cast(DPlus)e)
				foreach(s;p.summands)
					recursiveInsert(set,s);
			else DPlus.insert(set,e);
		}
		foreach(s;summands){
			if(auto dint=cast(DInt)s){ // TODO: -∫_x f(x) ?
				recursiveInsert(integralSummands,dint.expr);
				assert(dint !in integrals);
				integrals.insert(dint);
			}
		}
		if(integralSummands.length){
			auto integralSum=dPlus(integralSummands);
			auto simplSum=integralSum.simplify(facts.incDeBruijnVar(1,0).simplify(one));
			if(integralSum!=simplSum){
				summands=summands.setMinus(integrals);
				return dPlus(summands)+dIntSmp(simplSum,facts);
			}
		}
		return null;
	}

	static DExpr sumSimplify(DExprSet summands,DExpr facts){
		DExprSet sumSummands;
		DExprSet sums;
		static void recursiveInsert(ref DExprSet set,DExpr e){
			if(auto p=cast(DPlus)e)
				foreach(s;p.summands)
					recursiveInsert(set,s);
			else DPlus.insert(set,e);
		}
		foreach(s;summands){
			if(auto dsum=cast(DSum)s){ // TODO: -∑_x f(x) ?
				recursiveInsert(sumSummands,dsum.expr);
				assert(dsum !in sums);
				sums.insert(dsum);
			}
		}
		if(sumSummands.length){
			auto sumSum=dPlus(sumSummands);
			auto simplSum=sumSum.simplify(facts.incDeBruijnVar(1,0).simplify(one));
			if(sumSum!=simplSum){
				summands=summands.setMinus(sums);
				return dPlus(summands)+dSumSmp(simplSum,facts);
			}
		}
		return null;
	}

	// returns [common,e1only,e2only] such that e1=common*e1only, e2=common*e2only
	static DExpr[3] splitCommonFactors(DExpr e1,DExpr e2){
		auto common=intersect(e1.factors.setx,e2.factors.setx); // TODO: optimize?
		if(!common.length) return [one,e1,e2];
		auto e1only=e1.factors.setx.setMinus(common);
		auto e2only=e2.factors.setx.setMinus(common);
		return [dMult(common),dMult(e1only),dMult(e2only)];
	}

	static DExpr recursiveCombine(DExpr e1, DExpr e2,DExpr facts){
		auto splt=splitCommonFactors(e1,e2);
		auto common=splt[0],sum1=splt[1],sum2=splt[2];
		if(common != one){
			if(!cast(Dℚ)common){
				auto sum=(sum1+sum2).simplify(facts);
				auto summands=sum.summands.setx; // TODO: improve performance!
				if(sum1!in summands||sum2!in summands)
					return dDistributeMult(sum,common).simplify(facts); // was: sum*common
			}
		}
		return null;
	}

	override DExpr simplifyImpl(DExpr facts){
		/+// static int i; if(++i>20000) dw(this," ",facts); // for debugging perforation bug.
		//static int i=0; if(++i>1000) dw(this,facts); scope(exit) --i;
		static bool[TupleX!(DExpr,DExpr)] has;
		scope(exit) has.remove(tuplex(cast(DExpr)this,facts));
		if(tuplex(cast(DExpr)this,facts) in has){ writeln("!"); return this; }
		has[tuplex(cast(DExpr)this,facts)]=true;+/
		DExprSet summands;
		foreach(s;this.summands)
			insertAndSimplify(summands,s,facts);
		if(auto r=integralSimplify(summands,facts)) return r.simplify(facts);
		if(auto r=sumSimplify(summands,facts)) return r.simplify(facts);
		return dPlus(summands);
	}

	static DExpr constructHook(DExprSet operands){
		if(operands.length==0) return zero;
		return null;
	}
}

class DMult: DCommutAssocOp{
	DExprSet operands;
	alias subExprs=Seq!operands;
	override @property Precedence precedence(){ return Precedence.mult; }
	override string symbol(Format formatting,int binders){
		if(formatting==Format.gnuplot||formatting==Format.python||formatting==Format.maple||formatting==Format.sympy||formatting==Format.mathematica||formatting==Format.lisp) return "*";
		else if(formatting==Format.matlab) return ".*";
		else return "·";
	}
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp) return toStringImplImpl(operands,formatting,prec,binders);
		auto frac=this.getFractionalFactor();
		if(frac.c<0 && this.hasFactor(frac)){
			if(formatting==Format.maple){
				return "(-"~(dℚ(-frac.c)*this.withoutFactor(frac)).toStringImpl(formatting,Precedence.uminus,binders)~")";
			}else{
				return addp(prec,"-"~(dℚ(-frac.c)*this.withoutFactor(frac)).toStringImpl(formatting,Precedence.uminus,binders),Precedence.uminus);
			}
		}
		//if(frac[0]!=1&&frac[1]!=1) // TODO
		// TODO: use suitable data structures
		return toStringImplImpl(operands,formatting,prec,binders);
	}
	mixin Visitors;

	static void insert(string file=__FILE__,int line=__LINE__)(ref DExprSet factors,DExpr factor)in{assert(!!factor);}body{
		if(factor==one) return;
		if(factor==zero) factors.clear();
		if(zero in factors) return;
		if(factor in factors){
			factors.remove(factor);
			insert(factors,factor^^2);
		}else{
			factors.insert(factor);
		}
	}
	static void insertAndSimplify(ref DExprSet factors,DExpr factor,DExpr facts)in{assert(factor&&facts);}body{
		foreach(i;0..2){
			if(auto dm=cast(DMult)factor){
				foreach(f;dm.factors)
					insertAndSimplify(factors,f,facts);
				return;
			}
			if(!i) factor=factor.simplify(facts);
		}
		// TODO: use suitable data structures
		static MapX!(Q!(DExpr,DExpr,DExpr),DExpr) combineCache;
		static DExpr combine()(DExpr e1,DExpr e2,DExpr facts){
			if(q(e1,e2,facts) in combineCache) return combineCache[q(e1,e2,facts)];
			auto r=combineImpl(e1,e2,facts);
			combineCache[q(e1,e2,facts)]=r;
			combineCache[q(e2,e1,facts)]=r;
			return r;
		}
		static DExpr combineImpl(DExpr e1,DExpr e2,DExpr facts)in{assert(!cast(DMult)e1&&!cast(DMult)e2);}body{
			if(e1==one) return e2;
			if(e2==one) return e1;
			static DExpr combineInf(DExpr e1,DExpr e2,DExpr facts){
				if(e1==dInf && e2==mone) return null;
				if(e2==dInf && e1==mone) return null;
				if(e1==dInf){
					if(e2.mustBeLessThanZero()) return -dInf;
					if((-e2).simplify(facts).mustBeLessThanZero()) return dInf;
				}else if(e1==-dInf){
					if(auto r=combineInf(dInf,e2,facts))
						return -r;
				}
				return null;
			}
			if(auto r=combineInf(e1,e2,facts)) return r.simplify(facts);
			if(auto r=combineInf(e2,e1,facts)) return r.simplify(facts);
			if(e1==e2) return (e1^^2).simplify(facts);
			if(e1==zero||e2==zero) return zero;
			if(cast(Dℚ)e2||cast(DFloat)e2) swap(e1,e2);
			if(auto q1=cast(Dℚ)e1){
				if(q1.c==1) return e2;
				if(auto q2=cast(Dℚ)e2)
					return dℚ(q1.c*q2.c);
			}
			if(cast(Dℚ)e1||cast(DFloat)e1){
				if(auto p=cast(DPlus)e2){
					DExprSet summands;
					foreach(s;p.summands) summands.insert(e1*s);
					return dPlus(summands).simplify(facts);
				}
			}

			static DExpr combineWithFloat(DExpr e1,DExpr e2){
				if(auto f=cast(DFloat)e1){
					if(auto g=cast(DFloat)e2)
						return (f.c*g.c).dFloat;
					if(auto q2=cast(Dℚ)e2)
						return (f.c*toReal(q2.c)).dFloat;
				}
				return null;
			}
			static DExpr combineFloat(DExpr e1,DExpr e2){
				if(auto r=combineWithFloat(e1,e2)) return r;
				if(auto r=combineWithFloat(e2,e1)) return r;
				return null;
			}

			if(auto r=combineFloat(e1,e2)) return r;
			if(cast(DPow)e2) swap(e1,e2);
			if(!cast(Dℚ)e1 && e1==(-e2).simplify(facts)) return (-e1^^2).simplify(facts);
			if(auto p=cast(DPow)e1){
				if(p.operands[0]==e2){
					return (p.operands[0]^^(p.operands[1]+1)).simplify(facts);
				}
				if(p.operands[0]==-e2){
					return (-p.operands[0]^^(p.operands[1]+1)).simplify(facts);
				}
				if(auto d=cast(Dℚ)p.operands[0]){
					if(auto e=cast(Dℚ)e2){
						if(d.c==-e.c)
							return (-d^^(p.operands[1]+1)).simplify(facts);
						if(d.c==e.c.opUnary!"/"())
							return (d^^(p.operands[1]-1)).simplify(facts);
						if(d.c==-e.c.opUnary!"/"())
							return (-d^^(p.operands[1]-1)).simplify(facts);
					}
				}
				if(auto pf=cast(DPow)e2){
					if(p.operands[0]==pf.operands[0])
						return (p.operands[0]^^(p.operands[1]+pf.operands[1])).simplify(facts);
					static DExpr tryCombine(DExpr a,DExpr b,DExpr facts){
						DExprSet s;
						a=a.simplify(facts), b=b.simplify(facts);
						if(cast(DMult)a||cast(DMult)b) return null; // TODO: ok?
						DMult.insertAndSimplify(s,a,facts);
						DMult.insertAndSimplify(s,b,facts);
						if(a !in s || b !in s)
							return dMult(s).simplify(facts);
						return null;
					}
					auto exp1=p.operands[1],exp2=pf.operands[1];
					if(exp1==exp2){
						auto a=p.operands[0],b=pf.operands[0];
						if(auto r=tryCombine(a,b,facts))
							return (r^^exp1).simplify(facts);
					}
					if(exp1==(-exp2).simplify(facts)){
						auto a=p.operands[0],b=1/pf.operands[0];
						if(auto r=tryCombine(a,b,facts))
							return (r^^exp1).simplify(facts);
					}
				}
			}
			if(cast(DIvr)e2) swap(e1,e2);
			if(auto ivr1=cast(DIvr)e1){ // TODO: this should all be done by DIvr.simplify instead
				// TODO: this does not actually combine all facts optimally
				auto simple2=e2.simplify((e1*facts).simplify(one));
				if(simple2!=e2) return (simple2*e1).simplify(facts);
				if(auto ivr2=cast(DIvr)e2) with(DIvr.Type){
					// TODO: this does not actually combine all facts optimally
					auto simple1=e1.simplify((e2*facts).simplify(one));
					if(simple1!=e1) return (simple1*e2).simplify(facts);
					// combine a≤0 and -a≤0 to a=0
					if(ivr1.type==leZ&&ivr2.type==leZ){
						if(ivr1.e==(-ivr2.e).simplify(facts)){
							auto r=dEqZ(ivr1.e);
							r=r.simplify(facts);
							return r;
						}
						if(ivr1.e.mustBeLessThan(ivr2.e)) return e2;
						if(ivr2.e.mustBeLessThan(ivr1.e)) return e1;

						// TODO: better inconsistency checks!
						foreach(v;ivr1.freeVars()) with(BoundStatus){
							DExpr b1,b2;
							auto s1=ivr1.getBoundForVar(v,b1);
							auto s2=ivr2.getBoundForVar(v,b2);
							if(s1==fail || s2==fail) continue;
							// if(s1==s2) // TODO
							if(s1 != s2){
								if(s1==lowerBound){
									if(b2.mustBeLessThan(b1))
										return zero;
								}else{
									assert(s1==upperBound);
									if(b1.mustBeLessThan(b2))
										return zero;
								}
							}
						}

					}
					if(ivr2.type==eqZ) swap(ivr1,ivr2);
					if(ivr1.type==eqZ){
						if(ivr1.e==ivr2.e||ivr1.e==(-ivr2.e).simplify(facts)){ // TODO: jointly canonicalize
							// combine a=0 and a≠0 to 0
							if(ivr2.type==neqZ)
								return zero;
							// combine a=0 and a≤0 to a=0
							if(ivr2.type==leZ)
								return ivr1;
						}
					}

				}
			}
			if(auto l2=cast(DLog)e2)
				if(auto z2=l2.e.isInteger())
					if(z2.c>=0)
						if(auto p1=cast(DPow)e1)
							if(p1.operands[1] == mone)
								if(auto l1=cast(DLog)p1.operands[0])
									if(auto z1=l1.e.isInteger()){
										assert(z1.c.den==1&&z2.c.den==1);
										if(z2.c.num!=0 && z1.c.num!=1){
											if(z1.c>=0){
												if(auto r=integerLog(z2.c.num,z1.c.num))
													return r;
											}
											// TODO: generalize/improve the following simplification rule:
											if((z2.c.num%z1.c.num)==0)
												return (one+dLog(dℚ(z2.c.num/z1.c.num))*p1).simplify(facts);
										}
									}
			if(cast(DPlus)e2) swap(e1,e2);
			if(!e2.hasFreeVars()){
				if(auto p=cast(DPlus)e1){
					foreach(s;p.summands){
						auto x=(s*e2).simplify(facts);
						if(x.hasFactor(e2)) continue;
						auto summands=p.summands.setx;
						assert(s in summands);
						summands.remove(s);
						return (dPlus(summands)*e2+x).simplify(facts);
					}
				}
			}

			if(auto c1=cast(DMCase)e1)
				if(auto c2=cast(DMCase)e2)
					if(c1.e==c2.e)
						return dMCase(c1.e,c1.val*c2.val,c1.err*c2.err).simplify(facts);

			/+// TODO: do we want auto-distribution?
			if(cast(DPlus)e1) return dDistributeMult(e1,e2);
			if(cast(DPlus)e2) return dDistributeMult(e2,e1);+/
			// TODO: refine condition
			// TODO: use faster polynomial multiplication if possible?
			// (for example, only expand polynomial products in a sum of polynomials)
			if(isPolynomial(e1) && isPolynomial(e2)){
				if(cast(DPlus)e1) return dDistributeMult(e1,e2);
				if(cast(DPlus)e2) return dDistributeMult(e2,e1);
			}
			return null;
		}
		foreach(f;factors){
			if(auto nwf=combine(f,factor,facts)){
				factors.remove(f);
				if(factors.length||nwf != one)
					insertAndSimplify(factors,nwf,facts);
				return;
			}
		}
		assert(factors.length==1||one !in factors);
		assert(!cast(DMult)factor,text(factors," ",factor.simplify(one)));
		factors.insert(factor);
	}

	static MapX!(DExpr,DExpr) basicSimplifyCache;
	final DExpr basicSimplify(){
		if(this in basicSimplifyCache) return basicSimplifyCache[this];
		DExprSet simple;
		foreach(f;operands) insertAndSimplify(simple,f,one);
		auto r=dMult(simple);
		basicSimplifyCache[this]=r;
		return r;
	}

	override DExpr simplifyImpl(DExpr facts){
		// TODO: this is a major bottleneck!
		auto ne=basicSimplify();
		if(ne != this) return ne.simplify(facts);
		assert(!cast(DPlus)facts,text(facts));
		foreach(f;this.factors) if(auto d=cast(DDiscDelta)f){ // TODO: do this in a nicer way
			auto wo=this.withoutFactor(f);
			auto var=cast(DVar)d.var;
			if(var&&wo.hasFreeVar(var) && !d.e.hasFreeVar(var))
				return (wo.substitute(var,d.e)*d).simplify(facts);
		}
	Louter: foreach(f;this.factors) if(auto d=cast(DDelta)f){
			auto fact=dEqZ(d.var).simplify(facts);
			foreach(f;fact.factors) if(!cast(DIvr)f) continue Louter; // TODO: remove this if possible
			facts=facts*fact;
		}
		if(facts != one) facts=facts.simplify(one);
		DExprSet myFactors,myFacts,myIntegralFacts;
		foreach(f;this.factors){
			if(auto ivr=cast(DIvr)f){
				 // TODO: improve criterion (the point is to avoid simplifying identical subterms exponentially many times)
				if(!hasIntegrals(ivr.e))
					insertAndSimplify(myFacts,f,facts);
				else myIntegralFacts.insert(f);
			}else myFactors.insert(f);
		}
		DExpr newFacts=facts;
		if(myFacts.length){
			if(newFacts != one){
				DExprSet newFactsSet=newFacts.factors.setx;
				foreach(f;myFacts) insertAndSimplify(newFactsSet,f,one);
				newFacts=dMult(newFactsSet);
			}else newFacts=dMult(myFacts);
		}
		DExprSet simpFactors;
		assert(!cast(DPlus)newFacts,text(facts," ",myFacts," ",dMult(myFacts)));
		foreach(f;myFactors) insertAndSimplify(simpFactors,f,newFacts);
		foreach(f;myFacts) insertAndSimplify(simpFactors,f,one);
		foreach(f;myIntegralFacts) simpFactors.insert(f);
		return dMult(simpFactors);
	}
	static DExpr constructHook(DExprSet operands){
		if(operands.length==0) return one;
		return null;
	}
}

mixin FactoryFunction!DMult;
mixin FactoryFunction!DPlus;

auto distributeMult(DExpr sum,DExpr e){
	DExpr[] r;
	foreach(s;sum.summands)
		r~=s*e;
	return r;
}

auto dDistributeMult(DExpr sum,DExpr e){
	// TODO: does this actually do anything?
	DExprSet r;
	//writeln(sum," ",e);
	foreach(s;sum.summands)
		DPlus.insert(r,s*e);
	return dPlus(r);
}

auto operands(T)(DExpr x){
	static struct Operands{
		DExpr x;
		int opApply(scope int delegate(DExpr) dg){
			if(auto m=cast(T)x){
				foreach(f;m.operands)
					if(auto r=dg(f))
						return r;
				return 0;
			}else return dg(x);
		}
	}
	return Operands(x);
}
alias factors=operands!DMult;
alias summands=operands!DPlus;

DExpr negateSummands(DExpr e){
	static DExpr negateFactor(DExpr e){
		bool negated=false;
		DExprSet r;
		foreach(f;e.factors){
			auto q=cast(Dℚ)f;
			if(!negated && q){
				negated=true;
				if(f !is mone) DMult.insert(r,dℚ(-q.c));
			}else DMult.insert(r,f);
		}
		if(!negated) DMult.insert(r,mone);
		return dMult(r);
	}
	DExprSet r;
	foreach(s;e.summands){
		DPlus.insert(r,negateFactor(s));
	}
	return dPlus(r);
}

Dℚ getFractionalFactor(DExpr e){
	ℚ r=1;
	foreach(f;e.factors)
		if(auto q=cast(Dℚ)f)
			r=r*q.c;
	return dℚ(r);
}

DExpr dMinus(DExpr e1,DExpr e2){ return e1+-e2; }

abstract class DBinaryOp: DOp{
	DExpr[2] operands;
	alias subExprs=Seq!operands;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp)
			return text("(",symbol(formatting,binders)," ",operands[0].toStringImpl(formatting,prec,binders)," ",operands[1].toStringImpl(formatting,prec,binders),")");
		return addp(prec, operands[0].toStringImpl(formatting,precedence,binders) ~ symbol(formatting,binders) ~ operands[1].toStringImpl(formatting,precedence,binders));
	}
}

class DPow: DBinaryOp{
	override Precedence precedence(){ return Precedence.pow; }
	override @property string symbol(Format formatting,int binders){
		if(formatting==Format.gnuplot) return "**";
		else if(formatting==Format.matlab) return ".^";
		else if(formatting==Format.python||formatting==Format.sympy) return "**";
		else return "^";
	}
	override bool rightAssociative(){ return true; }

	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.python) return "nan_to_num("~operands[0].toStringImpl(formatting,precedence.pow,binders)~"**"~operands[1].toStringImpl(formatting,precedence.pow,binders)~")";
		if(formatting==Format.lisp){
			if(operands[1]==mone){
				return text("(/ 1 ",operands[0].toStringImpl(formatting,Precedence.none,binders),")");
			}
			return super.toStringImpl(formatting,Precedence.none,binders);
		}
		auto frc=operands[1].getFractionalFactor();
		if(frc.c<0){
			if(formatting==Format.matlab||formatting==Format.gnuplot){
				addp(prec,text(dNeqZ(operands[0]).toStringImpl(formatting,Precedence.div,binders),"./",
				               (operands[0]+dEqZ(operands[0])).toStringImpl(formatting,Precedence.div,binders)),
					 Precedence.div);
			}else{
				auto pre=formatting==Format.default_?"⅟":"1/";
				auto exp=(-operands[1]).simplify(one);
				return addp(prec,pre~(exp==one?operands[0]:operands[0]^^exp).toStringImpl(formatting,Precedence.div,binders),Precedence.div);
			}
		}
		// also nice, but often hard to read: ½⅓¼⅕⅙
		if(formatting==Format.default_){
			if(auto c=operands[1].isInteger()){
				assert(c.c.den==1);
				return addp(prec,operands[0].toStringImpl(formatting,Precedence.pow,binders)~highNum(c.c.num));
			}
			if(auto c=cast(Dℚ)operands[1])
				if(c.c.num==1)
					if(2<=c.c.den&&c.c.den<=4)
						return text("  √∛∜"d[cast(size_t)c.c.den.toLong()],overline(operands[0].toStringImpl(formatting,precedence.none,binders)));
		}
		/+if(formatting==Format.matlab)
		 return text("fixNaN(",super.toStringImpl(formatting,prec),")");+/// TODO: why doesn't this work?
		return super.toStringImpl(formatting,prec,binders);
	}
	mixin Visitors;
	/+private+/ static DExpr staticSimplify(DExpr e1,DExpr e2,DExpr facts=one){
		auto ne1=e1.simplify(facts);
		auto ne2=e2.simplify(facts);
		if(ne1!=e1||ne2!=e2) return dPow(ne1,ne2).simplify(facts);
		if(e1 != mone){
			auto c=e1.getFractionalFactor();
			if(c.c<0)
				if(e2.isInteger())
					return (mone^^e2*(-e1)^^e2).simplify(facts);
		}
		if(auto m=cast(DMult)e1){
			DExprSet outside;
			DExprSet within;
			bool nat=!!e2.isInteger();
			foreach(f;m.operands){
				if(nat||dLtZ(f).simplify(facts)==zero)
					DMult.insert(outside,f^^e2);
				else DMult.insert(within,f);
			}
			if(outside.length){
				if(within.length)
					return (dMult(outside)*dMult(within)^^e2).simplify(facts);
				else return dMult(outside).simplify(facts);
			}
		}
		if(auto p=cast(DPow)e1){
			if(p.operands[0]!=mone){
				auto e2p=p.operands[1]*e2;
				if(p.operands[1].isFractional()) return (p.operands[0]^^e2p).simplify(facts);
				return (dLtZ(p.operands[0])*(mone^^p.operands[1])^^e2*(-p.operands[0])^^e2p+
				        dGeZ(p.operands[0])*p.operands[0]^^e2p).simplify(facts);
			}
		}
		if(e1==one||e2==zero) return one;
		if(e1==mone && e2==mone) return mone;
		if(e2==one) return e1;
		if(e1.mustBeZeroOrOne()&&(-e2).simplify(facts).mustBeLessOrEqualZero())
			return (dNeqZ(e2)*e1+dEqZ(e2)).simplify(facts);
		if(e1==zero) return dEqZ(e2).simplify(facts);
		if(auto d=e2.isInteger()){
			if(auto c=cast(Dℚ)e1){
				assert(d.c.den==1);
				return dℚ(pow(c.c,d.c.num));
			}
		}
		foreach(f;e2.factors){
			if(auto l=cast(DLog)f){ // TODO: more principled way of handling this, with more cases
				if(auto e=cast(DE)e1)
					return (l.e^^e2.withoutFactor(f)).simplify(facts);
				if(auto d=cast(Dℚ)e1){
					if(auto c=cast(Dℚ)l.e){
						if(c.c<d.c) return (c^^(dLog(d)*e2.withoutFactor(f))).simplify(facts);
						else return null;
					}else return (l.e^^(dLog(d)*e2.withoutFactor(f))).simplify(facts);
				}
			}
		}
		if(auto c=cast(Dℚ)e1){ // TODO: more simplifications with constant base
			auto q=e2.getFractionalFactor();
			if(q.c<0 && c.c.den!=1)  return (dℚ(c.c.opUnary!"/"())^^-e2).simplify(one);
			if(c==mone){ // canonicalize powers of -1 (TODO: this only happens in dead subexpressions, can we do something else?)
				if(q.c>1||q.c<0){
					auto k=2*q.c.den;
					auto nq = (q.c.num%k+k)%k;
					return (e1^^(e2*(dℚ(nq)/q))).simplify(facts);
				}
			}
			if(1<q.c.den&&q.c.den<=5) // TODO: 5 ok?
				if(auto r=nthRoot(c.c.num,q.c.den)){
					return (r^^(e2*q.c.den)/c.c.den^^e2).simplify(facts);
				}
		}
		if(cast(DPlus)e1){
			if(auto r=expandPow(e1,e2))
				return r.simplify(facts);
		}

		/+if(e1.isFraction()&&e2.isFraction()){
			auto nd=e2.getFraction();
			if(nd[0]%nd[1]!=0&&abs(nd[0])>abs(nd[1])){
				auto wh=nd[0]/nd[1];
				return (e1^^wh).simplify(facts)*(e1^^(e2-wh).simplify(facts));
			}
		}+/

		if(auto f1=cast(DFloat)e1){
			if(auto f2=cast(DFloat)e2)
				return (f1.c^^f2.c).dFloat;
			if(auto q2=cast(Dℚ)e2)
				return (f1.c^^toReal(q2.c)).dFloat;
		}
		if(auto q1=cast(Dℚ)e1)
			if(auto f2=cast(DFloat)e2)
				return (toReal(q1.c)^^f2.c).dFloat;
		if(auto fct=factorDIvr!(e=>e^^e2)(e1)) return fct.simplify(facts);
		if(e2.hasAny!DIvr(false)){
			DExprSet r;
			bool changed=false;
			foreach(s;e2.summands){
				DExpr f;
				if(auto ns=factorDIvr!(e=>e1^^e)(s)){
					changed=true;
					f=ns;
				}else f=e1^^s;
				DMult.insert(r,f);
			}
			if(changed) return dMult(r).simplify(facts);
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(operands[0],operands[1],facts);
		return r?r:this;
	}
}

mixin FactoryFunction!DPow;
DExpr dDiv(DExpr e1,DExpr e2){ return e1*e2^^mone; }


DExpr expandPow(DExpr e1,DExpr e2,long limit=-1){
	auto c=e2.isInteger();
	if(!c||c.c<=0||limit>=0&&c.c>limit) return null;
	assert(c.c.den==1);
	auto a=cast(DPlus)e1;
	if(!a) return null;
	DExpr s;
	foreach(x;a.summands){
		s=x;
		break;
	}
	assert(!!s);
	auto rest=a.withoutSummand(s);
	DExprSet r;
	auto ncrange=nC(c.c.num);
	for(ℤ i=0,j=c.c.num;i<=c.c.num;i++,j--,ncrange.popFront())
		DPlus.insert(r,ncrange.front*s^^i*rest^^j);
	return dPlus(r);
}

DExpr expandPow(DPow p,long limit=-1){
	auto r=expandPow(p.operands[0],p.operands[1],limit);
	return r?r:p;
}

struct DPolynomial{
	DVar var;
	DExpr[long] coefficients;
	long degree=-1;
	bool initialized(){ return !!var; }
	T opCast(T:bool)(){ return initialized(); }
	void addCoeff(long exp,DExpr coeff)in{assert(exp>=0);}body{
		degree=max(degree,exp);
		coefficients[exp]=coefficients.get(exp,zero)+coeff;
	}
	DExpr toDExpr(){
		DExprSet r;
		foreach(k,v;coefficients)
			DPlus.insert(r,v*var^^k);
		return dPlus(r);
	}
	struct Zero{
		DExpr expr;
		DExpr cond;
	}
	Zero[] zeros()in{assert(degree<=2);}body{ // TODO: get rid of allocation?
		Zero[] r;
		auto a=coefficients.get(2,zero);
		auto b=coefficients.get(1,zero);
		auto c=coefficients.get(0,zero);
		r~=Zero(-c/b,dEqZ(a)*dNeqZ(b));
		r~=Zero((-b-(b^^2-4*a*c)^^(one/2))/(2*a),dNeqZ(a)*dGeZ(b^^2-4*a*c));
		r~=Zero((-b+(b^^2-4*a*c)^^(one/2))/(2*a),dNeqZ(a)*dGtZ(b^^2-4*a*c));
		return r;
	}
}

bool hasFactor(DExpr e,DExpr factor){
	foreach(f;e.factors) if(factor==f) return true;
	return false;
}

DExpr withoutFactor(DExpr e,DExpr factor){
	auto s=e.factors.setx;
	assert(factor in s);
	return dMult(s.without(factor));
}

DExpr withoutSummand(DExpr e,DExpr summand){
	auto s=e.summands.setx;
	assert(summand in s);
	return dPlus(s.without(summand));
}

DExpr polyNormalize(DExpr e,DVar v=null,long limit=-1){
	DExprSet normSet;
	Louter: foreach(s;e.summands){
		if(!v||s.hasFreeVar(v)){
			if(auto p=cast(DPow)s){
				DPlus.insert(normSet,p.expandPow(limit));
				continue;
			}
			if(auto p=cast(DMult)s){
				foreach(f;p.factors){
					if(auto a=cast(DPlus)f){
						DPlus.insert(normSet,dDistributeMult(a,s.withoutFactor(f)));
						continue Louter;
					}
				}
				foreach(f;p.factors){
					if(auto norm=polyNormalize(f,v,limit)){
						if(norm != f){
							DPlus.insert(normSet,p.withoutFactor(f)*norm);
							continue Louter;
						}
					}
				}
			}
		}
		DPlus.insert(normSet,s);
	}
	auto r=dPlus(normSet).simplify(one);
	if(r != e) return polyNormalize(r,v,limit);
	return r;

}

// TODO: keep flag in expressions instead?
bool isPolynomial(DExpr e){
	if(cast(DVar)e) return true;
	if(!e.hasFreeVars()) return true;
	if(auto p=cast(DPow)e){
		if(auto q=p.operands[1].isInteger())
			return q.c.num >= 0 && isPolynomial(p.operands[0]);
		return false;
	}
	if(auto m=cast(DMult)e){
		foreach(f;m.factors)
			if(!isPolynomial(f))
				return false;
		return true;
	}
	if(auto m=cast(DPlus)e){
		foreach(s;m.summands)
			if(!isPolynomial(s))
				return false;
		return true;
	}
	return false;
}

DPolynomial asPolynomialIn(DExpr e,DVar v,long limit=-1){
	auto normalized=polyNormalize(e,v,limit);
	auto r=DPolynomial(v);
	bool addCoeff(long exp,DExpr coeff){
		if(exp<0) return false;
		if(coeff.hasFreeVar(v)) return false;
		r.addCoeff(exp,coeff);
		return true;
	}
 Lsum:foreach(s;normalized.summands){
		foreach(f;s.factors){
			if(f==v){
				if(!addCoeff(1,s.withoutFactor(v)))
					return DPolynomial.init;
				continue Lsum;
			}
			auto p=cast(DPow)f;
			if(!p||p.operands[0] != v) continue;
			auto c=p.operands[1].isInteger();
			if(!c) continue;
			assert(c.c.den==1);
			auto coeff=s.withoutFactor(p);
			assert(c.c.num<=long.max);
			if(!addCoeff(c.c.num.toLong(),coeff))
				return DPolynomial.init;
			continue Lsum;
		}
		if(!addCoeff(0,s)) return DPolynomial.init;
	}
	if(~limit && r.degree>limit) return DPolynomial.init;
	return r;
}

DExpr[2] asLinearFunctionIn(DExpr e,DVar v){ // returns [b,a] if e=av+b
	auto p=e.asPolynomialIn(v);
	if(p==DPolynomial.init||p.degree>1) return [null,null];
	return [p.coefficients.get(0,zero),p.coefficients.get(1,zero)];
}


abstract class DUnaryOp: DOp{
	DExpr operand;
	alias subExprs=Seq!operand;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp)
			return text("(",symbol(formatting,binders)," ",operand.toStringImpl(formatting,prec,binders),")");
		return addp(prec, symbol(formatting,binders)~operand.toStringImpl(formatting,precedence,binders));
	}
}
DExpr dUMinus(DExpr e){ return mone*e; }

bool approxEqual(real a,real b){
	return a==b;
}

// TODO: improve these procedures: they are way too naive
bool couldBeZero(DExpr e){
	if(cast(DΠ)e) return false;
	if(cast(DE)e) return false;
	if(auto c=cast(Dℚ)e) return c.c==0;
	if(auto c=cast(DFloat)e){
		return approxEqual(c.c,0);
	}
	if(auto p=cast(DPow)e) return couldBeZero(p.operands[0]);
	if(cast(DGaussInt)e) return false;
	if(cast(DGaussIntInv)e) return false;
	if(auto p=cast(DPlus)e){
		bool allLarge=true,allSmall=true;
		foreach(s;p.summands){
			if(!mustBeLessThanZero(s)) allSmall=false;
			if(!mustBeLessThanZero((-s).simplify(one))) allLarge=false;
			if(!allSmall&&!allLarge) break;
		}
		if(allSmall||allLarge) return false;
	}
	if(auto m=cast(DMult)e){
		bool allDistinct=true;
		foreach(f;m.factors){
			if(couldBeZero(f)){
				allDistinct=false;
				break;
			}
		}
		if(allDistinct) return false;
	}
	if(auto p=cast(DPlus)e){
		bool allLessOrEqual=true;
		bool allGreaterOrEqual=true;
		bool existsNonZero=false;
		foreach(s;p.summands){
			if(!mustBeLessOrEqualZero(s))
				allLessOrEqual=false;
			if(!mustBeLessOrEqualZero((-s).simplify(one)))
				allGreaterOrEqual=false;
			if(!allLessOrEqual&&!allGreaterOrEqual)
				break;
			if(!couldBeZero(s))
				existsNonZero=true;
		}
		if(existsNonZero&&(allLessOrEqual||allGreaterOrEqual)){
			assert(!allLessOrEqual||!allGreaterOrEqual);
			return false;
		}
	}
	return true;
}

bool mustBeZeroOrOne(DExpr e){
	if(e==zero || e==one) return true;
	if(cast(DIvr)e) return true;
	if(auto m=cast(DMult)e) return util.all!mustBeZeroOrOne(m.factors);
	return false;
}

bool mustBeLessOrEqualZero(DExpr e){
	bool mustBeLessOrEqualZeroImpl(DExpr e){
		if(cast(DΠ)e||cast(DE)e) return false;
		if(auto c=cast(Dℚ)e) return c.c<=0;
		if(auto c=cast(DFloat)e) return c.c<=0;
		if(auto p=cast(DPow)e){
			if(auto exp=p.operands[1].isInteger()){
				assert(exp.c.den==1);
				if(exp.c.num%2){
					return mustBeLessOrEqualZeroImpl(p.operands[0]);
				}
			}
		}
		return false;
	}
	if(mustBeLessOrEqualZeroImpl(e)) return true;
	bool mustBeGreaterOrEqualZeroImpl(DExpr e){
		if(cast(DΠ)e||cast(DE)e) return true;
		if(auto c=cast(Dℚ)e) return c.c>=0;
		if(auto c=cast(DFloat)e) return c.c>=0;
		if(auto p=cast(DPow)e){
			if(auto exp=p.operands[1].isInteger()){
				assert(exp.c.den==1);
				return !(exp.c.num%2)||mustBeGreaterOrEqualZeroImpl(p.operands[0]);
			}
			if(p.operands[1].isFractional()) return true;
			if(mustBeGreaterOrEqualZeroImpl(p.operands[0])) return true;
		}
		if(mustBeZeroOrOne(e)) return true;
		return false;
	}
	if(auto m=cast(DMult)e){
		auto ff=m.getFractionalFactor();
		if(ff.c<=0){
			bool allGreaterEqual=true;
			foreach(f;m.factors){
				if(cast(Dℚ)f) continue;
				if(!mustBeGreaterOrEqualZeroImpl(f)){
					allGreaterEqual=false; break;
				}
			}
			if(allGreaterEqual) return true;
		}
	}
	if(auto p=cast(DPlus)e){
		bool allLessOrEqual=true;
		foreach(s;p.summands){
			if(!mustBeLessOrEqualZero(s)){
				allLessOrEqual=false; break;
			}
		}
		if(allLessOrEqual) return true;
	}
	return false;
}
bool mustBeLessThanZero(DExpr e){
	return !couldBeZero(e)&&mustBeLessOrEqualZero(e);
}

bool mustBeLessThan(DExpr e1,DExpr e2){
	return mustBeLessThanZero((e1-e2).simplify(one));
}
bool mustBeAtMost(DExpr e1,DExpr e2){
	return mustBeLessOrEqualZero((e1-e2).simplify(one));
}

DExpr cancelFractions(bool isDelta)(DExpr e,DIvr.Type type=DIvr.Type.eqZ){
	bool simple=false;
	int nfreeVar=0;
	foreach(v;e.freeVars) nfreeVar++;
	DExpr cancel=one;
	if(nfreeVar==1){
		DVar var;
		foreach(v;e.freeVars){ var=v; break; }
		int count=0,tot=0;
		foreach(s;e.summands){
			++tot;
			if(s.hasFreeVar(var))
				++count;
		}
		if(tot>1&&count==1){
			simple=true;
			foreach(s;e.summands){
				if(!s.hasFreeVar(var)) continue;
				auto f=s.getFractionalFactor();
				if(f==mone) break;
				cancel=(mone/f).simplify(one);
				if((s*cancel).simplify(one).getFractionalFactor()!=mone)
					cancel=one;
				break;
			}
		}
	}
	if(!simple) cancel=uglyFractionCancellation(e).simplify(one);
	static if(!isDelta)
		with(DIvr.Type)
			if(!util.among(type,eqZ,neqZ))
				cancel=dAbs(cancel).simplify(one);
	if(cancel!=one){
		static if(isDelta) return dDelta(dDistributeMult(e,cancel))*dAbs(cancel);
		else return dIvr(type,dDistributeMult(e,cancel));
	}
	auto nege=(-e).simplify(one);
	if(!simple&&(util.among(type,DIvr.Type.eqZ,DIvr.Type.neqZ))&&(e.getFractionalFactor().c<0||nege.getFractionalFactor().c>=0&&nege.isMoreCanonicalThan(e))){
		static if(isDelta) return dDelta(nege);
		else return dIvr(type,nege);
	}
	return null;
}


DExpr uglyFractionCancellation(DExpr e){
	ℤ ngcd=0,dlcm=1;
	foreach(s;e.summands){
		auto f=s.getFractionalFactor();
		if(f.c.den==0) continue;
		assert(f.c.den>0);
		ngcd=gcd(ngcd,abs(f.c.num));
		dlcm=lcm(dlcm,f.c.den);
	}
	if(!ngcd) return one;
	return dℚ(ℚ(dlcm,ngcd));
}

Q!(DExpr,DExpr) splitCommonDenominator(DExpr e){
	DExprSet denom;
	foreach(s;e.summands){
		DExprSet cden;
		foreach(f;s.factors){
			if(auto p=cast(DPow)f){
				auto n=p.operands[1].isInteger();
				if(n&&n.c<0){
					assert(n.c.den==1);
					// TODO: improve
					DMult.insert(cden,n==mone?p.operands[0]:p.operands[0]^^dℚ(-n.c));
				}
			}
		}
		if(cden.length) denom.insert(dMult(cden));
	}
	if(!denom.length) return q(e,one);
	DExprSet num;
	foreach(s;e.summands){
		DExprSet cnum=denom.dup;
		foreach(f;s.factors){
			if(auto p=cast(DPow)f){
				auto n=p.operands[1].isInteger();
				if(n&&n.c<0){
					// TODO: improve calculation of toRemove
					auto toRemove=n==mone?p.operands[0]:p.operands[0]^^dℚ(-n.c);
					if(toRemove in cnum){
						cnum.remove(toRemove);
						continue;
					}
				}
			}
			DMult.insert(cnum,f);
		}
		DPlus.insert(num,dMult(cnum));
	}
	return q(dPlus(num),dMult(denom));
}

enum BoundStatus{
	fail,
	lowerBound,
	upperBound,
	equal,
}

BoundStatus getBoundForVar(DIvr ivr,DVar var,out DExpr bound){
	enum r=BoundStatus.fail;
	with(DIvr.Type) if(ivr.type!=leZ&&ivr.type!=eqZ) return r;
	foreach(s;ivr.e.summands){
		if(!s.hasFactor(var)) continue; // TODO: non-linear constraints
		auto cand=s.withoutFactor(var);
		if(cand.hasFreeVar(var)) return r;
		BoundStatus result;
		with(DIvr.Type) if(ivr.type==leZ){
			auto lZ=dLtZ(cand).simplify(one)==one;
			auto gZ=dGtZ(cand).simplify(one)==one;
			if(!lZ&&!gZ) return r;
			result=lZ?BoundStatus.lowerBound:BoundStatus.upperBound;
		}else{
			assert(ivr.type==eqZ);
			result=BoundStatus.equal;
		}
		auto ne=(var-ivr.e/cand).simplify(one); // TODO: are there cases where this introduces division by 0?
		if(ne.hasFreeVar(var)) return r;
		// TODO: must consider strictness!
		bound=ne;
		return result;
	}
	return r;
}

Q!(bool,DExpr[3]) getBoundsForVar(alias boundLe=dLe)(DExpr ivrs,DVar var,DExpr facts=one){
	DExprSet lowers,uppers;
	foreach(f;ivrs.factors){
		if(f is one) break;
		auto ivr=cast(DIvr)f;
		assert(!!ivr);
		assert(ivr.type!=DIvr.Type.neqZ);
		DExpr bound;
		auto status=ivr.getBoundForVar(var,bound);
		final switch(status) with(BoundStatus){
		case fail:
			return q(false,cast(DExpr[3])[null,null,null]);
		case lowerBound:
			lowers.insert(bound.simplify(facts));
			break;
		case upperBound:
			uppers.insert(bound.simplify(facts));
			break;
		case equal:
			lowers.insert(bound.simplify(facts));
			uppers.insert(bound.simplify(facts));
		}
	}
	DExprSet lowLeUps;
	foreach(lower;lowers)
		foreach(upper;uppers)
			lowLeUps.insert(boundLe(lower,upper));
	auto lower=lowers.length?dMax(lowers).simplify(facts):null;
	auto upper=uppers.length?dMin(uppers).simplify(facts):null;
	auto lowLeUp=dMult(lowLeUps);
	return q(true,cast(DExpr[3 ])[lower,upper,lowLeUp]);
}

// attempt to produce an equivalent expression where 'var' does not occur non-linearly in constraints
DExpr linearizeConstraints(alias filter=e=>true)(DExpr e,DVar var){ // TODO: don't re-build the expression if no constraints change.
	if(!e.hasFreeVar(var)) return e;
	if(auto p=cast(DPlus)e){
		DExprSet r;
		foreach(s;p.summands) DPlus.insert(r,linearizeConstraints!filter(s,var));
		return dPlus(r);
	}
	if(auto m=cast(DMult)e){
		DExprSet r;
		foreach(f;m.factors) DMult.insert(r,linearizeConstraints!filter(f,var));
		return dMult(r);
	}
	if(auto p=cast(DPow)e){
		return linearizeConstraints(p.operands[0],var)^^linearizeConstraints!filter(p.operands[1],var);
	}
	if(auto ivr=cast(DIvr)e) if(filter(ivr)) return linearizeConstraint(ivr,var);
	if(auto delta=cast(DDelta)e) if(filter(delta)) return linearizeConstraint(delta,var);
	return e; // TODO: enough?
}

DExpr linearizeConstraint(T)(T cond,DVar var) if(is(T==DIvr)||is(T==DDelta))
in{static if(is(T==DIvr)) with(DIvr.Type) assert(util.among(cond.type,eqZ,neqZ,leZ));}body{
	alias Type=DIvr.Type;
	alias eqZ=Type.eqZ, neqZ=Type.neqZ, leZ=Type.leZ, lZ=Type.lZ;
	enum isDelta=is(T==DDelta);
	class Unwind:Exception{this(){super("");}} // TODO: get rid of this?
	void unwind(){ throw new Unwind(); }
	DExpr doIt(DExpr parity,Type ty,DExpr lhs,DExpr rhs){ // invariant: var does not occur in rhs or parity
		if(auto p=cast(DPlus)lhs){
			auto ow=splitPlusAtVar(lhs,var);
			if(cast(DPlus)ow[1]){
				if(auto poly=(lhs-rhs).asPolynomialIn(var,2)){
					auto a=poly.coefficients.get(2,zero);
					auto b=poly.coefficients.get(1,zero);
					auto c=poly.coefficients.get(0,zero);
					auto disc=b^^2-4*a*c;
					auto z1=(-b-disc^^(one/2))/(2*a),z2=(-b+disc^^(one/2))/(2*a);
					if(ty==leZ){
						static if(isDelta) assert(0); // (recursive base case; never happens for deltas)
						auto evenParity=linearizeConstraints(dGeZ(parity*a),var);
						return dEqZ(a)*doIt(parity,ty,b*var+c,rhs)+
						dNeqZ(a)*(
						  dLtZ(disc)*dLeZ((lhs-rhs).substitute(var,-b/(2*a)))+
						  dGeZ(disc)*(
						    evenParity*(
						      dGeZ(a)*dLe(z1,var)*dLe(var,z2)+
						      dLeZ(a)*dLe(z2,var)*dLe(var,z1)
						    )+
						    dEqZ(evenParity)*(
						      dGeZ(a)*(dLe(var,z1)+dNeqZ(disc)*dLe(z2,var)+dEqZ(disc)*dLt(z2,var))+
						      dLeZ(a)*(dLe(var,z2)+dNeqZ(disc)*dLe(z1,var)+dEqZ(disc)*dLt(z1,var))
						    )
						  )
						);
					}else if(ty==eqZ){
						return dIvr(eqZ,a)*doIt(parity,ty,b*var+c,rhs)+
							dIvr(neqZ,a)*dIvr(leZ,-disc)*(doIt(one,ty,var,z1)+dIvr(neqZ,disc)*doIt(one,ty,var,z2));
					}else{
						return dIvr(eqZ,a)*doIt(parity,ty,b*var+c,rhs)+
							dIvr(neqZ,a)*(dIvr(lZ,disc)+dIvr(leZ,-disc)*doIt(one,ty,var,z1)*doIt(one,ty,var,z2));
                    }
				}
			}else return doIt(parity,ty,ow[1],rhs-ow[0]);
		}else if(auto m=cast(DMult)lhs){
			auto ow=splitMultAtVar(m,var);
			if(!cast(DMult)ow[1]){
				// TODO: make sure this is correct for deltas
				// (this is what the case split code did)
				static if(isDelta) auto rest=dDelta(rhs);
				else auto rest=dIvr(ty,-rhs);
				return dIvr(eqZ,ow[0])*rest+dIvr(neqZ,ow[0])*doIt(parity*ow[0],ty,ow[1],rhs/ow[0]);
			} // TODO: what if ow[1] is a product?
		}else if(auto p=cast(DPow)lhs){
			auto e1=p.operands[0].polyNormalize(var),e2=p.operands[1];
			DExpr negatePower()in{
				auto q2=cast(Dℚ)e2;
				assert(!!q2 && q2.c<0);
			}body{
				auto lhsInv=e1^^(-e2);
				auto r=dIvr(neqZ,rhs)*doIt(-parity*rhs*lhsInv,ty,lhsInv.polyNormalize(var),rhs^^mone);
				if(ty==leZ){
					static if(isDelta) assert(0);
					r=linearizeConstraints(dIvr(leZ,parity*lhsInv),var)*dIvr(eqZ,rhs)+r;
				}else if(ty==neqZ){
					static if(isDelta) assert(0);
					r=dIvr(eqZ,rhs)+r;
				}
				return r;
			}
			auto n=e2.isInteger();
			if(n){
				assert(n.c.den==1);
				if(n.c.num<0) return negatePower();
				if(!(n.c.num&1)){ // even integer power
					auto z2=rhs^^(1/n), z1=-z2;
					static if(isDelta) assert(ty==eqZ);
					if(ty==leZ){
						auto le=dIvr(leZ,-rhs)*doIt(mone,ty,e1,z1)*doIt(one,ty,e1,z2);
						auto ge=dIvr(leZ,rhs)+dIvr(lZ,-rhs)*(doIt(one,ty,e1,z1)+dIvr(neqZ,z2)*doIt(mone,ty,e1,z2));
						auto evenParity=linearizeConstraints(dIvr(leZ,-parity),var);
						return evenParity*le+dIvr(eqZ,evenParity)*ge;
					}else if(ty==eqZ){
						return dIvr(leZ,-rhs)*(doIt(one,ty,e1,z1)+dIvr(neqZ,z2)*doIt(one,ty,e1,z2));
					}else{
						assert(ty==neqZ);
						return dIvr(lZ,rhs)+dIvr(leZ,-rhs)*doIt(one,ty,e1,z1)*doIt(one,ty,e1,z2);
					}
				}else{ // odd integer power
					return dIvr(leZ,-rhs)*doIt(parity,ty,e1,rhs^^(1/n))
						+dIvr(lZ,rhs)*doIt(parity,ty,e1,-(-rhs)^^(1/n));
				}
			}else if(auto q2=cast(Dℚ)e2){
				// fractional power. assume e1>=0. (TODO: make sure the analysis respects this)
				if(q2.c<0) return negatePower();
				assert(q2.c>=0 && q2.c.den != 1);
				auto r=dIvr(leZ,-rhs)*doIt(parity,ty,e1,rhs^^dℚ(q2.c.opUnary!"/"));
				static if(isDelta) assert(ty==eqZ);
				if(ty==leZ){
					auto oddParity=linearizeConstraints(dIvr(lZ,parity).simplify(one),var);
					r=oddParity*dIvr(lZ,rhs)+r;
				}else if(ty==neqZ){
					r=dIvr(lZ,rhs)+r;
				}
				return r;
			}else if(!e1.hasFreeVar(var)&&dLeZ(e1).simplify(one)==zero){
				auto r=dIvr(lZ,-rhs)*doIt(parity,ty,(dLog(e1)*e2).simplify(one),dLog(rhs));
				static if(isDelta) assert(ty==eqZ);
				if(ty==leZ){
					auto oddParity=linearizeConstraints(dIvr(lZ,parity).simplify(one),var);
					r=oddParity*dIvr(leZ,rhs)+r;
				}else if(ty==neqZ){
					r=dIvr(leZ,rhs)+r;
				}else assert(ty==eqZ);
				return r;
			}
		}else if(auto l=cast(DLog)lhs){
			return doIt(parity,ty,l.e,dE^^rhs);
		}else if(auto g=cast(DGaussInt)lhs){
			auto r=dLt(zero,rhs)*dLt(rhs,dΠ^^(one/2))*doIt(parity,ty,g.x,dGaussIntInv(rhs));
			static if(isDelta) assert(ty==eqZ);
			if(ty==leZ){
				auto oddParity=linearizeConstraints(dIvr(lZ,parity).simplify(one),var);
				auto evenParity=dEqZ(oddParity);
				r=oddParity*dLe(rhs,zero)+evenParity*dLe(dΠ^^(one/2),rhs)+r;
			}else if(ty==neqZ) r=dLe(rhs,zero)+dLe(dΠ^^(one/2),rhs)+r;
			else assert(ty==eqZ);
			return r;
		}else if(auto g=cast(DGaussIntInv)lhs){
			return doIt(parity,ty,g.x,dGaussInt(rhs));
		}
		lhs=lhs.simplify(one);
		auto numden=lhs.splitCommonDenominator();
		numden[1]=numden[1].simplify(one);
		if(numden[1]!=one){
			numden[0]=numden[0].simplify(one);
			auto num=numden[0],den=numden[1];
			return doIt(parity*den,ty,(num-rhs*den).simplify(one),zero);
		}
		if(ty==leZ){
			static if(isDelta) assert(0);
			auto evenParity=linearizeConstraints(dIvr(leZ,-parity),var);
			return evenParity*dIvr(leZ,lhs-rhs)+dIvr(eqZ,evenParity)*dIvr(leZ,rhs-lhs);
		}
		static if(isDelta){
			if(lhs != var) unwind(); // TODO: get rid of this?
			auto diff=dAbs(dDiff(var,cond.var)).simplify(one);
			auto pole=dIvr(eqZ,diff).simplify(one).linearizeConstraints(var).polyNormalize(var).simplify(one);
			DExprSet special;
			foreach(s;pole.summands){
				DExpr summand=null;
				if(s.hasFreeVar(var)) foreach(f;s.factors){
					if(!f.hasFreeVar(var)) continue;
					auto ivr=cast(DIvr)f;
					if(ivr&&ivr.type == eqZ){
						auto val=solveFor(ivr.e,var); // TODO: modify solveFor such that it only solves linear equations and returns additional constraints.
						if(!val || ivr.substitute(var,val).simplify(one) != one)
							continue; // TODO: get rid of this
						summand=s*cond.substitute(var,val);
						break;
					}
				}else summand=s; // TODO: is this necessary?
				if(summand is null) unwind();
				DPlus.insert(special,summand);
			}
			return dIvr(neqZ,diff).linearizeConstraints(var)*dDelta(lhs-rhs)/diff+dPlus(special);
		}
		else return dIvr(ty,lhs-rhs);
	}
	static if(isDelta) auto ty=eqZ;
	else auto ty=cond.type;
	static if(isDelta) auto e=cond.var;
	else auto e=cond.e;
	try return doIt(one,ty,e.polyNormalize(var),zero);
	catch(Unwind) return cond;
}

struct SolutionInfo{
	static struct UseCase{
		bool caseSplit;
		bool bound;
	}
	bool needCaseSplit;
	static struct CaseSplit{
		DExpr constraint;
		DExpr expression;
	}
	CaseSplit[] caseSplits;
	static struct Bound{
		DExpr isLower;
		void setLower(){ isLower=mone; }
		void invertIflZ(DExpr e){
			if(isLower) isLower=isLower*e;
		}
	}
	Bound bound;
}
alias SolUse=SolutionInfo.UseCase;

// solve lhs = rhs, or lhs ≤ rhs, where var does not occur free in rhs
DExpr solveFor(DExpr lhs,DVar var,DExpr rhs,SolUse usage,ref SolutionInfo info){
	if(lhs==var){
		if(usage.bound) info.bound.setLower();
		return rhs;
	}
	if(auto p=cast(DPlus)lhs){
		auto ow=splitPlusAtVar(lhs,var);
		if(cast(DPlus)ow[1]){
			auto ba=(lhs-rhs).asLinearFunctionIn(var); // TODO: other polynomial equations?
			auto b=ba[0],a=ba[1];
			if(a&&b){
				if(couldBeZero(a)){
					info.needCaseSplit=true;
					if(usage.caseSplit)
						info.caseSplits~=SolutionInfo.CaseSplit(a,-b);
				}
				if(usage.bound){
					info.bound.setLower();
					info.bound.invertIflZ(a);
				}
				return -b/a;
			}
			return null;
		}
		auto r=ow[1].solveFor(var,rhs-ow[0],usage,info); // TODO: withoutSummands
		foreach(ref x;info.caseSplits) x.expression=x.expression+ow[0];
		return r;
	}
	if(auto m=cast(DMult)lhs){
		auto ow=splitMultAtVar(m,var);
		if(cast(DMult)ow[1]) return null; // TODO
		if(couldBeZero(ow[0])){
			info.needCaseSplit=true;
			if(usage.caseSplit)
				info.caseSplits~=SolutionInfo.CaseSplit(ow[0],zero);
		}
		auto r=ow[1].solveFor(var,rhs/ow[0],usage,info);
		foreach(ref x;info.caseSplits) x.expression=x.expression*ow[0];
		if(usage.bound) info.bound.invertIflZ(ow[0]);
		return r;
	}
	if(auto p=cast(DPow)lhs){
		if(p.operands[1]==mone){
			if(couldBeZero(rhs)){ // TODO: is this right? (This is guaranteed never to happen for dirac deltas, so maybe optimize it out for that caller).
				info.needCaseSplit=true;
				if(usage.caseSplit) info.caseSplits~=SolutionInfo.CaseSplit(rhs,one);
			}
			auto r=p.operands[0].solveFor(var,one/rhs,usage,info);
			info.caseSplits=info.caseSplits.partition!(x=>x.expression==zero);
			foreach(ref x;info.caseSplits) x.expression=one/x.expression;
			if(usage.bound) info.bound.invertIflZ(-p.operands[0]*rhs);
			return r;
		}/+else if(p.operands[1].isFraction()){
			dw(lhs," ",rhs," ",usage);
			return null; // TODO
		}+/
		return null;
	}
	return null;
}

DExpr solveFor(DExpr lhs,DVar var){
	// TODO: this can return zero when there is actually no solution.
	// (this is not a problem for the current caller.)
	SolutionInfo info;
	SolUse usage={caseSplit:true,bound:false};
	if(auto s=lhs.solveFor(var,zero,usage,info)){
		s=s.simplify(one);
		DExpr[] prefix,suffix;
		foreach(i,ref x;info.caseSplits){
			if(!i) prefix~=dNeqZ(x.constraint).simplify(one);
			else prefix~=(prefix[i-1]*dNeqZ(x.constraint)).simplify(one);
		}
		foreach_reverse(i,ref x;info.caseSplits){
			if(i+1==info.caseSplits.length) suffix~=dNeqZ(x.constraint).simplify(one);
			else suffix~=(suffix[i+1]*dNeqZ(x.constraint)).simplify(one);
		}
		auto constraints=(prefix.length?prefix[$-1]:one);
		constraints=constraints.simplify(one);
		if(constraints==one) return s;
		auto r=constraints==zero?zero:constraints*s;
		foreach(i,ref x;info.caseSplits){
			auto curConstr=(i?prefix[i-1]:one)*(i+1<suffix.length?suffix[i+1]:one);
			auto psol=solveFor(x.expression,var);
			if(!psol) return null;
			r=r+curConstr*dEqZ(x.constraint)*psol;
		}
		return r;
	}
	return null;
}


std.typecons.Tuple!(DIvr.Type,"type",DExpr,"e") negateDIvr(DIvr.Type type,DExpr e){
	final switch(type) with(DIvr.Type){
		case lZ: return typeof(return)(leZ,-e); // currently probably unreachable
		case leZ: return typeof(return)(lZ,-e);
		case eqZ: return typeof(return)(neqZ,e);
		case neqZ: return typeof(return)(eqZ,e);
	}
}
DExpr negateDIvr(DIvr ivr){
	return dIvr(negateDIvr(ivr.type,ivr.e).expand);
}

T without(T,DExpr)(T a,DExpr b){
	T r;
	foreach(x;a) if(x != b) r.insert(x);
	return r;
}

struct DExprHoles(T){
	DExpr expr;
	static struct Hole{
		DVar var;
		T expr;
	}
	Hole[] holes; // TODO: avoid allocation if only a few holes
}

DExprHoles!T getHoles(alias filter,T=DExpr)(DExpr e){
	DExprHoles!T r;
	DExpr doIt(DExpr e){
		// TODO: add a general visitor with rewrite capabilities
		if(auto expr=filter(e)){
			auto var=dVar("(hole)"~to!string(r.holes.length));
			r.holes~=DExprHoles!T.Hole(var,expr);
			return var;
		}
		if(auto m=cast(DMult)e){
			DExprSet r;
			foreach(f;m.factors) DMult.insert(r,doIt(f));
			return dMult(r);
		}
		if(auto p=cast(DPlus)e){
			DExprSet r;
			foreach(f;p.summands) DPlus.insert(r,doIt(f));
			return dPlus(r);
		}
		if(auto p=cast(DPow)e)
			return doIt(p.operands[0])^^doIt(p.operands[1]);
		if(auto gi=cast(DGaussInt)e)
			return dGaussInt(doIt(gi.x));
		if(auto gi=cast(DGaussIntInv)e)
			return dGaussIntInv(doIt(gi.x));
		if(auto lg=cast(DLog)e)
			return dLog(doIt(lg.e));
		if(auto dl=cast(DDelta)e)
			return dDelta(doIt(dl.var));
		if(auto dl=cast(DDiscDelta)e)
			return dDiscDelta(doIt(dl.e),doIt(dl.var));
		if(auto ivr=cast(DIvr)e)
			return dIvr(ivr.type,doIt(ivr.e));
		/+if(auto sn=cast(DSin)e)
			return dSin(doIt(sn.e));
		if(auto fl=cast(DFloor)e)
			return dFloor(doIt(fl.e));
		if(auto cl=cast(DCeil)e)
			return dCeil(doIt(cl.e));
		if(auto bo=cast(DBitOr)e){
			DExprSet r;
			foreach(f;bo.operands) DBitOr.insert(r,doIt(f));
			return dBitOr(r);
		}
		if(auto bx=cast(DBitXor)e){
			DExprSet r;
			foreach(f;bx.operands) DBitXor.insert(r,doIt(f));
			return dBitXor(r);
		}
		if(auto ba=cast(DBitAnd)e){
			DExprSet r;
			foreach(f;ba.operands) DBitAnd.insert(r,doIt(f));
			return dBitAnd(r);
		}+/
		if(auto tpl=cast(DTuple)e)
			return dTuple(tpl.values.map!doIt.array);
		/+if(auto rcd=cast(DRecord)e){
			DExpr[string] nvalues;
			foreach(k,v;rcd.values) nvalues[k]=doIt(v);
			return dRecord(nvalues);
		}
		if(auto ab=cast(DAbs)e)
			return dAbs(doIt(ab.e));
		if(auto idx=cast(DIndex)e)
			return dIndex(doIt(idx.e),doIt(idx.i));
		if(auto iu=cast(DIUpdate)e)
			return dIUpdate(doIt(iu.e),doIt(iu.i),doIt(iu.n));
		if(auto slc=cast(DSlice)e)
			return dSlice(doIt(e.e),doIt(e.l),doIt(e.r));
		if(auto ru=cast(DRUpdate)e)
			return dRUpdate(doIt(e.e),e.f,doIt(e.n));
		if(auto fld=cast(DField)e)
			return dField(doIt(fld.e),fld.f);+/
		if(auto val=cast(DVal)e)
			return dVal(doIt(val.e));
		/+if(auto ap=cast(DApply)e)
			return dApply(doIt(ap.fun),doIt(ap.arg));
		if(auto ar=cast(DArray)e)
			return dArray(doIt(ar.length),ar.entries);
		if(auto ce=cast(DCat)e)
		    return dCat(operands.map!doIt.array)+/
		return e;
	}
	r.expr=doIt(e);
	return r;
}

// TODO: keep ivrs and nonIvrs separate in DMult
DExpr[2] splitIvrs(DExpr e){
	DExpr ivrs=one;
	DExpr nonIvrs=one;
	foreach(f;e.factors){
		if(cast(DIvr)f) ivrs=ivrs*f;
		else nonIvrs=nonIvrs*f;
	}
	return [ivrs,nonIvrs];
}

DExpr factorDIvr(alias wrap)(DExpr e){
	if(!e.hasAny!DIvr(false)) return null;
	if(auto ivr=cast(DIvr)e) return ivr*wrap(one)+negateDIvr(ivr)*wrap(zero);
	if(e.factors.all!(x=>!!cast(DIvr)x)) return factorDIvrProduct!wrap(e);
	auto h=getHoles!(x=>x.factors.any!(y=>!!cast(DIvr)y)?x:null)(e);
	if(!h.holes.length) return null;
	DExpr doIt(DExpr facts,DExpr cur,size_t i){
		facts=facts.simplify(one);
		if(facts==zero) return zero;
		if(i==h.holes.length) return facts*wrap(cur);
		auto var=h.holes[i].var,expr=h.holes[i].expr;
		auto ivrsNonIvrs=splitIvrs(expr), ivrs=ivrsNonIvrs[0], nonIvrs=ivrsNonIvrs[1];
		ivrs=ivrs.simplify(one), nonIvrs=nonIvrs.simplify(one);
		auto neg=negateDIvrProduct(ivrs).simplify(one);
		auto pos=ivrs.simplify(one);
		return doIt(facts*pos,cur.substitute(var,nonIvrs),i+1) +
			doIt(facts*neg,cur.substitute(var,zero),i+1);
	}
	auto r=doIt(one,h.expr,0);
	return r;
}

DExpr factorDIvrProduct(alias wrap)(DExpr e){
	auto ivrsNonIvrs=splitIvrs(e), ivrs=ivrsNonIvrs[0], nonIvrs=ivrsNonIvrs[1];
	ivrs=ivrs.simplify(one), nonIvrs=nonIvrs.simplify(one);
	return factorDIvrProduct!wrap(ivrs,nonIvrs);
}

DExpr negateDIvrProduct(DExpr ivrs)in{
	assert(ivrs.factors.all!(x=>!!cast(DIvr)x));
}body{
	auto r=zero;
	auto cur=one;
	foreach(f;ivrs.factors){
		auto ivr=cast(DIvr)f;
		assert(!!ivr);
		r=r+cur*negateDIvr(ivr);
		cur=cur*ivr;
	}
	return r;
}

DExpr factorDIvrProduct(alias wrap)(DExpr ivrs,DExpr nonIvrs)in{
	assert(ivrs.factors.all!(x=>!!cast(DIvr)x));
}body{
	auto tt=wrap(nonIvrs),ff=wrap(zero);
	auto r=ivrs*tt;
	return ivrs*tt+negateDIvrProduct(ivrs)*ff;
}


class DIvr: DExpr{ // iverson brackets
	enum Type{ // TODO: remove redundancy?
		eqZ,
		neqZ,
		lZ,
		leZ,
	}
	Type type;
	alias subExprs=Seq!(type,e);
	@conditionallyEven!((Type t,DExpr e)=>util.among(t,DIvr.Type.eqZ,DIvr.Type.neqZ)) DExpr e;
	mixin Visitors;

	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp)
			return text("(ite (",type==Type.eqZ?"=":type==Type.neqZ?"not (=":type==Type.lZ?"<":type==Type.leZ?"<=":""," ",e.toStringImpl(formatting,Precedence.none,binders)," 0)",type==Type.neqZ?")":""," 1 0)");
		with(Type){
			if(formatting==Format.gnuplot){
				auto es=e.toStringImpl(formatting,Precedence.none,binders);
				final switch(type){
				case eqZ: return text("(",es,"==0)");
				case neqZ: return text("(",es,"!=0)");
				case lZ: assert(0);
				case leZ: return text("(",es,"<=0)");
				}
			}else if(formatting==Format.mathematica){
				auto es=e.toStringImpl(formatting,Precedence.none,binders);
				final switch(type){
				case eqZ: return text("Boole[",es,"==0]");
				case neqZ: return text("Boole[",es,"!=0]");
				case lZ: assert(0);
				case leZ: return text("Boole[",es,"<=0]");
				}
			}else if(formatting==Format.maple){
				//return "piecewise("~e.toStringImpl(formatting,Precedence.none)~(type==eqZ?"=":type==neqZ?"<>":type==lZ?"<":"<=")~"0,1,0)";
				auto es=e.toStringImpl(formatting,Precedence.none,binders);
				final switch(type){
					//case eqZ: return text("piecewise(",es,"=0,1,0)");
					case eqZ: return text("piecewise(abs(",es,")<pZ,1,0)");
					//case neqZ: return text("piecewise(",es,"<>0,1,0)");
					case neqZ: return text("piecewise(abs(",es,")>pZ,1,0)");
					case lZ: assert(0);
					//case leZ: return text("piecewise(",es,"<=0,1,0)");
					case leZ: return text("piecewise(",es,"<pZ,1,0)");
				}
			}else if(formatting==Format.python){
				auto es=e.toStringImpl(formatting,Precedence.none,binders);
				string cmp="";
				final switch(type){
					case eqZ:  return text("equal(",es,",0)");
					case neqZ: return text("not_equal(",es,",0)");
					case lZ: return cmp=text("less(",es,",0)");
					case leZ: return cmp=text("less_equal(",es,",0)");
				}
			}else if(formatting==Format.sympy){
				auto es=e.toStringImpl(formatting,Precedence.none,binders);
				final switch(type){
					case eqZ: return text("Piecewise((1,And(",es,">-pZ,",es,"<pZ)),(0,1))");
					case neqZ: return text("Piecewise((1,Or(",es,"<-pZ,",es,">pZ)),(0,1))");
					case lZ: assert(0);
					case leZ: return text("Piecewise((1,",es,"<pZ),(1,0))");
				}
			}else if(formatting==Format.matlab){
				return "("~e.toStringImpl(formatting,Precedence.none,binders)~(type==eqZ?"==":type==neqZ?"!=":type==lZ?"<":"<=")~"0)";
			}else{
				return "["~e.toStringImpl(formatting,Precedence.none,binders)~(type==eqZ?"=":type==neqZ?"≠":type==lZ?"<":"≤")~"0]";
			}
		}
	}

	static DExpr staticSimplify(Type type,DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne != e) return dIvr(type,ne).simplify(facts);
		if(auto r=cancelFractions!false(e,type)) return r.simplify(facts);
		// TODO: better decision procedures
		if(type==Type.eqZ){
			if(!couldBeZero(e)) return zero;
			if(auto eivr=cast(DIvr)e) return negateDIvr(eivr).simplify(facts);
		}
		if(type==Type.neqZ){
			if(!couldBeZero(e)) return one;
			if(mustBeZeroOrOne(e)) return e;
		}
		if(type==Type.leZ){
			if(mustBeLessOrEqualZero(e)) return one;
			if(mustBeLessThanZero((-e).simplify(facts))) return zero;
			if(mustBeLessOrEqualZero((-e).simplify(facts))) return dIvr(Type.eqZ,e).simplify(facts);
		}
		with(Type) if(type==eqZ||type==neqZ){ // TODO: figure out why this causes non-termination in mult_uniform_test
			if(auto p=cast(DPow)e){
				auto isZ=dIvr(lZ,-p.operands[1])*dIvr(eqZ,p.operands[0]);
				return (type==eqZ?isZ:dIvr(eqZ,isZ)).simplify(facts);
			}
		}
		if(auto c=cast(Dℚ)e){
			DExpr x(bool b){ return b?one:zero; }
			final switch(type) with(Type){
			case eqZ: return x(c.c==0);
			case neqZ: return x(c.c!=0);
			case lZ: return x(c.c<0);
			case leZ: return x(c.c<=0);
			}
		}
		if(auto f=cast(DFloat)e){
			// TODO: ok?
			DExpr y(bool b){ return b?one:zero; }
			final switch(type) with(Type){
			case eqZ: return y(approxEqual(f.c,0));
			case neqZ: return y(!approxEqual(f.c,0));
			case lZ: return y(f.c<=0&&!approxEqual(f.c,0));
			case leZ: return y(f.c<=0||approxEqual(f.c,0));
			}
		}
		if(type==Type.lZ) return (dIvr(Type.leZ,e)*dIvr(Type.neqZ,e)).simplify(facts);
		if(type==Type.eqZ||type==Type.neqZ){
			auto f=e.getFractionalFactor();
			if(f!=one && f!=zero && f!=mone) return dIvr(type,e/f).simplify(facts);
		}
		// TODO: make these check faster (also: less convoluted)
		auto neg=negateDIvr(type,e);
		neg.e=neg.e.simplify(facts);
		foreach(f;facts.factors){
			if(auto ivr=cast(DIvr)f){
				// TODO: more elaborate implication checks
				if(ivr.type==type){
					if(ivr.e==e) return one;
					if(ivr.type==Type.leZ){
						if(e.mustBeAtMost(ivr.e))
							return one;
					}
				}
				import util: among;
				if(neg.type==ivr.type && (neg.e==ivr.e||
					type.among(Type.eqZ,Type.neqZ)&&(-neg.e).simplify(facts)==ivr.e))
					return zero; // TODO: ditto
				if(ivr.type==Type.leZ){
					if(type==Type.leZ){
						assert(neg.type==type.lZ);
						if(neg.e==ivr.e) assert(neg.e.mustBeAtMost(ivr.e),text(neg.e));
						if(neg.e.mustBeAtMost(ivr.e)) return dEqZ(e).simplify(facts);
					}else if(type==Type.eqZ||type==Type.neqZ){
						if(e.mustBeLessThan(ivr.e)||(-e).mustBeLessThan(ivr.e))
							return type==Type.eqZ?zero:one;
					}
				}
			}
		}
		if(e.hasFreeVars())
			if(auto fct=factorDIvr!(e=>dIvr(type,e))(e))
				return fct.simplify(facts);
		if(type==Type.leZ){
			DExprSet nf;
			foreach(f;e.factors){
				if(cast(DMult)e?
				   dLtZ(f).simplify(facts)==zero :
				   mustBeLessOrEqualZero((-f).simplify(facts))
				){
					DMult.insert(nf,dNeqZ(f));
					continue;
				}
				if(auto p=cast(DPow)f){
					if(auto q=cast(Dℚ)p.operands[1]){
						assert(q.c.den==1 && q.c.num&1);
						DMult.insert(nf,p.operands[0]);
						continue;
					}
					if(p.operands[1].getFractionalFactor().c<0){
						DMult.insert(nf, p.operands[0]^^(-p.operands[1]));
						continue;
					}
				}
				nf.insert(f);
			}
			auto ne2=dMult(nf).simplify(facts);
			if(ne2!=e) return dIvr(type,ne2).simplify(facts);
		}else if(util.among(type,Type.eqZ,Type.neqZ)){
			if(auto m=cast(DMult)e){
				DExprSet nf;
				foreach(f;m.factors) DMult.insert(nf,dNeqZ(f));
				auto ne2=dMult(nf).simplify(facts);
				if(ne2!=e) return dIvr(type,ne2).simplify(facts);
			}else if(auto p=cast(DPlus)e){
				bool allNonNegative=true;
				bool allNonPositive=true;
				bool onlyNegativeFractions=true;
				bool onlyPositiveFractions=true;
				bool onlyOne=true;
				foreach(s;p.summands){
					allNonNegative &= mustBeLessOrEqualZero((-s).simplify(facts));
					allNonPositive &= mustBeLessOrEqualZero(s);
					auto f=s.getFractionalFactor().simplify(facts);
					if(f!=one) onlyOne=false;
					if(!mustBeLessThanZero(f))
						onlyNegativeFractions=false;
					if(!mustBeLessThanZero((-f).simplify(facts)))
						onlyPositiveFractions=false;
				}
				if(allNonNegative&&allNonPositive) return dIvr(type,zero).simplify(facts);
				if(!onlyOne&&(onlyPositiveFractions||onlyNegativeFractions)&&(allNonNegative||allNonPositive)){
					DExprSet ns;
					foreach(s;p.summands){
						if(allNonPositive) s=(-s).simplify(facts);
						auto f=s.getFractionalFactor().simplify(facts);
						if(f==zero) continue;
						ns.insert((s/f).simplify(facts));
					}
					DExprSet nf;
					foreach(s;ns) DMult.insert(nf,dIvr(Type.eqZ,s));
					auto isZero=dMult(nf).simplify(facts);
					if(type==Type.eqZ){
						return isZero;
					}else{
						assert(type==Type.neqZ);
						return dIvr(Type.eqZ,isZero).simplify(facts);
					}
				}
			}
		}
		// TODO: eliminate common denominators in a sum?
		if(auto l=cast(DLog)e)
			return dIvr(type,l.e-one).simplify(facts);
		auto q=e.getFractionalFactor();
		if(q.c<0){
			if(e.hasFactor(q)){
				if(auto l=cast(DLog)(e.withoutFactor(q)))
					return dIvr(type,one-l.e).simplify(facts);
			}
		}
		if(auto var=e.getCanonicalFreeVar()){
			/+bool onlyOne=true;
			foreach(v;e.freeVars) if(v!=var){ onlyOne=false; break; }+/
			if(type==Type.eqZ){
				SolutionInfo info;
				SolUse usage={caseSplit:false,bound:false};
				auto sol=e.solveFor(var,zero,usage,info);
				if(sol&&!info.needCaseSplit){
					if(facts.substitute(var,sol).simplify(one)==zero)
						return zero;
					/+if(onlyOne){
						auto nexp=(sol-var).simplify(facts);
						auto mnexp=(-nexp).simplify(facts);
						if(nexp!=e&&mnexp!=e) return dIvr(Type.eqZ,nexp).simplify(facts);
					}+/
				}
			}
			/+if(onlyOne){
				auto oivr=cast(DIvr)dIvr(type,e);
				static DExprSet active;
				if(e !in active){
					active.insert(e);
					auto r=linearizeConstraint!DIvr(oivr,var).simplify(facts);
					active.remove(e);
					if(!cast(DIvr)r||(cast(DIvr)r).e!=e)
						return r;
				}
			}+/
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(type,e,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DIvr;

DExpr dBounded(string what)(DExpr e,DExpr lo,DExpr hi) if(what=="[]"){
	return dLe(lo,e)*dLe(e,hi);
}

DExpr dBounded(string what)(DExpr e,DExpr lo,DExpr hi) if(what=="[)"){
	return dLe(lo,e)*dLt(e,hi);
}

DExpr dBounded(string what)(DExpr e,DExpr lo,DExpr hi) if(what=="()"){
	return dLt(lo,e)*dLt(e,hi);
}

bool isMoreCanonicalThan(DExpr e1,DExpr e2){
	return e1.toHash()<e2.toHash(); // TODO: find something more stable
}

DVar getCanonicalVar(T)(T vars){
	DVar r=null;
	bool isMoreCanonicalThan(DVar a,DVar b){
		if(b is null) return true;
		return a.toString()<b.toString();
	}
	foreach(v;vars)
		if(isMoreCanonicalThan(v,r)) r=v;
	return r;
}

DVar getCanonicalFreeVar(DExpr e){
	return getCanonicalVar(e.freeVars);
}

bool isContinuousMeasure(DExpr expr){
	if(!expr.hasFreeVars()) return true;
	if(auto d=cast(DDistApply)expr) return false;
	if(auto d=cast(DDelta)expr) return false;
	if(auto d=cast(DDiscDelta)expr) return false;
	if(cast(DIvr)expr||cast(DVar)expr||cast(DPow)expr||cast(DLog)expr||cast(DSin)expr||cast(DFloor)expr||cast(DCeil)expr||cast(DGaussInt)expr||cast(DGaussIntInv)expr||cast(DAbs)expr)
		return true;
	if(auto p=cast(DPlus)expr){
		foreach(s;p.summands)
			if(!isContinuousMeasure(s))
				return false;
		return true;
	}
	if(auto m=cast(DMult)expr){
		foreach(f;m.factors)
			if(!isContinuousMeasure(f))
				return false;
		return true;
	}
	if(auto i=cast(DInt)expr) return isContinuousMeasure(i.expr);
	if(auto c=cast(DMCase)expr){
		if(!isContinuousMeasure(c.val)) return false;
		return isContinuousMeasure(c.err);
	}
	return false;
}

bool isContinuousMeasureIn(DExpr expr,DVar var){ // TODO: get rid of code duplication.
	if(!expr.hasFreeVar(var)) return true;
	if(auto d=cast(DDistApply)expr) return !d.arg.hasFreeVar(var);
	if(auto d=cast(DDelta)expr) return !d.var.hasFreeVar(var);
	if(auto d=cast(DDiscDelta)expr) return !d.var.hasFreeVar(var);
	if(cast(DIvr)expr||cast(DVar)expr||cast(DPow)expr||cast(DLog)expr||cast(DSin)expr||cast(DFloor)expr||cast(DCeil)expr||cast(DGaussInt)expr||cast(DGaussIntInv)expr||cast(DAbs)expr)
		return true;
	if(auto p=cast(DPlus)expr){
		foreach(s;p.summands)
			if(!isContinuousMeasureIn(s,var))
				return false;
		return true;
	}
	if(auto m=cast(DMult)expr){
		foreach(f;m.factors)
			if(!isContinuousMeasureIn(f,var))
				return false;
		return true;
	}
	if(auto i=cast(DInt)expr) return isContinuousMeasureIn(i.expr,var.incDeBruijnVar(1,0));
	if(auto c=cast(DMCase)expr){
		if(!isContinuousMeasureIn(c.val,var.incDeBruijnVar(1,0))) return false;
		return isContinuousMeasureIn(c.err,var);
	}
	return false;
}

class DDelta: DExpr{ // Dirac delta, for ℝ
	@even DExpr var;
	alias subExprs=Seq!var;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.mathematica){
			return text("DiracDelta[",var.toStringImpl(formatting,Precedence.none,binders),"]");
		}else if(formatting==Format.maple){
			return text("Dirac(",var.toStringImpl(formatting,Precedence.none,binders),")");
			/+auto vars=var.toStringImpl(formatting,Precedence.none);
			return text("piecewise(abs(",vars,")<lZ,1/(2*(",vars,")))");+/
		}else if(formatting==Format.python){
			return text("delta(",var.toStringImpl(formatting,Precedence.none,binders),")");
		}else if(formatting==Format.sympy){
			return text("DiracDelta(",var.toStringImpl(formatting,Precedence.none,binders),")");
		}else if(formatting==Format.lisp){
			return text("(dirac ",var.toStringImpl(formatting,Precedence.none,binders),")");
		}else{
			DExprSet vals,vars;
			foreach(s;var.summands){
				if(!s.hasFreeVars()) vals.insert(s);
				else vars.insert(s);
			}
			auto e1=dPlus(vals), e2=dPlus(vars);
			if(e2.hasFactor(mone)) e2=e2.withoutFactor(mone);
			else e1=e1.negateSummands();
			return "δ("~e1.toStringImpl(formatting,Precedence.none,binders)~")["~e2.toStringImpl(formatting,Precedence.none,binders)~"]";
		}
	}

	mixin Visitors;

	static DExpr staticSimplify(DExpr var,DExpr facts=one){
		auto nvar=var.simplify(one); // cannot use all facts! (might remove a free variable)
		if(nvar != var) return dDelta(nvar).simplify(facts);
		if(auto r=cancelFractions!true(nvar)) return r.simplify(facts);
		if(auto fct=factorDIvr!(var=>dDelta(var))(nvar)) return fct.simplify(facts);
		if(dEqZ(nvar).simplify(facts)==zero)
			return zero;
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(var,facts);
		return r?r:this;
	}

	static DExpr performSubstitution(DDelta d,DExpr expr){
		auto var=db1;
		SolutionInfo info;
		SolUse usage={caseSplit:false,bound:false};
		if(auto s=d.var.solveFor(var,zero,usage,info)){
			s=s.incDeBruijnVar(-1,0).simplify(one);
			if(info.needCaseSplit) return null;
			auto r=unbind(expr,s)/dAbs(dDiff(var,d.var,s));
			return r.simplify(one);
		}
		return null;
	}
}
mixin FactoryFunction!DDelta;

class DDiscDelta: DExpr{ // point mass for discrete data types
	DExpr e,var;
	alias subExprs=Seq!(e,var);
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.mathematica)
			return text("DiracDelta[",(e-var).toStringImpl(formatting,Precedence.none,binders),"]");
		if(formatting==Format.lisp) // TODO: better name
			return text("(dirac2 ",var.toStringImpl(formatting,Precedence.subscript,binders),e.toStringImpl(formatting,Precedence.none,binders),")");
		// TODO: encoding for other CAS?
		auto isTpl=!!cast(DTuple)e;
		return "δ("~e.toStringImpl(formatting,Precedence.none,binders)[isTpl..$-isTpl]~")["~var.toStringImpl(formatting,Precedence.subscript,binders)~"]";
	}

	mixin Visitors;

	static DExpr constructHook(DExpr e,DExpr var){
		static bool isNumeric(DExpr e){ // TODO: merge dDelta and dDiscDelta completely, such that type information is irrelevant
			return cast(Dℚ)e||cast(DPlus)e||cast(DMult)e||cast(DPow)e||cast(DIvr)e||cast(DFloor)e||cast(DCeil)e||cast(DLog)e;
		}
		if(isNumeric(e)||isNumeric(var)) return dDelta(var-e);
		return null;
	}
	static DExpr staticSimplify(DExpr e,DExpr var,DExpr facts=one){
		// the problem is that there might be a relation between e.g. multiple tuple entries, and we are not
		// allowed to introduce free variables from var into e, or remove free variables from var.
		// TODO: filter more precisely
		auto ne=e.simplify(one), nvar=var.simplify(one);
		if(ne != e || nvar != var) return dDiscDelta(ne,nvar).simplify(facts); // (might be rewritten to normal delta)
		if(auto fct=factorDIvr!(e=>dDiscDelta(e,nvar))(ne)) return fct.simplify(facts);
		if(auto fct=factorDIvr!(var=>dDiscDelta(ne,var))(nvar)) return fct.simplify(facts);
		//if(dEq(var,e).simplify(facts) is zero) return zero; // a simplification like this might be possible (but at the moment we can compare only real numbers
		if(auto vtpl=cast(DTuple)var){ // δ(1,2,3,...)[(x,y,z,...)].
			if(auto etpl=cast(DTuple)e){
				if(vtpl.values.length==etpl.values.length){
					DExprSet factors;
					foreach(i;0..vtpl.values.length)
						DMult.insert(factors,dDiscDelta(etpl[i],vtpl[i]));
					return dMult(factors).simplify(facts);
				}
			}
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,var,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DDiscDelta;

DExpr[2] splitPlusAtVar(DExpr e,DVar var){
	DExprSet outside, within;
	//writeln("splitting: ",e,"\nat: ",var);
	//scope(exit) writeln("res: ",dPlus(outside),", ",dPlus(within));
	DExpr[2] handlePow(DPow p){
		DExpr[2] fail=[null,null];
		auto a=cast(DPlus)p.operands[0];
		auto c=p.operands[1].isInteger();
		if(!a||!c||c.c<=0) return fail;
		assert(c.c.den==1);
		auto ow=splitPlusAtVar(a,var);
		if(ow[0]==zero || ow[1]==zero) return fail;
		DExpr outside=ow[0]^^c;
		DExprSet within;
		for(ℤ i=0;i<c.c.num;i++)
			DPlus.insert(within,nCr(c.c.num,i)*ow[0]^^i*ow[1]^^(c.c.num-i));
		return [outside,dPlus(within)];
	}
 Lsum: foreach(s;e.summands){
		if(s.hasFreeVar(var)){
			auto rest=s;
			DExpr[2][] toExpand;
			foreach(f;s.factors){
				if(auto p=cast(DPow)f){
					auto ow=handlePow(p);
					if(ow[0]){
						assert(!!ow[1]);
						rest=rest.withoutFactor(f);
						toExpand~=ow;
					}
				}
			}
			void insertExpansion(int i,DExpr cur,bool isWithin){
				if(i==toExpand.length){
					//writeln("inserting: ",cur);
					DPlus.insert(isWithin?within:outside,cur);
					return;
				}
				insertExpansion(i+1,cur*toExpand[i][0],isWithin);
				insertExpansion(i+1,cur*toExpand[i][1],true);
			}
			if(rest.hasFreeVar(var)) DPlus.insert(within,s);
			else insertExpansion(0,rest,false);
		}else DPlus.insert(outside,s);
	}
	return [dPlus(outside),dPlus(within)];
}

DExpr[2] splitMultAtVar(DExpr e,DVar var){
	DExprSet within;
	DExprSet outside;
	foreach(f;e.factors){
		if(f.hasFreeVar(var)){
			if(auto p=cast(DPow)f){
				if(p.operands[0].hasFreeVar(var)||dLeZ(p.operands[0]).simplify(one)!=zero){
					DMult.insert(within,f);
				}else{
					auto ow=splitPlusAtVar(p.operands[1],var);
					DMult.insert(outside,p.operands[0]^^ow[0]);
					DMult.insert(within,p.operands[0]^^ow[1]);
				}
			}else DMult.insert(within,f);
		}else DMult.insert(outside,f);
	}
	if(!outside.length) return [one,e];
	if(!within.length) return [e,one];
	return [dMult(outside),dMult(within)];
}

DExpr dMin(DExpr a,DExpr b){
	return dLt(a,b)*a+dLe(b,a)*b;
}
DExpr dMax(DExpr a,DExpr b){
	return dLt(b,a)*a+dLe(a,b)*b;
}

DExpr dOpt(string which)(DExprSet exprs)if(which=="min"||which=="max")in{
	assert(exprs.length);
}do{
	DExprSet considered;
	DExprSet unconsidered=exprs.dup;
	DExprSet summands;
	foreach(expr;exprs){
		DExprSet factors;
		factors.insert(expr);
		foreach(cexpr;considered){
			static if(which=="min"){
				factors.insert(dLt(expr,cexpr));
			}else{
				factors.insert(dGt(expr,cexpr));
			}
		}
		foreach(cexpr;unconsidered){
			if(cexpr==expr) continue;
			static if(which=="min"){
				factors.insert(dLe(expr,cexpr));
			}else{
				factors.insert(dGe(expr,cexpr));
			}
		}
		summands.insert(dMult(factors));
		considered.insert(expr);
		unconsidered.remove(expr);
	}
	return dPlus(summands);
}

DExpr dMin(DExprSet exprs)in{
	assert(exprs.length);
}do{
	return dOpt!"min"(exprs);
}

DExpr dMax(DExprSet exprs)in{
	assert(exprs.length);
}do{
	return dOpt!"max"(exprs);
}

version(INTEGRATION_STATS){
	int integrations=0;
	int successfulIntegrations=0;
	static ~this(){
		writeln(integrations," / ",successfulIntegrations);
	}
}

DExpr[2] splitIntegrableFactor(DExpr e){
	DExpr integrable=one;
	DExpr nonIntegrable=one;
	foreach(f;e.factors){
		if(auto p=cast(DPow)f) if(p.operands[0]==dE){ // TODO: check polynomial degree
			integrable=integrable*f; // TODO: use DExprSet
			continue;
		}
		nonIntegrable=nonIntegrable*f;
	}
	return [integrable,nonIntegrable];
}

/+import std.datetime;
StopWatch sw;
static ~this(){
	writeln(sw.peek().to!("msecs",double));
}+/

static DExpr unbind(DExpr expr, DExpr nexpr){
	return expr.substitute(db1,nexpr.incDeBruijnVar(1,0)).incDeBruijnVar(-1,0);
}

import integration;
class DInt: DOp{
	@binder DExpr expr;
	alias subExprs=Seq!expr;
	final DExpr getExpr(DExpr e){ return unbind(expr,e); }
	override @property Precedence precedence(){ return Precedence.intg; }
	override @property string symbol(Format formatting,int binders){ return "∫"; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.mathematica){
			return text("Integrate[",expr.toStringImpl(formatting,Precedence.none,binders+1),",{",DDeBruijnVar.displayName(1,formatting,binders+1),",-Infinity,Infinity}]");
		}else if(formatting==Format.maple){
			return text("int(",expr.toStringImpl(formatting,Precedence.none,binders+1),",",DDeBruijnVar.displayName(1,formatting,binders+1),"=-infinity..infinity)");
		}else if(formatting==Format.python||formatting==Format.sympy){
			return text("integrate(",expr.toStringImpl(formatting,Precedence.none,binders+1),",(",DDeBruijnVar.displayName(1,formatting,binders+1),",-oo,oo))");
		}else if(formatting==Format.gnuplot && !hasFreeVars(this)){
			writeln("warning: replacing integral by 1");
			return "1";
		}else if(formatting==Format.lisp){
			return text("(integrate ",DDeBruijnVar.displayName(1,formatting,binders+1)," ",expr.toStringImpl(formatting,Precedence.none,binders),")");
		}else{
			return addp(prec,symbol(formatting,binders)~"d"~DDeBruijnVar.displayName(1,formatting,binders+1)~expr.toStringImpl(formatting,Precedence.intg,binders+1));
		}
	}

	version(INTEGRAL_STATS){
		static int numIntegrals=0;
		static void[0][DExpr] integrals;
		static ~this(){
			writeln("A: ",numIntegrals);
			writeln("B: ",integrals.length);
		}
	}

	static MapX!(Q!(DExpr,DExpr),DExpr) ssimplifyCache;

	static DExpr staticSimplify(DExpr expr,DExpr facts=one)in{assert(expr&&facts);}body{
		auto nexpr=expr.simplify(facts.incDeBruijnVar(1,0).simplify(one));
		if(expr != nexpr) return dIntSmp(nexpr,facts);
		auto ow=expr.splitMultAtVar(db1);
		ow[0]=ow[0].incDeBruijnVar(-1,0).simplify(facts);
		if(ow[0]==zero) return zero;
		if(ow[0]!=one||ow[1]!=expr) return (ow[0]*dIntSmp(ow[1],facts)).simplify(facts);
		//version(DISABLE_INTEGRATION){
		if(opt.integrationLevel==IntegrationLevel.none)
			return null;
		version(INTEGRAL_STATS){
			numIntegrals++;
			integrals[expr]=[];
		}
		if(auto r=definiteIntegral(expr,facts))
			return r.simplify(facts);
		return null;
	}

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(expr,facts);
		return r?r:this;
	}

	mixin Visitors;
}
mixin FactoryFunction!DInt;

bool hasIntegrals(DExpr e){ return hasAny!DInt(e); }

import summation;
class DSum: DOp{
	@binder DExpr expr;
	alias subExprs=Seq!expr;
	final DExpr getExpr(DExpr e){ return unbind(expr,e); }
	override @property Precedence precedence(){ return Precedence.intg; }
	override @property string symbol(Format formatting,int binders){ return "∑"; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.mathematica){
			return text("Sum[",expr.toStringImpl(formatting,Precedence.none,binders+1),",{",DDeBruijnVar.displayName(1,formatting,binders+1),",-Infinity,Infinity}]");
		}else if(formatting==Format.maple){
			return text("sum(",expr.toStringImpl(formatting,Precedence.none,binders+1),",",DDeBruijnVar.displayName(1,formatting,binders+1),"=-infinity..infinity)"); // TODO: correct?
		}else if(formatting==Format.python||formatting==Format.sympy){
			return text("sum(",expr.toStringImpl(formatting,Precedence.none,binders+1),",(",DDeBruijnVar.displayName(1,formatting,binders+1),",-oo,oo))"); // TODO: correct?
		}else if(formatting==Format.lisp){
			return text("(sum ",DDeBruijnVar.displayName(1,formatting,binders+1)," ",expr.toStringImpl(formatting,Precedence.none,binders+1),")");
		}else{
			return addp(prec,symbol(formatting,binders)~"_"~DDeBruijnVar.displayName(1,formatting,binders+1)~expr.toStringImpl(formatting,precedence,binders+1));
		}
	}
	static MapX!(Q!(DExpr,DExpr),DExpr) ssimplifyCache;
	static DExpr staticSimplifyCache(DExpr expr,DExpr facts=one){
		auto t=q(expr,facts);
		if(t in ssimplifyCache) return ssimplifyCache[t]; // TODO: better solution available?
		auto r=staticSimplify(expr,facts);
		ssimplifyCache[t]=r?r:t[0];
		return r;
	}

	static DExpr staticSimplify(DExpr expr,DExpr facts=one){
		if(opt.integrationLevel==IntegrationLevel.none){
			if(expr==zero) return zero;
			return null;
		}
		auto nexpr=expr.simplify((facts.incDeBruijnVar(1,0)*dIsℤ(db1)).simplify(one));
		if(nexpr != expr) return dSum(nexpr).simplify(facts);
		auto ow=expr.splitMultAtVar(db1);
		ow[0]=ow[0].incDeBruijnVar(-1,0).simplify(facts);
		if(ow[0]==zero) return zero;
		if(ow[0]!=one||ow[1]!=expr) return (ow[0]*dSumSmp(ow[1],facts)).simplify(facts);
		if(opt.integrationLevel!=IntegrationLevel.deltas){
			if(auto r=computeSum(expr,facts))
				return r.simplify(facts);
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(expr,facts); // TODO: staticSimplify(expr) is significantly faster, fix
		return r?r:this;
	}
	mixin Visitors;
}
mixin FactoryFunction!DSum;

import limits;
class DLim: DOp{
	DExpr e;
	@binder DExpr x;
	alias subExprs=Seq!(e,x);
	override @property string symbol(Format formatting,int binders){ return text("lim[",DDeBruijnVar.displayName(1,formatting,binders+1)," → ",e.toStringImpl(formatting,Precedence.none,binders+1),"]"); }
	override Precedence precedence(){ return Precedence.lim; } // TODO: ok?
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp)
			return text("(limit (-> ",DDeBruijnVar.displayName(1,formatting,binders+1),e.toStringImpl(formatting,Precedence.none,binders+1),") ",x.toStringImpl(formatting,Precedence.none,binders+1),")");
		return addp(prec,symbol(formatting,binders)~x.toStringImpl(formatting,precedence,binders+1));
	}

	static DExpr staticSimplify(DExpr e,DExpr x,DExpr facts=one){
		auto ne=e.simplify(facts), nx=x.simplify(facts.incDeBruijnVar(1,0).simplify(one));
		if(ne != e || nx != x) return dLim(ne,nx).simplify(facts);
		if(auto r=getLimit(db1,e,x,facts))
			return r.incDeBruijnVar(-1,0);
		return null;
	}

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,x);
		return r?r:this;
	}

	mixin Visitors;
}
mixin FactoryFunction!DLim;

bool hasLimits(DExpr e){ return hasAny!DLim(e); }

import differentiation;
class DDiff: DOp{
	@binder DExpr e;
	DExpr x;
	alias subExprs=Seq!(e,x);
	override @property string symbol(Format formatting,int binders){ return "d/d"~DDeBruijnVar.displayName(1,formatting,binders); }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp)
			return text("(differentiate ",DDeBruijnVar.displayName(1,formatting,binders+1)," ",e.toStringImpl(formatting,Precedence.none,binders+1)," ",x.toStringImpl(formatting,Precedence.none,binders),")");
		return addp(prec,symbol(formatting,binders+1)~"["~e.toStringImpl(formatting,Precedence.none,binders+1)~"]("~x.toStringImpl(formatting,Precedence.none,binders)~")");
	}

	static DExpr constructHook(DExpr e,DExpr x){
		return staticSimplify(e,x);
	}

	static DExpr staticSimplify(DExpr e,DExpr x,DExpr facts=one){
		auto ne=e.simplify(facts.incDeBruijnVar(1,0).simplify(one));
		if(auto r=differentiate(db1,ne))
			return unbind(r,x).simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,x);
		return r?r:this;
	}
	mixin Visitors;
}
mixin FactoryFunction!DDiff;

class DAbs: DOp{
	DExpr e;
	alias subExprs=Seq!e;
	override @property string symbol(Format formatting,int binders){ return "|"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){ // TODO: matlab, maple
		if(formatting==Format.lisp) return text("(abs ",e.toStringImpl(formatting,prec,binders),")");
		return "|"~e.toStringImpl(formatting,Precedence.none,binders)~"|";
	}
	mixin Visitors;
	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		e=e.simplify(facts);
		if(auto q=cast(Dℚ)e)
			return dℚ(abs(q.c));
		if(cast(DE)e) return e;
		if(cast(DΠ)e) return e;
		if(auto m=cast(DMult)e){ // TODO: does this preclude some DMult-optimizations and should therefore be done differently?
			DExprSet r;
			foreach(f;m.factors)
				DMult.insert(r,dAbs(f));
			return dMult(r);
		}
		return -e*dLtZ(e)+e*dGeZ(e); // TODO: just use this expression from the beginning?
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e);
		return r?r:this;
	}
}

mixin FactoryFunction!DAbs;

class DLog: DOp{
	DExpr e;
	alias subExprs=Seq!e;
	override @property string symbol(Format formatting,int binders){ return "log"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp) return text("(log ",e.toStringImpl(formatting,prec,binders),")");
		auto es=e.toStringImpl(formatting,Precedence.none,binders);
		if(formatting==Format.python) return text("nan_to_num(log(",es,"))");
		if(formatting==Format.mathematica) return text("Log[",es,"]");
		return text("log(",es,")");
	}
	mixin Visitors;
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne != e) return dLog(ne).simplify(facts);
		if(auto c=cast(DE)e) return one;
		if(e==one) return zero;
		if(auto m=cast(DMult)e){
			DExprSet r,s;
			bool sign=false;
			foreach(f;m.factors){
				auto pos=dGeZ(f).simplify(facts);
				if(pos==one)
					r.insert(f);
				else if(pos==zero){
					sign^=true;
					if(f!= mone) r.insert(-f);
				}else s.insert(f); // TODO: use dAbs?
			}
			if(!(r.length&&s.length)&&r.length<=1) return null;
			DExprSet logs;
			foreach(x;r) DPlus.insert(logs,dLog(x));
			DPlus.insert(logs,dLog(sign?-dMult(s):dMult(s)));
			return dPlus(logs).simplify(facts);
		}
		if(auto q=cast(Dℚ)e)
			if(q.c.den!=1)
				return dLog(dℚ(q.c.num))-dLog(dℚ(q.c.den));
		if(auto f=cast(DFloat)e){
			import std.math: log;
			return dFloat(log(f.c));
		}
		if(auto p=cast(DPow)e){
			if(auto q=cast(Dℚ)p.operands[1])
				if(!(q.c.num&1)&&q.c.den==1)
					return (p.operands[1]*dLog(dAbs(p.operands[0]))).simplify(facts);
			return (p.operands[1]*dLog(p.operands[0])).simplify(facts);
		}
		if(auto fct=factorDIvr!(e=>dLog(e))(e)) return fct.simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DLog;

class DSin: DOp{
	DExpr e;
	alias subExprs=Seq!e;
	override @property string symbol(Format formatting,int binders){ return "sin"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp) return text("(sin ",e.toStringImpl(formatting,Precedence.none,binders),")");
		if(formatting==Format.mathematica) return text("Sin[",e.toStringImpl(formatting,Precedence.none,binders),"]");
		return "sin("~e.toStringImpl(formatting,Precedence.none,binders)~")";
	}
	mixin Visitors;
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!= e) return dSin(ne).simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DSin;
DExpr dCos(DExpr x){ return dSin(x+dΠ/2); }

class DFloor: DOp{
	DExpr e;
	alias subExprs=Seq!e;
	override @property string symbol(Format formatting,int binders){ return "⌊.⌋"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.default_)   return "⌊"~e.toStringImpl(formatting,Precedence.none,binders)~"⌋";
		if(formatting==Format.lisp) return text("(floor ",e.toStringImpl(formatting,Precedence.none,binders),")");
		return text("floor(",e.toStringImpl(formatting,Precedence.none,binders),")");
	}
	mixin Visitors;
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!=e) return dFloor(ne).simplify(facts);
		if(auto q=cast(Dℚ)e)
			return dℚ(floor(q.c));
		if(auto f=cast(DFloat)e){
			import std.format: format;
			import std.math: floor;
			return ℤ(format("%.0f",floor(f.c))).dℚ;
		}
		if(cast(DIvr)e||cast(DCeil)e||cast(DFloor)e) return e;
		if(facts.hasFactor(dIsℤ(e))) return e;
		if(auto p=cast(DPlus)e){
			DExpr integral=zero;
			foreach(s;p.summands)
				if(dIsℤ(s).simplify(facts)==one) integral=integral+s;
			if(integral != zero) return (integral+dFloor(e-integral)).simplify(facts);
		}
		if(auto m=cast(DMult)e){
			if(all!(f=>dIsℤ(f).simplify(facts)==one)(m.factors))
				return e;
		}
		if(auto p=cast(DPow)e)
			if(all!(f=>dIsℤ(f).simplify(facts)==one)(p.operands[]))
				return e;
		auto q=e.getFractionalFactor();
		if(q.c<0) return -dCeil(-e).simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DFloor;

class DCeil: DOp{
	DExpr e;
	alias subExprs=Seq!e;
	override @property string symbol(Format formatting,int binders){ return "⌈.⌉"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp) return text("(ceil ",e.toStringImpl(formatting,Precedence.none,binders),")");
		return "⌈"~e.toStringImpl(formatting,Precedence.none,binders)~"⌉";
	}
	mixin Visitors;
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!=e) return dCeil(ne).simplify(facts);
		if(auto q=cast(Dℚ)e)
			return dℚ(ceil(q.c));
		if(auto f=cast(DFloat)e){
			import std.format: format;
			import std.math: ceil;
			return ℤ(format("%.0f",ceil(f.c))).dℚ;
		}
		if(cast(DIvr)e||cast(DCeil)e||cast(DFloor)e) return e;
		if(facts.hasFactor(dIsℤ(e))) return e;
		if(auto p=cast(DPlus)e){
			DExpr integral=zero;
			foreach(s;p.summands)
				if(dIsℤ(s).simplify(facts)==one) integral=integral+s;
			if(integral != zero) return (integral+dCeil(e-integral)).simplify(one);
		}
		if(auto m=cast(DMult)e){
			if(all!(f=>dIsℤ(f).simplify(facts)==one)(m.factors))
				return e;
		}
		if(auto p=cast(DPow)e)
			if(all!(f=>dIsℤ(f).simplify(facts)==one)(p.operands[]))
				return e;
		auto q=e.getFractionalFactor();
		if(q.c<0) return -dFloor(-e).simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DCeil;

DExpr dMod(DExpr e1,DExpr e2){
	return e1-dFloor(e1/e2)*e2;
}

template BitwiseImpl(string which){
	DExprSet operands;
	alias subExprs=Seq!operands;
	mixin ToString;
	override @property Precedence precedence(){ return mixin("Precedence."~which); }
	override @property string symbol(Format formatting,int binders){ return " "~which~" "; }
	mixin Visitors;
	static void insert(ref DExprSet operands,DExpr operand)in{assert(!!operand);}body{
		if(operand==zero){
			static if(which=="bitAnd") operands.clear();
			else static if(which=="bitOr"||which=="bitXor") return;
			else static assert(0);
		}
		static if(which=="bitXor"){
			if(operand in operands){
				operands.remove(operand);
				return;
			}
		}
		operands.insert(operand);
	}
	static void insertAndSimplify(ref DExprSet operands,DExpr operand,DExpr facts){
		operand=operand.simplify(facts);
		if(auto other=mixin("cast(D"~upperf(which)~")operand")){
			foreach(o;other.operands)
				insertAndSimplify(operands,o,facts);
			return;
		}
		DExpr combine(DExpr e1,DExpr e2,DExpr facts){
			if(e1==e2){
				static if(which=="bitXor") return zero;
				else return e1;
			}
			if(auto n1=e1.isInteger()){
				if(auto n2=e2.isInteger){
					assert(n1.c.den==1 && n2.c.den==1);
					static if(which=="bitOr")
						return dℚ(n1.c.num|n2.c.num);
					else static if(which=="bitXor")
						return dℚ(n1.c.num^n2.c.num);
					else static if(which=="bitAnd")
						return dℚ(n1.c.num&n2.c.num);
					else static assert(0);
				}
			}
			return null;
		}
		foreach(o;operands){
			if(auto nws=combine(o,operand,facts)){
				assert(o in operands);
				operands.remove(o);
				insertAndSimplify(operands,nws,facts);
				return;
			}
		}
		insert(operands,operand);
	}
	override DExpr simplifyImpl(DExpr facts){
		DExprSet operands;
		foreach(o;this.operands)
			insertAndSimplify(operands,o,facts);
		static if(which=="bitOr"||which=="bitAnd"){
			if(util.all!(x=>mustBeZeroOrOne(x))(operands)){
				static if(which=="bitOr"){
					DExprSet ops;
					foreach(op;operands) DPlus.insert(ops, dNeqZ(op));
					return dNeqZ(dPlus(ops)).simplify(facts);
				}else{
					static assert(which=="bitAnd");
					DExprSet ops;
					foreach(op;operands) DMult.insert(ops, dNeqZ(op));
					return dMult(ops).simplify(facts);
				}
			}
		}
		return mixin("d"~upperf(which))(operands);
	}
	static DExpr constructHook(DExprSet operands){
		static if(which=="bitOr"||which=="bitXor")
			if(!operands.length) return zero;
		return null;
	}
}
class DCommutAssocIdemOp: DCommutAssocOp { }
class DBitOr: DCommutAssocIdemOp{ // TODO: this is actually also idempotent
	mixin BitwiseImpl!"bitOr";
}
class DBitXor: DCommutAssocOp{
	mixin BitwiseImpl!"bitXor";
}
class DBitAnd: DCommutAssocIdemOp{ // TODO: this is actually also idempotent
	mixin BitwiseImpl!"bitAnd";
}
mixin FactoryFunction!DBitOr;
mixin FactoryFunction!DBitXor;
mixin FactoryFunction!DBitAnd;

class DGaussInt: DOp{
	DExpr x;
	alias subExprs=Seq!x;
	override @property string symbol(Format formatting,int binders){ return "(d/dx)⁻¹[e^(-x²)]"; }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.gnuplot){
			return "sqrt(pi)*(erf("~x.toStringImpl(formatting,Precedence.none,binders)~")+1)/2";
		}else if(formatting==Format.mathematica){
			return "Sqrt[Pi]*(Erf["~x.toStringImpl(formatting,Precedence.none,binders)~"]+1)/2";
		}else if(formatting==Format.maple){
			return "sqrt(Pi)*(erf("~x.toStringImpl(formatting,Precedence.none,binders)~")+1)/2";
		}else if(formatting==Format.matlab) return "(sqrt(pi)*(erf("~x.toStringImpl(formatting,Precedence.none,binders)~")+1)/2)";
		else if(formatting==Format.lisp) return text("(gauss-integral ",x.toStringImpl(formatting,Precedence.none,binders),")");
		else if(formatting==Format.sympy) return "sqrt(pi)*(erf("~x.toStringImpl(formatting,Precedence.none,binders)~")+1)/2";
		else return addp(prec,symbol(formatting,binders)~"("~x.toStringImpl(formatting,Precedence.none,binders)~")");
	}

	static DExpr staticSimplify(DExpr x,DExpr facts=one){
		if(x==dInf){
			return dΠ^^(one/2);
		}else if(x==-dInf){
			return zero;
		}
		if(x==zero){
			return dΠ^^(one/2)/2;
		}
		auto nx=x.simplify(facts);
		if(auto g=cast(DGaussIntInv)nx) return g.x;
		if(nx != x) return dGaussInt(nx).simplify(facts);
		if(auto fct=factorDIvr!(e=>dGaussInt(e))(x)) return fct.simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(x);
		return r?r:this;
	}
	mixin Visitors;
}
mixin FactoryFunction!DGaussInt;

class DGaussIntInv: DOp{
	DExpr x;
	alias subExprs=Seq!x;
	override @property string symbol(Format formatting,int binders){ return "(d/dx)⁻¹[e^(-x²)]⁻¹"; }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.gnuplot){
			return "inverf(2/sqrt(pi)*("~x.toStringImpl(formatting,Precedence.none,binders)~")-1)";
		}else if(formatting==Format.mathematica){
			return "InverseErf[2/Sqrt[Pi]*("~x.toStringImpl(formatting,Precedence.none,binders)~")-1]";
		}else if(formatting==Format.maple){
			return "erfinv(2/sqrt(Pi)*("~x.toStringImpl(formatting,Precedence.none,binders)~")-1)";
		}else if(formatting==Format.matlab) return "erfinv(2/sqrt(pi)*("~x.toStringImpl(formatting,Precedence.none,binders)~")-1)";
		else if(formatting==Format.lisp) return text("(inverse-gauss-integral ",x.toStringImpl(formatting,Precedence.none,binders),")");
		else if(formatting==Format.sympy) return "erfinv(2/sqrt(pi)*("~x.toStringImpl(formatting,Precedence.none,binders)~")-1)";
		else return addp(prec,symbol(formatting,binders)~"("~x.toStringImpl(formatting,Precedence.none,binders)~")");
	}
	static DExpr staticSimplify(DExpr x,DExpr facts=one){
		auto nx=x.simplify(facts);
		if(nx==(dΠ^^(one/2)/2).simplify(one)) return zero; // TODO: evaluate more cases
		if(auto g=cast(DGaussInt)nx) return g.x;
		if(nx != x) return dGaussIntInv(nx).simplify(facts);
		if(auto fct=factorDIvr!(e=>dGaussIntInv(e))(x)) return fct.simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(x);
		return r?r:this;
	}
	mixin Visitors;
}
mixin FactoryFunction!DGaussIntInv;

class DInf: DExpr{ // TODO: explicit limits?
	alias subExprs=Seq!();
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp) return "infinity";
		return "∞";
	}
	mixin Constant;
}

private static DInf theDInf;
@property DInf dInf(){ return theDInf?theDInf:(theDInf=new DInf); }

bool isInfinite(DExpr e){
	return e==dInf || e==-dInf;
}

class DTuple: DExpr{
	DExpr[] values;
	alias subExprs=Seq!values;
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		if(formatting==Format.lisp) return text("(tuple ",values.map!(v=>v.toStringImpl(formatting,Precedence.none,binders)).join(" "),")");
		return text("(",values.map!(v=>v.toStringImpl(formatting,Precedence.none,binders)).join(","),values.length==1?",":"",")");
	}
	mixin Visitors;
	static DTuple staticSimplify(DExpr[] values,DExpr facts=one){
		auto nvalues=values.map!(v=>v.simplify(facts)).array;
		if(nvalues!=values) return dTuple(nvalues);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(values,facts);
		return r?r:this;
	}
	final @property size_t length(){ return values.length; }
	final @property DExpr opIndex(size_t i){ return values[i]; }
}
mixin FactoryFunction!DTuple;

class DArrayLiteral: DExpr{ // TODO: add support for indexing etc?
	DExpr[] values;
	alias subExprs=Seq!values;
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		if(formatting==Format.lisp) return text("(array-literal ",values.map!(v=>v.toStringImpl(formatting,Precedence.none,binders)).join(" "),")");
		return text("[",values.map!(v=>v.toStringImpl(formatting,Precedence.none,binders)).join(","),values.length==1?",":"","]");
	}
	mixin Visitors;
	static DArrayLiteral staticSimplify(DExpr[] values,DExpr facts=one){
		auto nvalues=values.map!(v=>v.simplify(facts)).array;
		if(nvalues!=values) return dArrayLiteral(nvalues);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(values,facts);
		return r?r:this;
	}
	final @property size_t length(){ return values.length; }
	final @property DExpr opIndex(size_t i){ return values[i]; }
}
mixin FactoryFunction!DArrayLiteral;

class DRecord: DExpr{
	DExpr[string] values;
	alias subExprs=Seq!values;
	final DRecord update(string f,DExpr n){
		auto nvalues=values.dup;
		nvalues[f]=n;
		return dRecord(nvalues);
	}

	override string toStringImpl(Format formatting, Precedence prec, int binders){
		if(formatting==Format.lisp){
			auto r="(record ";
			foreach(k,v;values)
				r~=text("(:",k," ",v.toStringImpl(formatting,Precedence.none,binders),")");
			r~=")";
			return r;
		}
		// TODO: other CAS?
		auto r="{";
		foreach(k,v;values){
			r~="."~k~" ↦ "~v.toStringImpl(formatting,Precedence.none,binders);
			r~=",";
		}
		return r.length!=1?r[0..$-1]~"}":"{}";
	}
	mixin Visitors;
	static DRecord staticSimplify(DExpr[string] values,DExpr facts=one){
		DExpr[string] nvalues;
		foreach(k,v;values) nvalues[k]=v.simplify(facts);
		if(nvalues!=values) return dRecord(nvalues);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(values,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DRecord;

class DIndex: DOp{
	DExpr e,i; // TODO: multiple indices?
	alias subExprs=Seq!(e,i);
	override string symbol(Format formatting,int binders){ return "@("; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		if(formatting==Format.lisp) return text("(select ",e.toStringImpl(formatting,Precedence.none,binders)," ",i.toStringImpl(formatting,Precedence.none,binders),")");
		return addp(prec, e.toStringImpl(formatting,Precedence.index,binders)~"@["~i.toStringImpl(formatting,Precedence.none,binders)~"]");
	}
	mixin Visitors;
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,i,facts);
		return r?r:this;
	}
	static DExpr staticSimplify(DExpr e,DExpr i,DExpr facts=one){
		auto ne=e.simplify(facts);
		auto ni=i.simplify(facts);
		if(auto c=ni.isInteger()){
			if(auto tpl=cast(DTuple)ne){
				assert(c.c.den==1);
				if(0<=c.c.num&&c.c.num<tpl.values.length)
					return tpl.values[cast(size_t)c.c.num.toLong()].simplify(facts);
			}
		}
		if(auto arr=cast(DArray)ne){
			return arr.entries.apply(ni).simplify(facts);
		}
		if(ne != e || ni != i) return dIndex(ne,ni);
		return null;
	}
}
mixin FactoryFunction!DIndex;

class DIUpdate: DOp{
	DExpr e,i,n; // TODO: multiple indices?
	alias subExprs=Seq!(e,i,n);
	override string symbol(Format formatting,int binders){ return "[ ↦ ]"; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		if(formatting==Format.lisp) return text("(store ",e.toStringImpl(formatting,Precedence.none,binders)," ",i.toStringImpl(formatting,Precedence.none,binders)," ",n.toStringImpl(formatting,Precedence.none,binders));
		return addp(prec, e.toStringImpl(formatting,Precedence.index,binders)~"["~i.toStringImpl(formatting,Precedence.none,binders)~
					" ↦ "~n.toStringImpl(formatting,Precedence.none,binders)~"]");
	}
	mixin Visitors;

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,i,n,facts);
		return r?r:this;
	}

	static DExpr staticSimplify(DExpr e,DExpr i,DExpr n,DExpr facts=one){
		auto ne=e.simplify(facts);
		auto ni=i.simplify(facts);
		auto nn=n.simplify(facts);
		if(auto c=ni.isInteger()){
			if(auto tpl=cast(DTuple)ne){
				assert(c.c.den==1);
				if(0<=c.c.num&&c.c.num<tpl.values.length){
					auto nvalues=tpl.values.dup;
					nvalues[cast(size_t)c.c.num.toLong()]=nn;
					return dTuple(nvalues);
				}
			}
		}
		if(auto arr=cast(DArray)ne){
			auto dbv=db1;
			auto nni=ni.incDeBruijnVar(1,0);
			auto nnn=nn.incDeBruijnVar(1,0);
			auto r=dArray(arr.length,
			              dLambda(arr.entries.expr*dNeq(dbv,nni)
			                      + dEq(dbv,nni)*nnn));
			return r.simplify(facts);
		}
		if(ne != e || ni != i || nn != n) return dIUpdate(ne,ni,nn);
		return null;
	}
}
mixin FactoryFunction!DIUpdate;

class DSlice: DOp{
	DExpr e,l,r; // TODO: multiple indices?
	alias subExprs=Seq!(e,l,r);
	override string symbol(Format formatting,int binders){ return "[]"; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		if(formatting==Format.lisp) return text("(slice ",e.toStringImpl(formatting,Precedence.none,binders)," ",l.toStringImpl(formatting,Precedence.none,binders)," ",r.toStringImpl(formatting,Precedence.none,binders),")");
		return addp(prec, e.toStringImpl(formatting,Precedence.index,binders)~"["~l.toStringImpl(formatting,Precedence.none,binders)~".."~r.toStringImpl(formatting,Precedence.none,binders)~"]");
	}
	mixin Visitors;

	override DExpr simplifyImpl(DExpr facts){
		auto res=staticSimplify(e,l,r,facts);
		return res?res:this;
	}

	static DExpr staticSimplify(DExpr e,DExpr l,DExpr r,DExpr facts=one){
		auto ne=e.simplify(facts);
		auto nl=l.simplify(facts);
		auto nr=r.simplify(facts);
		if(auto c=nl.isInteger()){
			if(auto d=nr.isInteger()){
				if(auto tpl=cast(DTuple)ne){
					assert(c.c.den==1 && d.c.den==1);
					if(0<=c.c.num&&c.c.num<tpl.values.length&&0<=d.c.num&&d.c.num<tpl.values.length)
						return dTuple(tpl.values[cast(size_t)c.c.num.toLong()..cast(size_t)d.c.num.toLong()]).simplify(facts);
				}
			}
		}
		if(auto arr=cast(DArray)ne){
			auto dbv=db1;
			return dArray(nr-nl,dLambda(arr.entries.expr.substitute(dbv,dbv+nl)*dBounded!"[)"(dbv,zero,nr-nl))).simplify(facts);
		}
		// distribute over case distinction:
		if(ne==zero) return zero;
		if(auto p=cast(DPlus)ne){
			DExprSet res;
			foreach(s;p.summands) DPlus.insert(res,dSlice(s,nl,nr));
			return dPlus(res).simplify(facts);
		}
		if(auto m=cast(DMult)ne){
			foreach(fc;m.factors){
				if(cast(DTuple)fc||cast(DArray)fc)
					return (m.withoutFactor(fc)*dSlice(fc,nl,nr)).simplify(facts);
				if(cast(DIvr)fc)
					return (dSlice(m.withoutFactor(fc),nl,nr)*fc).simplify(facts);
			}
		}
		if(ne != e || nl != l || nr != r) return dSlice(ne,nl,nr);
		return null;
	}
}
mixin FactoryFunction!DSlice;

class DRUpdate: DOp{ // TODO: allow updating multiple fields at once
	DExpr e; // TODO: multiple indices?
	string f;
	DExpr n;
	alias subExprs=Seq!(e,f,n);
	override string symbol(Format formatting,int binders){ return "[ ↦ ]"; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		if(formatting==Format.lisp) return text("(store ",e.toStringImpl(formatting,Precedence.none,binders)," :",f," ",n.toStringImpl(formatting,Precedence.none,binders),")");
		return addp(prec, e.toStringImpl(formatting,Precedence.index,binders)~"{."~f~
					" ↦ "~n.toStringImpl(formatting,Precedence.none,binders)~"}");
	}
	mixin Visitors;

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,f,n,facts);
		return r?r:this;
	}

	static DExpr staticSimplify(DExpr e,string f,DExpr n,DExpr facts=one){
		auto ne=e.simplify(facts);
		auto nn=n.simplify(facts);
		if(auto rec=cast(DRecord)ne)
			return rec.update(f,nn).simplify(facts);
		if(ne != e || nn != n) return dRUpdate(ne,f,nn);
		return null;
	}
}
mixin FactoryFunction!DRUpdate;

class DLambda: DOp{ // lambda functions DExpr → DExpr
	/+private+/ @binder DExpr expr;
	alias subExprs=Seq!expr;
	DExpr apply(DExpr e){
		return unbind(expr,e);
	}
	override @property Precedence precedence(){ return Precedence.lambda; }
	override @property string symbol(Format formatting,int binders){ return "λ"; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp)
			return text("(lambda (",DDeBruijnVar.displayName(1,formatting,binders+1),") ",expr.toStringImpl(formatting,Precedence.none,binders+1),")");
		// TODO: formatting for other CAS systems
		return addp(prec,text("λ",DDeBruijnVar.displayName(1,formatting,binders+1),". ",expr.toStringImpl(formatting,Precedence.lambda,binders+1)));
	}
	mixin Visitors;
	final DLambda substitute(DVar var,DExpr expr){
		auto r=cast(DLambda)super.substitute(var,expr);
		assert(!!r);
		return r;
	}
	static DLambda staticSimplify(DExpr expr,DExpr facts=one){
		auto nexpr=expr.simplify(facts.incDeBruijnVar(1,0).simplify(one));
		if(nexpr != expr){
			auto r=dLambda(nexpr).simplify(facts);
			assert(!r||cast(DLambda)r);
			return cast(DLambda)r;
		}
		return null;
	}
	override DLambda simplifyImpl(DExpr facts){
		auto r=staticSimplify(expr,facts);
		return r?r:this;
	}
	final DLambda simplify(DExpr facts){
		auto r=cast(DLambda)super.simplify(facts);
		assert(!!r);
		return r;
	}
}
mixin FactoryFunction!DLambda;

DLambda dTupleLambda(DVar[] args,DExpr fun){
	import std.range: iota;
	fun=fun.incDeBruijnVar(1,0).substituteAll(args,iota(args.length).map!(i=>db1[dℚ(i)]).array);
	return dLambda(fun);
}

class DApply: DOp{
	DExpr fun,arg;
	alias subExprs=Seq!(fun,arg);
	override @property string symbol(Format formatting,int binders){ return " "; }
	override @property Precedence precedence(){ return Precedence.apply; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		auto isTpl=!!cast(DTuple)arg;
		return addp(prec,text(fun.toStringImpl(formatting,Precedence.apply,binders),"(",arg.toStringImpl(formatting,Precedence.none,binders)[isTpl..$-isTpl],")"));
	}
	mixin Visitors;
	override DExpr simplifyImpl(DExpr facts){
		auto nfun=fun.simplify(facts),narg=arg.simplify(facts);
		if(auto l=cast(DLambda)nfun)
			return l.apply(narg).simplify(facts);
		return dApply(nfun,narg);
	}
}
mixin FactoryFunction!DApply;

class DDistLambda: DOp{
	/+private+/ @binder DExpr expr;
	alias subExprs=Seq!expr;
	DExpr apply(DExpr e){
		return unbind(expr,e);
	}
	override @property Precedence precedence(){ return Precedence.lambda; }
	override @property string symbol(Format formatting,int binders){ return "Λ"; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp)
			return text("(dist-lambda (",DDeBruijnVar.displayName(1,formatting,binders+1),") ",expr.toStringImpl(formatting,Precedence.none,binders+1),")");
		// TODO: formatting for other CAS systems
		return addp(prec,text("Λ",DDeBruijnVar.displayName(1,formatting,binders+1),". ",expr.toStringImpl(formatting,Precedence.lambda,binders+1)));
	}
	mixin Visitors;
	final DDistLambda substitute(DVar var,DExpr expr){
		auto r=cast(DDistLambda)super.substitute(var,expr);
		assert(!!r);
		return r;
	}
	static DDistLambda staticSimplify(DExpr expr,DExpr facts=one){
		auto nexpr=expr.simplify(facts.incDeBruijnVar(1,0).simplify(one));
		if(nexpr != expr){
			auto r=dDistLambda(nexpr).simplify(facts);
			assert(!r||cast(DDistLambda)r);
			return cast(DDistLambda)r;
		}
		return null;
	}
	override DDistLambda simplifyImpl(DExpr facts){
		auto r=staticSimplify(expr,facts);
		return r?r:this;
	}
	final DDistLambda simplify(DExpr facts){
		auto r=cast(DDistLambda)super.simplify(facts);
		assert(!!r);
		return r;
	}
}
mixin FactoryFunction!DDistLambda;


class DDistApply: DOp{
	DExpr fun,arg;
	alias subExprs=Seq!(fun,arg);
	override @property string symbol(Format formatting,int binders){ return "["; } // TODO: ambiguous (same syntax as DApply). Replace symbol by ⟦ and also use ⟦ instead of [ for deltas.
	override @property Precedence precedence(){ return Precedence.apply; }
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		auto isTpl=!!cast(DTuple)arg;
		return addp(prec,text(fun.toStringImpl(formatting,Precedence.apply,binders),"[",arg.toStringImpl(formatting,Precedence.none,binders)[isTpl..$-isTpl],"]"));
	}
	mixin Visitors;
	override DExpr simplifyImpl(DExpr facts){
		auto nfun=fun.simplify(facts),narg=arg.simplify(one); // cannot use all facts for arg! (might remove a free variable)
		if(auto l=cast(DDistLambda)nfun)
			return l.apply(narg).simplify(facts);
		return dDistApply(nfun,narg);
	}
}
mixin FactoryFunction!DDistApply;

class DArray: DExpr{
	DExpr length;
	DLambda entries;
	alias subExprs=Seq!(length,entries);
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		if(formatting==Format.lisp) return text("(array ",length.toStringImpl(formatting,Precedence.none,binders)," ",entries.toStringImpl(formatting,Precedence.none,binders),")");// TODO: how to do this in z3?
		if(length==zero) return "[]";
		auto r=text("[",DDeBruijnVar.displayName(1,formatting,binders+1)," ↦ ",entries.expr.toStringImpl(formatting,Precedence.none,binders+1),"] (",length,")");
		if(prec!=Precedence.none) r="("~r~")"; // TODO: ok?
		return r;
	}
	mixin Visitors;
	static DExpr staticSimplify(DExpr length,DLambda entries,DExpr facts=one){
		auto nlength=length.simplify(facts);
		auto nentries=nlength==zero?dLambda(zero):cast(DLambda)entries.simplify(facts);
		assert(!!nentries);
		if(nlength==one){ // TODO: use the fact that indices are integers for simplification
			nentries=cast(DLambda)dLambda(nentries.apply(zero).incDeBruijnVar(1,0)).simplify(facts);
			assert(!!nentries);
		}
		if(nlength!= length||nentries!= entries) return dArray(nlength,nentries);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(length,entries,facts);
		return r?r:this;
	}
}
mixin FactoryFunction!DArray;

class DCat: DAssocOp{ // TODO: this should have n arguments, as it is associative!
	override @property Precedence precedence(){ return Precedence.plus; }
	override @property string symbol(Format formatting,int binders){ return "~"; }

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(operands,facts);
		return r?r:this;
	}
	mixin Visitors;
	/+private+/ static DExpr staticSimplify(DExpr[] operands,DExpr facts=one){
		auto nop=operands.map!(a=>a.simplify(facts)).array;
		if(nop!=operands) return dCat(nop).simplify(facts);
		DExpr doCat(DExpr e1,DExpr e2){
			auto a1=cast(DArray)e1;
			auto a2=cast(DArray)e2;
			if(a1&&a1.length==zero) return e2;
			if(a2&&a2.length==zero) return e1;
			if(!a1||!a2) return null;
			auto dbv=db1;
			return dArray(a1.length+a2.length,
			              dLambda(a1.entries.expr*dLt(dbv,a1.length)
			                      +a2.entries.expr.substitute(dbv,dbv-a1.length)*dGe(dbv,a1.length)));
		}
		nop=[];
		foreach(i;0..operands.length-1){
			auto e1=operands[i];
			auto e2=operands[i+1];
			if(auto c=doCat(e1,e2)){
				nop=operands[0..i]~c;
				foreach(j;i+2..operands.length){
					if(auto cat=doCat(nop[$-1],operands[j]))
						nop[$-1]=cat;
					else nop~=operands[j];
				}
				return dCat(nop).simplify(facts);
			}
		}
		return null;
	}
}
mixin FactoryFunction!DCat;

class DField: DOp{
	DExpr e;
	string f;
	alias subExprs=Seq!(e,f);
	override string symbol(Format formatting,int binders){ return "."; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec,int binders){
		if(formatting==Format.lisp) return text("(select ",e.toStringImpl(formatting,Precedence.none,binders)," :",f);
		return addp(prec, e.toStringImpl(formatting,Precedence.field,binders)~"."~f);
	}
	mixin Visitors;

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,f,facts);
		return r?r:this;
	}

	static DExpr staticSimplify(DExpr e,string f,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(f=="length"){
			if(auto tpl=cast(DTuple)ne)
				return dℚ(ℤ(tpl.length));
			if(auto arr=cast(DArray)ne)
				return arr.length;
			if(auto cat=cast(DCat)ne){
				DExprSet s;
				foreach(op;cat.operands)
					DPlus.insert(s,dField(op,f));
				return dPlus(s).simplify(facts);
			}
		}
		if(auto rec=cast(DRecord)ne)
			if(f in rec.values) return rec.values[f].simplify(facts);
		if(auto ru=cast(DRUpdate)ne)
			return f == ru.f ? ru.n.simplify(facts) : dField(ru.e,f).simplify(facts);
		// distribute over case distinction:
		if(e==zero) return zero;
		if(auto p=cast(DPlus)ne){
			DExprSet r;
			foreach(s;p.summands) DPlus.insert(r,dField(s,f));
			return dPlus(r).simplify(facts);
		}
		if(auto m=cast(DMult)ne){
			foreach(fc;m.factors){
				if(cast(DTuple)fc||cast(DArray)fc||cast(DRecord)fc)
					return (m.withoutFactor(fc)*dField(fc,f)).simplify(facts);
				if(cast(DIvr)fc)
					return (dField(m.withoutFactor(fc),f)*fc).simplify(facts);
			}
		}
		if(ne != e) return dField(ne,f);
		return null;
	}
}
mixin FactoryFunction!DField;

abstract class DMonad: DExpr{}

class DVal: DMonad{
	DExpr e;
	alias subExprs=Seq!e;
	mixin Visitors;
	override DExpr simplifyImpl(DExpr facts){
		auto ne=e.simplify(facts);
		if(ne==e) return this;
		return dVal(ne);
	}
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		auto isTpl=!!cast(DTuple)e;
		return text("val(",e.toStringImpl(formatting,Precedence.none,binders)[isTpl..$-isTpl],")");
	}
}
mixin FactoryFunction!DVal;

class DErr: DMonad{ // monad for side-effects
	alias subExprs=Seq!();
	mixin Constant;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		return "⊥";
	}
}
mixin FactoryFunction!DErr;

class DMCase: DExpr{ // TODO: generalize?
	DExpr e;
	@binder DExpr val;
	DExpr err;
	alias subExprs=Seq!(e,val,err);
	mixin Visitors;
	override DExpr simplifyImpl(DExpr facts){
		auto ne=e.simplify(facts);
		auto nval=val.simplify(facts.incDeBruijnVar(1,0).simplify(one));
		auto nerr=err.simplify(facts);
		if(cast(DMonad)ne){
			if(auto v=cast(DVal)ne)
				return unbind(val,v.e).simplify(facts);
			if(cast(DErr)ne)
				return nerr;
		}
		if(auto fact=factorDIvr!(e=>dMCase(e,nval,nerr))(ne)) return fact;
		if(ne==e&&nerr==err&&nval==val) return this;
		return dMCase(ne,nval,nerr);
	}
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		return text("(case(",e.toStringImpl(formatting,Precedence.none,binders),"){ val(",DDeBruijnVar.displayName(1,formatting,binders+1),") ⇒ ",val.toStringImpl(formatting,Precedence.none,binders+1),";⊥ ⇒ ",err.toStringImpl(formatting,Precedence.none,binders),"})");
	}
}
mixin FactoryFunction!DMCase;

class DBind: DOp{
	DExpr e,f;
	alias subExprs=Seq!(e,f);
	mixin Visitors;
	override @property string symbol(Format formatting,int binders){
		return ">>=";
	}
	override @property Precedence precedence(){
		return Precedence.bind;
	}
	override string toStringImpl(Format formatting, Precedence prec, int binders){
		return addp(prec, text(e.toStringImpl(formatting,prec,binders),">>=",f.toStringImpl(formatting,prec,binders)));
	}
	override DExpr simplifyImpl(DExpr facts){
		auto ne=e.simplify(facts), nf=f.simplify(facts);
		if(cast(DMonad)ne){
			if(auto val=cast(DVal)ne)
				return dApply(f,val.e).simplify(facts);
			if(cast(DErr)ne)
				return ne;
		}
		if(ne==e&&nf==f) return this;
		return dBind(ne,nf);
	}
}
mixin FactoryFunction!DBind;

class DNormalize: DExpr{
	DExpr e;
	alias subExprs=Seq!e;
	mixin Visitors;
	override string toStringImpl(Format formatting,Precedence prec,int binders){
		return text("normalize(",e.toStringImpl(formatting,Precedence.none,binders),")");
	}
	override DExpr simplifyImpl(DExpr facts){
		auto ne=e.simplify(facts);
		if(auto onorm=cast(DNormalize)ne)
			return onorm;
		auto nnorm=dIntSmp(dDistApply(ne.incDeBruijnVar(1,0),db1),facts);
		auto iszero=dEqZ(nnorm).simplify(facts);
		if(iszero==zero) return dLambda(dDistApply(ne.incDeBruijnVar(1,0),db1)/nnorm).simplify(facts);
		if(iszero==one) return dLambda(dDiscDelta(dErr,db1));
		if(ne!=e) return dNormalize(ne).simplify(facts);
		return this;
	}
}
mixin FactoryFunction!DNormalize;

import std.traits: ParameterTypeTuple;
import std.typetuple;
T visit(T,S...)(DExpr node,S args){
	enum manualPropagate=false;
	auto result = T(args);
	alias TypeTuple!(__traits(getOverloads,T,"perform")) overloads;
	int runIt(DExpr node){
		static if(!manualPropagate)
			if(auto r=node.forEachSubExpr(&runIt))
				return r;
		foreach(i,ov;overloads){
			if(auto e = cast(ParameterTypeTuple!(ov)[0])node){
				if(auto r=result.perform(e))
					return r;
				return 0;
			}
		}
		return 0;
	}
	runIt(node);
	static if(!manualPropagate) return result;
}

auto allOf(T)(DExpr e,bool belowBindings=false){
	static struct AllOfVisitor{
		int delegate(T) dg;
		bool belowBindings;
		int r=0;
		int perform(T t){
			if(auto r=dg(t))
				return this.r=r;
			static if(is(T==DInt)||is(T==DSum)){
				if(belowBindings)
					if(auto r=t.expr.visit!AllOfVisitor(dg,belowBindings).r)
					   return this.r=r;
			}
			return 0;
		}
		static if(!is(T==DInt)&&!is(T==DSum)){
			int perform(DInt t){
				if(belowBindings){
					if(auto r=t.expr.visit!AllOfVisitor(dg,belowBindings).r)
					   return this.r=r;
				}
				return 0;
			}
			int perform(DSum t){ // static foreach would be nice here
				if(belowBindings){
					if(auto r=t.expr.visit!AllOfVisitor(dg,belowBindings).r)
					   return this.r=r;
				}
				return 0;
			}
		}
	}
	static struct AllOf{
		DExpr e;
		bool belowBindings;
		int opApply(scope int delegate(T) dg){
			return e.visit!AllOfVisitor(dg,belowBindings).r;
		}
	}
	return AllOf(e,belowBindings);
}

bool hasAny(T)(DExpr e,bool belowBindings=true){ foreach(x;allOf!T(e,belowBindings)) return true; return false; }

bool hasFreeVars(DExpr e){ foreach(x;e.freeVars) return true; return false; }


// derived functions

DExpr dIsℤ(DExpr e){
	return dEq(e,dFloor(e));
}

DExpr dGamma(DExpr t){
	t=t.incDeBruijnVar(1,0);
	auto x=db1;
	return dInt(x^^(t-1)*dE^^(-x)*dGeZ(x));
}

DExpr dBeta(DExpr x,DExpr y){ // constraints: x>0 and y>0
	x=x.incDeBruijnVar(1,0), y=y.incDeBruijnVar(1,0);
	auto t=db1;
	return dInt(dBounded!"[]"(t,zero,one)*t^^(x-1)*(1-t)^^(y-1));
}

DExpr dNChooseK(DExpr n,DExpr k){
	// TODO: better encoding?
	return dBounded!"[]"(k,zero,n)*dGamma(n+1)/(dGamma(n-k+1)*dGamma(k+1));
}



/+
enum locs=[ ];

DExpr dIvr(string file=__FILE__,int line=__LINE__)(DIvr.Type type, DExpr e){
	//pragma(msg, text(`"`,file," ",line,`",`));
	enum idx=locs.countUntil(text(file," ",line));
	static assert(idx!=-1);
	pragma(msg,idx);
	static if(idx==2) pragma(msg, file," ",line);
	if(idx==2){
		//if(auto r=DIvr.staticSimplify(type,e))
		//	return r;
	}else writeln(idx);
	return dIvrImpl(type,e);
}
+/
/+enum locs=[  ];
auto dMult(string file=__FILE__,int line=__LINE__)(DExpr e1,DExpr e2){
	//pragma(msg, text(`"`,file," ",line,`",`));
	//enum idx=locs.countUntil(text(file," ",line));
	//static assert(idx!=-1);
	//static if(idx==85) pragma(msg, file," ",line);
	DExprSet a;
	//enum idx=-2;
	static if(false){
		DMult.insertAndSimplify(a,e1,one);
		DMult.insertAndSimplify(a,e2,one);
	}else{
		DMult.insert(a,e1);
		DMult.insert(a,e2);

	}
	return dMult(a);
}+/


/+enum locs = [ ];
auto dPow(string file=__FILE__,int line=__LINE__)(DExpr e1, DExpr e2){
	//pragma(msg, text(`"`,file," ",line,`",`));
	/+enum idx=locs.countUntil(text(file," ",line));
	static assert(idx!=-1);
	//pragma(msg, idx);
	static if(idx==26) pragma(msg, file," ",line);
	static if(idx<=25)
		if(auto r=DPow.staticSimplify(e1,e2)) return r;+/
	return uniqueDExprNonCommutAssoc!(DPow)(e1,e2);
}

DExpr dDiv(string file=__FILE__,int line=__LINE__)(DExpr e1,DExpr e2){ return e1*dPow!(file,line)(e2,mone); }+/

