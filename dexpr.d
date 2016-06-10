// TODO: the caches should use weak references

import std.conv;
import hashtable, util;

alias Q=TupleX, q=tuplex;
static import std.typecons;

import std.algorithm, std.array;

import std.datetime;

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
	writeln("time: ",sw.peek().to!("seconds",double));
	writeln("freq: ",swCount);
}
enum measure="swCount++;sw.start();scope(exit)sw.stop();";+/

enum Format{
	default_,
	matlab,
	maple,
	mathematica,
	sympy,
}

//version=DISABLE_INTEGRATION;
enum Simpl{
	full,
	deltas,
	raw
}
Simpl simplification=Simpl.full;

enum Precedence{
	none,
	lambda,
	plus,
	uminus,
	lim,
	intg,
	mult,
	div,
	diff,
	pow,
	index,
	field=index,
	invalid,
}
hash_t g_hash=0;
abstract class DExpr{
	hash_t hash;
	this(){ hash = ++g_hash; }
	override hash_t toHash()@trusted{ return hash; }

	final override string toString(){ return toString(Format.default_); }

	string toString(Format formatting){
		auto r=toStringImpl(formatting,Precedence.none);
		if(formatting==Format.sympy) r=text("limit(",r,",pZ,0,'+')"); // pZ: positive zero
		else if(formatting==Format.maple) r=text("limit(",r,",pZ=0,right)");
		return r;
	}
	abstract string toStringImpl(Format formatting,Precedence prec);

	abstract int forEachSubExpr(scope int delegate(DExpr) dg);

	abstract DExpr simplifyImpl(DExpr facts);

	static MapX!(Q!(DExpr,DExpr),DExpr) simplifyMemo;
	final DExpr simplify(DExpr facts){
		if(q(this,facts) in simplifyMemo) return simplifyMemo[q(this,facts)];
		if(facts is zero) return zero;
		auto r=simplifyImpl(facts);
		assert(!!r,text(typeid(this)));
		simplifyMemo[q(this,facts)]=r;
		simplifyMemo[q(r,facts)]=r;
		/+foreach(ivr;r.allOf!DIvr){ // TODO: remove?
			assert(ivr is ivr.simplify(facts),text(this," ",r," ",facts));
			assert(ivr.type !is DIvr.Type.lZ);
		}+/
		return r;
	}

	// TODO: implement in terms of 'forEachSubExpr'?
	abstract DExpr substitute(DVar var,DExpr e);
	abstract DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context);
	abstract DExpr incBoundVar(int di,bool bindersOnly);
	abstract int freeVarsImpl(scope int delegate(DVar));
	final freeVars(){
		static struct FreeVars{ // TODO: move to util?
			DExpr self;
			int opApply(scope int delegate(DVar) dg){
				return self.freeVarsImpl(dg);
			}
		}
		return FreeVars(this);
	}
	final bool hasFreeVar(DVar var){
		foreach(v;freeVars) if(v is var) return true;
		return false;
	}

	bool isFraction(){ return false; }
	ℕ[2] getFraction(){ assert(0,"not a fraction"); }

	// helpers for construction of DExprs:
	enum ValidUnary(string s)=s=="-";
	enum ValidBinary(string s)=["+","-","*","/","^^","~"].canFind(s);
	template UnaryCons(string s)if(ValidUnary!s){
		static assert(s=="-");
		alias UnaryCons=dUMinus;
	}
	template BinaryCons(string s)if(ValidBinary!s){
		static if(s=="+") alias BinaryCons=dPlus;
		else static if(s=="-") alias BinaryCons=dMinus;
		else static if(s=="*") alias BinaryCons=dMult;
		else static if(s=="/") alias BinaryCons=dDiv;
		else static if(s=="^^") alias BinaryCons=dPow;
		else static if(s=="~") alias BinaryCons=dCat;
		else static assert(0);
	}
	final opUnary(string op)()if(op=="-"){ return UnaryCons!op(this); }
	final opBinary(string op)(DExpr e)if(ValidBinary!op){
		return BinaryCons!op(this,e);
	}
	final opBinary(string op)(long e)if(ValidBinary!op){
		return mixin("this "~op~" e.dℕ");
	}
	final opBinaryRight(string op)(long e)if(ValidBinary!op){
		return mixin("e.dℕ "~op~" this");
	}
	final opBinary(string op)(ℕ e)if(ValidBinary!op&&op!="~"){
		return mixin("this "~op~" e.dℕ");
	}
	final opBinaryRight(string op)(ℕ e)if(ValidBinary!op&&op!="~"){
		return mixin("e.dℕ "~op~" this");
	}

	final opBinary(string op)(real e)if(ValidBinary!op&&op!="~"){
		return mixin("this "~op~" e.dFloat");
	}
	final opBinaryRight(string op)(real e)if(ValidBinary!op&&op!="~"){
		return mixin("e.dFloat "~op~" this");
	}

	final opIndex(DExpr rhs){ return dIndex(this,rhs); }
	

	mixin template Constant(){
		override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
		override int freeVarsImpl(scope int delegate(DVar) dg){ return 0; }
		override DExpr substitute(DVar var,DExpr e){ assert(var !is this); return this; }
		override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){ assert(fun !is this); return this; }
		override DExpr incBoundVar(int di,bool bindersOnly){ return this; }
		override DExpr simplifyImpl(DExpr facts){ return this; }
	}
}
alias DExprSet=SetX!DExpr;
class DVar: DExpr{
	string name;
	private this(string name){ this.name=name; }
	override string toStringImpl(Format formatting,Precedence prec){
		if(formatting==Format.sympy||formatting==Format.matlab||formatting==Format.mathematica){
			return asciify(name);
			auto name=this.name.to!dstring; // TODO: why necessary? Phobos bug?
			name=name.replace("ξ"d,"xi"d);
			//pragma(msg, cast(dchar)('₀'+1));
			foreach(x;0..10)
				name=name.replace(""d~cast(dchar)('₀'+x),""d~cast(dchar)('0'+x));
			return name.to!string;
		}
		return name;
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
	override int freeVarsImpl(scope int delegate(DVar) dg){ return dg(this); }
	override DExpr substitute(DVar var,DExpr e){ return this is var?e:this; }
	override DExpr substituteFun(DFunVar var,DExpr q,DVar[] args,SetX!DVar context){ return this; }
	override DVar incBoundVar(int di,bool bindersOnly){ return this; }
	override DExpr simplifyImpl(DExpr facts){
		if(cast(DBoundVar)this||cast(DTmpBoundVar)this) return this;
		// TODO: make more efficient! (e.g. keep hash table in product expressions)
		foreach(f;facts.factors){
			if(auto ivr=cast(DIvr)f){
				if(ivr.type!=DIvr.Type.eqZ) continue;
				if(ivr.e.getCanonicalFreeVar()!is this) continue; // TODO: make canonical var smart
				SolutionInfo info;
				SolUse usage={caseSplit:false,bound:false};
				auto sol=ivr.e.solveFor(this,zero,usage,info);
				if(!sol||info.needCaseSplit) continue; // TODO: make more efficient!
				// TODO: we probably want to do a case split here.
				// TODO: allow this simplification to be disabled temporarily (for delta expressions)
				return sol;
			}
		}
		return this;
	}
}
DVar[string] dVarCache; // TODO: caching desirable? (also need to update parser if not)
DVar dVar(string name){
	if(name in dVarCache) return dVarCache[name];
	return dVarCache[name]=new DVar(name);
}

class DBoundVar: DVar{
	int i;
	private this(int i){ this.i=i; super("ξ"~lowNum(i)); }
	override DBoundVar incBoundVar(int di,bool bindersOnly){
		if(bindersOnly) return this;
		return dBoundVar(i+di);
	}
}
DBoundVar[int] uniqueMapBound;
DBoundVar dBoundVar(int i){
	return i !in uniqueMapBound ?
		uniqueMapBound[i]=new DBoundVar(i):
		uniqueMapBound[i];
}

class DTmpBoundVar: DVar{
	int i;
	static int curi=0;
	this(string name){ super(name); i=curi++; }
	override string toStringImpl(Format formatting,Precedence prec){
		if(name=="tmp") // Can be convenient for debugging. TODO: get rid of "tmp" vars
			return name~(cast(void*)this).to!string;
		return super.toStringImpl(formatting,prec);
	}
} // TODO: get rid of this!

DTmpBoundVar freshVar(string name="tmp"){ return new DTmpBoundVar(name); } // TODO: get rid of this!


DVar theDε;
DVar dε(){ return theDε?theDε:(theDε=new DVar("ε")); }


class Dℕ : DExpr{
	ℕ c;
	private this(ℕ c){ this.c=c; }
	override string toStringImpl(Format formatting,Precedence prec){
		string r=text(c);
		if(formatting==Format.maple){
			if(c<0) r="("~r~")";
		}else if(prec>Precedence.uminus&&c<0)
			r="("~r~")";
		return r;
	}
	override bool isFraction(){ return true; }
	override ℕ[2] getFraction(){ return [c,ℕ(1)]; }

	mixin Constant;
}

Dℕ[ℕ] uniqueMapDℕ; // TODO: get rid of this!
Dℕ dℕ(ℕ c){
	if(c in uniqueMapDℕ) return uniqueMapDℕ[c];
	return uniqueMapDℕ[c]=new Dℕ(c);
}
DExpr dℕ(long c){ return dℕ(ℕ(c)); }

Dℕ nthRoot(Dℕ x,ℕ n){
	ℕ k=1,r=0;
	while(k<x.c) k*=2;
	for(;k;k/=2){
		ℕ c=r+k;
		if(pow(c,n)<=x.c)
			r=c;
	}
	return pow(r,n)==x.c?dℕ(r):null;
}

class DFloat : DExpr{
	real c;
	private this(real c){ this.c=c; }
	override string toStringImpl(Format formatting,Precedence prec){
		import std.format;
		string r=format("%.16e",c);
		if(formatting==Format.mathematica){
			if(r.canFind("e"))
				r="("~r.replace("e","*10^")~")";
		}else if(formatting==Format.maple){
			if(c<0) r="("~r~")";
		}else if(prec>Precedence.uminus&&c<0)
			r="("~r~")";
		return r;
	}

	mixin Constant;
}

//DFloat[real] uniqueMapDFloat; // TODO: get rid of this!
DExpr dFloat(real c){
	import std.math: floor;
	import std.format: format;
	if(c==1) return one;
	if(c==0) return zero;
	//if(floor(c)==c) return dℕ(); // TODO: fix this
	//if(c in uniqueMapDFloat) return uniqueMapDFloat[c];
	//return uniqueMapDFloat[c]=new DFloat(c);
	return new DFloat(c);
}

class DE: DExpr{
	override string toStringImpl(Format formatting,Precedence prec){
		if(formatting==Format.maple) return "exp(1)";
		if(formatting==Format.mathematica) return "E";
		return "e";
	} // TODO: maple
	mixin Constant;
}
private static DE theDE;
@property DE dE(){ return theDE?theDE:(theDE=new DE); }

class DΠ: DExpr{
	override string toStringImpl(Format formatting,Precedence prec){ // TODO: maple
		if(formatting==Format.matlab) return "pi";
		if(formatting==Format.maple) return "Pi";
		if(formatting==Format.mathematica) return "Pi";
		else return "π";
	}
	mixin Constant;
}
private static DΠ theDΠ;
@property DΠ dΠ(){ return theDΠ?theDΠ:(theDΠ=new DΠ); }

private static DExpr theOne;
@property DExpr one(){ return theOne?theOne:(theOne=1.dℕ);}

private static DExpr theMOne;
@property DExpr mone(){ return theMOne?theMOne:(theMOne=(-1).dℕ);}

private static DExpr theZero;
@property DExpr zero(){ return theZero?theZero:(theZero=0.dℕ);}

abstract class DOp: DExpr{
	abstract @property string symbol(Format formatting);
	bool rightAssociative(){ return false; }
	abstract @property Precedence precedence();
	protected final string addp(Precedence prec, string s, Precedence myPrec=Precedence.invalid){
		if(myPrec==Precedence.invalid) myPrec=precedence;
		return prec > myPrec||rightAssociative&&prec==precedence? "(" ~ s ~ ")":s;
	}
}


abstract class DAssocOp: DOp{
	DExpr[] operands;
	protected mixin template Constructor(){ private this(DExpr[] e)in{assert(e.length>1); }body{ operands=e; } }
	override string toStringImpl(Format formatting,Precedence prec){
		string r;
		foreach(o;operands) r~=symbol(formatting)~o.toStringImpl(formatting,prec);
		return addp(prec, r[symbol(formatting).length..$]);
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		foreach(a;operands)
			if(auto r=dg(a))
				return r;
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		foreach(a;operands)
			if(auto r=a.freeVarsImpl(dg))
				return r;
		return 0;
	}
}


abstract class DCommutAssocOp: DOp{
	DExprSet operands;
	protected mixin template Constructor(){ private this(DExprSet e)in{assert(e.length>1); }body{ operands=e; } }
	override string toStringImpl(Format formatting,Precedence prec){
		string r;
		auto ops=operands.array.map!(a=>a.toStringImpl(formatting,precedence)).array;
		sort(ops);
		foreach(o;ops) r~=symbol(formatting)~o;
		return addp(prec, r[symbol(formatting).length..$]);
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		foreach(a;operands)
			if(auto r=dg(a))
				return r;
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		foreach(a;operands)
			if(auto r=a.freeVarsImpl(dg))
				return r;
		return 0;
	}
}

MapX!(TupleX!(typeof(typeid(DExpr)),DExpr[]),DExpr) uniqueMapAssoc;
MapX!(TupleX!(typeof(typeid(DExpr)),DExprSet),DExpr) uniqueMapCommutAssoc;
MapX!(TupleX!(typeof(typeid(DExpr)),DExpr,DExpr),DExpr) uniqueMapNonCommutAssoc;

auto uniqueDExprAssoc(T)(DExpr[] e){
	auto t=tuplex(typeid(T),e);
	if(t in uniqueMapAssoc) return cast(T)uniqueMapAssoc[t];
	auto r=new T(e);
	uniqueMapAssoc[t]=r;
	return r;
}
auto uniqueDExprCommutAssoc(T)(DExprSet e){
	auto t=tuplex(typeid(T),e);
	if(t in uniqueMapCommutAssoc) return cast(T)uniqueMapCommutAssoc[t];
	auto r=new T(e);
	uniqueMapCommutAssoc[t]=r;
	return r;
}
auto uniqueDExprNonCommutAssoc(T)(DExpr a, DExpr b){
	auto t=tuplex(typeid(T),a,b);
	if(t in uniqueMapNonCommutAssoc) return cast(T)uniqueMapNonCommutAssoc[t];
	auto r=new T(a,b);
	uniqueMapNonCommutAssoc[t]=r;
	return r;
}
MapX!(TupleX!(typeof(typeid(DExpr)),DExpr),DExpr) uniqueMapUnary;
auto uniqueDExprUnary(T)(DExpr a){
	if(auto r=T.constructHook(a)) return r;
	auto t=tuplex(typeid(T),a);
	if(t in uniqueMapUnary) return cast(T)uniqueMapUnary[t];
	auto r=new T(a);
	uniqueMapUnary[t]=r;
	return r;
}
string makeConstructorAssoc(T)(){
	enum Ts=__traits(identifier, T);
	return "auto " ~ lowerf(Ts)~"(DExpr[] f){"
		~"if(f.length==1) return f[0];"
		~"if(auto r="~Ts~".constructHook(f)) return r;"
		~"return uniqueDExprAssoc!("~__traits(identifier,T)~")(f);"
		~"}"
		~"auto " ~ lowerf(Ts)~"(DExpr e1,DExpr e2){"
		~"  return "~lowerf(Ts)~"([e1,e2]);"
		~"}";
}
string makeConstructorCommutAssoc(T)(){
	enum Ts=__traits(identifier, T);
	return "auto " ~ lowerf(Ts)~"(DExprSet f){"
		~"if(f.length==1) return f.element;"
		~"if(auto r="~Ts~".constructHook(f)) return r;"
		~"return uniqueDExprCommutAssoc!("~__traits(identifier,T)~")(f);"
		~"}"
		~"auto " ~ lowerf(Ts)~"(DExpr e1,DExpr e2){"
		~"  DExprSet a;"~Ts~".insert(a,e1);"~Ts~".insert(a,e2);"
		~"  return "~lowerf(Ts)~"(a);"
		~"}";
}

string makeConstructorNonCommutAssoc(T)(){
	enum Ts=__traits(identifier, T);
	return "auto " ~ lowerf(Ts)~"(DExpr e1, DExpr e2){ "
		~"static if(__traits(hasMember,"~Ts~",`constructHook`)){"
		~"  if(auto r="~Ts~".constructHook(e1,e2)) return r;}"
		~"return uniqueDExprNonCommutAssoc!("~__traits(identifier,T)~")(e1,e2);"
		~"}";
}

string makeConstructorUnary(T)(){
	return "auto " ~ lowerf(__traits(identifier, T))~"(DExpr e){ return uniqueDExprUnary!("~__traits(identifier,T)~")(e); }";
}

class DPlus: DCommutAssocOp{
	alias summands=operands;
	mixin Constructor;
	override @property Precedence precedence(){ return Precedence.plus; }
	override @property string symbol(Format formatting){ return "+"; }

	override DExpr substitute(DVar var,DExpr e){
		DExprSet res;
		foreach(s;summands) insert(res,s.substitute(var,e));
		return dPlus(res);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		DExprSet res;
		foreach(s;summands) insert(res,s.substituteFun(fun,q,args,context));
		return dPlus(res);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		DExprSet res;
		foreach(s;summands) insert(res,s.incBoundVar(di,bindersOnly));
		return dPlus(res);
	}

	static void insert(ref DExprSet summands,DExpr summand)in{assert(!!summand);}body{
		if(summand is zero) return;
		if(summand in summands){
			summands.remove(summand);
			insert(summands,2*summand);
		}else{
			summands.insert(summand);
		}
	}
	static MapX!(Q!(DExprSet,DExpr,DExpr),DExprSet) insertMemo;
	static void insertAndSimplify(ref DExprSet summands,DExpr summand,DExpr facts){
		// swCount++;sw.start(); scope(exit) sw.stop();
		if(q(summands,summand,facts) in insertMemo){
			summands=insertMemo[q(summands,summand,facts)].dup;
			return;
		}
		auto origIndex=q(summands.dup,summand,facts);
		scope(exit) insertMemo[origIndex]=summands.dup;
		summand=summand.simplify(facts);
		if(auto dp=cast(DPlus)summand){
			foreach(s;dp.summands)
				insertAndSimplify(summands,s,facts);
			return;
		}
		if(auto p=cast(DPow)summand){
			if(cast(DPlus)p.operands[0]){
				auto expanded=expandPow(p);
				if(expanded !is p){
					insertAndSimplify(summands,expanded,facts);
					return;
				}
			}
		}

		DExpr combine(DExpr e1,DExpr e2,DExpr facts){
			if(e1 is zero) return e2;
			if(e2 is zero) return e1;
			if(e1 is e2) return 2*e1;


			static DExpr combineFractions(DExpr e1,DExpr e2){
				if(e1.isFraction()&&e2.isFraction()){
					auto nd1=e1.getFraction();
					auto nd2=e2.getFraction();
					return dℕ(nd1[0]*nd2[1]+nd2[0]*nd1[1])/dℕ(nd1[1]*nd2[1]);
				}
				return null;
			}
			
			if(auto r=combineFractions(e1,e2)) return r;

			static DExpr combineWithFloat(DExpr e1,DExpr e2){
				if(auto f=cast(DFloat)e1){
					if(auto g=cast(DFloat)e2)
						return (f.c+g.c).dFloat;
					if(e2.isFraction()){
						auto nd=e2.getFraction();
						return (f.c+toReal(nd[0])/toReal(nd[1])).dFloat;
					}
				}
				return null;
			}
			static DExpr combineFloat(DExpr e1,DExpr e2){
				if(auto r=combineWithFloat(e1,e2)) return r;
				if(auto r=combineWithFloat(e2,e1)) return r;
				return null;
			}

			if(auto r=combineFloat(e1,e2)) return r;

			if(auto r=recursiveCombine(e1,e2,facts))
				return r;

			static DExpr combineIvr(DExpr e1,DExpr e2,DExpr facts){
				if(auto ivr1=cast(DIvr)e1){
					if(ivr1.type is DIvr.Type.eqZ){
						if(e2 is dIvr(DIvr.Type.lZ,ivr1.e).simplify(facts))
							return dIvr(DIvr.Type.leZ,ivr1.e);
						if(e2 is dIvr(DIvr.Type.lZ,-ivr1.e).simplify(facts))
							return dIvr(DIvr.Type.leZ,-ivr1.e);
						if(e2 is dIvr(DIvr.Type.neqZ,ivr1.e).simplify(facts))
							return one;
					}else if(ivr1.type is DIvr.Type.leZ){
						if(e2 is dIvr(DIvr.Type.leZ,-ivr1.e).simplify(facts))
							return 2*dIvr(DIvr.Type.eqZ,ivr1.e)+dIvr(DIvr.Type.neqZ,ivr1.e);
						if(e2 is dIvr(DIvr.Type.lZ,-ivr1.e).simplify(facts))
							return one;
					}
				}
				return null;
			}
			if(auto r=combineIvr(e1,e2,facts)) return r;
			if(auto r=combineIvr(e2,e1,facts)) return r;
			
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
		DVar tmp=freshVar(); // TODO: get rid of this!
		// dw("!! ",summands);
		foreach(s;summands){
			if(auto dint=cast(DInt)s){
				if(cast(DBoundVar)dint.var&&dint.var !is dBoundVar(1)) return null;
				integralSummands.insert(dint.getExpr(tmp));
				integrals.insert(dint);
			}
		}
		if(integralSummands.length){
			auto integralSum=dPlus(integralSummands).simplify(facts);
			auto simplSummands=integralSum.summands.setx;
			if(simplSummands.setMinus(integralSummands).length){
				summands=summands.setMinus(integrals);
				return dPlus(summands)+dIntSmp(tmp,dPlus(simplSummands));
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
		if(common !is one){
			if(!common.isFraction()){
				auto sum=(sum1+sum2).simplify(facts);
				auto summands=sum.summands.setx; // TODO: improve performance!
				if(sum1!in summands||sum2!in summands)
					return dDistributeMult(sum,common); // was: sum*common
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
		if(auto r=integralSimplify(summands,facts)) return r;
		return dPlus(summands);
	}

	static DExpr constructHook(DExprSet operands){
		if(operands.length==0) return zero;
		return null;
	}
}

class DMult: DCommutAssocOp{
	alias factors=operands;
	//mixin Constructor;
	private this(DExprSet e)in{assert(e.length>1); }body{ assert(one !in e,text(e)); operands=e; }
	override @property Precedence precedence(){ return Precedence.mult; }
	override string symbol(Format formatting){
		if(formatting==Format.maple||formatting==Format.sympy||formatting==Format.mathematica) return "*";
		else if(formatting==Format.matlab) return ".*";
		else return "·";
	}
	override string toStringImpl(Format formatting,Precedence prec){
		auto frac=this.getFractionalFactor().getFraction();
		if(frac[0]<0){
			if(formatting==Format.maple){
				return "(-"~(-this).toStringImpl(formatting,Precedence.uminus)~")";
			}else{
				return addp(prec,"-"~(-this).toStringImpl(formatting,Precedence.uminus),Precedence.uminus);
			}
		}
		//if(frac[0]!=1&&frac[1]!=1) // TODO
		// TODO: use suitable data structures
		return super.toStringImpl(formatting,prec);
	}
	override DExpr substitute(DVar var,DExpr e){
		if(auto evar=cast(DVar)e){ // TODO: make this unnecessary, this is a hack to improve performance
			if(!hasFreeVar(evar)){
				DExprSet res;
				foreach(f;factors) res.insert(f.substitute(var,e));
				return dMult(res);
			}	
		}
		DExprSet res;
		foreach(f;factors) insert(res,f.substitute(var,e));
		return dMult(res);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		DExprSet res;
		foreach(f;factors) insert(res,f.substituteFun(fun,q,args,context));
		return dMult(res);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		DExprSet res;
		foreach(f;factors) res.insert(f.incBoundVar(di,bindersOnly)); // TODO: ok?
		return dMult(res);
	}

	override bool isFraction(){ return factors.all!(a=>a.isFraction()); }
	override ℕ[2] getFraction(){
		ℕ n=1,d=1;
		foreach(f;factors){
			auto nd=f.getFraction();
			n*=nd[0], d*=nd[1];
		}
		return [n,d];
	}

	static MapX!(Q!(DExprSet,DExpr,DExpr),DExprSet) insertMemo;
	static void insert(ref DExprSet factors,DExpr factor,DExpr facts=null)in{assert(!!factor);}body{
		if(q(factors,factor,facts) in insertMemo){
			factors=insertMemo[q(factors,factor,facts)].dup;
			return;
		}
		auto origIndex=q(factors.dup,factor,facts);
		scope(exit) insertMemo[origIndex]=factors.dup;
		//if(zero in factors||factor is zero){ factors.clear(); factors.insert(zero); return; }
		if(auto dm=cast(DMult)factor){
			foreach(f;dm.factors)
				insert(factors,f,facts);
			return;
		}
		// TODO: use suitable data structures
		static DExpr combine(DExpr e1,DExpr e2,DExpr facts){
			if(e1 is one) return e2;
			if(e2 is one) return e1;
			static DExpr combineInf(DExpr e1,DExpr e2){
				if(e1 is dInf && e2 is mone) return null;
				if(e2 is dInf && e1 is mone) return null;
				if(e1 is dInf){
					if(e2.mustBeLessThanZero()) return -dInf;
					if((-e2).mustBeLessThanZero()) return dInf;
				}else if(e1 is -dInf){
					if(auto r=combineInf(dInf,e2))
						return -r;
				}
				return null;
			}
			if(auto r=combineInf(e1,e2)) return r;
			if(auto r=combineInf(e2,e1)) return r;
			if(e1 is e2) return e1^^2;
			if(e1 is zero||e2 is zero) return zero;
			if(e2.isFraction()) swap(e1,e2);
			if(e1.isFraction()){
				auto nd1=e1.getFraction();
				if(nd1[0]==1&&nd1[1]==1) return e2;
				if(e2.isFraction()){
					auto nd2=e2.getFraction();
					auto n=nd1[0]*nd2[0],d=nd1[1]*nd2[1];
					auto g=gcd(n,d);
					if(g==0) return null;
					if(g==1&&(nd1[0]==1&&nd2[1]==1||nd1[1]==1&&nd2[0]==1))
						return null;
					return dℕ(n/g)/dℕ(d/g);
				}
			}
			if(e1.isFraction()||cast(DFloat)e1){
				if(auto p=cast(DPlus)e2){
					DExprSet summands;
					foreach(s;p.summands) summands.insert(e1*s);
					return dPlus(summands);
				}
			}

			static DExpr combineWithFloat(DExpr e1,DExpr e2){
				if(auto f=cast(DFloat)e1){
					if(auto g=cast(DFloat)e2)
						return (f.c*g.c).dFloat;
					if(e2.isFraction()){
						auto nd=e2.getFraction();
						return (f.c*toReal(nd[0])/toReal(nd[1])).dFloat;
					}
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
			if(!cast(Dℕ)e1&&!cast(Dℕ)e2 && e1 is -e2) return -e1^^2;
			if(auto p=cast(DPow)e1){
				static bool testValid(DExpr e1,DExpr e2){
					e1=e1.simplify(one); e2=e2.simplify(one);
					if(e1.isFraction&&e2.isFraction()){
						auto nd=e2.getFraction();
						if(nd[0]%nd[1]!=0&&abs(nd[0])>abs(nd[1])){
							return false;
						}
					}
					return true;
				}

				if(p.operands[0] is e2){
					if(!cast(Dℕ)e2 && testValid(p.operands[0],p.operands[1]+1))
						return p.operands[0]^^(p.operands[1]+1);
				}
				if(p.operands[0] is -e2){
					if(!cast(Dℕ)e2 && testValid(p.operands[0],p.operands[1]+1))
						return -p.operands[0]^^(p.operands[1]+1);
				}
				if(auto d=cast(Dℕ)p.operands[0]){
					if(auto e=cast(Dℕ)e2){
						if(d.c==-e.c && testValid(-d,p.operands[1]+1))
							return -d^^(p.operands[1]+1);
					}
				}
				if(auto pf=cast(DPow)e2){
					if(p.operands[0] is pf.operands[0]){
						if(testValid(p.operands[0],p.operands[1]+pf.operands[1]))
							return p.operands[0]^^(p.operands[1]+pf.operands[1]);
					}
					static DExpr tryCombine(DExpr a,DExpr b,DExpr facts){
						if(cast(DMult)a||cast(DMult)b) return null; // TODO: ok?
						if(cast(Dℕ)a&&cast(Dℕ)b&&a is mone||b is mone) return null;
						DExprSet s;
						DMult.insert(s,a,facts);
						DMult.insert(s,b,facts);
						if(a !in s || b !in s)
							return dMult(s);
						return null;
					}
					auto exp1=p.operands[1],exp2=pf.operands[1];
					if(exp1 is exp2){
						auto a=p.operands[0],b=pf.operands[0];
						if(auto r=tryCombine(a,b,facts))
							return r^^exp1;
					}
					if(exp1 is -exp2){
						auto a=p.operands[0],b=1/pf.operands[0];
						if(auto r=tryCombine(a,b,facts))
							return r^^exp1;
					}
				}
			}
			if(cast(DIvr)e2) swap(e1,e2);
			if(auto ivr1=cast(DIvr)e1){ // TODO: this should all be done by DIvr.simplify instead
				if(facts){ // TODO: this does not actually combine all facts optimally
					auto simple=e2.simplify(e1*facts);
					if(simple!is e2) return simple*e1;
				}
				if(auto ivr2=cast(DIvr)e2) with(DIvr.Type){
					if(facts){ // TODO: this does not actually combine all facts optimally
						auto simple=e1.simplify(e2*facts);
						if(simple!is e1) return simple*e2;
					}
					// combine a≤0 and -a≤0 to a=0
					if(ivr1.type==leZ&&ivr2.type==leZ){
						if(ivr1.e is -ivr2.e){
							auto r=dIvr(eqZ,ivr1.e);
							if(facts) r=r.simplify(facts);
							return r;
						}
						if(ivr1.e.mustBeLessThan(ivr2.e)) return e2;
						if(ivr2.e.mustBeLessThan(ivr1.e)) return e1;

						// TODO: better inconsistency checks!
						foreach(v;ivr1.freeVars()) with(BoundStatus){
							DExpr b1,b2;
							auto s1=ivr1.getBoundForVar(v,b1);
							auto s2=ivr2.getBoundForVar(v,b2);
							if(s1 is fail || s2 is fail) continue;
							// if(s1==s2) // TODO
							if(s1 != s2){
								if(s1 is lowerBound){
									if(b2.mustBeLessThan(b1))
										return zero;
								}else{
									assert(s1 is upperBound);
									if(b1.mustBeLessThan(b2))
										return zero;
								}
							}
						}

					}
					if(ivr2.type==eqZ) swap(ivr1,ivr2);
					if(ivr1.type==eqZ){
						if(ivr1.e is ivr2.e||ivr1.e is -ivr2.e){ // TODO: jointly canonicalize
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
			/+// TODO: do we want auto-distribution?
			if(cast(DPlus)e1) return dDistributeMult(e1,e2);
			if(cast(DPlus)e2) return dDistributeMult(e2,e1);+/

			return null;
		}
		if(facts) factor=factor.simplify(facts);
		foreach(f;factors){
			if(auto nwf=combine(f,factor,facts)){
				factors.remove(f);
				if(factors.length||nwf !is one)
					insert(factors,nwf,facts);
				return;
			}
		}
		assert(factors.length==1||one !in factors);
		factors.insert(factor);
	}
	override DExpr simplifyImpl(DExpr facts){
		// TODO: this is a mayor bottleneck!
		DExprSet myFactors;
		DExprSet myFacts;
		foreach(f;this.factors) if(auto d=cast(DDelta)f) facts=facts*dIvr(DIvr.Type.eqZ,d.e).simplify(facts);
		foreach(f;this.factors){
			if(cast(DIvr)f) insert(myFacts,f,facts);
			else myFactors.insert(f);
		}
		auto myFactsM=dMult(myFacts);
		DExpr newFacts=facts*myFactsM;
		DExprSet simpFactors;
		foreach(f;myFactors) insert(simpFactors,f,newFacts);
		return dMult(simpFactors)*myFactsM;
	}
	static DExpr constructHook(DExprSet operands){
		if(operands.length==0) return one;
		return null;
	}
}

mixin(makeConstructorCommutAssoc!DMult);
mixin(makeConstructorCommutAssoc!DPlus);

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

DExpr getFractionalFactor(DExpr e){
	DExpr r=one;
	foreach(f;e.factors)
		if(f.isFraction())
			r=r*f;
	return r;
}

DExpr dMinus(DExpr e1,DExpr e2){ return e1+-e2; }

abstract class DBinaryOp: DOp{
	DExpr[2] operands;
	protected mixin template Constructor(){ private this(DExpr e1, DExpr e2){ operands=[e1,e2]; } }
	override string toStringImpl(Format formatting,Precedence prec){
		return addp(prec, operands[0].toStringImpl(formatting,precedence) ~ symbol(formatting) ~ operands[1].toStringImpl(formatting,precedence));
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		foreach(a;operands)
			if(auto r=dg(a))
				return r;
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		foreach(a;operands)
			if(auto r=a.freeVarsImpl(dg))
				return r;
		return 0;
	}
}

class DPow: DBinaryOp{
	mixin Constructor;
	override Precedence precedence(){ return Precedence.pow; }
	override @property string symbol(Format formatting){
		if(formatting==Format.matlab) return ".^";
		else if(formatting==Format.sympy) return "**";
		else return "^";
	}
	override bool rightAssociative(){ return true; }

	override bool isFraction(){ return cast(Dℕ)operands[0] && cast(Dℕ)operands[1]; }
	override ℕ[2] getFraction(){
		auto d=cast(Dℕ)operands[0];
		assert(d && operands[1] is -one);
		return [ℕ(1),d.c];
	}

	override string toStringImpl(Format formatting,Precedence prec){
		auto frc=operands[1].getFractionalFactor().getFraction();
		if(frc[0]<0){
			if(formatting==Format.matlab){
				addp(prec,text(dIvr(DIvr.Type.neqZ,operands[0]).toStringImpl(formatting,Precedence.div),"./",
							   (operands[0]+dIvr(DIvr.Type.eqZ,operands[0])).toStringImpl(formatting,Precedence.div)),
					 Precedence.div);
			}else{
				auto pre=formatting==Format.default_?"⅟":"1/";
				return addp(prec,pre~(operands[0]^^-operands[1]).toStringImpl(formatting,Precedence.div),Precedence.div);
			}
		}
		// also nice, but often hard to read: ½⅓¼⅕⅙
		if(formatting==Format.default_){		
			if(auto c=cast(Dℕ)operands[1])
				return addp(prec,operands[0].toStringImpl(formatting,Precedence.pow)~highNum(c.c));
			if(auto c=cast(DPow)operands[1]){
				if(auto e=cast(Dℕ)c.operands[1]){
					if(e.c==-1){
						if(auto d=cast(Dℕ)c.operands[0]){
							if(2<=d.c&&d.c<=4)
								return text("  √∛∜"d[cast(size_t)d.c.toLong()],overline(operands[0].toStringImpl(formatting,precedence.none)));
						}
					}
				}
			}
		}
		/+if(formatting==Format.matlab)
		 return text("fixNaN(",super.toStringImpl(formatting,prec),")");+/// TODO: why doesn't this work?
		return super.toStringImpl(formatting,prec);
	}

	override DExpr substitute(DVar var,DExpr e){
		return operands[0].substitute(var,e)^^operands[1].substitute(var,e);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return operands[0].substituteFun(fun,q,args,context)^^operands[1].substituteFun(fun,q,args,context);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return operands[0].incBoundVar(di,bindersOnly)^^operands[1].incBoundVar(di,bindersOnly);
	}

	static DExpr constructHook(DExpr e1,DExpr e2){
		return staticSimplify(e1,e2);
	}

	private static DExpr staticSimplify(DExpr e1,DExpr e2,DExpr facts=one){
		auto ne1=e1.simplify(facts);
		auto ne2=e2.simplify(facts);
		if(ne1!is e1||ne2!is e2) return dPow(ne1,ne2).simplify(facts);
		if(e1 !is mone) if(auto c=cast(Dℕ)e1) if(c.c<0) return mone^^e2*dℕ(-c.c)^^e2;
		if(auto m=cast(DMult)e1){
			DExprSet outside;
			DExprSet within;
			bool nat=!!cast(Dℕ)e2;
			foreach(f;m.operands){
				if(nat||dIvr(DIvr.Type.lZ,f).simplify(facts) is zero)
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
			if(p.operands[0]!is mone){
				return (dIvr(DIvr.Type.lZ,p.operands[0])*(mone^^p.operands[1])^^e2*(-p.operands[0])^^(p.operands[1]*e2)+
						dIvr(DIvr.Type.leZ,-p.operands[0])*p.operands[0]^^(p.operands[1]*e2)).simplify(facts);
			}
		}
		if(e1 is one||e2 is zero) return one;
		if(e1 is -one && e2 is -one) return -one;
		if(e2 is one) return e1;
		if(e1.mustBeZeroOrOne()&&(-e2).mustBeLessOrEqualZero())
			return (dIvr(DIvr.Type.neqZ,e2)*e1+dIvr(DIvr.Type.eqZ,e2)).simplify(facts);
		if(auto d=cast(Dℕ)e2){
			if(auto c=cast(Dℕ)e1){
				if(d.c>0) return dℕ(pow(c.c,d.c));
				else if(d.c != -1) return dℕ(pow(c.c,-d.c))^^mone;
			}
		}
		if(auto l=cast(DLog)e2){ // TODO: more principled way of handling this, with more cases
			if(auto e=cast(DE)e1)
				return l.e;
			if(auto d=cast(Dℕ)e1){
				if(auto c=cast(Dℕ)l.e){
					if(c.c<d.c) return c^^dLog(d);
					else return null;
				}else return l.e^^dLog(d);
			}
		}
		if(auto c=cast(Dℕ)e1){ // TODO: more simplifications with constant base
			foreach(f;e2.factors){
				if(!f.isFraction()) continue;
				auto nd=f.getFraction();
				if(nd[0]!=1||nd[1]>5) continue; // TODO: 5 ok?
				if(auto r=nthRoot(c,nd[1]))
					return r^^(e2/f);
			}
		}
		if(cast(DPlus)e1){
			if(auto r=expandPow(e1,e2))
				return r;
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
			if(e2.isFraction()){
				auto nd=e2.getFraction();
				return (f1.c^^(toReal(nd[0])/toReal(nd[1]))).dFloat;
			}
		}
		if(e1.isFraction()){
			if(auto f2=cast(DFloat)e2){
				auto nd=e1.getFraction();
				return ((toReal(nd[0])/toReal(nd[1]))^^f2.c).dFloat;
			}
		}
		if(auto fct=factorDIvr!(e=>e^^e2)(e1)) return fct.simplify(facts);
		if(auto fct=factorDIvr!(e=>e1^^e)(e2)) return fct.simplify(facts);
		return null;
	}

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(operands[0],operands[1],facts);
		return r?r:this;
	}
}

mixin(makeConstructorNonCommutAssoc!DPow);
DExpr dDiv(DExpr e1,DExpr e2){ return e1*e2^^mone; }


DExpr expandPow(DExpr e1,DExpr e2,long limit=-1){
	auto c=cast(Dℕ)e2;
	if(!c||c.c<=0||limit>=0&&c.c>limit) return null;
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
	auto ncrange=nC(c.c);
	for(ℕ i=0,j=c.c;i<=c.c;i++,j--,ncrange.popFront())
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
		r~=Zero(-c/b,dIvr(DIvr.Type.eqZ,a));
		r~=Zero((-b-(b^^2-4*a*c)^^(one/2))/(2*a),dIvr(DIvr.Type.neqZ,a)*dIvr(DIvr.Type.leZ,-(b^^2-4*a*c)));
		r~=Zero((-b+(b^^2-4*a*c)^^(one/2))/(2*a),dIvr(DIvr.Type.neqZ,a)*dIvr(DIvr.Type.lZ,-(b^^2-4*a*c)));
		return r;
	}
}

bool hasFactor(DExpr e,DExpr factor){
	foreach(f;e.factors) if(factor is f) return true;
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

DExpr polyNormalize(DExpr e,DVar v,long limit=-1){
	DExprSet normSet;
	Louter: foreach(s;e.summands){
		if(s.hasFreeVar(v)){
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
						if(norm !is f){
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
	if(r !is e) return polyNormalize(r,v,limit);
	return r;

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
			if(f is v){
				if(!addCoeff(1,s/v))
					return DPolynomial.init;
				continue Lsum;
			}
			auto p=cast(DPow)f;
			if(!p||p.operands[0] !is v) continue;
			auto c=cast(Dℕ)p.operands[1];
			if(!c) continue;
			auto coeff=s/p;
			assert(c.c<=long.max);
			if(!addCoeff(c.c.toLong(),coeff))
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
	if(p.degree>1) return [null,null];
	return [p.coefficients.get(0,zero),p.coefficients.get(1,zero)];
}


abstract class DUnaryOp: DOp{
	DExpr operand;
	protected mixin template Constructor(){ private this(DExpr e){ operand=e; } }
	override string toStringImpl(Format formatting,Precedence prec){
		return addp(prec, symbol(formatting)~operand.toStringImpl(formatting,precedence));
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
	if(auto c=cast(Dℕ)e) return c.c==0;
	if(auto c=cast(DFloat)e){
		return approxEqual(c.c,0);
	}
	if(auto p=cast(DPow)e) return couldBeZero(p.operands[0]);
	if(cast(DGaussInt)e) return false;
	if(auto p=cast(DPlus)e){
		bool allLarge=true,allSmall=true;
		foreach(s;p.summands){
			if(!mustBeLessThanZero(s)) allSmall=false;
			if(!mustBeLessThanZero(-s)) allLarge=false;
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
			if(!mustBeLessOrEqualZero(-s))
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
	if(e is zero || e is one) return true;
	if(cast(DIvr)e) return true;
	return false;
}

bool mustBeLessOrEqualZero(DExpr e){
	bool mustBeLessOrEqualZeroImpl(DExpr e){
		if(cast(DΠ)e||cast(DE)e) return false;
		if(auto c=cast(Dℕ)e) return c.c<=0;
		if(auto c=cast(DFloat)e) return c.c<=0;
		if(auto p=cast(DPow)e){
			if(auto exp=cast(Dℕ)p.operands[1]){
				if(exp.c%2){
					return mustBeLessOrEqualZeroImpl(p.operands[0]);
				}
			}
		}
		return false;
	}
	if(mustBeLessOrEqualZeroImpl(e)) return true;
	bool mustBeGreaterOrEqualZeroImpl(DExpr e){
		if(cast(DΠ)e||cast(DE)e) return true;
		if(auto c=cast(Dℕ)e) return c.c>=0;
		if(auto c=cast(DFloat)e) return c.c>=0;
		if(auto p=cast(DPow)e){
			if(auto exp=cast(Dℕ)p.operands[1]){
				return !(exp.c%2)||mustBeLessOrEqualZeroImpl(-p.operands[0]);
			}
			if(p.operands[1].isFraction()) return true; // TODO: ok?
		}
		return false;		
	}
	if(auto m=cast(DMult)e){
		auto ff=m.getFractionalFactor();
		if(mustBeLessOrEqualZeroImpl(ff)){
			bool allGreaterEqual=true;
			foreach(f;m.factors){
				if(f.isFraction()) continue;
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

DExpr uglyFractionCancellation(DExpr e){
	ℕ ngcd=0,dlcm=1;
	foreach(s;e.summands){
		auto f=s.getFractionalFactor();
		assert(f.isFraction());
		auto nd=f.getFraction();
		if(nd[1]==0) continue;
		assert(nd[1]>0);
		ngcd=gcd(ngcd,abs(nd[0]));
		dlcm=lcm(dlcm,nd[1]);
	}
	if(!ngcd) return one;
	return dℕ(dlcm)/ngcd;
}

private static DExpr getCommonDenominator(DExpr e){
	DExpr r=one;
	foreach(s;e.summands){
		foreach(f;s.factors){
			if(auto p=cast(DPow)f){
				if(p.operands[1] !is mone) continue;
				auto den=p.operands[0];
				if(!r.hasFactor(den)) r=r*den;
			}
		}
	}
	return r;
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
			auto lZ=dIvr(DIvr.Type.lZ,cand).simplify(one)==one;
			auto gZ=dIvr(DIvr.Type.lZ,-cand).simplify(one)==one;
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
						auto evenParity=linearizeConstraints(dIvr(leZ,-parity*a),var);
						return dIvr(eqZ,a)*doIt(parity,ty,b*var+c,rhs)+
						  dIvr(neqZ,a)*(
						    dIvr(lZ,disc)*dIvr(leZ,(lhs-rhs).substitute(var,-b/(2*a)))
						    +dIvr(leZ,-disc)*(
						      evenParity*(
						        dIvr(leZ,-a)*dIvr(leZ,z1-var)*dIvr(leZ,var-z2)
						        + dIvr(leZ,a)*dIvr(leZ,z2-var)*dIvr(leZ,var-z1)
						      )+
						      dIvr(eqZ,evenParity)*(
						        dIvr(leZ,-a)*(dIvr(leZ,var-z1)+dIvr(neqZ,disc)*dIvr(leZ,z2-var)+dIvr(eqZ,disc)*dIvr(lZ,z2-var))
						        + dIvr(leZ,a)*(dIvr(leZ,var-z2)+dIvr(neqZ,disc)*dIvr(leZ,z1-var)+dIvr(eqZ,disc)*dIvr(lZ,z1-var))
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
				assert(e2.isFraction());
				auto nd=e2.getFraction();
				assert(nd[0]<0 && nd[1]>=0);
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
			auto n=cast(Dℕ)e2;
			if(n){
				if(n.c<0) return negatePower();
				if(!(n.c&1)){ // even integer power
					auto z2=rhs^^(1/n), z1=-z2;
					if(ty==leZ){
						static if(isDelta) assert(0);
						auto le=dIvr(leZ,-rhs)*doIt(mone,ty,e1,z1)*doIt(one,ty,e1,z2);
						auto ge=dIvr(leZ,rhs)+dIvr(lZ,-rhs)*(doIt(one,ty,e1,z1)+dIvr(neqZ,z2)*doIt(mone,ty,e1,z2));
						auto evenParity=linearizeConstraints(dIvr(leZ,-parity),var);
						return evenParity*le+dIvr(eqZ,evenParity)*ge;
					}else if(ty==eqZ){
						return dIvr(leZ,-rhs)*(doIt(one,ty,e1,z1)+dIvr(neqZ,z2)*doIt(one,ty,e1,z2));
					}else{
						assert(ty==neqZ);
						static if(isDelta) assert(0);
						return dIvr(lZ,rhs)+dIvr(leZ,-rhs)*doIt(one,ty,e1,z1)*doIt(one,ty,e1,z2);
					}
				}else{ // odd integer power
					return dIvr(leZ,-rhs)*doIt(parity,ty,e1,rhs^^(1/n))
						+dIvr(lZ,rhs)*doIt(parity,ty,e1,-(-rhs)^^(1/n));
				}
			}else if(e2.isFraction()){
				// fractional power. assume e1>=0. (TODO: make sure the analysis respects this)
				auto nd=e2.getFraction();
				if(nd[0]<0) return negatePower();
				assert(nd[0]>=0 && nd[1]>=0 && nd[1]!=1);
				auto r=dIvr(leZ,-rhs)*doIt(parity,ty,e1,(rhs^^(dℕ(nd[1])/nd[0])));
				if(ty==leZ){
					auto oddParity=linearizeConstraints(dIvr(lZ,parity),var);
					r=oddParity*dIvr(lZ,rhs)+r;
				}else if(ty==neqZ){
					static if(isDelta) assert(0);
					r=dIvr(lZ,rhs)+r;
				}
				return r;
			}
		}
		if(ty==leZ){
			static if(isDelta) assert(0);
			auto evenParity=linearizeConstraints(dIvr(leZ,-parity),var);
			return evenParity*dIvr(leZ,lhs-rhs)+dIvr(eqZ,evenParity)*dIvr(leZ,rhs-lhs);
		}
		static if(isDelta){
			if(lhs != var) unwind(); // TODO: get rid of this?
			auto diff=dAbs(dDiff(var,cond.e));
			auto pole=dIvr(eqZ,diff).linearizeConstraints(var).polyNormalize(var).simplify(one);
			DExprSet special;
			foreach(s;pole.summands){
				DExpr summand=null;
				if(s.hasFreeVar(var)) foreach(f;s.factors){
					if(!f.hasFreeVar(var)) continue;
					auto ivr=cast(DIvr)f;
					if(ivr&&ivr.type == eqZ){
						auto val=solveFor(ivr.e,var); // TODO: modify solveFor such that it only solves linear equations and returns additional constraints.
						if(!val || ivr.substitute(var,val).simplify(one) !is one)
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
	try return doIt(one,ty,cond.e.polyNormalize(var),zero);
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
	if(lhs is var){
		if(usage.bound) info.bound.setLower();
		return rhs;
	}
	if(auto p=cast(DPlus)lhs){
		auto ow=splitPlusAtVar(lhs,var);
		if(cast(DPlus)ow[1]){
			if(!usage.caseSplit) return null;
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
		if(p.operands[1] is mone){
			if(couldBeZero(rhs)){ // TODO: is this right? (This is guaranteed never to happen for dirac deltaas, so maybe optimize it out for that caller).
				info.needCaseSplit=true;
				if(usage.caseSplit) info.caseSplits~=SolutionInfo.CaseSplit(rhs,one);
			}
			auto r=p.operands[0].solveFor(var,one/rhs,usage,info);
			info.caseSplits=info.caseSplits.partition!(x=>x.expression is zero);
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
		auto constraints=one;
		foreach(ref x;info.caseSplits)
			constraints=constraints*dIvr(DIvr.Type.neqZ,x.constraint);
		auto r=constraints is zero?zero:constraints*s;
		foreach(ref x;info.caseSplits){
			auto curConstr=constraints.withoutFactor(dIvr(DIvr.Type.neqZ,x.constraint));
			auto psol=solveFor(x.expression,var);
			if(!psol) return null;
			r=r+curConstr*dIvr(DIvr.Type.eqZ,x.constraint)*psol;
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
	foreach(x;a) if(x !is b) r.insert(x);
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
		if(auto lg=cast(DLog)e)
			return dLog(doIt(lg.e));
		if(auto dl=cast(DDelta)e)
			return dDelta(doIt(dl.e));
		if(auto ivr=cast(DIvr)e)
			return dIvr(ivr.type,doIt(ivr.e));
		return e;
	}
	r.expr=doIt(e);
	return r;
}

DExpr factorDIvr(alias wrap)(DExpr e){
	auto h=getHoles!(x=>cast(DIvr)x,DIvr)(e);
	if(!h.holes.length) return null;
	DExpr doIt(DExpr facts,DExpr cur,size_t i){
		if(facts is zero) return zero;
		if(i==h.holes.length) return facts*wrap(cur);
		auto var=h.holes[i].var,expr=h.holes[i].expr;
		auto neg=negateDIvr(expr).simplify(facts);
		auto pos=expr.simplify(facts);
		return doIt(facts*pos,cur.substitute(var,one),i+1) +
			doIt(facts*neg,cur.substitute(var,zero),i+1);
	}
	auto r=doIt(one,h.expr,0);
	if(h.holes.length>13) dw(e," ",r);
	return r;
}

class DIvr: DExpr{ // iverson brackets
	enum Type{ // TODO: remove redundancy?
		eqZ,
		neqZ,
		lZ,
		leZ,
	}
	Type type;
	DExpr e;
	this(Type type,DExpr e){
		this.type=type; this.e=e;
		foreach(d;e.allOf!DDelta) assert(0);
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: correct?
	override int freeVarsImpl(scope int delegate(DVar) dg){ return e.freeVarsImpl(dg); }
	override DExpr substitute(DVar var,DExpr exp){ return dIvr(type,e.substitute(var,exp)); }
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){ return dIvr(type,e.substituteFun(fun,q,args,context)); }
	override DExpr incBoundVar(int di,bool bindersOnly){ return dIvr(type,e.incBoundVar(di,bindersOnly)); }

	override string toStringImpl(Format formatting,Precedence prec){
		with(Type){
			if(formatting==Format.mathematica){
				auto es=e.toStringImpl(formatting,Precedence.none);
				final switch(type){
				case eqZ: return text("Boole[",es,"==0]");
				case neqZ: return text("Boole[",es,"!=0]");
				case lZ: assert(0);
				case leZ: return text("Boole[",es,"<=0]");
				}
			}else if(formatting==Format.maple){
				//return "piecewise("~e.toStringImpl(formatting,Precedence.none)~(type==eqZ?"=":type==neqZ?"<>":type==lZ?"<":"<=")~"0,1,0)";
				auto es=e.toStringImpl(formatting,Precedence.none);
				final switch(type){
					//case eqZ: return text("piecewise(",es,"=0,1,0)");
					case eqZ: return text("piecewise(abs(",es,")<pZ,1,0)");
					//case neqZ: return text("piecewise(",es,"<>0,1,0)");
					case neqZ: return text("piecewise(abs(",es,")>pZ,1,0)");
					case lZ: assert(0);
					//case leZ: return text("piecewise(",es,"<=0,1,0)");
					case leZ: return text("piecewise(",es,"<pZ,1,0)");
				}
			}else if(formatting==Format.sympy){
				auto es=e.toStringImpl(formatting,Precedence.none);
				final switch(type){
				case eqZ: return text("Piecewise((1,And(",es,">-pZ,",es,"<pZ)),(0,1))");
				case neqZ: return text("Piecewise((1,Or(",es,"<-pZ,",es,">pZ)),(0,1))");
				case lZ: assert(0);
				case leZ: return text("Piecewise((1,",es,"<pZ),(1,0))");
				}
			}else if(formatting==Format.matlab){
				return "("~e.toStringImpl(formatting,Precedence.none)~(type==eqZ?"==":type==neqZ?"!=":type==lZ?"<":"<=")~"0)";
			}else{
				return "["~e.toStringImpl(formatting,Precedence.none)~(type==eqZ?"=":type==neqZ?"≠":type==lZ?"<":"≤")~"0]";
			}
		}
	}

	static DExpr constructHook(Type type,DExpr e){
		//return staticSimplify(type,e);
		return null;
	}

	static DExpr staticSimplify(Type type,DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne !is e) return dIvr(type,ne).simplify(facts);
		// TODO: make these check faster (also: less convoluted)
		auto neg=negateDIvr(type,e);
		bool foundLe=false, foundNeq=false;
		foreach(f;facts.factors){
			if(auto ivr=cast(DIvr)f){
				// TODO: more elaborate implication checks
				if(ivr.type==type){
					if(ivr.e is e) return one;
					if(ivr.type==Type.leZ){
						if(e.mustBeAtMost(ivr.e))
							return one;
					}
				}
				import util: among;
				if(neg.type==ivr.type && (neg.e is ivr.e||type.among(Type.eqZ,Type.neqZ)&&neg.e is -ivr.e))
					return zero; // TODO: ditto
				if(neg.type==Type.lZ){
					if(ivr.type==Type.leZ){
						if(neg.e is ivr.e) assert(neg.e.mustBeAtMost(ivr.e));
						if(neg.e.mustBeAtMost(ivr.e)) foundLe=true;
						else if(neg.e.mustBeLessThan(ivr.e)) return zero;
					}else if(neg.e is ivr.e ||neg.e is -ivr.e&&ivr.type==Type.neqZ) foundNeq=true;
				}
			}
		}
		if(foundLe&&foundNeq){
			assert(type==type.leZ);
			return zero;
		}
		// TODO: better decision procedures
		if(type==Type.eqZ&&!couldBeZero(e)) return zero;
		if(type==Type.neqZ&&!couldBeZero(e)) return one;
		if(type==Type.leZ){
			if(mustBeLessOrEqualZero(e)) return one;
			if(mustBeLessThanZero(-e)) return zero;
			if(mustBeLessOrEqualZero(-e)) return dIvr(Type.eqZ,e).simplify(facts);
		}
		with(Type) if(type==eqZ||type==neqZ){ // TODO: figure out why this causes non-termination in mult_uniform_test
			if(auto p=cast(DPow)e){
				auto isZ=dIvr(lZ,-p.operands[1])*dIvr(eqZ,p.operands[0]);
				return (type==eqZ?isZ:dIvr(eqZ,isZ)).simplify(facts);
			}
		}
		if(auto c=cast(Dℕ)e){
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
		auto cancel=uglyFractionCancellation(e);
		if(cancel!=one) return dIvr(type,dDistributeMult(e,cancel)).simplify(facts);
		if(type==Type.lZ) return (dIvr(Type.leZ,e)*dIvr(Type.neqZ,e)).simplify(facts);
		if(type==Type.eqZ||type==Type.neqZ){
			auto f=e.getFractionalFactor();
			if(f!=one && f!=zero && f!=mone) return dIvr(type,e/f).simplify(facts);
		}
		foreach(v;e.freeVars()){ // TODO: do this right
			if(auto fct=factorDIvr!(e=>dIvr(type,e))(e)) return fct.simplify(facts);
			break;
		}
		auto denom=getCommonDenominator(e);
		if(denom !is one){
			auto dcancel=dDistributeMult(e,denom);
			final switch(type) with(Type){
				case eqZ,neqZ:
					auto r=dIvr(type,dcancel).simplify(facts);
					if(!cast(DIvr)r) return r;
				case leZ,lZ: break;
					auto r=(dIvr(leZ,-denom)*dIvr(type,dcancel)+
							dIvr(lZ,denom)*dIvr(type,-dcancel)).simplify(facts);
					if(r is zero || r is one) return r;
				// TODO: unfortunately, due to how definiteIntegral is implemented, we
				// cannot use this rewrite to normalize as follows. Fix this.
				/+case eqZ,neqZ:
					return dIvr(type,dcancel).simplify(facts);
				case leZ,lZ: break;
					return (dIvr(leZ,-denom)*dIvr(type,dcancel)+
							dIvr(lZ,denom)*dIvr(type,-dcancel)).simplify(facts);+/
			}
		}
		if(auto l=cast(DLog)e)
			return dIvr(type,l.e-one).simplify(facts);
		if(e.hasFactor(mone))
			if(auto l=cast(DLog)(e.withoutFactor(mone)))
				return dIvr(type,one-l.e).simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(type,e,facts);
		return r?r:this;
	}

}

DExpr dBounded(string what)(DExpr e,DExpr lo,DExpr hi) if(what=="[]"){
	return dIvr(DIvr.Type.leZ,lo-e)*dIvr(DIvr.Type.leZ,e-hi);
}

DExpr dBounded(string what)(DExpr e,DExpr lo,DExpr hi) if(what=="[)"){
	return dIvr(DIvr.Type.leZ,lo-e)*dIvr(DIvr.Type.lZ,e-hi);
}

DVar getCanonicalFreeVar(DExpr e){
	DVar r=null;
	bool isMoreCanonicalThan(DVar a,DVar b){
		if(b is null) return true;
		return a.name<b.name;
	}
	foreach(v;e.freeVars)
		if(isMoreCanonicalThan(v,r)) r=v;
	return r;
}

MapX!(DExpr,DExpr)[DIvr.Type.max+1] uniqueMapDIvr;
DExpr dIvr(DIvr.Type type,DExpr e){
	if(auto r=DIvr.constructHook(type,e)) return r;
	if(e in uniqueMapDIvr[type]) return uniqueMapDIvr[type][e];
	if(type==DIvr.Type.eqZ||type==DIvr.Type.neqZ){
		// TODO: is there a better way to make the argument canonical?
		if(-e in uniqueMapDIvr[type])
			return uniqueMapDIvr[type][-e];
	}
	auto r=new DIvr(type,e);
	uniqueMapDIvr[type][e]=r;
	return r;

}

class DDelta: DExpr{ // Dirac delta, for ℝ
	DExpr e;
	private this(DExpr e){ this.e=e; }
	override string toStringImpl(Format formatting,Precedence prec){
		if(formatting==Format.mathematica){
			return text("DiracDelta[",e.toStringImpl(formatting,Precedence.none),"]");
		}else if(formatting==Format.maple){
			return text("Dirac(",e.toStringImpl(formatting,Precedence.none),")");
			/+auto es=e.toStringImpl(formatting,Precedence.none);
			return text("piecewise(abs(",es,")<lZ,1/(2*(",es,")))");+/
		}else if(formatting==Format.sympy){
			return text("DiracDelta(",e.toStringImpl(formatting,Precedence.none),")");
		}else{
			return "δ["~e.toStringImpl(formatting,Precedence.none)~"]";
		}
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: ok?
	override int freeVarsImpl(scope int delegate(DVar) dg){ return e.freeVarsImpl(dg); }
	override DExpr substitute(DVar var,DExpr exp){ return dDelta(e.substitute(var,exp)); }
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dDelta(e.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){ return dDelta(e.incBoundVar(di,bindersOnly)); }

	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(one); // cannot use all facts! (might remove a free variable)
		if(ne !is e) return dDelta(ne);
		auto cancel=uglyFractionCancellation(e);
		if(cancel!=one) return dDelta(dDistributeMult(e,cancel))*cancel;
		if(e.hasFactor(mone)) return dDelta(-e);
		if(auto fct=factorDIvr!(e=>dDelta(e))(e)) return fct.simplify(facts);
		if(dIvr(DIvr.Type.eqZ,e).simplify(facts) is zero)
			return zero;
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}

	static DExpr performSubstitution(DVar var,DDelta d,DExpr expr,bool caseSplit){
		SolutionInfo info;
		SolUse usage={caseSplit:caseSplit,bound:false};
		if(auto s=d.e.solveFor(var,zero,usage,info)){
			s=s.simplify(one);
			if(!caseSplit && info.needCaseSplit) return null;
			auto constraints=one;
			foreach(ref x;info.caseSplits)
				constraints=constraints*dIvr(DIvr.Type.neqZ,x.constraint);
			auto r=constraints is zero?zero:
				constraints*expr.substitute(var,s)/dAbs(dDiff(var,d.e,s));
			foreach(ref x;info.caseSplits){
				auto curConstr=constraints.withoutFactor(dIvr(DIvr.Type.neqZ,x.constraint));
				r=r+curConstr*dIvr(DIvr.Type.eqZ,x.constraint)*dIntSmp(var,expr*dDelta(x.expression));
			}
			return r;
		}
		return null;
	}
}

//mixin(makeConstructorUnary!DDelta);

auto dDelta(DExpr a)in{assert(!cast(DTuple)a);}body{ // TODO: more preconditions
	if(auto r=DDelta.constructHook(a)) return r;
	// TODO: is there a better way to make the argument canonical?
	auto t1=tuplex(typeid(DDelta),a);
	if(t1 in uniqueMapUnary) return cast(DDelta)uniqueMapUnary[t1];
	auto t2=tuplex(typeid(DDelta),-a);
	if(t2 in uniqueMapUnary) return cast(DDelta)uniqueMapUnary[t2];
	auto r=new DDelta(a);
	uniqueMapUnary[t1]=r;
	return r;
}


class DDiscDelta: DExpr{ // point mass for discrete data types
	DVar var;
	DExpr e;
	private this(DVar var,DExpr e){
		this.var=var;
		this.e=e;
	}
	override string toStringImpl(Format formatting,Precedence prec){
		 // TODO: encoding for other CAS?
		return "δ_"~var.toStringImpl(formatting,Precedence.none)
			~"["~e.toStringImpl(formatting,Precedence.none)~"]";
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: ok?
	override int freeVarsImpl(scope int delegate(DVar) dg){
		if(auto r=dg(var))
			return r;
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		if(this.var is var  && exp is e) return one; // TODO: this is a hack and should be removed
		auto v=cast(DVar)this.var.substitute(var,exp);
		assert(!!v);
		return dDiscDelta(v,e.substitute(var,exp));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dDiscDelta(var,e.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){ return dDiscDelta(var.incBoundVar(di,bindersOnly),e.incBoundVar(di,bindersOnly)); }

	static DExpr constructHook(DVar var,DExpr e){
		return staticSimplify(var,e);
	}
	static DExpr staticSimplify(DVar var,DExpr e,DExpr facts=one){
		// cannot use all facts during simplification (e.g. see test/tuples5.prb)
		// the problem is that there might be a relation between e.g. multiple tuple entries, and we are not
		// allowed to introduce var as a free variable in e.
		// TODO: filter more precisely
		auto ne=e.simplify(one);
		if(ne !is e) return dDiscDelta(var,ne);
		//if(dIvr(DIvr.Type.eq,var,e).simplify(facts) is zero) return zero; // a simplification like this might be possible
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(var,e,facts);
		return r?r:this;
	}
}

import type; // TODO: remove this import
DExpr dDelta(DVar var,DExpr e,Type ty){ // TODO: dexpr shouldn't know about type, but this is most convenient for overloading
	if(ty is ℝ) return dDelta(e-var);
	assert(cast(TupleTy)ty||cast(ArrayTy)ty||cast(AggregateTy)ty,text(ty)); // TODO: add more supported types
	return dDiscDelta(var,e);
}

MapX!(TupleX!(DVar,DExpr),DExpr) uniqueMapDDiscDelta;
DExpr dDiscDelta(DVar var,DExpr e){
	if(auto r=DDiscDelta.constructHook(var,e)) return r;
	// TODO: is there a better way to make the argument canonical?
	auto t=tuplex(var,e);
	if(t in uniqueMapDDiscDelta) return uniqueMapDDiscDelta[t];
	auto r=new DDiscDelta(var,e);
	uniqueMapDDiscDelta[t]=r;
	return r;
}


DExpr[2] splitPlusAtVar(DExpr e,DVar var){
	DExprSet outside, within;
	//writeln("splitting: ",e,"\nat: ",var);
	//scope(exit) writeln("res: ",dPlus(outside),", ",dPlus(within));
	DExpr[2] handlePow(DPow p){
		DExpr[2] fail=[null,null];
		auto a=cast(DPlus)p.operands[0];
		auto c=cast(Dℕ)p.operands[1];
		if(!a||!c||c.c<=0) return fail;
		auto ow=splitPlusAtVar(a,var);
		if(ow[0]is zero || ow[1] is zero) return fail;
		DExpr outside=ow[0]^^c;
		DExprSet within;
		for(ℕ i=0;i<c.c;i++)
			DPlus.insert(within,nCr(c.c,i)*ow[0]^^i*ow[1]^^(c.c-i));
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
				if(p.operands[0].hasFreeVar(var)){
					DMult.insert(within,f);
				}else{
					auto ow=splitPlusAtVar(p.operands[1],var);
					DMult.insert(outside,p.operands[0]^^ow[0]);
					DMult.insert(within,p.operands[0]^^ow[1]);
				}
			}else DMult.insert(within,f);
		}else DMult.insert(outside,f);
	}
	return [dMult(outside),dMult(within)];
}

DExpr dMin(DExpr a,DExpr b){
	return dIvr(DIvr.Type.lZ,a-b)*a+dIvr(DIvr.Type.leZ,b-a)*b;
}
DExpr dMax(DExpr a,DExpr b){
	return dIvr(DIvr.Type.lZ,b-a)*a+dIvr(DIvr.Type.leZ,a-b)*b;
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
		if(auto p=cast(DPow)f) if(p.operands[0] is dE){ // TODO: check polynomial degree
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

static DExpr unbind(DVar tvar, DExpr expr, DExpr nexpr){
	assert(tvar is dBoundVar(1),text(tvar)); // TODO: finally fix the dBoundVar situation...
	assert(cast(DBoundVar)tvar);
	return expr.substitute(tvar,nexpr).incBoundVar(-1,true);
}

import integration;
class DInt: DOp{
	private{
		DVar var;
		DExpr expr;
		this(DVar var,DExpr expr){ this.var=var; this.expr=expr; }
	}
	DExpr getExpr(DVar var){
		if(cast(DBoundVar)this.var) return unbind(this.var,expr,var);
		return expr;
	}
	override @property Precedence precedence(){ return Precedence.intg; }
	override @property string symbol(Format formatting){ return "∫"; }
	override string toStringImpl(Format formatting,Precedence prec){
		if(formatting==Format.mathematica){
			return text("Integrate[",expr.toStringImpl(formatting,Precedence.none),",{",var.toStringImpl(formatting,Precedence.none),",-Infinity,Infinity}]");
		}else if(formatting==Format.maple){
			return text("int(",expr.toStringImpl(formatting,Precedence.none),",",var.toStringImpl(formatting,Precedence.none),"=-infinity..infinity)");
		}else if(formatting==Format.sympy){
			return text("integrate(",expr.toStringImpl(formatting,Precedence.none),",(",var.toStringImpl(formatting,Precedence.none),",-oo,oo))");
		}else{
			return addp(prec,symbol(formatting)~"d"~var.toStringImpl(formatting,Precedence.none)~expr.toStringImpl(formatting,precedence));
		}
	}
	static DExpr constructHook(DVar var,DExpr expr,DExpr facts){
		return staticSimplifyFull(var,expr,facts);
	}

	version(INTEGRAL_STATS){
		static int numIntegrals=0;
		static void[0][DExpr] integrals;
		static ~this(){
			writeln("A: ",numIntegrals);
			writeln("B: ",integrals.length);
		}
	}

	static MapX!(Q!(DExpr,DExpr),DExpr) ssimplifyMemo;
	
	static DExpr staticSimplify(DVar var,DExpr expr,DExpr facts=one)in{assert(var&&expr&&facts);}body{
		static int dpt=0; dpt++; scope(exit) dpt--;
		//version(DISABLE_INTEGRATION){
		if(simplification==Simpl.raw)
			return null;
		version(INTEGRAL_STATS){
			numIntegrals++;
			auto dbvar=dBoundVar(1);
			auto newexpr=expr.incBoundVar(1).substitute(var,dbvar);
			integrals[newexpr]=[];
		}
		if(auto dbvar=cast(DBoundVar)var){
			auto nesting=dbvar.i;
			auto tmp=freshVar(); // TODO: get rid of this!
			auto nexpr=unbind(dBoundVar(1),expr.incBoundVar(-nesting,false),tmp);
			auto r=staticSimplify(tmp,nexpr,facts);
			return r?r.incBoundVar(nesting,false):null;
		}
		return definiteIntegral(var,expr,facts);
	}

	static DExpr staticSimplifyFull(DVar var,DExpr expr,DExpr facts=one)in{assert(var&&expr&&facts);}body{
		if(auto dbvar=cast(DBoundVar)var){
			auto nesting=dbvar.i-1;
			auto tmp=freshVar(); // TODO: get rid of this!
			auto nexpr=unbind(dBoundVar(1),expr.incBoundVar(-nesting,false),tmp);
			auto r=staticSimplifyFull(tmp,nexpr,facts);
			return r?r.incBoundVar(nesting,false):null;
		}
		auto nexpr=expr.simplify(facts);
		if(expr !is nexpr) return dIntSmp(var,nexpr,facts);
		auto ow=expr.splitMultAtVar(var);
		if(ow[0] !is one) return ow[0]*dIntSmp(var,ow[1],facts);
		return staticSimplify(var,expr);
	}
	
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplifyFull(var,expr,facts);
		return r?r:this;
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return expr.freeVarsImpl(v=>v is var?0:dg(v));
	}
	override DExpr substitute(DVar var,DExpr e){
		if(this.var is var) return this;
		auto ne=e;
		if(cast(DBoundVar)this.var) ne=e.incBoundVar(1,true);
		return dInt(this.var,expr.substitute(var,ne));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		auto nq=q;
		if(cast(DBoundVar)this.var) nq=q.incBoundVar(1,true);
		auto nexpr=expr.substituteFun(fun,nq,args,context);
		if(auto ctxv=cast(DContextVars)var){
			if(ctxv.fun is fun){
				auto r=nexpr;
				foreach(v;context) r=dInt(v,r);
				return r;
			}
		}
		return dInt(this.var,nexpr);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		auto dbvar=cast(DBoundVar)var;
		if(bindersOnly&&dbvar){
			auto nvar=dBoundVar(dbvar.i+di);
			auto tmp=freshVar(); // TODO: get rid of this!
			return dInt(nvar,expr.substitute(var,tmp).incBoundVar(di,bindersOnly).substitute(tmp,nvar));
		}else return dInt(var.incBoundVar(di,bindersOnly),expr.incBoundVar(di,bindersOnly));
	}
}

bool hasIntegrals(DExpr e){ return hasAny!DInt(e); }

MapX!(TupleX!(typeof(typeid(DExpr)),DBoundVar,DExpr,DExpr),DExpr) uniqueMapBinding;
auto uniqueBindingDExpr(T)(DBoundVar v,DExpr a,DExpr b=null){
	auto t=tuplex(typeid(T),v,a,b);
	if(t in uniqueMapBinding) return cast(T)uniqueMapBinding[t];
	static if(is(typeof(new T(v,a)))) auto r=new T(v,a);
	else auto r=new T(v,a,b);
	uniqueMapBinding[t]=r;
	return r;
}

DExpr dIntSmp(DVar var,DExpr expr,DExpr facts=one){
	if(auto r=DInt.constructHook(var,expr,facts)) return r;
	return dInt(var,expr);
}

DExpr dInt(DVar var,DExpr expr)in{assert(var&&expr);}body{
	if(cast(DContextVars)var) return new DInt(var,expr); // TODO: fix
	//if(auto dbvar=cast(DBoundVar)var) return uniqueBindingDExpr!DInt(dbvar,expr);
	auto dbvar=cast(DBoundVar)var;
	if(!dbvar){
		assert(!expr.hasFreeVar(dBoundVar(1)));
		dbvar=dBoundVar(1);
		expr=expr.incBoundVar(1,true).substitute(var,dbvar);
	}
	return uniqueBindingDExpr!DInt(dbvar,expr);
}

import summation;
class DSum: DOp{
		private{
		DBoundVar var;
		DExpr expr;
		this(DBoundVar var,DExpr expr){ this.var=var; this.expr=expr; }
	}
	DExpr getExpr(DVar var){ return unbind(this.var,expr,var); }
	override @property Precedence precedence(){ return Precedence.intg; }
	override @property string symbol(Format formatting){ return "∑"; }
	override string toStringImpl(Format formatting,Precedence prec){
		if(formatting==Format.mathematica){
			return text("Sum[",expr.toStringImpl(formatting,Precedence.none),",{",var.toStringImpl(formatting,Precedence.none),",-Infinity,Infinity}]");
		}else if(formatting==Format.maple){
			return text("sum(",expr.toStringImpl(formatting,Precedence.none),",",var.toStringImpl(formatting,Precedence.none),"=-infinity..infinity)"); // TODO: correct?
		}else if(formatting==Format.sympy){
			return text("sum(",expr.toStringImpl(formatting,Precedence.none),",(",var.toStringImpl(formatting,Precedence.none),",-oo,oo))"); // TODO: correct?
		}else{
			return addp(prec,symbol(formatting)~"_"~var.toStringImpl(formatting,Precedence.none)~expr.toStringImpl(formatting,precedence));
		}
	}
	static DExpr constructHook(DVar var,DExpr expr){
		return staticSimplify(var,expr);
	}

	static MapX!(Q!(DExpr,DExpr),DExpr) ssimplifyMemo;
	static DExpr staticSimplifyMemo(DVar var,DExpr expr,DExpr facts=one){
		auto t=q(dSum(var,expr),facts);
		if(t in ssimplifyMemo) return ssimplifyMemo[t]; // TODO: better solution available?
		auto r=staticSimplify(var,expr,facts);
		ssimplifyMemo[t]=r?r:t[0];
		return r;
	}
	
	static DExpr staticSimplify(DVar var,DExpr expr,DExpr facts=one){
		if(simplification==Simpl.raw){
			if(expr is zero) return zero;
			return null;
		}
		if(auto dbvar=cast(DBoundVar)var){
			int nesting=dbvar.i-1;
			auto tmp=freshVar(); // TODO: get rid of this!
			auto nexpr=unbind(dBoundVar(1),expr.incBoundVar(-nesting,false),tmp);
			auto r=staticSimplifyMemo(tmp,nexpr);
			return r?r.incBoundVar(nesting,false):null;
		}
		auto nexpr=expr.simplify(facts);
		if(nexpr !is expr) return dSum(var,nexpr).simplify(facts);
		if(simplification!=Simpl.deltas){
			if(auto r=computeSum(var,expr,facts))
				return r.simplify(facts);
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		 auto r=staticSimplify(var,expr);
		 return r?r:this;
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return expr.freeVarsImpl(v=>v is var?0:dg(v));
	}
	override DExpr substitute(DVar var,DExpr e){
		if(this.var is var) return this;
		auto ne=e;
		if(cast(DBoundVar)this.var) ne=e.incBoundVar(1,true);
		return dSum(this.var,expr.substitute(var,ne));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		auto nq=q;
		if(cast(DBoundVar)this.var) nq=q.incBoundVar(1,true);
		return dSum(var,expr.substituteFun(fun,nq,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		auto dbvar=cast(DBoundVar)var;
		if(bindersOnly&&dbvar){
			auto nvar=dBoundVar(dbvar.i+di);
			auto tmp=freshVar(); // TODO: get rid of this!
			return dSum(nvar,expr.substitute(var,tmp).incBoundVar(di,bindersOnly).substitute(tmp,nvar));
		}else return dSum(var.incBoundVar(di,bindersOnly),expr.incBoundVar(di,bindersOnly));
	}
}

DExpr dSumSmp(DVar var,DExpr expr){
	if(auto r=DSum.constructHook(var,expr)) return r;
	return dSum(var,expr);
}

DExpr dSum(DVar var,DExpr expr){
	//if(auto dbvar=cast(DBoundVar)var) return uniqueBindingDExpr!DSum(dbvar,expr);
	auto dbvar=cast(DBoundVar)var;
	if(!dbvar){
		dbvar=dBoundVar(1);
		expr=expr.incBoundVar(1,true).substitute(var,dbvar);
	}
	return uniqueBindingDExpr!DSum(dbvar,expr);
}


import limits;
class DLim: DOp{
	DVar v;
	DExpr e;
	DExpr x;
	this(DVar v,DExpr e,DExpr x){ this.v=v; this.e=e; this.x=x; }
	override @property string symbol(Format formatting){ return text("lim[",v," → ",e,"]"); }
	override Precedence precedence(){ return Precedence.lim; } // TODO: ok?
	override string toStringImpl(Format formatting,Precedence prec){
		return addp(prec,symbol(formatting)~x.toStringImpl(formatting,precedence));
	}

	static DExpr constructHook(DVar v,DExpr e,DExpr x){
		return staticSimplify(v,e,x);
	}

	static DExpr staticSimplify(DVar v,DExpr e,DExpr x,DExpr facts=one){
		if(auto dbvar=cast(DBoundVar)v){
			auto nesting=dbvar.i-1;
			auto tmp=freshVar(); // TODO: get rid of this!
			auto r=staticSimplify(tmp,e.incBoundVar(-nesting,false),unbind(v,x,tmp.incBoundVar(-nesting,false)));
			return r?r.incBoundVar(nesting,false):null;
		}
		auto ne=e.simplify(facts), nx=x.simplify(facts);
		if(ne !is e || nx !is x) return dLim(v,ne,nx).simplify(facts);
		if(auto r=getLimit(v,e,x,facts))
			return r;
		return null;
	}
	
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(v,e,x);
		return r?r:this;
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: correct?

	override int freeVarsImpl(scope int delegate(DVar) dg){
		if(auto r=e.freeVarsImpl(w=>w is v?0:dg(v)))
			return r;
		return x.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		auto nexp=exp;
		if(cast(DBoundVar)v) nexp=exp.incBoundVar(1,true);
		auto nx=x.substitute(var,nexp);
		auto ne=e;
		if(v !is var) ne=e.substitute(var,nexp);
		return dLim(v,ne,nx);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		auto nq=q;
		if(cast(DBoundVar)v) nq=q.incBoundVar(1,true);
		return dLim(v,e.substituteFun(fun,q,args,context),x.substituteFun(fun,nq,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		auto dbvar=cast(DBoundVar)v;
		if(bindersOnly&&dbvar){
			auto nv=dBoundVar(dbvar.i+di);
			auto tmp=freshVar(); // TODO: get rid of this!
			return dLim(nv,e.incBoundVar(di,bindersOnly),x.substitute(v,tmp).incBoundVar(di,bindersOnly).substitute(tmp,nv));
		}else return dLim(v.incBoundVar(di,bindersOnly),e.incBoundVar(di,bindersOnly),x.incBoundVar(di,bindersOnly));
	}
}

DExpr dLimSmp(DVar v,DExpr e,DExpr x){
	if(auto r=DLim.constructHook(v,e,x)) return r;
	return dLim(v,e,x);
}

DExpr dLim(DVar v,DExpr e,DExpr x){
	//if(auto dbvar=cast(DBoundVar)var) return uniqueBindingDExpr!DSum(dbvar,expr);
	assert(!e.hasFreeVar(v));
	auto dbvar=cast(DBoundVar)v;
	if(!dbvar){
		dbvar=dBoundVar(1);
		assert(!x.hasFreeVar(dbvar));
		x=x.incBoundVar(1,true).substitute(v,dbvar);
	}
	return uniqueBindingDExpr!DLim(dbvar,e,x);
}

bool hasLimits(DExpr e){ return hasAny!DLim(e); }

import differentiation;
class DDiff: DOp{
	DVar v;
	DExpr e;
	DExpr x;
	this(DVar v,DExpr e,DExpr x){ this.v=v; this.e=e; this.x=x; }
	override @property string symbol(Format formatting){ return "d/d"~v.toStringImpl(formatting,Precedence.none); }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Format formatting,Precedence prec){
		return addp(prec,symbol(formatting)~"["~e.toStringImpl(formatting,Precedence.none)~"]("~x.toStringImpl(formatting,Precedence.none)~")");
	}

	static DExpr constructHook(DVar v,DExpr e,DExpr x){
		return staticSimplify(v,e,x);
	}

	static DExpr staticSimplify(DVar v,DExpr e,DExpr x,DExpr facts=one){
		// TODO: bound var handling
		e=e.simplify(facts);
		if(auto r=differentiate(v,e))
			return r.substitute(v,x);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(v,e,x);
		return r?r:this;
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: correct?

	override int freeVarsImpl(scope int delegate(DVar) dg){
		if(auto r=e.freeVarsImpl(w=>w is v?0:dg(v)))
			return r;
		return x.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		auto nx=x.substitute(var,exp);
		auto ne=e;
		if(v !is var){
			auto nexp=exp;
			if(cast(DBoundVar)v) nexp=exp.incBoundVar(1,true);
			ne=e.substitute(var,nexp);
		}
		return dDiff(v,ne,nx);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		auto nq=q;
		if(cast(DBoundVar)v) nq=q.incBoundVar(1,true);
		return dDiff(v,e.substituteFun(fun,nq,args,context),x.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		auto dbvar=cast(DBoundVar)v;
		if(bindersOnly&&dbvar){
			auto nv=dBoundVar(dbvar.i+di);
			auto tmp=freshVar(); // TODO: get rid of this!
			return dDiff(nv,e.substitute(v,tmp).incBoundVar(di,bindersOnly).substitute(tmp,nv),x.incBoundVar(di,bindersOnly));
		}else return dDiff(v.incBoundVar(di,bindersOnly),e.incBoundVar(di,bindersOnly),x.incBoundVar(di,bindersOnly));
	}
}

MapX!(TupleX!(DVar,DExpr,DExpr),DExpr) uniqueMapDiff;
DExpr dDiff(DVar v,DExpr e,DExpr x){
	if(auto r=DDiff.constructHook(v,e,x)) return r;
	if(auto dbvar=cast(DBoundVar)v) return uniqueBindingDExpr!DDiff(dbvar,e,x);
	auto dbvar=dBoundVar(1);
	assert(!e.hasFreeVar(dbvar));
	e=e.incBoundVar(1,true).substitute(v,dbvar);
	return uniqueBindingDExpr!DDiff(dbvar,e,x);
}

DExpr dDiff(DVar v,DExpr e){ return dDiff(v,e,v); }

class DAbs: DOp{
	DExpr e;
	this(DExpr e){ this.e=e; }
	override @property string symbol(Format formatting){ return "|"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec){ // TODO: matlab, maple
		return "|"~e.toStringImpl(formatting,Precedence.none)~"|";
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return dg(e);
	}

	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dAbs(e.substitute(var,exp));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dAbs(e.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dAbs(e.incBoundVar(di,bindersOnly));
	}

	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		e=e.simplify(facts);
		if(e.isFraction()){
			auto nd=e.getFraction();
			assert(nd[1]>=0);
			return abs(nd[0])/dℕ(nd[1]);
		}
		if(cast(DE)e) return e;
		if(cast(DΠ)e) return e;
		if(auto m=cast(DMult)e){ // TODO: does this preclude some DMult-optimizations and should therefore be done differently?
			DExprSet r;
			foreach(f;m.factors)
				DMult.insert(r,dAbs(f));
			return dMult(r);
		}
		return -e*dIvr(DIvr.Type.lZ,e)+e*dIvr(DIvr.Type.leZ,-e); // TODO: just use this expression from the beginning?
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e);
		return r?r:this;
	}
}

DExpr dAbs(DExpr e){ return uniqueDExprUnary!DAbs(e); }


class DLog: DOp{
	DExpr e;
	this(DExpr e){ this.e=e; }
	override @property string symbol(Format formatting){ return "log"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec){
		auto es=e.toStringImpl(formatting,Precedence.none);
		if(formatting==Format.mathematica) return text("Log[",es,"]");
		return text("log(",es,")");
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return dg(e);
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dLog(e.substitute(var,exp));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dLog(e.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dLog(e.incBoundVar(di,bindersOnly));
	}

	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne !is e) return dLog(ne).simplify(facts);
		if(auto c=cast(DE)e) return one;
		if(e is one) return zero;
		if(auto m=cast(DMult)e){
			DExprSet r,s;
			bool sign=false;
			foreach(f;m.factors){
				auto pos=dIvr(DIvr.Type.leZ,-f).simplify(facts);
				if(pos is one)
					r.insert(f);
				else if(pos is zero){
					sign^=true;
					if(f!is mone) r.insert(-f);
				}else s.insert(f); // TODO: use dAbs?
			}
			if(!(r.length&&s.length)&&r.length<=1) return null;
			DExprSet logs;
			foreach(x;r) DPlus.insert(logs,dLog(x));
			DPlus.insert(logs,dLog(sign?-dMult(s):dMult(s)));
			return dPlus(logs).simplify(facts);
		}
		if(auto p=cast(DPow)e)
			return (p.operands[1]*dLog(dAbs(p.operands[0]))).simplify(facts);
		if(auto fct=factorDIvr!(e=>dLog(e))(e)) return fct.simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}

DExpr dLog(DExpr e){ return uniqueDExprUnary!DLog(e); }

class DSin: DOp{
	DExpr e;
	this(DExpr e){ this.e=e; }
	override @property string symbol(Format formatting){ return "sin"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec){
		return "sin("~e.toStringImpl(formatting,Precedence.none)~")";
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return dg(e);
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dSin(e.substitute(var,exp));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dSin(e.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dSin(e.incBoundVar(di,bindersOnly));
	}

	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!is e) return dSin(ne);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}

DExpr dSin(DExpr e){ return uniqueDExprUnary!DSin(e); }


class DFloor: DOp{
	DExpr e;
	this(DExpr e){ this.e=e; }
	override @property string symbol(Format formatting){ return "⌊.⌋"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec){
		return "⌊"~e.toStringImpl(formatting,Precedence.none)~"⌋";
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return dg(e);
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dFloor(e.substitute(var,exp));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dFloor(e.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dFloor(e.incBoundVar(di,bindersOnly));
	}
	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!is e) return dFloor(ne);
		if(e.isFraction()){
			auto nd=e.getFraction();
			return dℕ(floordiv(nd[0],nd[1]));
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}

DExpr dFloor(DExpr e){ return uniqueDExprUnary!DFloor(e); }


class DCeil: DOp{
	DExpr e;
	this(DExpr e){ this.e=e; }
	override @property string symbol(Format formatting){ return "⌈.⌉"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec){
		return "⌈"~e.toStringImpl(formatting,Precedence.none)~"⌉";
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return dg(e);
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dCeil(e.substitute(var,exp));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dCeil(e.substituteFun(fun,q,args,context));
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dCeil(e.incBoundVar(di,bindersOnly));
	}
	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!is e) return dCeil(ne);
		if(e.isFraction()){
			auto nd=e.getFraction();
			return dℕ(ceildiv(nd[0],nd[1]));
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,facts);
		return r?r:this;
	}
}

DExpr dCeil(DExpr e){ return uniqueDExprUnary!DCeil(e); }



class DGaussInt: DOp{
	DExpr x;
	this(DExpr x){ this.x=x; }
	override @property string symbol(Format formatting){ return "(d/dx)⁻¹[e^(-x²)]"; }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Format formatting,Precedence prec){
		if(formatting==Format.mathematica){
			return "Sqrt[Pi]*(Erf["~x.toStringImpl(formatting,Precedence.none)~"]+1)/2";
		}else if(formatting==Format.maple){
			return "sqrt(Pi)*(erf("~x.toStringImpl(formatting,Precedence.none)~")+1)/2";
		}else if(formatting==Format.matlab) return "(sqrt(pi)*(erf("~x.toStringImpl(formatting,Precedence.none)~")+1)/2)";
		else return addp(prec,symbol(formatting)~"("~x.toStringImpl(formatting,Precedence.none)~")");
	}

	static DExpr constructHook(DExpr x){
		return staticSimplify(x);
	}
	static DExpr staticSimplify(DExpr x,DExpr facts=one){
		if(x is dInf){
			return dΠ^^(one/2);
		}else if(x is -dInf){
			return zero;
		}
		if(x is zero){
			return dΠ^^(one/2)/2;
		}
		auto nx=x.simplify(facts);
		if(nx !is x) return dGaussInt(nx).simplify(facts);
		if(auto fct=factorDIvr!(e=>dGaussInt(e))(x)) return fct.simplify(facts);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(x);
		return r?r:this;
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return dg(x); }

	override int freeVarsImpl(scope int delegate(DVar) dg){
		return x.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		auto nx=x.substitute(var,exp);
		return dGaussInt(nx);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		auto nx=x.substituteFun(fun,q,args,context);
		return dGaussInt(nx);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dGaussInt(x.incBoundVar(di,bindersOnly));
	}
}

auto dGaussInt(DExpr x){ return uniqueDExprUnary!DGaussInt(x); }

class DInf: DExpr{ // TODO: explicit limits?
	override string toStringImpl(Format formatting,Precedence prec){ return "∞"; }
	mixin Constant;
}

private static DInf theDInf;
@property DInf dInf(){ return theDInf?theDInf:(theDInf=new DInf); }

bool isInfinite(DExpr e){
	return e is dInf || e is -dInf;
}

class DFunVar: DExpr{
	string name;
	/+private+/ this(string name){ this.name=name; } // TODO: make private!
	override string toStringImpl(Format formatting,Precedence prec){ return name; }

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
	override int freeVarsImpl(scope int delegate(DVar) dg){ return 0; }
	override DExpr substitute(DVar var,DExpr e){ return this; }
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){ assert(0); }
	override DExpr incBoundVar(int di,bool bindersOnly){ return this; }
	override DExpr simplifyImpl(DExpr facts){ return this; }
}
DFunVar[string] dFunVarCache; // TODO: caching desirable? (also need to update parser if not)
DFunVar dFunVar(string name){
	if(name in dFunVarCache) return dFunVarCache[name];
	return dFunVarCache[name]=new DFunVar(name);
}

class DFun: DOp{ // uninterpreted functions
	DFunVar fun;
	DExpr[] args;
	this(DFunVar fun, DExpr[] args){ this.fun=fun; this.args=args; }
	override @property string symbol(Format formatting){ return fun.name; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Format formatting,Precedence prec){
		if(formatting==Format.mathematica)
			return fun.name~"["~args.map!(a=>a.toStringImpl(formatting,Precedence.none)).join(",")~"]";
		return fun.name~"("~args.map!(a=>a.toStringImpl(formatting,Precedence.none)).join(",")~")";
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		foreach(a;args)
			if(auto r=dg(a))
				return r;
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		foreach(a;args)
			if(auto r=a.freeVarsImpl(dg))
				return r;
		return 0;
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dFun(fun,args.map!(a=>a.substitute(var,exp)).array);
	}

	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		auto newArgs=this.args.dup;
		if(newArgs.length&&cast(DContextVars)newArgs[$-1]) newArgs=newArgs[0..$-1];
		foreach(ref a;newArgs) a=a.substituteFun(fun,q,args,context);
		bool check(){
			if(fun !is this.fun) return false;
			if(args.length!=newArgs.length)
				return false;
			return true;
		}
		if(!check()) return dFun(this.fun,newArgs);
		auto r=q;
		foreach(i,a;newArgs) r=r.substitute(args[i],a); // TODO: this does not avoid capture properly
		//dw(q," ",r," ",this.args," ",args," ",newArgs);
		return r;
	}

	override DExpr incBoundVar(int di,bool bindersOnly){
		return dFun(fun,args.map!(a=>a.incBoundVar(di,bindersOnly)).array);
	}

	static DFun constructHook(DFunVar fun,DExpr[] args){
		return staticSimplify(fun,args);
	}
	static DFun staticSimplify(DFunVar fun,DExpr[] args,DExpr facts=one){
		auto nargs=args.map!(a=>a.simplify(one)).array; // cannot use all facts! (might remove a free variable)
		if(nargs!=args) return dFun(fun,nargs);
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(fun,args,facts);
		return r?r:this;
	}
}

MapX!(TupleX!(DFunVar,DExpr[]),DFun) uniqueMapDFun;
auto uniqueDFun(DFunVar fun,DExpr[] args){
	if(auto r=DFun.constructHook(fun,args)) return r;
	auto t=tuplex(fun,args);
	if(t in uniqueMapDFun) return uniqueMapDFun[t];
	auto r=new DFun(fun,args);
	uniqueMapDFun[t]=r;
	return r;
}

DFun dFun(DFunVar fun,DExpr[] args){
	return uniqueDFun(fun,args);
}
DFun dFun(DFunVar fun,DExpr arg){
	return dFun(fun,[arg]);
}

class DContextVars: DVar{
	DFunVar fun;
	this(string name,DFunVar fun){
		super(name);
		this.fun=fun;
	}
	override string toStringImpl(Format formatting,Precedence prec){
		return text(super.toStringImpl(formatting,prec),"⃗");
	}
}

MapX!(TupleX!(string,DFunVar),DContextVars) uniqueMapDVars;
auto dContextVars(string name,DFunVar fun){
	auto k=tuplex(name,fun);
	if(k in uniqueMapDVars) return uniqueMapDVars[k];
	auto r=new DContextVars(name,fun);
	uniqueMapDVars[k]=r;
	return r;
}


class DTuple: DExpr{ // Tuples. TODO: real tuple support
	DExpr[] values;
	this(DExpr[] values){
		this.values=values;
	}
	override string toStringImpl(Format formatting, Precedence prec){
		return text("(",values.map!(v=>v.toStringImpl(formatting,Precedence.none)).join(","),values.length==1?",":"",")");
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		foreach(v;values)
			if(auto r=dg(v))
				return r;
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		foreach(v;values)
			if(auto r=v.freeVarsImpl(dg))
				return r;
		return 0;
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dTuple(values.map!(v=>v.substitute(var,exp)).array);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dTuple(values.map!(v=>v.substituteFun(fun,q,args,context)).array);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dTuple(values.map!(v=>v.incBoundVar(di,bindersOnly)).array);
	}
	static DTuple constructHook(DExpr[] values){
		return staticSimplify(values);
	}
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

MapX!(TupleX!(DExpr[]),DTuple) uniqueMapDTuple;
auto uniqueDTuple(DExpr[] values){
	if(auto r=DTuple.constructHook(values)) return r;
	auto t=tuplex(values);
	if(t in uniqueMapDTuple) return uniqueMapDTuple[t];
	auto r=new DTuple(values);
	uniqueMapDTuple[t]=r;
	return r;
}

DTuple dTuple(DExpr[] values){
	return uniqueDTuple(values);
}

class DRecord: DExpr{ // Tuples. TODO: real tuple support
	DExpr[string] values;
	this(DExpr[string] values){
		this.values=values;
	}
	final DRecord update(string f,DExpr n){
		auto nvalues=values.dup;
		nvalues[f]=n;
		return dRecord(nvalues);
	}

	override string toStringImpl(Format formatting, Precedence prec){
		// TODO: other CAS?
		auto r="{";
		foreach(k,v;values){
			r~="."~k~" ↦ "~v.toStringImpl(formatting,Precedence.none);
			r~=",";
		}
		return r.length!=1?r[0..$-1]~"}":"{}";
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		foreach(k,v;values)
			if(auto r=dg(v))
				return r;
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		foreach(k,v;values)
			if(auto r=v.freeVarsImpl(dg))
				return r;
		return 0;
	}
	override DExpr substitute(DVar var,DExpr exp){
		DExpr[string] nvalues;
		foreach(k,v;values) nvalues[k]=v.substitute(var,exp);
		return dRecord(nvalues);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		DExpr[string] nvalues;
		foreach(k,v;values) nvalues[k]=v.substituteFun(fun,q,args,context);
		return dRecord(nvalues);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		DExpr[string] nvalues;
		foreach(k,v;values) nvalues[k]=v.incBoundVar(di,bindersOnly);
		return dRecord(nvalues);
	}
	static DRecord constructHook(DExpr[string] values){
		return staticSimplify(values);
	}
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

MapX!(TupleX!(TupleX!(string,DExpr)[]),DRecord) uniqueMapDRecord; // TODO: why no hash for built-in aas?
auto dRecord(DExpr[string] values){
	if(auto r=DRecord.constructHook(values)) return r;
	TupleX!(string,DExpr)[] tt;
	foreach(k,v;values) tt~=tuplex(k,v);
	sort!"a[0]<b[0]"(tt);
	auto t=tuplex(tt);
	if(t in uniqueMapDRecord)
		return uniqueMapDRecord[t];
	auto r=new DRecord(values);
	uniqueMapDRecord[t]=r;
	return r;
}

auto dRecord(){ return dRecord((DExpr[string]).init); }


class DIndex: DOp{
	DExpr e,i; // TODO: multiple indices?
	this(DExpr e,DExpr i){
		this.e=e; this.i=i;
	}
	override string symbol(Format formatting){ return "[]"; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec){
		return addp(prec, e.toStringImpl(formatting,Precedence.index)~"["~i.toStringImpl(formatting,Precedence.none)~"]");
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){
		if(auto r=dg(e)) return r;
		return dg(i);
	}

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,i,facts);
		return r?r:this;
	}

	override DExpr substitute(DVar var,DExpr exp){
		return e.substitute(var,exp)[i.substitute(var,exp)];
	}

	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SHSet!DVar context){
		return e.substituteFun(fun,q,args,context)[i.substituteFun(fun,q,args,context)];
	}

	override DExpr incBoundVar(int di,bool bindersOnly){
		return e.incBoundVar(di,bindersOnly)[i.incBoundVar(di,bindersOnly)];
	}

	override int freeVarsImpl(scope int delegate(DVar) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return i.freeVarsImpl(dg);
	}
	
	static DExpr staticSimplify(DExpr e,DExpr i,DExpr facts=one){
		auto ne=e.simplify(facts);
		auto ni=i.simplify(facts);
		if(auto c=cast(Dℕ)ni){
			if(auto tpl=cast(DTuple)ne)
				if(0<=c.c&&c.c<=tpl.values.length)
					return tpl.values[c.c.toLong()];
		}
		if(auto arr=cast(DArray)ne){
			auto dbvar=cast(DBoundVar)arr.entries.var;
			assert(!!dbvar);
			auto nesting=dbvar.i-1; // TODO: get rid of this logic if possible
			return arr.entries.incBoundVar(-nesting,false).apply(ni.incBoundVar(-nesting,false)).incBoundVar(nesting,false);
		}
		// distribute over case distinction:
		if(e is zero) return zero;
		if(auto p=cast(DPlus)ne){
			DExprSet r;
			foreach(s;p.summands) DPlus.insert(r,dIndex(s,ni));
			return dPlus(r).simplify(facts);
		}
		if(auto m=cast(DMult)ne){
			foreach(fc;m.factors){
				if(cast(DTuple)fc||cast(DArray)fc)
					return (m.withoutFactor(fc)*dIndex(fc,ni)).simplify(facts);
			}
		}
		if(ne !is e || ni !is i) return dIndex(ne,ni);
		return null;
	}
	static DExpr constructHook(DExpr e,DExpr i){
		return staticSimplify(e,i);
	}
}

mixin(makeConstructorNonCommutAssoc!DIndex);

class DIUpdate: DOp{
	DExpr e,i,n; // TODO: multiple indices?
	this(DExpr e,DExpr i,DExpr n){
		this.e=e; this.i=i; this.n=n;
	}
	override string symbol(Format formatting){ return "[ ↦ ]"; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec){
		return addp(prec, e.toStringImpl(formatting,Precedence.index)~"["~i.toStringImpl(formatting,Precedence.none)~
					" ↦ "~n.toStringImpl(formatting,Precedence.none)~"]");
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){
		if(auto r=dg(e)) return r;
		if(auto r=dg(i)) return r;
		return dg(n);
	}

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,i,n,facts);
		return r?r:this;
	}

	override DExpr substitute(DVar var,DExpr exp){
		return dIUpdate(e.substitute(var,exp),i.substitute(var,exp),n.substitute(var,exp));
	}

	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SHSet!DVar context){
		return dIUpdate(e.substituteFun(fun,q,args,context),i.substituteFun(fun,q,args,context),n.substituteFun(fun,q,args,context));
	}

	override DExpr incBoundVar(int di,bool bindersOnly){
		return dIUpdate(e.incBoundVar(di,bindersOnly),i.incBoundVar(di,bindersOnly),n.incBoundVar(di,bindersOnly));
	}

	override int freeVarsImpl(scope int delegate(DVar) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		if(auto r=i.freeVarsImpl(dg)) return r;
		return n.freeVarsImpl(dg);
	}
	
	static DExpr staticSimplify(DExpr e,DExpr i,DExpr n,DExpr facts=one){
		auto ne=e.simplify(facts);
		auto ni=i.simplify(facts);
		auto nn=n.simplify(facts);
		if(auto c=cast(Dℕ)ni){
			if(auto tpl=cast(DTuple)ne){
				if(0<=c.c&&c.c<=tpl.values.length){
					auto nvalues=tpl.values.dup;
					nvalues[c.c.toLong()]=nn;
					return dTuple(nvalues);
				}
			}
		}
		if(auto arr=cast(DArray)ne){
			auto tmp=freshVar(); // TODO: get rid of this!
			auto dbvar=cast(DBoundVar)arr.entries.var;
			assert(!!dbvar);
			auto nesting=dbvar.i-1;
			/+dw("!? ",e," ",i," ",n);
			dw("entries: ",arr.entries);
			dw("new: ",n);
			dw("mod-entries: ",arr.entries.incBoundVar(-nesting,false));
			auto modr=dLambda(tmp,arr.entries.incBoundVar(-nesting,false).apply(tmp)*dIvr(DIvr.Type.neqZ,tmp-ni).incBoundVar(-nesting,false)+(dIvr(DIvr.Type.eqZ,tmp-ni)*nn).incBoundVar(-nesting,false));
			dw("mod-r: ", modr);
			dw("!?!");
			writeln("mod-r2: ", modr.incBoundVar(nesting,false));+/
			auto r=dArray(arr.length,
						  dLambda(tmp,arr.entries.incBoundVar(-nesting,false).apply(tmp)*dIvr(DIvr.Type.neqZ,tmp-ni).incBoundVar(-nesting,false)
								  +(dIvr(DIvr.Type.eqZ,tmp-ni)*nn).incBoundVar(-nesting,false)).incBoundVar(nesting,false));
			//dw(" ---> ",r);
			//dw("!!! ", dLambda(tmp,(dIvr(DIvr.Type.eqZ,tmp-ni)*nn).incBoundVar(-nesting,false)));
			//dw(nesting," ",arr.entries.incBoundVar(-nesting,false)," ",(dIvr(DIvr.Type.eqZ,tmp-ni)*nn).incBoundVar(-nesting,false));
			//dw(r);
			return r;
		}
		if(ne !is e || ni !is i || nn !is n) return dIUpdate(ne,ni,nn);
		return null;
	}
	
	static DExpr constructHook(DExpr e,DExpr i,DExpr n){
		return staticSimplify(e,i,n);
	}
}

MapX!(TupleX!(DExpr,DExpr,DExpr),DExpr) uniqueMapDIUpdate;
auto dIUpdate(DExpr e,DExpr i,DExpr n){
	if(auto r=DIUpdate.constructHook(e,i,n)) return r;
	auto t=tuplex(e,i,n);
	if(t in uniqueMapDIUpdate) return uniqueMapDIUpdate[t];
	auto r=new DIUpdate(e,i,n);
	uniqueMapDIUpdate[t]=r;
	return r;
}


class DRUpdate: DOp{
	DExpr e,n; // TODO: multiple indices?
	string f;
	this(DExpr e,string f,DExpr n){
		this.e=e; this.f=f; this.n=n;
	}
	override string symbol(Format formatting){ return "[ ↦ ]"; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec){
		return addp(prec, e.toStringImpl(formatting,Precedence.index)~"{."~f~
					" ↦ "~n.toStringImpl(formatting,Precedence.none)~"}");
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){
		if(auto r=dg(e)) return r;
		return dg(n);
	}

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,f,n,facts);
		return r?r:this;
	}

	override DExpr substitute(DVar var,DExpr exp){
		return dRUpdate(e.substitute(var,exp),f,n.substitute(var,exp));
	}

	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SHSet!DVar context){
		return dRUpdate(e.substituteFun(fun,q,args,context),f,n.substituteFun(fun,q,args,context));
	}

	override DExpr incBoundVar(int di,bool bindersOnly){
		return dRUpdate(e.incBoundVar(di,bindersOnly),f,n.incBoundVar(di,bindersOnly));
	}

	override int freeVarsImpl(scope int delegate(DVar) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return n.freeVarsImpl(dg);
	}
	
	static DExpr staticSimplify(DExpr e,string f,DExpr n,DExpr facts=one){
		auto ne=e.simplify(facts);
		auto nn=n.simplify(facts);
		if(auto rec=cast(DRecord)ne)
			return rec.update(f,nn);
		if(ne !is e || nn !is n) return dRUpdate(ne,f,nn);
		return null;
	}
	
	static DExpr constructHook(DExpr e,string f,DExpr n){
		return staticSimplify(e,f,n);
	}
}

MapX!(TupleX!(DExpr,string,DExpr),DExpr) uniqueMapDRUpdate;
auto dRUpdate(DExpr e,string f,DExpr n){
	if(auto r=DRUpdate.constructHook(e,f,n)) return r;
	auto t=tuplex(e,f,n);
	if(t in uniqueMapDRUpdate) return uniqueMapDRUpdate[t];
	auto r=new DRUpdate(e,f,n);
	uniqueMapDRUpdate[t]=r;
	return r;
}



class DLambda: DOp{ // lambda functions DExpr → DExpr
	private{
		DVar var;
		DExpr expr;
	}
	this(DVar var,DExpr expr){
		this.var=var; this.expr=expr;
	}
	DExpr getExpr(DVar var){
		assert(cast(DBoundVar)this.var);
		return unbind(this.var,expr,var);
	}
	DExpr apply(DExpr e){
		assert(!!cast(DBoundVar)var);
		return unbind(var,expr,e);
	}
	override @property Precedence precedence(){ return Precedence.lambda; }
	override @property string symbol(Format formatting){ return "λ"; }
	override string toStringImpl(Format formatting,Precedence prec){
		// TODO: formatting for other CAS systems
		return addp(prec,text("λ",var.toStringImpl(formatting,Precedence.none),". ",expr.toStringImpl(formatting,precedence.lambda)));
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return 0; // TODO: ok?
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return expr.freeVarsImpl(v=>v is var?0:dg(v));
	}
	override DLambda substitute(DVar var,DExpr e){
		if(this.var is var) return this;
		auto ne=e;
		if(cast(DBoundVar)this.var) ne=e.incBoundVar(1,true);
		return dLambda(this.var,expr.substitute(var,ne));
	}
	override DLambda substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		auto nq=q;
		if(cast(DBoundVar)this.var) nq=q.incBoundVar(1,true);
		return dLambda(var,expr.substituteFun(fun,nq,args,context));
	}
	override DLambda incBoundVar(int di,bool bindersOnly){
		auto dbvar=cast(DBoundVar)var;
		if(bindersOnly&&dbvar){
			auto nvar=dBoundVar(dbvar.i+di);
			auto tmp=freshVar(); // TODO: get rid of this!
			return dLambda(nvar,expr.substitute(var,tmp).incBoundVar(di,bindersOnly).substitute(tmp,nvar));
		}else return dLambda(var.incBoundVar(di,bindersOnly),expr.incBoundVar(di,bindersOnly));
	}

	static DLambda constructHook(DVar var,DExpr expr){
		return staticSimplify(var,expr);
	}
	static DLambda staticSimplify(DVar var,DExpr expr,DExpr facts=one){
		if(auto dbvar=cast(DBoundVar)var){
			auto nesting=dbvar.i-1;
			auto tmp=freshVar(); // TODO: get rid of this!
			auto nexpr=unbind(dBoundVar(1),expr.incBoundVar(-nesting,false),tmp);
			auto r=staticSimplify(tmp,nexpr,facts);
			return r?r.incBoundVar(nesting,false):null;
		}
		auto nexpr=expr.simplify(facts);
		if(nexpr !is expr){
			auto r=dLambda(var,nexpr).simplify(facts);
			assert(!r||cast(DLambda)r);
			return cast(DLambda)r;
		}
		return null;
	}
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(var,expr);
		return r?r:this;
	}
}

DLambda dLambdaSmp(DVar var,DExpr expr)in{assert(var&&expr);}body{
	if(auto r=DLambda.constructHook(var,expr)) return r;
	return dLambda(var,expr);
}


DLambda dLambda(DVar var,DExpr expr)in{assert(var&&expr);}body{
	auto dbvar=cast(DBoundVar)var;
	if(!dbvar){
		dbvar=dBoundVar(1);
		assert(!expr.hasFreeVar(dbvar));
		expr=expr.incBoundVar(1,true).substitute(var,dbvar);
	}
	return uniqueBindingDExpr!DLambda(dbvar,expr);
}

class DArray: DExpr{
	DExpr length;
	DLambda entries;
	this(DExpr length,DLambda entries){
		this.length=length;
		this.entries=entries;
	}
	override string toStringImpl(Format formatting,Precedence prec){
		if(length is zero) return "[]";
		auto r=text("[",entries.var," ↦ ",entries.expr,"] (",length,")");
		if(prec!=Precedence.none) r="("~r~")"; // TODO: ok?
		return r;
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		if(auto r=length.forEachSubExpr(dg)) return r;
		if(auto r=entries.forEachSubExpr(dg)) return r; // TODO: ok?
		return 0;
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		if(auto r=length.freeVarsImpl(dg)) return r;
		if(auto r=entries.freeVarsImpl(dg)) return r; // TODO: ok?
		return 0;
	}
	override DExpr substitute(DVar var,DExpr e){
		return dArray(length.substitute(var,e),entries.substitute(var,e));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dArray(length.substituteFun(fun,q,args,context),entries.substituteFun(fun,q,args,context));
	}
	override DArray incBoundVar(int di,bool bindersOnly){
		return dArray(length.incBoundVar(di,bindersOnly),entries.incBoundVar(di,bindersOnly));
	}
	static DArray constructHook(DExpr length,DLambda entries){
		return staticSimplify(length,entries);
	}
	static DArray staticSimplify(DExpr length,DLambda entries,DExpr facts=one){
		auto nlength=length.simplify(facts);
		auto nentries=cast(DLambda)entries.simplify(facts);
		assert(!!nentries);
		if(nlength!is length||nentries!is entries) return dArray(nlength,nentries);
		return null;
	}
	override DArray simplifyImpl(DExpr facts){
		auto r=staticSimplify(length,entries,facts);
		return r?r:this;
	}
}

MapX!(TupleX!(DExpr,DLambda),DArray) uniqueMapDArray;
auto dArray(DExpr length,DLambda entries){
	if(auto r=DArray.constructHook(length,entries)) return r;
	auto t=tuplex(length,entries);
	if(t in uniqueMapDArray) return uniqueMapDArray[t];
	auto r=new DArray(length,entries);
	uniqueMapDArray[t]=r;
	return r;
}

auto dArray(DExpr length){ return dArray(length,dLambda(dBoundVar(1),zero)); }
auto dArray(DExpr length,DExpr default_){
	auto tmp=freshVar(); // TODO: get rid of this
	return dArray(length,dLambda(tmp,default_));
}
auto dArray(DExpr[] entries){
	auto tmp=freshVar(); // TODO: get rid of this!
	// TODO: not necessarily very clean for types that are not real numbers, but can be interpreted in terms of linear algebra
	DExpr body_=zero;
	foreach(i,e;entries) body_=body_+dIvr(DIvr.Type.eqZ,tmp-i)*entries[i];
	return dArray(dℕ(ℕ(entries.length)),dLambda(tmp,body_));
}

class DCat: DAssocOp{ // TODO: this should have n arguments, as it is associative!
	mixin Constructor;
	override @property Precedence precedence(){ return Precedence.plus; }
	override @property string symbol(Format formatting){ return "~"; }
	
	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(operands,facts);
		return r?r:this;
	}

	override DExpr substitute(DVar var,DExpr e){
		return dCat(operands.map!(a=>a.substitute(var,e)).array);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SetX!DVar context){
		return dCat(operands.map!(a=>a.substituteFun(fun,q,args,context)).array);
	}
	override DExpr incBoundVar(int di,bool bindersOnly){
		return dCat(operands.map!(a=>a.incBoundVar(di,bindersOnly)).array);
	}
	static DExpr constructHook(DExpr[] operands){
		return staticSimplify(operands);
	}
	private static DExpr staticSimplify(DExpr[] operands,DExpr facts=one){
		auto nop=operands.map!(a=>a.simplify(facts)).array;
		if(nop!=operands) return dCat(nop).simplify(facts);
		DExpr doCat(DExpr e1,DExpr e2){
			auto a1=cast(DArray)e1;
			auto a2=cast(DArray)e2;
			if(a1&&a1.length is zero) return e2;
			if(a2&&a2.length is zero) return e1;
			if(!a1||!a2) return null;
			auto tmp=freshVar(); // TODO: get rid of this!
			auto dbvar=cast(DBoundVar)a1.entries.var;
			assert(!!dbvar && dbvar is a2.entries.var);
			auto nesting=dbvar.i-1;
			return dArray(a1.length+a2.length,
						  dLambda(tmp,
								  a1.entries.incBoundVar(-nesting,false).apply(tmp)*dIvr(DIvr.Type.lZ,tmp-a1.length)
								  +a2.entries.incBoundVar(-nesting,false).apply(tmp-a1.length)*dIvr(DIvr.Type.leZ,a1.length-tmp))
						  .incBoundVar(nesting,false));
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
mixin(makeConstructorAssoc!DCat);

class DField: DOp{
	DExpr e;
	string f;
	this(DExpr e,string f){
		this.e=e; this.f=f;
	}
	override string symbol(Format formatting){ return "."; }
	override @property Precedence precedence(){
		return Precedence.index; // TODO: ok? (there is no precedence to the rhs)
	}
	override string toStringImpl(Format formatting, Precedence prec){
		return addp(prec, e.toStringImpl(formatting,Precedence.field)~"."~f);
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){
		return dg(e);
	}

	override DExpr simplifyImpl(DExpr facts){
		auto r=staticSimplify(e,f,facts);
		return r?r:this;
	}

	override DExpr substitute(DVar var,DExpr exp){
		return dField(e.substitute(var,exp),f);
	}

	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args,SHSet!DVar context){
		return dField(e.substituteFun(fun,q,args,context),f);
	}

	override DExpr incBoundVar(int di,bool bindersOnly){
		return dField(e.incBoundVar(di,bindersOnly),f);
	}

	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	
	static DExpr staticSimplify(DExpr e,string f,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(f=="length"){
			if(auto tpl=cast(DTuple)ne)
				return dℕ(ℕ(tpl.length));
			if(auto arr=cast(DArray)ne)
				return arr.length;
			if(auto cat=cast(DCat)ne){
				DExprSet s;
				foreach(op;cat.operands)
					DPlus.insert(s,dField(op,f));
				return dPlus(s).simplify(facts);
			}
		}
		if(auto rec=cast(DRecord)e)
			if(f in rec.values) return rec.values[f];
		// distribute over case distinction:
		if(e is zero) return zero;
		if(auto p=cast(DPlus)e){
			DExprSet r;
			foreach(s;p.summands) DPlus.insert(r,dField(s,f));
			return dPlus(r).simplify(facts);
		}
		if(auto m=cast(DMult)e){
			foreach(fc;m.factors){
				if(cast(DTuple)fc||cast(DArray)fc||cast(DRecord)fc)
					return (m.withoutFactor(fc)*dField(fc,f)).simplify(facts);
			}
		}
		if(ne !is e) return dField(ne,f);
		return null;
	}
	
	static DExpr constructHook(DExpr e,string f){
		return staticSimplify(e,f);
	}
}

MapX!(TupleX!(DExpr,string),DField) uniqueMapDField;
auto dField(DExpr e,string f){
	if(auto r=DField.constructHook(e,f)) return r;
	auto t=tuplex(e,f);
	if(t in uniqueMapDField) return uniqueMapDField[t];
	auto r=new DField(e,f);
	uniqueMapDField[t]=r;
	return r;
}


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
		scope int delegate(T) dg;
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

DExpr dGamma(DExpr t){
	auto x=freshVar(); // TODO: get rid of this
	return dInt(x,x^^(t-1)*dE^^(-x)*dIvr(DIvr.Type.leZ,-x));
}

DExpr dBeta(DExpr x,DExpr y){ // constraints: x>0 and y>0
	auto t=freshVar(); // TODO: get rid of this
	return dInt(t,dBounded!"[]"(t,zero,one)*t^^(x-1)*(1-t)^^(y-1));
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
