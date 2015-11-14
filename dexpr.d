// TODO: the caches should use weak references

import std.conv;
import hashtable, util;

import std.algorithm, std.array;
import std.typecons: Q=Tuple, q=tuple;

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
}

enum formatting=Format.default_;
//enum formatting=Format.matlab;
//enum formatting=Format.maple; version=DISABLE_INTEGRATION;

enum Precedence{
	none,
	plus,
	uminus,
	lim,
	intg,
	mult,
	div,
	diff,
	pow,
	invalid,
}

abstract class DExpr{
	override string toString(){
		return toStringImpl(Precedence.none);
	}
	abstract string toStringImpl(Precedence prec);

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
		return r;
	}

	// TODO: implement in terms of 'forEachSubExpr'?
	abstract DExpr substitute(DVar var,DExpr e);
	abstract DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args);
	abstract DExpr incDeBruin(int di);
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
	enum ValidBinary(string s)=["+","-","*","/","^^"].canFind(s);
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
	final opBinary(string op)(ℕ e)if(ValidBinary!op){
		return mixin("this "~op~" e.dℕ");
	}
	final opBinaryRight(string op)(ℕ e)if(ValidBinary!op){
		return mixin("e.dℕ "~op~" this");
	}

	final opBinary(string op)(double e)if(ValidBinary!op){
		return mixin("this "~op~" e.dFloat");
	}
	final opBinaryRight(string op)(double e)if(ValidBinary!op){
		return mixin("e.dFloat "~op~" this");
	}


	mixin template Constant(){
		override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
		override int freeVarsImpl(scope int delegate(DVar) dg){ return 0; }
		override DExpr substitute(DVar var,DExpr e){ assert(var !is this); return this; }
		override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){ assert(fun !is this); return this; }
		override DExpr incDeBruin(int di){ return this; }
		override DExpr simplifyImpl(DExpr facts){ return this; }
	}
}
alias DExprSet=SetX!DExpr;
class DVar: DExpr{
	string name;
	/+private+/ this(string name){ this.name=name; } // TODO: make private!
	override string toStringImpl(Precedence prec){ return name; }

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
	override int freeVarsImpl(scope int delegate(DVar) dg){ return dg(this); }
	override DExpr substitute(DVar var,DExpr e){ return this is var?e:this; }
	override DExpr substituteFun(DFunVar var,DExpr q,DVar[] args){ return this; }
	override DVar incDeBruin(int di){ return this; }
	override DExpr simplifyImpl(DExpr facts){
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

class DDeBruinVar: DVar{
	int i;
	private this(int i){ this.i=i; super("ξ"~lowNum(i)); }
	override DDeBruinVar incDeBruin(int di){ return dDeBruinVar(i+di); }
}
DDeBruinVar[int] uniqueMapDeBruin;
DDeBruinVar dDeBruinVar(int i){
	return i !in uniqueMapDeBruin ?
		uniqueMapDeBruin[i]=new DDeBruinVar(i):
		uniqueMapDeBruin[i];
}

class Dℕ : DExpr{
	ℕ c;
	private this(ℕ c){ this.c=c; }
	override string toStringImpl(Precedence prec){
		string r=text(c);
		static if(formatting==Format.maple){
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
	double c;
	private this(double c){ this.c=c; }
	override string toStringImpl(Precedence prec){
		import std.format;
		string r=format("%.16e",c);
		static if(formatting==Format.maple){
			if(c<0) r="("~r~")";
		}else if(prec>Precedence.uminus&&c<0)
			r="("~r~")";
		return r;
	}

	mixin Constant;
}

//DFloat[double] uniqueMapDFloat; // TODO: get rid of this!
DExpr dFloat(double c){
	import std.math: floor;
	import std.format: format;
	if(floor(c)==c) return dℕ(ℕ(format("%.0f",c))); // TODO: don't rely on format here!
	//if(c in uniqueMapDFloat) return uniqueMapDFloat[c];
	//return uniqueMapDFloat[c]=new DFloat(c);
	return new DFloat(c);
}

class DE: DExpr{
	override string toStringImpl(Precedence prec){ return "e"; }
	mixin Constant;
}
private static DE theDE;
@property DE dE(){ return theDE?theDE:(theDE=new DE); }

class DΠ: DExpr{
	override string toStringImpl(Precedence prec){
		static if(formatting==Format.matlab) return "pi";
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
	abstract @property string symbol();
	bool rightAssociative(){ return false; }
	abstract @property Precedence precedence();
	protected final string addp(Precedence prec, string s, Precedence myPrec=Precedence.invalid){
		if(myPrec==Precedence.invalid) myPrec=precedence;
		return prec > myPrec||rightAssociative&&prec==precedence? "(" ~ s ~ ")":s;
	}
}

abstract class DCommutAssocOp: DOp{
	DExprSet operands;
	protected mixin template Constructor(){ private this(DExprSet e)in{assert(e.length>1); }body{ operands=e; } }
	override string toStringImpl(Precedence prec){
		string r;
		auto ops=operands.array.map!(a=>a.toStringImpl(precedence)).array;
		sort(ops);
		foreach(o;ops) r~=symbol~o;
		return addp(prec, r[symbol.length..$]);
	}
}

MapX!(TupleX!(typeof(typeid(DExpr)),DExprSet),DExpr) uniqueMapCommutAssoc;
MapX!(TupleX!(typeof(typeid(DExpr)),DExpr,DExpr),DExpr) uniqueMapNonCommutAssoc;

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
	override @property string symbol(){ return "+"; }

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
	override DExpr substitute(DVar var,DExpr e){
		DExprSet res;
		foreach(s;summands) insert(res,s.substitute(var,e));
		return dPlus(res);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] vars){
		DExprSet res;
		foreach(s;summands) insert(res,s.substituteFun(fun,q,vars));
		return dPlus(res);
	}
	override DExpr incDeBruin(int di){
		DExprSet res;
		foreach(s;summands) insert(res,s.incDeBruin(di));
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
				if(expanded !is p) insertAndSimplify(summands,expanded,facts);
				return;
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
						return (f.c+toDouble(nd[0])/toDouble(nd[1])).dFloat;
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

			static DExpr combineIvr(DExpr e1,DExpr e2){
				if(auto ivr1=cast(DIvr)e1){
					if(ivr1.type is DIvr.Type.eqZ){
						if(e2 is dIvr(DIvr.Type.lZ,ivr1.e))
							return dIvr(DIvr.Type.leZ,ivr1.e);
						if(e2 is dIvr(DIvr.Type.lZ,-ivr1.e))
							return dIvr(DIvr.Type.leZ,-ivr1.e);
						if(e2 is dIvr(DIvr.Type.neqZ,ivr1.e))
							return one;
					}else if(ivr1.type is DIvr.Type.leZ){
						if(e2 is dIvr(DIvr.Type.leZ,-ivr1.e))
							return 2*dIvr(DIvr.Type.eqZ,ivr1.e)+dIvr(DIvr.Type.neqZ,ivr1.e);
						if(e2 is dIvr(DIvr.Type.lZ,-ivr1.e))
							return one;
					}
				}
				return null;
			}
			if(auto r=combineIvr(e1,e2)) return r;
			if(auto r=combineIvr(e2,e1)) return r;
			
			return null;
		}
		// TODO: use suitable data structures
		foreach(s;summands){
			if(auto nws=combine(s,summand,facts)){
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
		DVar tmp=new DVar("tmp"); // TODO: get rid of this!
		// dw("!! ",summands);
		foreach(s;summands){
			if(auto dint=cast(DInt)s){
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
					return sum*common;
			}
		}
		return null;
	}

	override DExpr simplifyImpl(DExpr facts){
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
	override @property string symbol(){
		static if(formatting==Format.maple) return "*";
		else static if(formatting==Format.matlab) return ".*";
		else return "·";
	}
	override string toStringImpl(Precedence prec){
		auto frac=this.getFractionalFactor().getFraction();
		if(frac[0]<0){
			static if(formatting==Format.maple){
				return "(-"~(-this).toStringImpl(Precedence.uminus)~")";
			}else{
				return addp(prec,"-"~(-this).toStringImpl(Precedence.uminus),Precedence.uminus);
			}
		}
		//if(frac[0]!=1&&frac[1]!=1) // TODO
		// TODO: use suitable data structures
		return super.toStringImpl(prec);
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
	override DExpr substitute(DVar var,DExpr e){
		DExprSet res;
		foreach(f;factors) insert(res,f.substitute(var,e));
		return dMult(res);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		DExprSet res;
		foreach(f;factors) insert(res,f.substituteFun(fun,q,args));
		return dMult(res);
	}
	override DExpr incDeBruin(int di){
		DExprSet res;
		foreach(f;factors) insert(res,f.incDeBruin(di));
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
						return (f.c*toDouble(nd[0])/toDouble(nd[1])).dFloat;
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
					static DExpr tryCombine(DExpr a,DExpr b){
						DExprSet s;
						DMult.insert(s,a);
						DMult.insert(s,b);
						if(a !in s || b !in s)
							return dMult(s);
						return null;
					}
					auto exp1=p.operands[1],exp2=pf.operands[1];
					if(exp1 is exp2){
						auto a=p.operands[0],b=pf.operands[0];
						if(auto r=tryCombine(a,b))
							return r^^exp1;
					}
					if(exp1 is -exp2){
						auto a=p.operands[0],b=1/pf.operands[0];
						if(auto r=tryCombine(a,b))
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
						if(ivr1.e is -ivr2.e)
							return dIvr(eqZ,ivr1.e);
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
					insert(factors,nwf);
				return;
			}
		}
		assert(factors.length==1||one !in factors);
		factors.insert(factor);
	}
	override DExpr simplifyImpl(DExpr facts){
		DExprSet myFactors;
		DExprSet myFacts;
		foreach(f;this.factors) if(auto d=cast(DDelta)f) facts=facts*dIvr(DIvr.Type.eqZ,d.e);
		foreach(f;this.factors){
			if(cast(DIvr)f) insert(myFacts,f,facts);
			else myFactors.insert(f);
		}
		auto myFactsM=dMult(myFacts);
		DExpr newFacts=facts*myFactsM;
		DExprSet simpFactors;
		foreach(f;myFactors) insert(simpFactors,f.simplify(newFacts),newFacts);
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
	override string toStringImpl(Precedence prec){
		return addp(prec, operands[0].toStringImpl(precedence) ~ symbol ~ operands[1].toStringImpl(precedence));
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
	override @property string symbol(){
		static if(formatting==Format.matlab) return ".^";
		else return "^";
	}
	override bool rightAssociative(){ return true; }

	override bool isFraction(){ return cast(Dℕ)operands[0] && cast(Dℕ)operands[1]; }
	override ℕ[2] getFraction(){
		auto d=cast(Dℕ)operands[0];
		assert(d && operands[1] is -one);
		return [ℕ(1),d.c];
	}

	override string toStringImpl(Precedence prec){
		auto frc=operands[1].getFractionalFactor().getFraction();
		if(frc[0]<0){
			enum pre=formatting==Format.matlab?"1./":formatting==Format.maple?"1/":"⅟";
			return addp(prec,pre~(operands[0]^^-operands[1]).toStringImpl(Precedence.div),Precedence.div);
		}
			// also nice, but often hard to read: ½⅓¼⅕⅙
		static if(formatting==Format.default_){		
			if(auto c=cast(Dℕ)operands[1])
				return addp(prec,operands[0].toStringImpl(Precedence.pow)~highNum(c.c));
			if(auto c=cast(DPow)operands[1]){
				if(auto e=cast(Dℕ)c.operands[1]){
					if(e.c==-1){
						if(auto d=cast(Dℕ)c.operands[0]){
							if(2<=d.c&&d.c<=4)
								return text("  √∛∜"d[d.c.toLong()],overline(operands[0].toString()));
						}
					}
				}
			}
		}
		return super.toStringImpl(prec);
	}

	override DExpr substitute(DVar var,DExpr e){
		return operands[0].substitute(var,e)^^operands[1].substitute(var,e);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return operands[0].substituteFun(fun,q,args)^^operands[1].substituteFun(fun,q,args);
	}
	override DExpr incDeBruin(int di){
		return operands[0].incDeBruin(di)^^operands[1].incDeBruin(di);
	}

	static DExpr constructHook(DExpr e1,DExpr e2){
		return staticSimplify(e1,e2);
	}

	private static DExpr staticSimplify(DExpr e1,DExpr e2,DExpr facts=one){
		auto ne1=e1.simplify(facts);
		auto ne2=e2.simplify(facts);
		if(ne1!is e1||ne2!is e2) return dPow(ne1,ne2);
		if(e1 !is mone) if(auto c=cast(Dℕ)e1) if(c.c<0) return mone^^e2*dℕ(-c.c)^^e2;
		if(auto m=cast(DMult)e1){ // TODO: do we really want auto-distribution?
			DExprSet factors;
			foreach(f;m.operands){
				DMult.insert(factors,f^^e2);
			}
			return dMult(factors);
		}
		if(auto p=cast(DPow)e1) return p.operands[0]^^(p.operands[1]*e2);
		if(e1 is one||e2 is zero) return one;
		if(e1 is -one && e2 is -one) return -one;
		if(e2 is one) return e1;
		if(e1.mustBeZeroOrOne()&&(-e2).mustBeLessOrEqualZero())
			return dIvr(DIvr.Type.neqZ,e2)*e1+dIvr(DIvr.Type.eqZ,e2);
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
				if(nd[0]!=1) continue;
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
				return (f1.c^^(toDouble(nd[0])/toDouble(nd[1]))).dFloat;
			}
		}
		if(e1.isFraction()){
			if(auto f2=cast(DFloat)e2){
				auto nd=e1.getFraction();
				return ((toDouble(nd[0])/toDouble(nd[1]))^^f2.c).dFloat;
			}
		}
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
	DExpr[] coefficients;
	bool initialized(){ return !!var; }
	T opCast(T:bool)(){ return initialized(); }
	long degree(){ return coefficients.length-1; }
	void addCoeff(long exp,DExpr coeff)in{assert(exp>=0);}body{
		while(coefficients.length<=exp) coefficients~=zero;
		coefficients[exp]=coefficients[exp]+coeff;
	}
	DExpr toDExpr(){
		DExprSet r;
		foreach(i;0..coefficients.length)
			DPlus.insert(r,coefficients[i]*var^^i);
		return dPlus(r);
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
	if(!r.coefficients.length) r.coefficients~=zero;
	return r;
}

abstract class DUnaryOp: DOp{
	DExpr operand;
	protected mixin template Constructor(){ private this(DExpr e){ operand=e; } }
	override string toStringImpl(Precedence prec){
		return addp(prec, symbol~operand.toStringImpl(precedence));
	}
}
DExpr dUMinus(DExpr e){ return mone*e; }

// TODO: improve these procedures:
bool couldBeZero(DExpr e){
	if(cast(DΠ)e) return false;
	if(cast(DE)e) return false;
	if(auto c=cast(Dℕ)e) return c.c==0;
	if(auto c=cast(DFloat)e) return c.c==0;
	if(auto p=cast(DPow)e) return couldBeZero(p.operands[0]);
	return true;
}

bool mustBeZeroOrOne(DExpr e){
	if(e is zero || e is one) return true;
	if(cast(DIvr)e) return true;
	return false;
}

bool mustBeLessOrEqualZero(DExpr e){
	if(auto c=cast(Dℕ)e) return c.c<=0;
	if(auto c=cast(DFloat)e) return c.c<=0;
	if(auto p=cast(DPow)e){
		if(auto exp=cast(Dℕ)p.operands[1]){
			if(exp.c%2){
				return mustBeLessOrEqualZero(p.operands[0]);
			}
		}
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
}

BoundStatus getBoundForVar(DIvr ivr,DVar var,out DExpr bound){ // TODO: get rid of this in favour of the next function?
	enum r=BoundStatus.fail;
	with(DIvr.Type) if(ivr.type!=leZ) return r;
	foreach(s;ivr.e.summands){
		if(!s.hasFactor(var)) continue; // TODO: non-linear constraints
		auto cand=s.withoutFactor(var);
		if(cand.hasFreeVar(var)) return r;
		auto lZ=dIvr(DIvr.Type.lZ,cand)==one;
		auto gZ=dIvr(DIvr.Type.lZ,-cand)==one;
		if(!lZ&&!gZ) return r;
		auto ne=(var-ivr.e/cand).simplify(one); // TODO: are there cases where this introduces division by 0?
		if(ne.hasFreeVar(var)) return r;
		// TODO: must consider strictness!
		bound=ne;
		return lZ?BoundStatus.lowerBound:BoundStatus.upperBound;
	}
	return r;
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
		if(cast(DPlus)ow[1]) return null; // TODO (polynomials,...)
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
		if(p.operands[1] !is -one) return null; // TODO
		if(couldBeZero(rhs)){ // TODO: is this right? (This is guaranteed never to happen for dirac deltaas, so maybe optimize it out for that caller).
			info.needCaseSplit=true;
			if(usage.caseSplit) info.caseSplits~=SolutionInfo.CaseSplit(rhs,one);
		}
		auto r=p.operands[0].solveFor(var,one/rhs,usage,info);
		info.caseSplits=info.caseSplits.partition!(x=>x.expression is zero);
		foreach(ref x;info.caseSplits) x.expression=one/x.expression;
		if(usage.bound) if(usage.bound) info.bound.invertIflZ(-p.operands[0]*rhs);
		return r;
	}
	return null;
}


Q!(DIvr.Type,"type",DExpr,"e") negateDIvr(DIvr.Type type,DExpr e){
	final switch(type) with(DIvr.Type){
		case lZ: return typeof(return)(leZ,-e);
		case leZ: return typeof(return)(lZ,-e); // currently probably unreachable
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

DExpr factorDIvr(alias wrap)(DExpr e){
	foreach(ivr;e.allOf!DIvr){ // TODO: do all in bulk?
		auto neg=negateDIvr(ivr);
		return ivr*wrap(e.simplify(ivr))+neg*wrap(e.simplify(neg));
	}
	return null;
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
	this(Type type,DExpr e){ this.type=type; this.e=e; }

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: correct?
	override int freeVarsImpl(scope int delegate(DVar) dg){ return e.freeVarsImpl(dg); }
	override DExpr substitute(DVar var,DExpr exp){ return dIvr(type,e.substitute(var,exp)); }
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){ return dIvr(type,e.substituteFun(fun,q,args)); }
	override DExpr incDeBruin(int di){ return dIvr(type,e.incDeBruin(di)); }

	override string toStringImpl(Precedence prec){
		with(Type){
			static if(formatting==Format.maple){
				return "piecewise("~e.toString()~(type==eqZ?"=":type==neqZ?"<>":type==lZ?"<":"<=")~"0,1,0)";
			}else static if(formatting==Format.matlab){
				return "("~e.toString()~(type==eqZ?"==":type==neqZ?"!=":type==lZ?"<":"<=")~"0)";
			}else{
				return "["~e.toString()~(type==eqZ?"=":type==neqZ?"≠":type==lZ?"<":"≤")~"0]";
			}
		}
	}

	static DExpr constructHook(Type type,DExpr e){
		return staticSimplify(type,e);
	}

	static DExpr staticSimplify(Type type,DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne !is e){
			auto r=dIvr(type,ne);
			if(facts !is one) r=r.simplify(facts);
			return r;
		}
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
		auto cancel=uglyFractionCancellation(e);
		if(cancel!=one) return dIvr(type,dDistributeMult(e,cancel));
		if(type==Type.lZ) return dIvr(Type.leZ,e)*dIvr(Type.neqZ,e);
		if(auto fct=factorDIvr!(e=>dIvr(type,e))(e)) return fct;
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
		if(cast(DDeBruinVar)a&&!cast(DDeBruinVar)b) return true;
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

class DDelta: DExpr{ // Dirac delta function
	DExpr e;
	private this(DExpr e){ this.e=e; }
	override string toStringImpl(Precedence prec){
		static if(formatting==Format.maple){
			return text("Dirac(",e.toString(),")");
		}else{
			return "δ["~e.toString()~"]";
		}
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: ok?
	override int freeVarsImpl(scope int delegate(DVar) dg){ return e.freeVarsImpl(dg); }
	override DExpr substitute(DVar var,DExpr exp){ return dDelta(e.substitute(var,exp)); }
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dDelta(e.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){ return dDelta(e.incDeBruin(di)); }

	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(one); // cannot use all facts! (might remove a free variable)
		if(ne !is e) return dDelta(ne);
		auto cancel=uglyFractionCancellation(e);
		if(cancel!=one) return dDelta(dDistributeMult(e,cancel))*cancel;
		if(auto fct=factorDIvr!(e=>dDelta(e))(e)) return fct;
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
			auto rest=expr.withoutFactor(d);
			auto constraints=one;
			foreach(ref x;info.caseSplits)
				constraints=constraints*dIvr(DIvr.Type.neqZ,x.constraint);
			auto r=constraints is zero?zero:
				constraints*rest.substitute(var,s)/dAbs(dDiff(var,d.e,s));
			foreach(ref x;info.caseSplits){
				auto curConstr=constraints.withoutFactor(dIvr(DIvr.Type.neqZ,x.constraint));
				r=r+curConstr*dIvr(DIvr.Type.eqZ,x.constraint)*dIntSmp(var,rest*dDelta(x.expression));
			}
			return r;
		}
		return null;
	}
}

//mixin(makeConstructorUnary!DDelta);

auto dDelta(DExpr a){
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

DExpr[2] splitPlusAtVar(DExpr e,DVar var){
	DExprSet outside, within;
	//writeln("splitting: ",e,"\nat: ",var);
	//scope(exit) writeln("res: ",dPlus(outside),", ",dPlus(within));
	DExpr[2] handlePow(DPow p){
		DExpr[2] fail=[null,null];
		auto a=cast(DPlus)p.operands[0];
		auto c=cast(Dℕ)p.operands[1];
		if(!a||!c) return fail;
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
						rest=rest/f;
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

bool hasZerosOfMeasureZero(DExpr e){
	// TODO: check the necessary preconditions for those
	// (the given equation must be nondegenerate.)
	return true; // TODO: actually check this!
}



/+import std.datetime;
StopWatch sw;
static ~this(){
	writeln(sw.peek().to!("msecs",double));
}+/

static DExpr getDeBruinExpr(DVar tvar, DExpr expr, DVar var){
	//assert(tvar is dDeBruinVar(1),text(tvar)); // TODO: finally fix the deBruinVar situation...
	assert(!cast(DDeBruinVar)var);
	return expr.substitute(tvar,var).incDeBruin(-1);		
}

import integration;
class DInt: DOp{
	private{
		DDeBruinVar var;
		DExpr expr;
		this(DDeBruinVar var,DExpr expr){ this.var=var; this.expr=expr; }
	}
	DExpr getExpr(DVar var){ return getDeBruinExpr(this.var,expr,var); }
	override @property Precedence precedence(){ return Precedence.intg; }
	override @property string symbol(){ return "∫"; }
	override string toStringImpl(Precedence prec){
		static if(formatting==Format.maple){
			return text("int(",expr.toString(),",",var.toString(),"=-infinity..infinity)");
		}else{
			return addp(prec,symbol~"d"~var.toString()~expr.toStringImpl(precedence));
		}
	}
	static DExpr constructHook(DVar var,DExpr expr){
		return staticSimplify(var,expr);
	}

	version(INTEGRAL_STATS){
		static int numIntegrals=0;
		static void[0][DExpr] integrals;
		static ~this(){
			writeln("A: ",numIntegrals);
			writeln("B: ",integrals.length);
		}
	}

	static DExpr staticSimplify(DVar var,DExpr expr,DExpr facts=one){
		version(DISABLE_INTEGRATION){
			if(expr is zero) return zero;
			return null;
		}
		version(INTEGRAL_STATS){
			numIntegrals++;
			auto dbvar=dDeBruinVar(1);
			auto newexpr=expr.incDeBruin(1).substitute(var,dbvar);
			integrals[newexpr]=[];
		}

		if(cast(DDeBruinVar)var){
			auto tmp=new DVar("tmp"); // TODO: get rid of this!
			return staticSimplify(tmp,getDeBruinExpr(var,expr,tmp));
		}

		auto nexpr=expr.simplify(facts); // TODO: this pattern always simplifies everything twice, make efficient
		if(nexpr !is expr) expr=nexpr;
		/*static dInt(DVar var,DExpr expr){
			if(cast(DDeBruinVar)var){
				if(auto hooked=staticSimplify(var,expr)){
					bool check(){
						foreach(i;hooked.allOf!DInt)
							if(i.var is var)
								return true;
							return false;
					}
					if(!check()) hooked=hooked.incDeBruin(-1); // TODO: is this right?
					return hooked;
				}
			}
			return .dInt(var,expr);
			}*/
		auto ow=expr.splitMultAtVar(var);
		if(ow[0] !is one) return ow[0]*dIntSmp(var,ow[1]);
		DExpr deltaSubstitution(bool caseSplit){
			// TODO: only extract deltas once?
			// TODO: detect when to give up early?
			foreach(f;expr.factors){
				if(!f.hasFreeVar(var)) continue;
				if(auto d=cast(DDelta)f){
					if(auto r=DDelta.performSubstitution(var,d,expr,caseSplit))
						return r.simplify(facts);
				}
			}
			return null;
		}
		if(auto r=deltaSubstitution(false))
			return r;
		foreach(T;Seq!(DDelta,DIvr)){ // TODO: need to split on DIvr?
			foreach(f;expr.factors){
				if(auto p=cast(DPlus)f){
					bool check(){
						foreach(d;p.allOf!T)
							if(d.e.hasFreeVar(var))
								return true;
						return false;
					}
					if(check()){
						/+DExprSet works;
						DExprSet doesNotWork;+/
						DExprSet s;
						foreach(k;distributeMult(p,expr.withoutFactor(f))){
							/+auto ow=k.splitMultAtVar(var);
							auto r=staticSimplify(var,ow[1],facts);
							if(r) DPlus.insert(works,ow[0]*r);
							else DPlus.insert(doesNotWork,k);+/
							DPlus.insert(s,dIntSmp(var,k));
						}
						/+if(works.length){
							auto r=dPlus(works).simplify(facts);
							if(doesNotWork.length) r = r + dInt(var,dPlus(doesNotWork));
							return r;
						}+/
						//dw(s);
						return dPlus(s).simplify(facts);
					}
				}
			}
		}
		if(auto r=deltaSubstitution(true))
			return r;
		if(expr is one) return null; // (infinite integral)

		if(auto r=definiteIntegral(var,expr))
			return r.simplify(facts);
		// Fubini
		foreach(f;expr.factors){
			// assert(f.hasFreeVar(var));
			if(auto other=cast(DInt)f){
				assert(!!cast(DDeBruinVar)other.var);
				auto tmpvar1=new DVar("tmp1"); // TODO: get rid of this!
				auto tmpvar2=new DVar("tmp2"); // TODO: get rid of this!
				auto intExpr=expr.withoutFactor(f).substitute(var,tmpvar1)*
					(cast(DInt)other.substitute(var,tmpvar1)).getExpr(tmpvar2);
				auto ow=intExpr.splitMultAtVar(tmpvar1);
				if(auto res=staticSimplify(tmpvar1,ow[1]))
					return dIntSmp(tmpvar2,res*ow[0]);
			}
		}
		if(!expr.hasFreeVar(var)) return expr*dInt(var,one); // (infinite integral)
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
		return dInt(this.var,expr.substitute(var,e));
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dInt(var,expr.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dInt(var.incDeBruin(di),expr.incDeBruin(di));
	}
}

bool hasIntegrals(DExpr e){ return hasAny!DInt(e); }

MapX!(TupleX!(typeof(typeid(DExpr)),DDeBruinVar,DExpr,DExpr),DExpr) uniqueMapBinding;
auto uniqueBindingDExpr(T)(DDeBruinVar v,DExpr a,DExpr b=null){
	auto t=tuplex(typeid(T),v,a,b);
	if(t in uniqueMapBinding) return cast(T)uniqueMapBinding[t];
	static if(is(typeof(new T(v,a)))) auto r=new T(v,a);
	else auto r=new T(v,a,b);
	uniqueMapBinding[t]=r;
	return r;
}

DExpr dIntSmp(DVar var,DExpr expr){
	if(auto r=DInt.constructHook(var,expr)) return r;
	return dInt(var,expr);
}

DExpr dInt(DVar var,DExpr expr){
	//if(auto dbvar=cast(DDeBruinVar)var) return uniqueBindingDExpr!DInt(dbvar,expr);
	auto dbvar=cast(DDeBruinVar)var;
	if(!dbvar){
		dbvar=dDeBruinVar(1);
		expr=expr.incDeBruin(1).substitute(var,dbvar);
	}
	return uniqueBindingDExpr!DInt(dbvar,expr);
}

import limits;
class DLim: DOp{
	DVar v;
	DExpr e;
	DExpr x;
	this(DVar v,DExpr e,DExpr x){ this.v=v; this.e=e; this.x=x; }
	override @property string symbol(){ return text("lim[",v," → ",e,"]"); }
	override Precedence precedence(){ return Precedence.lim; } // TODO: ok?
	override string toStringImpl(Precedence prec){
		return addp(prec,symbol~x.toStringImpl(precedence));
	}

	static DExpr constructHook(DVar v,DExpr e,DExpr x){
		return staticSimplify(v,e,x);
	}

	static DExpr staticSimplify(DVar v,DExpr e,DExpr x,DExpr facts=one){
		if(cast(DDeBruinVar)v){
			auto tmp=new DVar("tmp"); // TODO: get rid of this!
			return staticSimplify(tmp,getDeBruinExpr(v,e,tmp),getDeBruinExpr(v,x,tmp));
		}
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
		auto nx=x.substitute(var,exp);
		auto ne=e;
		if(v !is var) ne=e.substitute(var,exp);
		return dLim(v,ne,nx);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dLim(v,e.substituteFun(fun,q,args),x.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dLim(v.incDeBruin(di),e.incDeBruin(di),x.incDeBruin(di));
	}
}

DExpr dLimSmp(DVar v,DExpr e,DExpr x){
	if(auto r=DLim.constructHook(v,e,x)) return r;
	return dLim(v,e,x);
}

DExpr dLim(DVar v,DExpr e,DExpr x){
	//if(auto dbvar=cast(DDeBruinVar)var) return uniqueBindingDExpr!DInt(dbvar,expr);
	assert(!e.hasFreeVar(v));
	auto dbvar=cast(DDeBruinVar)v;
	if(!dbvar){
		dbvar=dDeBruinVar(1);
		x=x.incDeBruin(1).substitute(v,dbvar);
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
	override @property string symbol(){ return "d/d"~v.toString(); }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Precedence prec){
		return addp(prec,symbol~"["~e.toString()~"]("~x.toString()~")");
	}

	static DExpr constructHook(DVar v,DExpr e,DExpr x){
		return staticSimplify(v,e,x);
	}

	static DExpr staticSimplify(DVar v,DExpr e,DExpr x,DExpr facts=one){
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
		if(v !is var) ne=e.substitute(var,exp);
		return dDiff(v,ne,nx);
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dDiff(v,e.substituteFun(fun,q,args),x.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dDiff(v.incDeBruin(di),e.incDeBruin(di),x.incDeBruin(di));
	}
}

MapX!(TupleX!(DVar,DExpr,DExpr),DExpr) uniqueMapDiff;
DExpr dDiff(DVar v,DExpr e,DExpr x){
	if(auto dbvar=cast(DDeBruinVar)v) return uniqueBindingDExpr!DDiff(dbvar,e,x);
	if(auto r=DDiff.constructHook(v,e,x)) return r;
	auto dbvar=dDeBruinVar(1);
	e=e.incDeBruin(1).substitute(v,dbvar);
	return uniqueBindingDExpr!DDiff(dbvar,e,x);
}

DExpr dDiff(DVar v,DExpr e){ return dDiff(v,e,v); }

class DAbs: DOp{
	DExpr e;
	this(DExpr e){ this.e=e; }
	override @property string symbol(){ return "|"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Precedence prec){
		return "|"~e.toString()~"|";
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
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dAbs(e.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dAbs(e.incDeBruin(di));
	}

	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		e=e.simplify(facts);
		if(e.isFraction()){
			auto nd=e.getFraction();
			assert(nd[1]>0);
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
	override @property string symbol(){ return "log"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Precedence prec){
		return "log("~e.toString()~")";
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
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dLog(e.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dLog(e.incDeBruin(di));
	}

	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		e=e.simplify(facts);
		if(auto c=cast(DE)e) return one;
		if(e is one) return zero;
		if(auto m=cast(DMult)e){
			DExprSet r;
			foreach(f;m.factors)
				r.insert(dLog(f));
			return dPlus(r);
		}
		if(auto p=cast(DPow)e)
			return p.operands[1]*dLog(p.operands[0]);
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
	override @property string symbol(){ return "sin"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Precedence prec){
		return "sin("~e.toString()~")";
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
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dSin(e.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dSin(e.incDeBruin(di));
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
	override @property string symbol(){ return "⌊.⌋"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Precedence prec){
		return "⌊"~e.toString()~"⌋";
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
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dFloor(e.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dFloor(e.incDeBruin(di));
	}
	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!is e) return dFloor(ne);
		if(e.isFraction()){
			auto nd=e.getFraction();
			return dℕ(nd[0]/nd[1]);
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
	override @property string symbol(){ return "⌈.⌉"; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Precedence prec){
		return "⌈"~e.toString()~"⌉";
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
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		return dCeil(e.substituteFun(fun,q,args));
	}
	override DExpr incDeBruin(int di){
		return dCeil(e.incDeBruin(di));
	}
	static DExpr constructHook(DExpr e){
		return staticSimplify(e);
	}
	static DExpr staticSimplify(DExpr e,DExpr facts=one){
		auto ne=e.simplify(facts);
		if(ne!is e) return dCeil(ne);
		if(e.isFraction()){
			auto nd=e.getFraction();
			return dℕ((nd[0]+nd[1]-1)/nd[1]);
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
	override @property string symbol(){ return "(d/dx)⁻¹[e^(-x²)]"; }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Precedence prec){
		return addp(prec,symbol~"("~x.toString()~")");
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
		if(nx !is x) return dGaussInt(nx);
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
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		auto nx=x.substituteFun(fun,q,args);
		return dGaussInt(nx);
	}
	override DExpr incDeBruin(int di){
		return dGaussInt(x.incDeBruin(di));
	}
}

auto dGaussInt(DExpr x){ return uniqueDExprUnary!DGaussInt(x); }

class DInf: DExpr{ // TODO: explicit limits?
	override string toStringImpl(Precedence prec){ return "∞"; }
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
	override string toStringImpl(Precedence prec){ return name; }

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
	override int freeVarsImpl(scope int delegate(DVar) dg){ return 0; }
	override DExpr substitute(DVar var,DExpr e){ return this; }
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){ assert(0); }
	override DExpr incDeBruin(int di){ return this; }
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
	override @property string symbol(){ return fun.name; }
	override Precedence precedence(){ return Precedence.none; }
	override string toStringImpl(Precedence prec){
		return fun.name~"("~args.map!(to!string).join(",")~")";
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

	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){
		if(fun !is this.fun) return this;
		auto r=q;
		foreach(i,a;this.args) r=r.substitute(args[i],a);
		return r;
	}

	override DExpr incDeBruin(int di){
		return dFun(fun,args.map!(a=>a.incDeBruin(di)).array);
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


import std.traits: ParameterTypeTuple;
import std.typetuple;
auto visit(T,S...)(DExpr node,S args){
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

auto allOf(T)(DExpr e,bool belowIntegrals=false){
	static struct AllOfVisitor{
		scope int delegate(T) dg;
		bool belowIntegrals;
		int r=0;
		int perform(T t){
			if(auto r=dg(t))
				return this.r=r;
			static if(is(T==DInt)){
				if(belowIntegrals)
					if(auto r=t.expr.visit!AllOfVisitor(dg,belowIntegrals).r)
					   return this.r=r;
			}
			return 0;
		}
		static if(!is(T==DInt)){
			int perform(DInt t){
				if(belowIntegrals){
					if(auto r=t.expr.visit!AllOfVisitor(dg,belowIntegrals).r)
					   return this.r=r;
				}
				return 0;
			}
		}
	}
	static struct AllOf{
		DExpr e;
		bool belowIntegrals;
		int opApply(scope int delegate(T) dg){
			return e.visit!AllOfVisitor(dg,belowIntegrals).r;
		}
	}
	return AllOf(e,belowIntegrals);
}

bool hasAny(T)(DExpr e,bool belowIntegrals=true){ foreach(x;allOf!T(e,belowIntegrals)) return true; return false; }
