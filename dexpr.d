import std.conv;
import hashtable, util;

import std.algorithm, std.array;

enum Precedence{
	none,
	plus,
	uminus,
	intg,
	diff,
	mult,
	pow,
	invalid,
}

abstract class DExpr{
	override string toString(){
		return toStringImpl(Precedence.none);
	}
	abstract string toStringImpl(Precedence prec);

	abstract int forEachSubExpr(scope int delegate(DExpr) dg);

	// TODO: implement in terms of 'forEachSubExpr'?
	abstract DExpr substitute(DVar var,DExpr e);
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
	DExpr solveFor(DVar var,DExpr rhs, ref DExpr[] constraints){ return null; }

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

	mixin template Constant(){
		override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
		override int freeVarsImpl(scope int delegate(DVar) dg){ return 0; }
		override DExpr substitute(DVar var,DExpr e){ assert(var !is this); return this; }
		override DExpr incDeBruin(int di){ return this; }
	}
}
alias DExprSet=SetX!DExpr;
class DVar: DExpr{
	string name;
	private this(string name){ this.name=name; }
	override string toStringImpl(Precedence prec){ return name; }

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; }
	override int freeVarsImpl(scope int delegate(DVar) dg){ return dg(this); }
	override DExpr substitute(DVar var,DExpr e){ return this is var?e:this; }
	override DVar incDeBruin(int di){ return this; }
	override DExpr solveFor(DVar var,DExpr e,ref DExpr[] constraints){
		if(this is var) return e;
		return null;
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
		if(prec>Precedence.uminus&&c<0)
			r="("~r~")";
		return r;
	}
	override bool isFraction(){ return true; }
	override ℕ[2] getFraction(){ return [c,ℕ(1)]; }

	mixin Constant;
}


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

Dℕ[ℕ] uniqueMapDℕ;
Dℕ dℕ(ℕ c){
	if(c in uniqueMapDℕ) return uniqueMapDℕ[c];
	return uniqueMapDℕ[c]=new Dℕ(c);
}
DExpr dℕ(long c){ return dℕ(ℕ(c)); }

class DE: DExpr{
	override string toStringImpl(Precedence prec){ return "e"; }
	mixin Constant;
}
private static DE theDE;
@property DE dE(){ return theDE?theDE:(theDE=new DE); }

class DΠ: DExpr{
	override string toStringImpl(Precedence prec){ return "π"; }
	mixin Constant;
}
private static DΠ theDΠ;
@property DΠ dΠ(){ return theDΠ?theDΠ:(theDΠ=new DΠ); }

private static DExpr theOne;
@property DExpr one(){ return theOne?theOne:(theOne=1.dℕ);}

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

DExprSet shallow(T)(DExprSet arg){
	DExprSet r;
	foreach(x;arg){
		if(auto t=cast(T)x){
			foreach(y;t.operands){
				T.insert(r,y);
			}
		}
	}
	if(!r.length) return arg;
	foreach(x;arg) if(!cast(T)x) T.insert(r,x);
	return r;
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
	return "auto " ~ lowerf(Ts)~"(DExprSet f){ auto fsh=f.shallow!"~__traits(identifier,T)~";"
		~"if(fsh.length==1) return fsh.element;"
		~"if(auto r="~Ts~".constructHook(fsh)) return r;"
		~"return uniqueDExprCommutAssoc!("~__traits(identifier,T)~")(fsh);"
		~"}"
		~"auto " ~ lowerf(Ts)~"(DExpr e1,DExpr e2){"
		~"  DExprSet a;"~Ts~".insert(a,e1);"~Ts~".insert(a,e2);"
		~"  return "~lowerf(Ts)~"(a);"
		~"}";
}

string makeConstructorNonCommutAssoc(T)(){
	enum Ts=__traits(identifier, T);
	return "auto " ~ lowerf(Ts)~"(DExpr e1, DExpr e2){ "
		~"static if(__traits(hasMember,"~Ts~",`constructHook`))"
		~"  if(auto r="~Ts~".constructHook(e1,e2)) return r;"
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
	override DExpr incDeBruin(int di){
		DExprSet res;
		foreach(s;summands) insert(res,s.incDeBruin(di));
		return dPlus(res);
	}
	override DExpr solveFor(DVar var,DExpr e,ref DExpr[] constraints){
		auto ow=splitPlusAtVar(this,var);
		if(cast(DPlus)ow[1]) return null; // TODO (polynomials,...)
		return ow[1].solveFor(var,e-ow[0],constraints);
	}

	static void insert(ref DExprSet summands,DExpr summand)in{assert(!!summand);}body{
		if(auto dp=cast(DPlus)summand){
			foreach(s;dp.summands)
				insert(summands,s);
			return;
		}
		static DExpr combine(DExpr e1,DExpr e2){
			if(e1 is zero) return e2;
			if(e2 is zero) return e1;
			if(e1 is e2) return 2*e1;
			if(e1.isFraction()&&e2.isFraction()){
				auto nd1=e1.getFraction();
				auto nd2=e2.getFraction();
				return dℕ(nd1[0]*nd2[1]+nd2[0]*nd1[1])/dℕ(nd1[1]*nd2[1]);
			}
			auto common=intersect(e1.factors.setx,e2.factors.setx); // TODO: optimize?
			if(common.length){
				auto cm=dMult(common);
				if(!cm.isFraction())
					return (e1/cm+e2/cm)*cm;
			}
			return null;
		}
		// TODO: use suitable data structures
		foreach(s;summands){
			if(auto nws=combine(s,summand)){
				summands.remove(s);
				insert(summands,nws);
				return;
			}
		}
		assert(summand !in summands);
		summands.insert(summand);
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
	override @property string symbol(){ return "·"; }
	override string toStringImpl(Precedence prec){
		auto frac=this.getFractionalFactor().getFraction();
		if(frac[0]<0){
			return addp(prec,"-"~(-this).toStringImpl(Precedence.uminus),Precedence.uminus);
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
	override DExpr incDeBruin(int di){
		DExprSet res;
		foreach(f;factors) insert(res,f.incDeBruin(di));
		return dMult(res);
	}
	override DExpr solveFor(DVar var,DExpr e,ref DExpr[] constraints){
		auto ow=splitMultAtVar(this,var);
		if(cast(DMult)ow[1]) return null; // TODO
		if(couldBeZero(ow[0])) constraints~=ow[0];
		return ow[1].solveFor(var,e/ow[0],constraints);
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

	static void insert(ref DExprSet factors,DExpr factor)in{assert(!!factor);}body{
		//if(zero in factors||factor is zero){ factors.clear(); factors.insert(zero); return; }
		if(auto dm=cast(DMult)factor){
			foreach(f;dm.factors)
				insert(factors,f);
			return;
		}

		// TODO: use suitable data structures
		static DExpr combine(DExpr e1,DExpr e2){
			if(e1 is one) return e2;
			if(e2 is one) return e1;
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
			if(e2.isFraction()){
				auto nd2=e2.getFraction();
				if(nd2[0]==1&&nd2[1]==1) return e1;
			}
			if(cast(DPow)e2) swap(e1,e2);
			if(auto p=cast(DPow)e1){
				if(p.operands[0] is e2)
					return p.operands[0]^^(p.operands[1]+1);
				if(auto d=cast(Dℕ)p.operands[0]){
					if(auto e=cast(Dℕ)e2){
						if(d.c==-e.c)
							return -d^^(p.operands[1]+1);
					}
				}
				if(auto pf=cast(DPow)e2){
					if(p.operands[0] is pf.operands[0])
						return p.operands[0]^^(p.operands[1]+pf.operands[1]);
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
			return null;
		}
		foreach(f;factors){
			if(auto nwf=combine(f,factor)){
				factors.remove(f);
				if(factors.length||nwf !is one)
					insert(factors,nwf);
				return;
			}
		}
		assert(factors.length==1||one !in factors);
		factors.insert(factor);
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
	override @property string symbol(){ return "^"; }
	override bool rightAssociative(){ return true; }

	override bool isFraction(){ return cast(Dℕ)operands[0] && cast(Dℕ)operands[1]; }
	override ℕ[2] getFraction(){
		auto d=cast(Dℕ)operands[0];
		assert(d && operands[1] is -one);
		return [ℕ(1),d.c];
	}

	override DExpr solveFor(DVar var,DExpr rhs,ref DExpr[] constraints){
		if(operands[1] !is -one) return null; // TODO
		if(rhs is zero) return null; // TODO: it might still be zero, how to handle?
		if(couldBeZero(rhs)) constraints~=rhs;
		return operands[0].solveFor(var,one/rhs,constraints);
	}

	override string toStringImpl(Precedence prec){
		// TODO: always use ⅟ if negative factor in exponent
		auto frc=operands[1].getFractionalFactor().getFraction();
		if(frc[0]<0)
			return addp(prec,"⅟"~(operands[0]^^-operands[1]).toStringImpl(Precedence.mult),Precedence.mult);
		// also nice, but often hard to read: ½⅓¼⅕⅙
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
		return super.toStringImpl(prec);
	}

	override DExpr substitute(DVar var,DExpr e){
		return operands[0].substitute(var,e)^^operands[1].substitute(var,e);
	}
	override DExpr incDeBruin(int di){
		return operands[0].incDeBruin(di)^^operands[1].incDeBruin(di);
	}

	static DExpr constructHook(DExpr e1,DExpr e2){
		if(e1 !is -one) if(auto c=cast(Dℕ)e1) if(c.c<0) return (-1)^^e2*dℕ(-c.c)^^e2;
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
		if(auto d=cast(Dℕ)e2){
			if(auto c=cast(Dℕ)e1){
				if(d.c>0) return dℕ(pow(c.c,d.c));
				else if(d.c!=-1) return dℕ(pow(c.c,-d.c))^^-1;
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
		return null;
	}
}

mixin(makeConstructorNonCommutAssoc!DPow);
DExpr dDiv(DExpr e1,DExpr e2){ return e1*e2^^-1; }


DExpr expandPow(DPow p,long limit=-1){
	auto c=cast(Dℕ)p.operands[1];
	if(!c||limit>=0&&c.c>limit) return p;
	auto a=cast(DPlus)p.operands[0];
	if(!cast(DPlus)p.operands[0]) return p;
	// TODO: do this more efficiently!
	DExprSet r;
	foreach(s;a.summands){
		auto cur=s*a^^(c-1);
		if(auto curp=cast(DPow)cur) cur=expandPow(curp,max(-1,limit-1));
		DPlus.insert(r,cur);
	}
	return dPlus(r);
}

struct DPolynomial{
	DVar var;
	DExpr[] coefficients;
	bool initialized(){ return !!var; }
	long degree(){ return coefficients.length-1; }
	void addCoeff(long exp,DExpr coeff){
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

DPolynomial asPolynomialIn(DExpr e,DVar v,long limit=-1){
	DExprSet normSet;
	foreach(s;e.summands){
		if(auto p=cast(DPow)s) DPlus.insert(normSet,p.expandPow(limit));
		else DPlus.insert(normSet,s);
	}
	auto normalized=dPlus(normSet);
	auto r=DPolynomial(v);
	bool addCoeff(long exp,DExpr coeff){
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
DExpr dUMinus(DExpr e){ return -1*e; }

bool couldBeZero(DExpr e){
	if(cast(DΠ)e) return false;
	if(cast(DE)e) return false;
	if(auto c=cast(Dℕ)e) return c.c==0;
	return true;
}

DExpr uglyFractionCancellation(DExpr e){
	ℕ ngcd=0,dlcm=1;
	foreach(s;e.summands){
		auto f=s.getFractionalFactor();
		assert(f.isFraction());
		auto nd=f.getFraction();
		assert(nd[1]>0);
		ngcd=gcd(ngcd,abs(nd[0]));
		dlcm=lcm(dlcm,nd[1]);
	}
	return dℕ(dlcm)/ngcd;
}

enum BoundStatus{
	fail,
	lowerBound,
	upperBound,
}

BoundStatus getBoundForVar(DIvr ivr,DVar var,out DExpr bound){ // TODO: handle cases where there is no bound
	enum r=BoundStatus.fail;
	with(DIvr.Type) if(!util.among(ivr.type,lZ,leZ)) return r;
	foreach(s;ivr.e.summands){
		if(!s.hasFreeVar(var)) continue;
		auto cand=s/var;
		if(cand.hasFreeVar(var)) return r;
		auto lZ=dIvr(DIvr.Type.lZ,cand)==one;
		auto gZ=dIvr(DIvr.Type.lZ,-cand)==one;
		if(!lZ&&!gZ) return r;
		auto ne=var-ivr.e/cand;
		if(ne.hasFreeVar(var)) return r;
		// TODO: must consider strictness!
		bound=ne;
		return lZ?BoundStatus.lowerBound:BoundStatus.upperBound;
	}
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
	this(Type type,DExpr e){ this.type=type; this.e=e; }

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: correct?
	override int freeVarsImpl(scope int delegate(DVar) dg){ return e.freeVarsImpl(dg); }
	override DExpr substitute(DVar var,DExpr exp){ return dIvr(type,e.substitute(var,exp)); }
	override DExpr incDeBruin(int di){ return dIvr(type,e.incDeBruin(di)); }

	override string toStringImpl(Precedence prec){
		with(Type) return "["~e.toString()~(type==eqZ?"=":type==neqZ?"≠":type==lZ?"<":"≤")~"0]";
	}

	static DExpr constructHook(Type type,DExpr e){
		// TODO: better decision procedures
		if(type==Type.eqZ&&!couldBeZero(e)) return zero;
		if(type==Type.neqZ&&!couldBeZero(e)) return one;
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
		return null;
	}
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
	auto r=new DIvr(type,e);
	uniqueMapDIvr[type][e]=r;
	return r;

}

class DDelta: DExpr{ // Dirac delta function
	DExpr e;
	private this(DExpr e){ this.e=e; }
	override string toStringImpl(Precedence prec){ return "δ["~e.toString()~"]"; }

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO: ok?
	override int freeVarsImpl(scope int delegate(DVar) dg){ return e.freeVarsImpl(dg); }
	override DExpr substitute(DVar var,DExpr exp){ return dDelta(e.substitute(var,exp)); }
	override DExpr incDeBruin(int di){ return dDelta(e.incDeBruin(di)); }

	static DExpr constructHook(DExpr e){
		auto cancel=uglyFractionCancellation(e);
		if(cancel!=one) return dDelta(dDistributeMult(e,cancel))*cancel;
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

DExpr specialIntegral(DVar v,DExpr e){ // TODO: merge with definiteIntegral?
	static DExpr gaussianIntegral(DVar v,DExpr e){
		// detect e^^(-a*x^^2+b*x+c), and integrate to e^^(b^^2/4a+c)*(pi/a)^^(1/2).
		// TODO: this assumes that a≥0!
		auto p=cast(DPow)e;
		if(!p) return null;
		if(!cast(DE)p.operands[0]) return null;
		auto q=p.operands[1].asPolynomialIn(v,2);
		if(!q.initialized) return null;
		if(q.coefficients.length!=3) return null;
		auto qc=q.coefficients;
		auto a=-qc[2],b=qc[1],c=qc[0];
		if(a is zero) return null;
		return dE^^(b^^2/(4*a)+c)*(dΠ/a)^^(one/2);
	}
	if(auto r=gaussianIntegral(v,e)) return r;
	return null;
}

DExpr dMin(DExpr a,DExpr b){
	return dIvr(DIvr.Type.lZ,a-b)*a+dIvr(DIvr.Type.leZ,b-a)*b;
}
DExpr dMax(DExpr a,DExpr b){
	return dIvr(DIvr.Type.lZ,b-a)*a+dIvr(DIvr.Type.leZ,a-b)*b;
}

DExpr definiteIntegral(DVar var,DExpr expr){
	// TODO: explicit antiderivative (d/dx)⁻¹
	// eg. the full antiderivative e^^(-a*x^^2+b*x) is given by:
	// e^^(b^^2/4a)*(d/dx)⁻¹(e^^(-x^^2))[(b-2*a*x)/2*a^^(1/2)]/a^^(1/2)
	DExpr ivrs=one;
	DExpr nonIvrs=one;
	foreach(f;expr.factors){
		assert(f.hasFreeVar(var));
		if(cast(DIvr)f) ivrs=ivrs*f;
		else nonIvrs=nonIvrs*f;
	}
	DExpr lower=null;
	DExpr upper=null;
	DExpr constraints=one;
	foreach(f;ivrs.factors){
		auto ivr=cast(DIvr)f;
		assert(!!ivr);
		DExpr bound;
		auto status=ivr.getBoundForVar(var,bound);
		final switch(status) with(BoundStatus){
		case fail: return null; // TODO: non-linear bounds
		case lowerBound:
			if(lower) lower=dMax(lower,bound);
			else lower=bound;
			break;
		case upperBound:
			if(upper) upper=dMin(upper,bound);
			else upper=bound;
			break;
		}
		if(ivr.type==DIvr.Type.lZ) constraints=constraints*dIvr(DIvr.Type.neqZ,var-bound);
	}
	//writeln(expr);
	//writeln("!! ",lower," ",upper," ",constraints);
	// TODO: add better approach for antiderivatives	
	if(upper&&lower&&constraints==one){
		if(nonIvrs==one) return dIvr(DIvr.Type.leZ,lower-upper)*(upper-lower);
	}
	
	return null; // no simpler expression available
}

class DInt: DOp{
	private{
		DDeBruinVar var;
		DExpr expr;
		this(DDeBruinVar var,DExpr expr){ this.var=var; this.expr=expr; }
	}
	DExpr getExpr(DVar var){
		assert(this.var is dDeBruinVar(1));
		return expr.substitute(this.var,var).incDeBruin(-1);
	}
	override @property Precedence precedence(){ return Precedence.intg; }
	override @property string symbol(){ return "∫"; }
	override string toStringImpl(Precedence prec){
		return addp(prec,symbol~"d"~var.toString()~expr.toStringImpl(precedence));
	}
	static DExpr constructHook(DVar var,DExpr expr){
		/*static dInt(DVar var,DExpr expr){
			if(cast(DDeBruinVar)var){
				if(auto hooked=constructHook(var,expr)){
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
		if(auto m=cast(DPlus)expr){
			DExprSet summands;
			foreach(s;m.summands)
				DPlus.insert(summands,dInt(var,s));
			return dPlus(summands);
		}
		auto ow=expr.splitMultAtVar(var);
		if(ow[0] !is one) return ow[0]*dInt(var,ow[1]);
		foreach(f;expr.factors){
			if(!f.hasFreeVar(var)) continue;
			if(auto d=cast(DDelta)f){
				DExpr[] constraints;
				if(auto s=d.e.solveFor(var,zero,constraints)){
					bool trivial(DExpr constraint){
						return dIvr(DIvr.Type.neqZ,constraint) is one;
					}
					constraints=constraints.remove!trivial;
					if(!constraints.length) // TODO!
						return (expr/f).substitute(var,s)/dAbs(dDiff(var,d.e,s));
				}
			}
		}
		foreach(f;expr.factors){
			if(auto p=cast(DPlus)f){
				bool check(){
					foreach(d;p.allOf!DDelta)
						if(d.e.hasFreeVar(var))
							return true;
					return false;
				}
				if(check()){
					DExprSet s;
					foreach(k;distributeMult(p,expr/f)){
						DPlus.insert(s,dInt(var,k));
					}
					return dPlus(s);
				}
			}
		}
		if(expr is one) return null; // (infinite integral)
		// Fubini
		foreach(f;expr.factors){
			// assert(f.hasFreeVar(var));
			if(auto other=cast(DInt)f){
				assert(!!cast(DDeBruinVar)other.var);
				auto tmpvar=new DVar("tmp"); // TODO: get rid of this!
				auto intExpr=(other.expr*(expr/f)).substitute(other.var,tmpvar).incDeBruin(-1);
				auto ow=intExpr.splitMultAtVar(var);
				if(auto res=constructHook(var,ow[1]))
					return dInt(tmpvar,res*ow[0]);
			}
		}
		if(!expr.hasFreeVar(var)) return expr*dInt(var,one); // (infinite integral)
		if(auto r=specialIntegral(var,expr)) return r;
		return definiteIntegral(var,expr);
	}
	override int forEachSubExpr(scope int delegate(DExpr) dg){
		 // TODO: correct?
		return expr.forEachSubExpr(dg);
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return expr.freeVarsImpl(v=>v is var?0:dg(v));
	}
	override DExpr substitute(DVar var,DExpr e){
		if(this.var is var) return this;
		return dInt(this.var,expr.substitute(var,e));
	}
	override DExpr incDeBruin(int di){
		return dInt(var.incDeBruin(di),expr.incDeBruin(di));
	}
}

MapX!(TupleX!(typeof(typeid(DExpr)),DDeBruinVar,DExpr,DExpr),DExpr) uniqueMapBinding;
auto uniqueBindingDExpr(T)(DDeBruinVar v,DExpr a,DExpr b=null){
	auto t=tuplex(typeid(T),v,a,b);
	if(t in uniqueMapBinding) return cast(T)uniqueMapBinding[t];
	static if(is(typeof(new T(v,a)))) auto r=new T(v,a);
	else auto r=new T(v,a,b);
	uniqueMapBinding[t]=r;
	return r;
}

DExpr dInt(DVar var,DExpr expr){
	if(auto dbvar=cast(DDeBruinVar)var) return uniqueBindingDExpr!DInt(dbvar,expr);
	if(auto r=DInt.constructHook(var,expr)) return r;
	auto dbvar=dDeBruinVar(1);
	expr=expr.incDeBruin(1).substitute(var,dbvar);
	return uniqueBindingDExpr!DInt(dbvar,expr);
}

DExpr differentiate(DVar v,DExpr e){
	if(v is e) return one;
	if(cast(DVar)e) return zero;
	if(cast(Dℕ)e) return zero;
	if(auto p=cast(DPlus)e){
		DExprSet r;
		foreach(s;p.summands)
			DPlus.insert(r,dDiff(v,s));
		return dPlus(r);
	}
	if(auto m=cast(DMult)e){
		DExprSet r;
		foreach(f;m.factors)
			DPlus.insert(r,dDiff(v,f)/f);
		return dPlus(r)*m;
	}
	if(auto p=cast(DPow)e)
		return p.operands[0]^^(p.operands[1]-1)*
			(dDiff(v,p.operands[0])*p.operands[1]+
			 p.operands[0]*dLog(p.operands[0])*dDiff(v,p.operands[1]));
	if(auto l=cast(DLog)e)
		return dDiff(v,l.e)/l.e;
	if(auto s=cast(DSin)e)
		return dDiff(v,s.e)*dSin(s.e+dΠ/2);
	if(!e.hasFreeVar(v)) return zero;
	return null;
}

class DDiff: DOp{
	DVar v;
	DExpr e;
	DExpr x;
	this(DVar v,DExpr e,DExpr x){ this.v=v; this.e=e; this.x=x; }
	override @property string symbol(){ return "d/d"~v.toString(); }
	override Precedence precedence(){ return Precedence.diff; }
	override string toStringImpl(Precedence prec){
		return addp(prec,symbol~"("~e.toString()~")["~x.toString()~"]");
	}

	static DExpr constructHook(DVar v,DExpr e,DExpr x){
		if(auto r=differentiate(v,e))
			return r.substitute(v,x);
		return null;
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
		return dg(e); // TODO: correct?
	}

	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dAbs(e.substitute(var,exp));
	}
	override DExpr incDeBruin(int di){
		return dAbs(e.incDeBruin(di));
	}

	static DExpr constructHook(DExpr e){
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
		return null;
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
		return dg(e); // TODO: correct?
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dLog(e.substitute(var,exp));
	}
	override DExpr incDeBruin(int di){
		return dLog(e.incDeBruin(di));
	}

	static DExpr constructHook(DExpr e){
		if(auto c=cast(DE)e) return one;
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
		return dg(e); // TODO: correct?
	}
	override int freeVarsImpl(scope int delegate(DVar) dg){
		return e.freeVarsImpl(dg);
	}
	override DExpr substitute(DVar var,DExpr exp){
		return dSin(e.substitute(var,exp));
	}
	override DExpr incDeBruin(int di){
		return dSin(e.incDeBruin(di));
	}

	static DExpr constructHook(DExpr e){
		return null;
	}
}

DExpr dSin(DExpr e){ return uniqueDExprUnary!DSin(e); }


class DFun: DOp{ // uninterpreted functions
	DVar fun;
	DExpr[] args;
	this(DVar fun, DExpr[] args){ this.fun=fun; this.args=args; }
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
	override DExpr incDeBruin(int di){
		return dFun(fun,args.map!(a=>a.incDeBruin(di)).array);
	}

	static DExpr constructHook(DExpr e){
		return null;
	}
}

MapX!(TupleX!(DVar,DExpr[]),DFun) uniqueMapDFun;
auto uniqueDFun(DVar fun,DExpr[] args){
	auto t=tuplex(fun,args);
	if(t in uniqueMapDFun) return uniqueMapDFun[t];
	auto r=new DFun(fun,args);
	uniqueMapDFun[t]=r;
	return r;
}

DFun dFun(DVar fun,DExpr[] args){
	return uniqueDFun(fun,args);
}
DFun dFun(DVar fun,DExpr arg){
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

auto allOf(T)(DExpr e){
	static struct AllOfVisitor{
		scope int delegate(T) dg;
		int r=0;
		int perform(T t){
			if(auto r=dg(t))
				return this.r=r;
			return 0;
		}
	}
	static struct AllOf{
		DExpr e;
		int opApply(scope int delegate(T) dg){
			return e.visit!AllOfVisitor(dg).r;
		}
	}
	return AllOf(e);
}

bool hasAny(T)(DExpr e){ foreach(x;e.allOf!T) return true; return false; }
