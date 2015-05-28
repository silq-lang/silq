import std.conv;
import hashtable, util;

import std.algorithm, std.array;

enum Precedence{
	none,
	uminus,
	plus,
	intg,
	mult,
	pow,
	invalid,
}

import std.bigint;
alias ℕ=BigInt;

abstract class DExpr{
	override string toString(){
		return toStringImpl(Precedence.none);
	}
	abstract string toStringImpl(Precedence prec);

	bool hasFreeVar(DVar var){ return false; }

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
}
alias DExprSet=SetX!DExpr;
class DVar: DExpr{
	string name;
	private this(string name){ this.name=name; }
	override string toStringImpl(Precedence prec){ return name; }

	override bool hasFreeVar(DVar var){ return this is var; }
}
DVar dVar(string name){ return new DVar(name); }

class Dℕ : DExpr{
	ℕ c;
	private this(ℕ c){ this.c=c; }
	override string toStringImpl(Precedence prec){
		string r=text(c);
		if(prec>Precedence.uminus&&c<0)
			r="("~r~")";
		return r;
	}
}

Dℕ[ℕ] uniqueMapDℕ;
DExpr dℕ(ℕ c){
	if(c in uniqueMapDℕ) return uniqueMapDℕ[c];
	return uniqueMapDℕ[c]=new Dℕ(c);
}
DExpr dℕ(long c){ return dℕ(ℕ(c)); }

class DE: DExpr{
	override string toStringImpl(Precedence prec){ return "e"; }
}
private static DE theDE;
@property DE dE(){ return theDE?theDE:(theDE=new DE); }

class DΠ: DExpr{
	override string toStringImpl(Precedence prec){ return "π"; }
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

	override bool hasFreeVar(DVar var){ return operands.any!(a=>a.hasFreeVar(var)); }
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
	static void insert(ref DExprSet summands,DExpr summand)in{assert(!!summand);}body{
		static DExpr combine(DExpr e1,DExpr e2){
			if(cast(Dℕ)e2) swap(e1,e2);
			if(auto c=cast(Dℕ)e1){
				if(c.c==0) return e2;
				if(auto d=cast(Dℕ)e2) return dℕ(c.c+d.c);
				if(auto p=cast(DPow)e2){
					if(auto d=cast(Dℕ)p.operands[0]){
						if(auto e=cast(Dℕ)p.operands[1]){
							assert(e.c==-1);
							return dℕ(c.c*d.c+1)/d;
						}
					}
				}
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
		if(summand !in summands) summands.insert(summand);
		else{ summands.remove(summand); insert(summands,2*summand); }
	}
	static DExpr constructHook(DExprSet operands){
		if(operands.length==0) return zero;
		return null;
	}
}

class DMult: DCommutAssocOp{
	alias factors=operands;
	mixin Constructor;
	override @property Precedence precedence(){ return Precedence.mult; }
	override @property string symbol(){ return "·"; }
	override string toStringImpl(Precedence prec){
		// TODO: use suitable data structures
		foreach(f;factors){
			if(auto c=cast(Dℕ)f){
				if(c.c<0){
					return addp(prec,"-"~(-this).toStringImpl(Precedence.uminus),Precedence.uminus);
				}
			}
		}
		return super.toStringImpl(prec);
	}
	static void insert(ref DExprSet factors,DExpr factor)in{assert(!!factor);}body{
		// TODO: use suitable data structures
		static DExpr combine(DExpr e1,DExpr e2){
			if(cast(Dℕ)e2) swap(e1,e2);
			if(auto c=cast(Dℕ)e1){
				if(c.c==1) return e2;
				if(auto d=cast(Dℕ)e2) return dℕ(c.c*d.c);
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
				}				
			}
			if(e1 is e2) return e1^^2;
			return null;
		}
		foreach(f;factors){
			if(auto nwf=combine(f,factor)){
				factors.remove(f);
				insert(factors,nwf);
				return;
			}
		}
		assert(factor !in factors);
		factors.insert(factor);
	}
	static DExpr constructHook(DExprSet operands){
		if(operands.length==0) return one;
		return null;
	}
}

mixin(makeConstructorCommutAssoc!DMult);
mixin(makeConstructorCommutAssoc!DPlus);

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

DExpr dMinus(DExpr e1,DExpr e2){ return e1+-e2; }

abstract class DBinaryOp: DOp{
	DExpr[2] operands;
	protected mixin template Constructor(){ private this(DExpr e1, DExpr e2){ operands=[e1,e2]; } }
	override string toStringImpl(Precedence prec){
		return addp(prec, operands[0].toStringImpl(precedence) ~ symbol ~ operands[1].toStringImpl(precedence));
	}
	override bool hasFreeVar(DVar var){ return operands[].any!(a=>a.hasFreeVar(var)); }
}

class DPow: DBinaryOp{
	mixin Constructor;
	override Precedence precedence(){ return Precedence.pow; }
	override @property string symbol(){ return "^"; }
	override bool rightAssociative(){ return true; }

	override string toStringImpl(Precedence prec){
		// TODO: always use ⅟ if negative factor in exponent
		if(auto c=cast(Dℕ)operands[1]){
			if(c.c==-1){
				if(auto d=cast(Dℕ)operands[0])
					if(2<=d.c&&d.c<=6)
						return addp(prec,text("  ½⅓¼⅕⅙"d[d.c.toLong()]),Precedence.mult);
				return addp(prec,"⅟"~operands[0].toStringImpl(Precedence.mult),Precedence.mult);
			}
			return addp(prec,operands[0].toStringImpl(Precedence.pow)~highNum(c.c));
		}
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
		if(auto c=cast(Dℕ)e1){
			if(auto d=cast(Dℕ)e2){
				if(d.c>0) dℕ(pow(c.c,d.c));
				else if(d.c!=-1) return dℕ(pow(c.c,-d.c))^^-1;
			}
		}
		return null;
	}
}

mixin(makeConstructorNonCommutAssoc!DPow);
DExpr dDiv(DExpr e1,DExpr e2){ return e1*e2^^-1; }

abstract class DUnaryOp: DOp{
	DExpr operand;
	protected mixin template Constructor(){ private this(DExpr e){ operand=e; } }
	override string toStringImpl(Precedence prec){
		return addp(prec, symbol~operand.toStringImpl(precedence));
	}
}
DExpr dUMinus(DExpr e){ return -1*e; }

class DConstr{
	override string toString(){
		return toStringImpl(Precedence.none);
	}
	abstract string toStringImpl(Precedence prec);
}

class DInd: DOp{
	
}

class DDelta: DExpr{
	DExpr e;
	this(DExpr e){ this.e=e; }
	override string toStringImpl(Precedence prec){ return "δ["~e.toString()~"]"; }
}

mixin(makeConstructorUnary!DDelta);

DExpr[2] splitPlusAtVar(DExpr e,DVar var){
	DExprSet within;
	DExprSet outside;
	foreach(s;e.summands){
		if(s.hasFreeVar(var)) DPlus.insert(within,s);
		else DPlus.insert(outside,s);
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

class DInt: DOp{
	DVar var;
	DExpr expr;
	private this(DVar var,DExpr expr){ this.var=var; this.expr=expr; }
	override @property Precedence precedence(){ return Precedence.intg; }
	override @property string symbol(){ return "∫"; }
	override string toStringImpl(Precedence prec){
		return addp(prec,symbol~"d"~var.toString()~addp(Precedence.intg,expr.toString()));
	}
	static DExpr constructHook(DVar var,DExpr expr){
		if(auto m=cast(DPlus)expr){
			DExprSet summands;
			foreach(s;m.summands)
				DPlus.insert(summands,dInt(var,s));
			return dPlus(summands);
		}
		if(auto m=cast(DMult)expr){ // TODO: separate powers
			auto ow=m.splitMultAtVar(var);
			if(ow[0] !is one) return ow[0]*dInt(var,ow[1]);
		}
		if(expr!is one && !expr.hasFreeVar(var)) return expr*dInt(var,one); // (infinite integral)
		return null;
	}
}

DExpr dInt(DVar var,DExpr expr){
	if(auto r=DInt.constructHook(var,expr)) return r;
	return new DInt(var,expr); // TODO: make unique modulo alpha-renaming
}
