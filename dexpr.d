import std.conv;
import hashtable, util;
import std.algorithm: canFind;

enum Precedence{
	none,
	uminus,
	plus,
	mult,
	pow,
}

import std.bigint;
alias ℕ=BigInt;

abstract class DExpr{
	override string toString(){
		return toStringImpl(Precedence.none);
	}
	abstract string toStringImpl(Precedence prec);

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
	protected final string addp(Precedence prec, string s){
		return prec > precedence||rightAssociative&&prec==precedence? "(" ~ s ~ ")":s;
	}
}

auto inOrder(S)(S s){
	return s; // TODO
}
abstract class DCommutAssocOp: DOp{
	DExprSet operands;
	protected mixin template Constructor(){ private this(DExprSet e)in{assert(e.length>1); }body{ operands=e; } }
	override string toStringImpl(Precedence prec){
		string r;
		if(operands.length>20) foreach(o;operands) r~=" "~symbol~" "~o.toStringImpl(precedence);
		else foreach(o;operands.inOrder) r~=symbol~o.toStringImpl(precedence);
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
	auto t=tuplex(typeid(T),a);
	if(t in uniqueMapUnary) return cast(T)uniqueMapUnary[t];
	auto r=new T(a);
	uniqueMapUnary[t]=r;
	return r;
}
string makeConstructorCommutAssoc(T,string dflt=null)(){
	enum Ts=__traits(identifier, T);
	return "auto " ~ lowerf(Ts)~"(DExprSet f){ auto fsh=f.shallow!"~__traits(identifier,T)~"; if(fsh.length==1) foreach(x;fsh) return x; "~(dflt.length?"if(!fsh.length) return "~dflt~";":"")~"return uniqueDExprCommutAssoc!("~__traits(identifier,T)~")(fsh); }" ~
		"auto " ~ lowerf(Ts)~"(DExpr e1,DExpr e2){ DExprSet a;"~Ts~".insert(a,e1);"~Ts~".insert(a,e2);return "~lowerf(Ts)~"(a); }";
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
		// TODO: use suitable data structures
		// TODO: eliminate repetition?
		if(auto c=cast(Dℕ)summand){
			if(c.c==0) return;
			foreach(s;summands){
				if(auto d=cast(Dℕ)s){
					summands.remove(s);
					summands.insert(dℕ(c.c+d.c));
					return;
				}
				if(auto p=cast(DPow)s){
					if(auto d=cast(Dℕ)p.operands[0]){
						if(auto e=cast(Dℕ)p.operands[1]){
							assert(e.c==-1);
							summands.remove(s);
							summands.insert(dℕ(c.c*d.c+1)/d);
							return;
						}
					}
				}
			}
		}
		if(auto p=cast(DPow)summand){
			if(auto d=cast(Dℕ)p.operands[0]){
				if(auto e=cast(Dℕ)p.operands[1]){
					assert(e.c==-1);
					foreach(s;summands){
						if(auto c=cast(Dℕ)s){
							summands.remove(s);
							summands.insert(dℕ(c.c*d.c+1)/d);
							return;
						}
					}
					
				}
			}
		}
		if(summand !in summands) summands.insert(summand);
		else{ summands.remove(summand); insert(summands,2*summand); }
	}
	static DExpr constructHook(DExprSet operands){
		if(operands.length==1) return operands.element;
		if(operands.length==0) return zero;
		return null;
	}
}

class DMult: DCommutAssocOp{
	alias factors=operands;
	mixin Constructor;
	override @property Precedence precedence(){ return Precedence.mult; }
	override @property string symbol(){ return "·"; }
	static void insert(ref DExprSet factors,DExpr factor)in{assert(!!factor);}body{
		// TODO: use suitable data structures
		// TODO: eliminate repetition?
		foreach(f;factors){
			if(f is factor){
				factors.remove(f);
				insert(factors,f^^2);
				return;
			}
			if(auto pf=cast(DPow)factor){
				if(f is pf.operands[0]){
					factors.remove(f);
					insert(factors,f^^(pf.operands[1]+1));
					return;
				}
				if(auto d=cast(Dℕ)f){
					if(auto e=cast(Dℕ)pf.operands[0]){
						if(d.c==-e.c){
							factors.remove(f);
							insert(factors,-e^^(pf.operands[1]));
							return;
						}
					}
				}
			}
			if(auto p=cast(DPow)f){
				if(p.operands[0] is factor){
					factors.remove(p);
					insert(factors,p.operands[0]^^(p.operands[1]+1));
					return;
				}
				if(auto d=cast(Dℕ)p.operands[0]){
					if(auto e=cast(Dℕ)factor){
						if(d.c==-e.c){
							factors.remove(f);
							insert(factors,-d^^(p.operands[1]+1));
							return;
						}
					}
				}
				if(auto pf=cast(DPow)factor){
					if(p.operands[0] is pf.operands[0]){
						factors.remove(p);
						insert(factors,p.operands[0]^^(p.operands[1]+pf.operands[1]));
						return;
					}
				}
			}
		}
		if(auto c=cast(Dℕ)factor){
			if(c.c==1) return;
			foreach(f;factors){
				if(auto d=cast(Dℕ)f){
					factors.remove(d);
					insert(factors,dℕ(c.c*d.c));
					return;
				}
			}
		}
		assert(factor !in factors);
		factors.insert(factor);
	}
	static DExpr constructHook(DExprSet operands){
		if(operands.length==1) return operands.element;
		if(operands.length==0) return one;
		return null;
	}
}

mixin(makeConstructorCommutAssoc!DMult);
mixin(makeConstructorCommutAssoc!DPlus);

DExpr dMinus(DExpr e1,DExpr e2){
	return e1.dPlus(e2.dUMinus);
}

abstract class DBinaryOp: DOp{
	DExpr[2] operands;
	protected mixin template Constructor(){ private this(DExpr e1, DExpr e2){ operands=[e1,e2]; } }
	override string toStringImpl(Precedence prec){
		return addp(prec, operands[0].toStringImpl(precedence) ~ symbol ~ operands[1].toStringImpl(precedence));
	}
	// abstract BinaryOp construct(DExpr a, DExpr b);
}

class DPow: DBinaryOp{
	mixin Constructor;
	override Precedence precedence(){ return Precedence.pow; }
	override @property string symbol(){ return "^"; }
	override bool rightAssociative(){ return true; }

	static DExpr constructHook(DExpr e1,DExpr e2){
		if(auto m=cast(DMult)e1){ // TODO: do we really want auto-distribution?
			DExprSet factors;
			foreach(f;m.operands)
				DMult.insert(factors,f^^e2);
			return dMult(factors);
		}
		if(auto p=cast(DPow)e1) return p.operands[0]^^(p.operands[1]*e2);
		if(e1 is one||e2 is zero) return one;
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


class DInt: DOp{
	DVar var;
	DExpr expr;
	private this(DVar var,DExpr expr){ this.var=var; this.expr=expr; }
	override @property Precedence precedence(){ return Precedence.mult; }
	override @property string symbol(){ return "∫"; }
	override string toStringImpl(Precedence prec){
		return addp(prec,symbol~"d"~var.toString()~addp(Precedence.mult,expr.toString()));
	}
}

DInt dInt(DVar var, DExpr expr){
	return new DInt(var,expr); // TODO: make unique modulo alpha-renaming?
}
