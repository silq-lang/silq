import std.conv;
import hashtable, util;


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
	private this(ℕ c)in{ assert(c>=0); }body{ this.c=c; }
	override string toStringImpl(Precedence prec){ return text(c); }
}

Dℕ[ℕ] uniqueMapDℕ;
DExpr dℕ(ℕ c){
	if(c<0) return dUMinus(dℕ(-c));
	if(c in uniqueMapDℕ) return uniqueMapDℕ[c];
	return uniqueMapDℕ[c]=new Dℕ(c);
}
DExpr dℕ(long c){ return dℕ(ℕ(c)); }

class DE: DExpr{
	override string toStringImpl(Precedence prec){ return "e"; }
}
static DE theDE;
@property DE dE(){ return theDE?theDE:theDE=new DE; }

class DΠ: DExpr{
	override string toStringImpl(Precedence prec){ return "π"; }
}
static DΠ theDΠ;
@property DΠ dΠ(){ return theDΠ?theDΠ:theDΠ=new DΠ; }

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

	protected static insertImpl(alias rep)(ref DExprSet operands, DExpr operand)in{assert(!!operand);}body{ // TODO: simplify better
		if(operand !in operands) operands.insert(operand);
		else{ operands.remove(operand); operands.insert(rep(operand,2)); }
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
	return "auto " ~ lowerf(__traits(identifier, T))~"(DExpr e1, DExpr e2){ return uniqueDExprNonCommutAssoc!("~__traits(identifier,T)~")(e1,e2); }";
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
		insertImpl!((a,b)=>dMult(dℕ(b),a))(summands,summand);
	}
}

class DMult: DCommutAssocOp{
	alias factors=operands;
	mixin Constructor;
	override @property Precedence precedence(){ return Precedence.mult; }
	override @property string symbol(){ return "·"; }
	static void insert(ref DExprSet factors,DExpr factor)in{assert(!!factor);}body{
		insertImpl!((a,b)=>dPow(a,dℕ(b)))(factors,factor);
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

class DDiv: DBinaryOp{
	mixin Constructor;
	override Precedence precedence(){ return Precedence.mult; }
	override @property string symbol(){ return "/"; }
}
class DPow: DBinaryOp{
	mixin Constructor;
	override Precedence precedence(){ return Precedence.pow; }
	override @property string symbol(){ return "^"; }
	override bool rightAssociative(){ return true; }
}

mixin(makeConstructorNonCommutAssoc!DDiv);
mixin(makeConstructorNonCommutAssoc!DPow);

abstract class DUnaryOp: DOp{
	DExpr operand;
	protected mixin template Constructor(){ private this(DExpr e){ operand=e; } }
	override string toStringImpl(Precedence prec){
		return addp(prec, symbol~operand.toStringImpl(precedence));
	}
}

class DUMinus: DUnaryOp{
	mixin Constructor;
	override @property string symbol(){ return "-"; }
	override @property Precedence precedence(){ return Precedence.uminus; }
}
mixin(makeConstructorUnary!DUMinus);

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
