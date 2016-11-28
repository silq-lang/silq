// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.algorithm, std.conv;
import std.functional;
import expression, declaration, util;

bool compatible(Expression lhs,Expression rhs){
	return lhs.eval() == rhs.eval();
}


class Type: Expression{
	this(){ if(!this.type) this.type=typeTy; sstate=SemState.completed; }
	override @property string kind(){ return "type"; }
	override string toString(){ return "T"; }
}

class ErrorTy: Type{
	this(){}//{sstate = SemState.error;}
	override string toString(){return "__error";}
	mixin VariableFree;
}


class ℝTy: Type{
	private this(){}
	override string toString(){
		return "ℝ";
	}
	mixin VariableFree;
}
private ℝTy theℝ;

ℝTy ℝ(){ return theℝ?theℝ:(theℝ=new ℝTy()); }

class AggregateTy: Type{
	DatDecl decl;
	this(DatDecl decl){
		this.decl=decl;
	}
	mixin VariableFree;
}

class ContextTy: Type{
	private this(){} // dummy
	mixin VariableFree;
}
private ContextTy theContextTy;
ContextTy contextTy(){ return theContextTy?theContextTy:(theContextTy=new ContextTy()); }



class TupleTy: Type{
	Expression[] types;
	private this(Expression[] types)in{
		assert(types.all!(x=>x.type==typeTy));
	}body{
		this.types=types;
	}
	override string toString(){
		if(!types.length) return "𝟙";
		if(types.length==1) return "("~types[0].toString()~")¹";
		string addp(Expression a){
			if(cast(FunTy)a) return "("~a.toString()~")";
			return a.toString();
		}
		return types.map!(a=>cast(TupleTy)a&&a!is unit?"("~a.toString()~")":addp(a)).join(" × ");
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		foreach(t;types)
			if(auto r=t.freeVarsImpl(dg))
				return r;
		return 0;
	}
	override TupleTy substitute(string name,Expression type){
		auto ntypes=types.dup;
		foreach(ref t;ntypes) t=t.substitute(name,type);
		return tupleTy(ntypes);
	}
}

TupleTy unit(){ return tupleTy([]); }

TupleTy tupleTy(Expression[] types)in{
	assert(types.all!(x=>x.type==typeTy));
}body{
	return memoize!((Expression[] types)=>new TupleTy(types))(types);
}

class ArrayTy: Type{
	Expression next;
	private this(Expression next)in{
		assert(next.type==typeTy);
	}body{
		this.next=next;
	}
	override string toString(){
		bool p=cast(FunTy)next||cast(TupleTy)next&&next!is unit;
		return p?"("~next.toString()~")[]":next.toString()~"[]";
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		return next.freeVarsImpl(dg);
	}
	override ArrayTy substitute(string name,Expression type){
		return arrayTy(next.substitute(name,type));
	}
	override ArrayTy eval(){
		return arrayTy(next.eval());
	}
}

ArrayTy arrayTy(Expression next)in{
	assert(next.type==typeTy);
}body{
	return memoize!((Expression next)=>new ArrayTy(next))(next);
}

class StringTy: Type{
	private this(){}
	override string toString(){
		return "string";
	}
	mixin VariableFree;
}

StringTy stringTy(){ return memoize!(()=>new StringTy()); }

class ForallTy: Type{
	string[] names;
	TupleTy dom;
	Expression cod;
	private this(string[] names,TupleTy dom,Expression cod)in{
		assert(names.length==dom.types.length);
		assert(cod.type==typeTy);
	}body{
		this.names=names; this.dom=dom; this.cod=cod;
	}
	override string toString(){
		auto d=dom.types.length==1?dom.types[0].toString():dom.toString(), c=cod.toString();
		if(dom&&dom.types.length>1||cast(FunTy)dom.types[0]) d="("~d~")";
		if(cast(TupleTy)cod) c="("~c~")";
		if(!cod.hasAnyFreeVar(names)){
			return d~" → "~c;
		}else{
			assert(names.length);
			return "∀"~(names.length==1?names[0]:"("~names.join(",")~")")~": "~d~". "~c;
		}
	}
	@property size_t nargs(){
		if(auto tplargs=cast(TupleTy)dom) return tplargs.types.length;
		return 1;
	}
	Expression argTy(size_t i)in{assert(i<nargs);}body{
		return dom.types[i];
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=dom.freeVarsImpl(dg)) return r;
		return cod.freeVarsImpl(v=>names.canFind(v)?0:dg(v));
	}
	private ForallTy relabel(string oname,string nname)in{assert(names.canFind(oname));}body{
		auto nnames=names.dup;
		foreach(ref v;nnames) if(v==oname) v=nname;
		auto nvar=varTy(nname);
		return forallTy(nnames,dom,cod.substitute(oname,nvar));
	}
	override ForallTy substitute(string name,Expression type){
		foreach(n;names){
			if(n!=name) continue;
			return relabel(n,n~"'").substitute(name,type);
		}
		auto ndom=dom.substitute(name,type);
		auto ncod=names.canFind(name)?cod:cod.substitute(name,type);
		return forallTy(names,ndom,ncod);
	}
	Expression tryApply(Expression[] rhs){
		if(rhs.length!=names.length) return null;
		foreach(i,r;rhs){
			if(!compatible(dom.types[i],rhs[i].type))
				return null;
		}
		Expression r=cod;
		foreach(i,n;names)
			r=r.substitute(n,rhs[i]); // TODO: avoid capturing!
		return r;
	}
}

ForallTy forallTy(string[] names,TupleTy dom,Expression cod){
	return memoize!((string[] names,TupleTy dom,Expression cod)=>new FunTy(names,dom,cod))(names,dom,cod);
}

alias FunTy=ForallTy;
FunTy funTy(TupleTy dom,Expression cod){
	return forallTy(dom.types.map!(_=>"").array,dom,cod);
}

/+FunTy funTy(TupleTy dom,Type cod){
	return memoize!((string[] names,TupleTy dom,Type cod)=>new FunTy(names,dom,cod))(names,dom,cod);
}+/


class VarTy: Type{
	string name;
	private this(string name){ this.name=name; }
	override string toString(){
		return name;
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		return dg(name);
	}
	override Expression substitute(string name,Expression type){
		if(this.name==name) return type;
		return this;
	}
}

VarTy varTy(string name){
	return memoize!((string name)=>new VarTy(name))(name);
}

class TypeTy: Type{
	this(){ this.type=this; super(); }
	override string toString(){
		return "*";
	}
	mixin VariableFree;
}
private TypeTy theTypeTy;
TypeTy typeTy(){ return theTypeTy?theTypeTy:(theTypeTy=new TypeTy()); }
