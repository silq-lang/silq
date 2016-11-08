// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.algorithm, std.conv;
import std.functional;
import expression, declaration;

class Type: Expression{
	this(){ if(!this.type) this.type=unit; } // TODO: "Type"?
	override @property string kind(){ return "type"; }
	override string toString(){ return "T"; }
}

class ErrorTy: Type{
	this(){}//{sstate = SemState.error;}
	override string toString(){return "__error";}
}


class ℝTy: Type{
	private this(){}
	override string toString(){
		return "ℝ";
	}
}
private ℝTy theℝ;

ℝTy ℝ(){ return theℝ?theℝ:(theℝ=new ℝTy()); }

class AggregateTy: Type{
	DatDecl decl;
	this(DatDecl decl){
		this.decl=decl;
	}
	override string toString(){ return decl.name.toString(); }
}

class ContextTy: Type{
	private this(){} // dummy
}
private ContextTy theContextTy;
ContextTy contextTy(){ return theContextTy?theContextTy:(theContextTy=new ContextTy()); }



class TupleTy: Type{
	Type[] types;
	private this(Type[] types){
		this.types=types;
		if(!types.length) this.type=this;
		super();
	}
	override string toString(){
		if(!types.length) return "𝟙";
		if(types.length==1) return "("~types[0].toString()~")¹";
		return types.map!(a=>cast(TupleTy)a&&a!is unit?"("~a.toString()~")":a.toString()).join(" × ");
	}
}

TupleTy unit(){ return tupleTy([]); }

TupleTy tupleTy(Type[] types){
	return memoize!((Type[] types)=>new TupleTy(types))(types);
}

class ArrayTy: Type{
	Type next;
	private this(Type next){
		this.next=next;
	}
	override string toString(){
		bool p=cast(FunTy)next||cast(TupleTy)next&&next!is unit;
		return p?"("~next.toString()~")[]":next.toString()~"[]";
	}
}

ArrayTy arrayTy(Type next){
	return memoize!((Type next)=>new ArrayTy(next))(next);
}

class StringTy: Type{
	private this(){}
	override string toString(){
		return "string";
	}
}

StringTy stringTy(){ return memoize!(()=>new StringTy()); }

class FunTy: Type{
	Type dom,cod;
	private this(Type dom,Type cod){
		this.dom=dom; this.cod=cod;
	}
	override string toString(){
		return dom.toString()~" → "~cod.toString();
	}
}

FunTy funTy(Type dom,Type cod){
	return memoize!((Type dom,Type cod)=>new FunTy(dom,cod))(dom,cod);
}
