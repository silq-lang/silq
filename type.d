import std.array, std.algorithm, std.conv;
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


class TupleTy: Type{
	Type[] types;
	private this(Type[] types){
		this.types=types;
		if(!types.length) this.type=this;
		super();
	}
	override string toString(){
		if(!types.length) return "𝟙";
		return types.map!(to!string).join(" × ");
	}
}

TupleTy theUnit;
TupleTy unit(){ return theUnit?theUnit:(theUnit=new TupleTy([])); }

TupleTy tupleTy(Type[] types){
	import std.functional;
	return memoize!((Type[] types)=>new TupleTy(types))(types);
}
