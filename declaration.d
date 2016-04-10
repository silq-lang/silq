import std.array, std.algorithm, std.conv;
import expression, scope_, util;

class Declaration: Expression{
	Identifier name;
	Scope scope_;
	this(Identifier name){ this.name=name; }
	override @property string kind(){ return "declaration"; }
	override string toString(){ return name.toString(); }
}

class Parameter: Expression{
	Identifier name;
	Expression type;
	this(Identifier name, Expression type){
		this.name=name; this.type=type;
	}
	override string toString(){ return name.toString()~": "~type.toString(); }
}

class FunctionDef: Declaration{
	Parameter[] params;
	
	CompoundExp body_;
	this(Identifier name, Parameter[] params, CompoundExp body_){
		super(name); this.params=params; this.body_=body_;
	}
	override string toString(){ return "def "~name.toString()~"("~join(map!(to!string)(params),",")~")"~body_.toString(); }
}


class DatDecl: Declaration{
	CompoundExp body_;
	this(Identifier name,CompoundExp body_){
		super(name); this.body_=body_;
	}
	override string toString(){
		return "dat "~name.toString()~body_.toString();
	}
}
