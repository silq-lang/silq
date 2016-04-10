import std.array, std.algorithm, std.conv;
import lexer, type, expression, scope_, util;

class Declaration: Expression{
	Identifier name;
	Scope scope_;
	this(Identifier name){ this.name=name; }
	override @property string kind(){ return "declaration"; }
	override string toString(){ return name.toString(); }
}

class CompoundDecl: Expression{
	Expression[] s;
	this(Expression[] ss){s=ss;}

	override string toString(){return "{\n"~indent(join(map!(a=>a.toString()~(a.isCompound()?"":";"))(s),"\n"))~"\n}";}
	override bool isCompound(){ return true; }

	// semantic information
	AggregateScope ascope_;
}



class VarDecl: Declaration{
	Expression dtype;
	this(Identifier name){ super(name); }
	override string toString(){ return name.toString()~(dtype?": "~dtype.toString():vtype?": "~vtype.toString():""); }

	// semantic information
	Type vtype;
}

class Parameter: VarDecl{
	this(Identifier name, Expression type){
		super(name); this.dtype=type;
	}
	override string toString(){ return name.toString()~(type?": "~type.toString():""); }
}

class FunctionDef: Declaration{
	Parameter[] params;
	
	CompoundExp body_;
	this(Identifier name, Parameter[] params, CompoundExp body_){
		super(name); this.params=params; this.body_=body_;
	}
	override string toString(){ return "def "~name.toString()~"("~join(map!(to!string)(params),",")~")"~body_.toString(); }

	override bool isCompound(){ return true; }

	FunctionScope fscope_;
}


class DatDecl: Declaration{
	Type dtype;
	CompoundDecl body_;
	this(Identifier name,CompoundDecl body_){
		super(name); this.body_=body_;
	}
	override string toString(){
		return "dat "~name.toString()~body_.toString();
	}

	override bool isCompound(){ return true; }

	// semantic information
	DataScope dscope_;
}

abstract class DefExp: Expression{
	Expression init;
	abstract VarDecl[] decls();

	abstract void setType(Type type);
}

class SingleDefExp: DefExp{
	VarDecl decl;
	override VarDecl[] decls(){ return [decl]; }
	this(VarDecl decl, BinaryExp!(Tok!":=") init){
		this.decl=decl; this.init=init;
	}
	override string toString(){
		return init.toString();
	}

	override void setType(Type type){
		assert(!!type);
		decl.type=type;
	}
}

class MultiDefExp: DefExp{
	VarDecl[] decls_;
	Expression init;
	override VarDecl[] decls(){ return decls_; }
	this(VarDecl[] decls_,Expression init){
		this.decls_=decls_;this.init=init;
	}
	override string toString(){
		return init.toString();
	}
	override void setType(Type type){
		assert(!!type);
		// TODO!
	}
}
