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
	Expression rret;
	CompoundExp body_;
	this(Identifier name, Parameter[] params, Expression rret, CompoundExp body_){
		super(name); this.params=params; this.rret=rret; this.body_=body_;
	}
	override string toString(){ return "def "~name.toString()~"("~join(map!(to!string)(params),",")~")"~body_.toString(); }

	override bool isCompound(){ return true; }

	// semantic information
	FunctionScope fscope_;
	Type ret;
	Type ftype;
	bool hasReturn;
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
	this(Expression init){ this.init=init; }
	abstract VarDecl[] decls();

	abstract void setType(Type type);
	abstract void setError();
}

class SingleDefExp: DefExp{
	VarDecl decl;
	override VarDecl[] decls(){ return [decl]; }
	this(VarDecl decl, BinaryExp!(Tok!":=") init){
		this.decl=decl; super(init);
	}
	override string toString(){
		return init.toString();
	}

	override void setType(Type type){
		assert(!!type);
		decl.vtype=type;
		if(!decl.vtype) decl.sstate=SemState.error;
	}
	override void setError(){
		decl.sstate=sstate=SemState.error;
	}
}

class MultiDefExp: DefExp{
	VarDecl[] decls_;
	override VarDecl[] decls(){ return decls_; }
	this(VarDecl[] decls_,Expression init){
		this.decls_=decls_; super(init);
	}
	override string toString(){
		return init.toString();
	}
	override void setType(Type type){
		assert(!!type);
		if(auto tt=cast(TupleTy)type){
			if(tt.types.length==decls_.length){
				foreach(i,decl;decls_){
					decl.vtype=tt.types[i];
				}
			}
		}
	}
	override void setError(){
		foreach(decl;decls_) decl.sstate=SemState.error;
		sstate=SemState.error;
	}
}
