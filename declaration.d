// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

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
	@property override string kind(){ return "variable"; }

	// semantic information
	Type vtype;
	Expression initializer;
}

class Parameter: VarDecl{
	this(Identifier name, Expression type){
		super(name); this.dtype=type;
	}
	override string toString(){ return name.toString()~(dtype?": "~dtype.toString():""); }
	@property override string kind(){ return "parameter"; }
}

class FunctionDef: Declaration{
	Parameter[] params;
	Expression rret;
	CompoundExp body_;
	bool isSquare=false;
	this(Identifier name, Parameter[] params, Expression rret, CompoundExp body_){
		super(name); this.params=params; this.rret=rret; this.body_=body_;
	}
	override string toString(){
		string d=isSquare?"[]":"()";
		return "def "~(name?name.toString():"")~d[0]~join(map!(to!string)(params),",")~d[1]~body_.toString();
	}

	override bool isCompound(){ return true; }

	// semantic information
	FunctionScope fscope_;
	VarDecl context;
	@property string contextName()in{assert(!!context);}body{ return context.name.name; }
	Type ret;
	Type ftype;
	bool hasReturn;
	bool isConstructor;

	@property Scope realScope(){
		if(isConstructor) return scope_.getDatDecl().scope_;
		return scope_;
	}
	@property bool isNested(){ return !!cast(NestedScope)realScope; }
}


class DatDecl: Declaration{
	AggregateTy dtype;
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
	BinaryExp!(Tok!":=") initializer;
	this(BinaryExp!(Tok!":=") init){ this.initializer=init; }
	abstract VarDecl[] decls();

	abstract void setType(Type type);
	abstract void setInitializer();
	abstract void setError();
}

class SingleDefExp: DefExp{
	VarDecl decl;
	override VarDecl[] decls(){ return [decl]; }
	this(VarDecl decl, BinaryExp!(Tok!":=") init){
		this.decl=decl; super(init);
	}
	override string toString(){
		return initializer.toString();
	}

	override void setType(Type type){
		assert(!!type);
		decl.vtype=type;
		if(!decl.vtype) decl.sstate=SemState.error;
	}
	override void setInitializer(){
		assert(!decl.initializer&&initializer);
		decl.initializer=initializer.e2;
	}
	override void setError(){
		decl.sstate=sstate=SemState.error;
	}
}

class MultiDefExp: DefExp{
	VarDecl[] decls_;
	override VarDecl[] decls(){ return decls_; }
	this(VarDecl[] decls_,BinaryExp!(Tok!":=") init){
		this.decls_=decls_; super(init);
	}
	override string toString(){
		return initializer.toString();
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
	override void setInitializer(){
		assert(initializer);
		auto tpl=cast(TupleExp)initializer.e2;
		if(!tpl) return;
		assert(tpl.length==decls.length);
		foreach(i;0..decls.length){
			assert(!decls[i].initializer);
			decls[i].initializer=tpl.e[i];
		}
	}
	override void setError(){
		foreach(decl;decls_) decl.sstate=SemState.error;
		sstate=SemState.error;
	}
}
