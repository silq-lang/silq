// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.algorithm, std.conv;
import lexer, type, expression, scope_, util;

class Declaration: Expression{
	Identifier name;
	Scope scope_;
	this(Identifier name){ this.name=name; }
	override @property string kind(){ return "declaration"; }
	final @property string getName(){ return (rename?rename:name).name; }
	override string toString(){ return getName; }

	mixin VariableFree;

	// semantic information
	Identifier rename=null;
}

class CompoundDecl: Expression{
	Expression[] s;
	this(Expression[] ss){s=ss;}

	override string toString(){return "{\n"~indent(join(map!(a=>a.toString()~(a.isCompound()?"":";"))(s),"\n"))~"\n}";}
	override bool isCompound(){ return true; }

	// semantic information
	AggregateScope ascope_;

	mixin VariableFree; // TODO!
}



class VarDecl: Declaration{
	Expression dtype;
	this(Identifier name){ super(name); }
	override string toString(){ return getName~(dtype?": "~dtype.toString():vtype?": "~vtype.toString():""); }
	@property override string kind(){ return "variable"; }

	// semantic information
	Expression vtype;
	Expression initializer;
}

class Parameter: VarDecl{
	this(Identifier name, Expression type){
		super(name); this.dtype=type;
	}
	override string toString(){ return getName~(dtype?": "~dtype.toString():""); }
	@property override string kind(){ return "parameter"; }
}

class FunctionDef: Declaration{
	Parameter[] params;
	bool isTuple;
	Expression rret;
	CompoundExp body_;
	bool isSquare=false;
	this(Identifier name, Parameter[] params, bool isTuple, Expression rret, CompoundExp body_)in{
		assert(isTuple||params.length==1);
	}body{
		super(name); this.params=params; this.isTuple=isTuple; this.rret=rret; this.body_=body_;
	}
	override string toString(){
		string d=isSquare?"[]":"()";
		return "def "~(name?getName:"")~d[0]~join(map!(to!string)(params),",")~(isTuple&&params.length==1?",":"")~d[1]~body_.toString();
	}

	override bool isCompound(){ return true; }

	// semantic information
	FunctionScope fscope_;
	VarDecl context;
	VarDecl contextVal;
	VarDecl thisVar; // for constructors
	@property string contextName()in{assert(!!context);}body{ return context.getName; }
	Expression ret; // return type
	FunTy ftype;
	bool hasReturn;
	bool isConstructor;
	string[] retNames;

	@property Scope realScope(){
		if(isConstructor) return scope_.getDatDecl().scope_;
		return scope_;
	}
	@property bool isNested(){ return !!cast(NestedScope)realScope; }

	@property size_t numArgs(){
		if(!ftype) return 0;
		return ftype.dom.numComponents;
	}

	@property size_t numReturns(){
		if(!ftype) return 0;
		return ftype.cod.numComponents;
	}
}


enum Variance{
	invariant_,
	covariant,
	contravariant,
}

class DatParameter: Parameter{
	Variance variance;
	this(Variance variance, Identifier name, Expression type){
		this.variance=variance;
		super(name,type);
	}
	override string toString(){
		final switch(variance)with(Variance){
			case invariant_: return super.toString();
			case covariant: return "+"~super.toString();
			case contravariant: return "-"~super.toString();
		}
	}
}

class DatDecl: Declaration{
	AggregateTy dtype;
	bool hasParams;
	DatParameter[] params;
	bool isTuple;
	CompoundDecl body_;
	this(Identifier name,bool hasParams,DatParameter[] params,bool isTuple,CompoundDecl body_)in{
		if(hasParams) assert(isTuple||params.length==1);
		else assert(isTuple&&params.length==0);
	}body{
		super(name);
		this.hasParams=hasParams;
		this.params=params;
		this.isTuple=isTuple;
		this.body_=body_;
	}
	override string toString(){
		return "dat "~getName~(hasParams?text("[",params.map!(to!string).joiner(","),"]"):"")~body_.toString();
	}

	override bool isCompound(){ return true; }

	final Expression[string] getSubst(Expression arg){
		Expression[string] subst;
		if(isTuple){
			foreach(i,p;params)
				subst[p.getName]=new IndexExp(arg,[new LiteralExp(Token(Tok!"0",to!string(i)))],false).eval();
		}else{
			assert(params.length==1);
			subst[params[0].getName]=arg;
		}
		return subst;
	}

	// semantic information
	DataScope dscope_;
	VarDecl context;
	@property string contextName()in{assert(!!context);}body{ return context.getName; }
	@property bool isNested(){ return !!cast(NestedScope)scope_; }
}

abstract class DefExp: Expression{
	BinaryExp!(Tok!":=") initializer;
	this(BinaryExp!(Tok!":=") init){ this.initializer=init; }
	abstract VarDecl[] decls();

	abstract void setType(Expression type);
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

	override void setType(Expression type){
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

	mixin VariableFree; // TODO
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
	override void setType(Expression type){
		assert(!!type);
		if(auto tt=cast(TupleTy)type){
			if(tt.types.length==decls_.length){
				foreach(i,decl;decls_){
					decl.vtype=tt.types[i];
				}
			}
		}else{
			assert(0,"TODO!");
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

	mixin VariableFree;
}

string getActualPath(string path){
	import std.path, file=std.file, options;
	auto ext = path.extension;
	if(ext=="") path = path.setExtension("psi");
	if(file.exists(path)) return path;
	foreach_reverse(p;opt.importPath){
		auto candidate=buildPath(p,path);
		if(file.exists(candidate))
			return candidate;
	}
	return path;
}

class ImportExp: Declaration{
	Expression[] e;
	this(Expression[] e){
		super(null);
		this.e=e;
	}
	static string getPath(Expression e){
		static string doIt(Expression e){
			import std.path;
			if(auto i=cast(Identifier)e) return i.name;
			if(auto f=cast(BinaryExp!(Tok!"."))e) return buildPath(doIt(f.e1),doIt(f.e2));
			assert(0);
		}
		return doIt(e);
	}
	override @property string kind(){ return "import declaration"; }
	override string toString(){ return "import "~e.map!(to!string).join(","); }
}
