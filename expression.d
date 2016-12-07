// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, scope_, type, declaration, util;

enum SemState{
	initial,
	started,
	completed,
	error,
}

abstract class Node{
	// debug auto cccc=0;
	Location loc;
	abstract @property string kind();

	// semantic information
	SemState sstate;
}


abstract class Expression: Node{
	Expression type;
	int brackets=0;
	override string toString(){return _brk("{}()");}
	protected string _brk(string s){return std.array.replicate("(",brackets)~s~std.array.replicate(")",brackets); return s;}

	override @property string kind(){return "expression";}
	bool isCompound(){ return false; }
	bool isConstant(){ return false; }

	Expression eval(){ return this; }
	
	abstract int freeVarsImpl(scope int delegate(string) dg);
	final Expression substitute(string name,Expression exp){
		return substitute([name:exp]);
	}
	abstract Expression substitute(Expression[string] subst); // TODO: name might be free in the _types_ of subexpressions

	final bool unify(Expression rhs,ref Expression[string] subst){
		if(this == rhs) return true;
		return unifyImpl(rhs,subst) || eval().unifyImpl(rhs.eval(),subst);
	}
	abstract bool unifyImpl(Expression rhs,ref Expression[string] subst);
	
	final freeVars(){
		static struct FreeVars{
			Expression self;
			int opApply(scope int delegate(string) dg){
				return self.freeVarsImpl(dg);
			}
		}
		return FreeVars(this);
	}
	final bool hasFreeVar(string name){
		foreach(var;freeVars){
			if(var == name)
				return true;
		}
		return false;
	}
	final bool hasAnyFreeVar(R)(R r){
		foreach(var;freeVars){
			if(r.canFind(var))
				return true;
		}
		return false;
	}
}

mixin template VariableFree(){
	override int freeVarsImpl(scope int delegate(string)){ return 0; }
	override Expression substitute(Expression[string] subst){ return this; }
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){ return false; }
}

class TypeAnnotationExp: Expression{
	Expression e,t;
	this(Expression e, Expression t){
		this.e=e; this.t=t;
	}
	override @property string kind(){ return e.kind; }
	override string toString(){ return _brk(e.toString()~": "~t.toString()); }
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return t.freeVarsImpl(dg);
	}
	override TypeAnnotationExp substitute(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto nt=t.substitute(subst);
		if(ne==e&&nt==t) return this;
		auto r=new TypeAnnotationExp(ne,nt);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		return e.unify(rhs,subst);
	}
}

// workaround for the bug:
UnaryExp!(Tok!"&") isAddressExp(Expression self){return cast(UnaryExp!(Tok!"&"))self;}

class ErrorExp: Expression{
	this(){}//{sstate = SemState.error;}
	override string toString(){return _brk("__error");}

	mixin VariableFree;
}

class LiteralExp: Expression{
	Token lit;
	this(Token lit){ // TODO: suitable contract
		this.lit=lit;
	}
	override string toString(){
		return lit.toString();
	}
	override bool isConstant(){ return true; }

	mixin VariableFree;
}

class Identifier: Expression{
	string name;
	// alias name this; // stupid compiler bug prevents this from being useful
	@property auto ptr(){return name.ptr;}
	@property auto length(){return name.length;}
	this(string name){ // TODO: make more efficient, this is a bottleneck!
		static string[string] uniq;
		auto n=uniq.get(name,null);
		if(n !is null) this.name = n;
		else this.name = uniq[name] = name;
		static int x = 0;
	}
	override string toString(){return _brk(name);}
	override @property string kind(){return "identifier";}

	mixin VariableFree;
	
	// semantic information:
	Declaration meaning;
	Scope scope_;
}

class PlaceholderExp: Expression{
	Identifier ident;
	this(Identifier ident){ this.ident = ident; }
	override string toString(){ return _brk("?"); }
	override @property string kind(){ return "placeholder"; }

	mixin VariableFree;
}


class UnaryExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){
		return _brk(TokChars!op~e.toString());
	}
	static if(op==Tok!"&"){
		override @property string kind(){
			return "address";
		}
		//override UnaryExp!(Tok!"&") isAddressExp(){return this;}
	}
	override bool isConstant(){ return e.isConstant(); }

	override int freeVarsImpl(scope int delegate(string) dg){
		return e.freeVarsImpl(dg);
	}
	override UnaryExp substitute(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new UnaryExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto ue=cast(typeof(this))rhs;
		if(!ue) return false;
		return e.unify(ue.e,subst);
	}
}
class PostfixExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return _brk(e.toString()~TokChars!op);}

	override int freeVarsImpl(scope int delegate(string) dg){
		return e.freeVarsImpl(dg);
	}
	override PostfixExp substitute(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new PostfixExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto pe=cast(PostfixExp)rhs;
		if(!pe) return false;
		return e.unify(pe.e,subst);
	}
}

class IndexExp: Expression{ //e[a...]
	Expression e;
	Expression[] a;
	this(Expression exp, Expression[] args){e=exp; a=args;}
	override string toString(){
		return _brk(e.toString()~'['~join(map!(to!string)(a),",")~']');
	}

	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		foreach(x;a) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override IndexExp substitute(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto na=a.dup;
		foreach(ref x;na) x=substitute(subst);
		if(ne==e&&na==a) return this;
		auto r=new IndexExp(ne,na);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto idx=cast(IndexExp)rhs;
		if(!idx||a.length!=idx.a.length) return false;
		return e.unify(idx.e,subst)&&all!(i=>a[i].unify(idx.a[i],subst))(iota(a.length));
	}
}

class CallExp: Expression{
	Expression e;
	Expression[] args;
	bool isSquare;
	this(Expression exp, Expression[] args, bool isSquare=false){e=exp; this.args=args; this.isSquare=isSquare; }
	override string toString(){
		return _brk(e.toString()~'('~join(map!(to!string)(args),",")~')');
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		foreach(x;args) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override CallExp substitute(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto nargs=args.dup;
		foreach(ref x;nargs) x=substitute(subst);
		if(ne==e&&nargs==args) return this;
		auto r=new CallExp(ne,nargs);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto ce=cast(CallExp)rhs;
		if(!ce||args.length!=ce.args.length) return false;
		return e.unify(ce.e,subst)&&all!(i=>args[i].unify(ce.args[i],subst))(iota(args.length));
	}
}

abstract class ABinaryExp: Expression{
	Expression e1,e2;
	this(Expression left, Expression right){e1=left; e2=right;}
	override bool isConstant(){
		return e1.isConstant() && e2.isConstant();
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e1.freeVarsImpl(dg)) return r;
		if(auto r=e2.freeVarsImpl(dg)) return r;
		return 0;
	}
}

class BinaryExp(TokenType op): ABinaryExp{
	this(Expression left, Expression right){super(left,right);}

	override string toString(){
		return _brk(e1.toString() ~ " "~TokChars!op~" "~e2.toString());
	}
	//override string toString(){return e1.toString() ~ " "~ e2.toString~TokChars!op;} // RPN
	static if(op==Tok!":="){
		override @property string kind(){ return "variable declaration"; }
	}
	override BinaryExp!op substitute(Expression[string] subst){
		auto ne1=e1.substitute(subst);
		auto ne2=e2.substitute(subst);
		if(ne1==e1&&ne2==e2) return this;
		auto r=new BinaryExp!op(ne1,ne2);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto be=cast(typeof(this))rhs;
		if(!be) return false;
		return e1.unify(be.e1,subst)&&e2.unify(be.e2,subst);
	}
}

class FieldExp: Expression{
	Expression e;
	Identifier f;

	this(Expression e,Identifier f){ this.e=e; this.f=f; }
	override string toString(){
		return _brk(e.toString()~"."~f.toString());
	}

	override int freeVarsImpl(scope int delegate(string) dg){
		return e.freeVarsImpl(dg);
	}
	override FieldExp substitute(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new FieldExp(ne,f);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto fe=cast(FieldExp)rhs;
		if(!fe||f!=fe.f) return false;
		return e.unify(rhs,subst);
	}
}

class IteExp: Expression{
	Expression cond;
	CompoundExp then, othw;
	this(Expression cond, CompoundExp then, CompoundExp othw){
		this.cond=cond; this.then=then; this.othw=othw;
	}
	override string toString(){return _brk("if "~cond.toString() ~ " " ~ then.toString() ~ (othw?" else " ~ (othw.s.length==1&&cast(IteExp)othw.s[0]?othw.s[0].toString():othw.toString()):""));}

	override bool isCompound(){ return true; }

	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=cond.freeVarsImpl(dg)) return r;
		if(auto r=then.freeVarsImpl(dg)) return r;
		if(othw) if(auto r=othw.freeVarsImpl(dg)) return r;
		return 0;
	}
	override IteExp substitute(Expression[string] subst){
		auto ncond=cond.substitute(subst);
		auto nthen=cast(CompoundExp)then.substitute(subst);
		auto nothw=othw?cast(CompoundExp)othw.substitute(subst):null;
		assert(!!nthen && !!nothw==!!othw);
		if(ncond==cond&&nthen==then&&nothw==othw) return this;
		auto r=new IteExp(ncond,nthen,nothw);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto ite=cast(IteExp)rhs;
		if(!ite) return false;
		return cond.unify(ite.cond,subst)&&then.unify(ite.then,subst)
			&&!othw&&!ite.othw||othw&&ite.othw&&othw.unify(ite.othw,subst);
	}
}

class RepeatExp: Expression{
	Expression num;
	CompoundExp bdy;
	this(Expression num, CompoundExp bdy){
		this.num=num; this.bdy=bdy;
	}
	override string toString(){ return _brk("repeat "~num.toString()~" "~bdy.toString()); }
	override @property string kind(){ return "repeat loop"; }
	override bool isCompound(){ return true; }

	mixin VariableFree; // TODO
}

class ForExp: Expression{
	Identifier var;
	bool leftExclusive;
	Expression left;
	bool rightExclusive;
	Expression right;
	CompoundExp bdy;
	this(Identifier var,bool leftExclusive,Expression left,bool rightExclusive,Expression right,CompoundExp bdy){
		this.var=var;
		this.leftExclusive=leftExclusive; this.left=left;
		this.rightExclusive=rightExclusive; this.right=right;
		this.bdy=bdy;
	}
	override string toString(){ return _brk("for "~var.toString()~" in "~
											(leftExclusive?"(":"[")~left.toString()~".."~right.toString()~
											(rightExclusive?")":"]")~bdy.toString()); }
	override @property string kind(){ return "for loop"; }
	override bool isCompound(){ return true; }

	// semantic information
	ForExpScope fescope_;
	VarDecl loopVar;

	mixin VariableFree; // TODO
}

class WhileExp: Expression{
	Expression cond;
	CompoundExp bdy;
	this(Expression cond,CompoundExp bdy){
		this.cond=cond;
		this.bdy=bdy;
	}
	override string toString(){ return _brk("while "~cond.toString()~bdy.toString()); }
	override @property string kind(){ return "while loop"; }
	override bool isCompound(){ return true; }	

	mixin VariableFree; // TODO
}

class CompoundExp: Expression{
	Expression[] s;
	this(Expression[] ss){s=ss;}

	override string toString(){return "{\n"~indent(join(map!(a=>a.toString()~(a.isCompound()?"":";"))(s),"\n"))~"\n}";}
	override bool isCompound(){ return true; }

	// semantic information
	BlockScope blscope_;

	mixin VariableFree; // TODO!
}

class TupleExp: Expression{
	Expression[] e;
	this(Expression[] e){
		this.e=e;
	}
	override string toString(){ return "("~e.map!(to!string).join(",")~")"; }
	final @property size_t length(){ return e.length; }

	override int freeVarsImpl(scope int delegate(string) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override TupleExp substitute(Expression[string] subst){
		auto ne=e.dup;
		foreach(ref x;ne) x=x.substitute(subst);
		if(ne==e) return this;
		auto r=new TupleExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto te=cast(TupleExp)rhs;
		if(!te||e.length!=te.e.length) return false;
		return all!(i=>e[i].unify(te.e[i],subst))(iota(e.length));
	}
}

class LambdaExp: Expression{
	FunctionDef fd;
	this(FunctionDef fd){
		this.fd=fd;
	}
	override string toString(){
		string d=fd.isSquare?"[]":"()";
		return d[0]~join(map!(to!string)(fd.params),",")~d[1]~fd.body_.toString();
	}

	mixin VariableFree; // TODO!
}

class ArrayExp: Expression{
	Expression[] e;
	this(Expression[] e){
		this.e=e;
	}
	override string toString(){ return "["~e.map!(to!string).join(",")~"]";}
	override bool isConstant(){ return e.all!(x=>x.isConstant()); }

	override int freeVarsImpl(scope int delegate(string) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override ArrayExp substitute(Expression[string] subst){
		auto ne=e.dup;
		foreach(ref x;ne) x=x.substitute(subst);
		if(ne==e) return this;
		auto r=new ArrayExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto ae=cast(ArrayExp)rhs;
		if(!ae||e.length!=ae.e.length) return false;
		return all!(i=>e[i].unify(ae.e[i],subst))(iota(e.length));
	}
}

class ReturnExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override string toString(){ return "return"~(e?" "~e.toString():""); }

	string expected;
	mixin VariableFree; // TODO!
}

class AssertExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override string toString(){ return "assert("~e.toString()~")"; }
	mixin VariableFree; // TODO!
}

class ObserveExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override string toString(){ return "observe("~e.toString()~")"; }

	mixin VariableFree; // TODO
}

class CObserveExp: Expression{
	Expression var;
	Expression val;
	this(Expression var,Expression val){
		this.var=var; this.val=val;
	}
	override string toString(){ return "cobserve("~var.toString()~","~val.toString()~")"; }

	mixin VariableFree; // TODO
}
