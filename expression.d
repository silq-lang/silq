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
	final Expression substitute(Expression[string] subst){
		auto r=substituteImpl(subst);
		if(!r.type){
			r.type=r.substituteImpl(subst);
			r.sstate=sstate;
		}
		return r;
	}
	abstract Expression substituteImpl(Expression[string] subst); // TODO: name might be free in the _types_ of subexpressions

	final bool unify(Expression rhs,ref Expression[string] subst){
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
	override Expression substituteImpl(Expression[string] subst){ return this; }
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){ return this==rhs; }
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
	override TypeAnnotationExp substituteImpl(Expression[string] subst){
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
		return _brk(lit.toString());
	}
	override bool isConstant(){ return true; }

	mixin VariableFree;
}

class Identifier: Expression{
	string name;
	@property auto ptr(){return name.ptr;}
	@property auto length(){return name.length;}
	this(string name){
		static string[string] uniq;
		auto n=uniq.get(name,null);
		if(n !is null) this.name = n;
		else this.name = uniq[name] = name;
	}
	override string toString(){return _brk(name);}
	override @property string kind(){return "identifier";}

	override int freeVarsImpl(scope int delegate(string) dg){
		return dg(name);
	}
	override Expression substituteImpl(Expression[string] subst){
		if(name in subst) return subst[name];
		return this;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		if(this==rhs){
			if(name !in subst) return true;
			if(subst[name]&&subst[name]!=this) return false;
			subst[name]=this;
			return true;
		}
		if(subst[name]==this) return false;
		if(subst[name]) return subst[name].unify(rhs,subst);
		if(rhs.hasFreeVar(name)) return false; // TODO: fixpoint types
		subst[name]=rhs;
		return true;
	}
	override bool opEquals(Object o){
		if(auto r=cast(Identifier)o){
			return name==r.name;
		}
		return false;
	}
	
	// semantic information:
	Declaration meaning;
	Scope scope_;
	bool calledDirectly=false;
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
	override UnaryExp substituteImpl(Expression[string] subst){
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
	override PostfixExp substituteImpl(Expression[string] subst){
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
	bool trailingComma;
	this(Expression exp, Expression[] args, bool trailingComma){e=exp; a=args; this.trailingComma=trailingComma; }
	override string toString(){
		return _brk(e.toString()~'['~join(map!(to!string)(a),",")~(trailingComma?",":"")~']');
	}
	override Expression eval(){
		if(a.length!=1) return this;
		auto ne=e.eval();
		auto na=a.dup;
		foreach(ref x;a) x=x.eval();
		Expression[] exprs;
		if(auto tpl=cast(TupleExp)ne) exprs=tpl.e;
		if(auto arr=cast(ArrayExp)ne) exprs=arr.e;
		if(exprs.length){
			if(auto le=cast(LiteralExp)na[0]){
				if(le.lit.type==Tok!"0"&&!le.lit.str.canFind(".")){
					auto idx=ℤ(le.lit.str);
					if(0<=idx&&idx<exprs.length) return exprs[cast(size_t)idx];
				}
			}
		}
		if(ne==e && na==a) return this;
		auto r=new IndexExp(ne,na,trailingComma);
		r.loc=loc;
		return r;
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		foreach(x;a) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override IndexExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto na=a.dup;
		foreach(ref x;na) x=substitute(subst);
		if(ne==e&&na==a) return this;
		auto r=new IndexExp(ne,na,trailingComma);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto idx=cast(IndexExp)rhs;
		if(!idx||a.length!=idx.a.length) return false;
		return e.unify(idx.e,subst)&&all!(i=>a[i].unify(idx.a[i],subst))(iota(a.length));
	}
}

class SliceExp: Expression{
	Expression e;
	Expression l,r;
	this(Expression exp, Expression left,Expression right){e=exp; l=left; r=right; }
	override string toString(){
		return _brk(e.toString()~'['~l.toString()~".."~r.toString()~']');
	}
	override Expression eval(){
		auto ne=e.eval(), nl=l.eval(), nr=r.eval();
		Expression[] exprs;
		auto tpl=cast(TupleExp)ne, arr=cast(ArrayExp)ne;
		if(tpl) exprs=tpl.e;
		if(arr) exprs=arr.e;
		if(tpl||arr){
			if(auto le=cast(LiteralExp)nl){
				if(auto re=cast(LiteralExp)nr){
					if(le.lit.type==Tok!"0"&&!le.lit.str.canFind(".")&&re.lit.type==Tok!"0"&&!re.lit.str.canFind(".")){
						auto lid=ℤ(le.lit.str), rid=ℤ(re.lit.str);
						if(cast(size_t)lid==0 && cast(size_t)rid==exprs.length) return e;
						if(0<=lid&&lid<=rid&&rid<=exprs.length){
							auto rexprs=exprs[cast(size_t)lid..cast(size_t)rid];
							if(tpl){
								auto res=new TupleExp(rexprs);
								res.loc=loc;
								return res;
							}
							if(arr){
								auto res=new ArrayExp(rexprs);
								res.loc=loc;
								return res;
							}
						}
					}
				}
			}
		}
		if(ne==e && nl==l && nr==r) return this;
		auto res=new SliceExp(ne,nl,nr);
		res.loc=loc;
		return res;
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto x=e.freeVarsImpl(dg)) return x;
		if(auto x=l.freeVarsImpl(dg)) return x;
		if(auto x=r.freeVarsImpl(dg)) return x;
		return 0;
	}
	override SliceExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto nl=l.substitute(subst);
		auto nr=r.substitute(subst);
		if(ne==e&&nl==l&&nr==r) return this;
		auto res=new SliceExp(ne,nl,nr);
		res.loc=loc;
		return res;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto sl=cast(SliceExp)rhs;
		return e.unify(sl.e,subst)&&l.unify(sl.l,subst)&&r.unify(sl.r,subst);
	}
}

string tupleToString(Expression e,bool isSquare){
	auto d=isSquare?"[]":"()";
	bool isTuple=!!cast(TupleExp)e;
	auto str=e.toString();
	if(isTuple||e.brackets){
		writeln(str);
		assert(str[0]=='(' && str[$-1]==')');
		str=str[1..$-1];
	}
	return d[0]~str~d[1];
}

class CallExp: Expression{
	Expression e;
	Expression arg;
	bool isSquare;
	this(Expression exp, Expression arg, bool isSquare=false){e=exp; this.arg=arg; this.isSquare=isSquare; }
	override string toString(){
		return _brk(e.toString()~arg.tupleToString(isSquare));
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return arg.freeVarsImpl(dg);
	}
	override CallExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto narg=arg.substitute(subst);
		if(ne==e&&narg==arg) return this;
		auto r=new CallExp(ne,narg,isSquare);
		r.loc=loc;
		if(sstate==SemState.completed){
			r.type=type.substitute(subst);
			r.sstate=SemState.completed;
		}
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return e.unify(ce.e,subst)&&arg.unify(ce.arg,subst);
	}
	override bool opEquals(Object rhs){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return e==ce.e&&arg==ce.arg;
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
	override BinaryExp!op substituteImpl(Expression[string] subst){
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
	override FieldExp substituteImpl(Expression[string] subst){
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
	override IteExp substituteImpl(Expression[string] subst){
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
	override string toString(){ return _brk("("~e.map!(to!string).join(",")~")"); }
	final @property size_t length(){ return e.length; }

	override int freeVarsImpl(scope int delegate(string) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override TupleExp substituteImpl(Expression[string] subst){
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
		return _brk(d[0]~join(map!(to!string)(fd.params),",")~d[1]~fd.body_.toString());
	}

	mixin VariableFree; // TODO!
}

class ArrayExp: Expression{
	Expression[] e;
	this(Expression[] e){
		this.e=e;
	}
	override string toString(){ return _brk("["~e.map!(to!string).join(",")~"]");}
	override bool isConstant(){ return e.all!(x=>x.isConstant()); }

	override int freeVarsImpl(scope int delegate(string) dg){
		foreach(x;e) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override ArrayExp substituteImpl(Expression[string] subst){
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
	override string toString(){ return _brk("assert("~e.toString()~")"); }
	mixin VariableFree; // TODO!
}

class ObserveExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override string toString(){ return _brk("observe("~e.toString()~")"); }

	mixin VariableFree; // TODO
}

class CObserveExp: Expression{
	Expression var;
	Expression val;
	this(Expression var,Expression val){
		this.var=var; this.val=val;
	}
	override string toString(){ return _brk("cobserve("~var.toString()~","~val.toString()~")"); }

	mixin VariableFree; // TODO
}
