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

	final Expression substitute(string name,Expression exp){
		return substitute([name:exp]);
	}
	final Expression substitute(Expression[string] subst){
		auto r=substituteImpl(subst);
		if(type == this) r.type=r;
		else r.type=type.substitute(subst);
		return r;
	}
	abstract Expression substituteImpl(Expression[string] subst); // TODO: name might be free in the _types_ of subexpressions

	final bool unify(Expression rhs,ref Expression[string] subst, bool meet){
		return unifyImpl(rhs,subst,meet) || eval().unifyImpl(rhs.eval(),subst,meet);
	}
	abstract bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet);

	abstract int freeVarsImpl(scope int delegate(string) dg);
	static struct FreeVars{
		Expression self;
		int opApply(scope int delegate(string) dg)in{
			assert(!!self);
		}do{
			if(auto r=self.freeVarsImpl(dg)) return r;
			if(self.type != self)
				foreach(v;self.type.freeVars())
					if(auto r=dg(v)) return r;
			return 0;
		}
	}
	final FreeVars freeVars()in{
		assert(!!this);
	}do{
		return FreeVars(this);
	}
	final bool hasFreeVar(string name)in{
		assert(!!this);
	}do{
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
	abstract int componentsImpl(scope int delegate(Expression) dg);
	static struct Components{
		Expression self;
		bool ignoreTypes;
		int opApply(scope int delegate(Expression) dg)in{
			assert(!!self);
		}do{
			if(auto r=self.componentsImpl(dg)) return r;
			return 0;
		}
	}
	final Components components()in{
		assert(!!this);
	}do{
		return Components(this,false);
	}
	final int subexpressionsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(this)) return r;
		foreach(x;components) if(auto r=x.subexpressionsImpl(dg)) return r;
		return 0;
	}
	static struct Subexpressions{
		Expression self;
		int opApply(scope int delegate(Expression) dg)in{
			assert(!!self);
		}do{
			if(auto r=self.subexpressionsImpl(dg)) return r;
			return 0;
		}
	}
	final Subexpressions subexpressions()in{
		assert(!!this);
	}do{
		return Subexpressions(this);
	}
	bool isSubtypeImpl(Expression rhs){
		return this == rhs;
	}
	Expression combineTypesImpl(Expression rhs,bool meet){
		if(this == rhs) return this;
		return null;
	}

	bool isClassical(){
		return false;
	}
	bool impliesConst(){
		return isClassical();
	}
	bool hasClassicalComponent(){
		return true;
	}
	Expression getClassical(){
		if(isClassical()) return this;
		return null;
	}
	Annotation getAnnotation(){
		return Annotation.none;
	}
	final bool isLifted(){ return getAnnotation()>=Annotation.lifted; }
	bool isMfree(){ return getAnnotation()>=Annotation.mfree; }
}

mixin template VariableFree(){
	override int freeVarsImpl(scope int delegate(string)){ return 0; }
	override Expression substituteImpl(Expression[string] subst){ return this; }
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		return combineTypes(this,rhs,meet)!is null;
	}
}

class TypeAnnotationExp: Expression{
	Expression e,t;
	this(Expression e, Expression t){
		this.e=e; this.t=t;
	}
	override @property string kind(){ return e.kind; }
	override string toString(){ return _brk(e.toString()~": "~t.toString()); }
	override bool isConstant(){
		return e.isConstant();
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return t.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		return dg(t);
	}
	override TypeAnnotationExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto nt=t.substitute(subst);
		if(ne==e&&nt==t) return this;
		auto r=new TypeAnnotationExp(ne,nt);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		return e.unify(rhs,subst,meet);
	}
	override Annotation getAnnotation(){
		return e.getAnnotation();
	}
}

// workaround for the bug:
UnaryExp!(Tok!"&") isAddressExp(Expression self){return cast(UnaryExp!(Tok!"&"))self;}

class ErrorExp: Expression{
	this(){}//{sstate = SemState.error;}
	override string toString(){return _brk("__error");}

	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0;
	}
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

	override bool opEquals(Object o){
		auto r=cast(LiteralExp)o;
		if(!r) return false;
		if(lit.type!=r.lit.type) return false;
		switch(lit.type){
			case Tok!"0":
				return ℤ(lit.str)==ℤ(r.lit.str);
			default:
				return this is r;
		}
	}

	override Annotation getAnnotation(){ return Annotation.lifted; }
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
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
	override string toString(){return _brk((classical?"!":"")~name);}
	override @property string kind(){return "identifier";}

	override int freeVarsImpl(scope int delegate(string) dg){
		return dg(name);
	}
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
	override Expression substituteImpl(Expression[string] subst){
		if(name in subst){
			if(classical)
				if(auto r=subst[name].getClassical())
					return r;
			return subst[name];
		}
		return this;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		if(this==rhs){
			if(name !in subst) return true;
			if(subst[name]&&subst[name]!=this) return false;
			subst[name]=this;
			return true;
		}
		if(name !in subst) return false;
		if(subst[name]==this) return false;
		if(type==typeTy&&rhs.type==typeTy)
			if(rhs.isClassical()<classical) return false;
		if(subst[name]){
			if(!subst[name].unify(rhs,subst,meet))
				return false;
			if(subst[name].type==typeTy&&rhs.type==typeTy)
				if(auto cmb=combineTypes(subst[name],rhs,meet)) // TODO: good?
					subst[name]=cmb;
			return true;
		}
		if(rhs.hasFreeVar(name)) return false; // TODO: fixpoint types
		subst[name]=rhs;
		return true;
	}
	override bool opEquals(Object o){
		if(auto r=cast(Identifier)o){
			return name==r.name && classical==r.classical && meaning==r.meaning;
		}
		return false;
	}

	override bool isClassical(){
		assert(type==typeTy);
		return classical;
	}
	override bool hasClassicalComponent(){
		assert(type==typeTy);
		return classical;
	}
	override Expression getClassical(){
		assert(type==typeTy);
		if(classical) return this;
		if(!meaning) return varTy(name,typeTy,true);
		auto r=new Identifier(name);
		r.classical=true;
		r.type=type;
		r.meaning=meaning;
		r.sstate=SemState.completed;
		return r;

	}

	override Annotation getAnnotation(){ return Annotation.lifted; }

	// semantic information:
	Declaration meaning;
	Scope scope_;
	bool calledDirectly=false;
	bool classical=false;
}

class PlaceholderExp: Expression{
	Identifier ident;
	this(Identifier ident){ this.ident = ident; }
	override string toString(){ return _brk("?"); }
	override @property string kind(){ return "placeholder"; }

	mixin VariableFree;
	override int componentsImpl(scope int delegate(Expression) dg){ return 0; }
}


class UnaryExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){
		import std.uni;
		return _brk(TokChars!op~(TokChars!op[$-1].isAlpha()?" ":"")~e.toString());
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
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override UnaryExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new UnaryExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ue=cast(typeof(this))rhs;
		if(!ue) return false;
		return e.unify(ue.e,subst,meet);
	}
	override bool opEquals(Object o){
		auto ue=cast(UnaryExp!op)o;
		return ue&&e==ue.e;
	}

	override Annotation getAnnotation(){ return e.getAnnotation(); }
}
class PostfixExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return _brk(e.toString()~TokChars!op);}

	override int freeVarsImpl(scope int delegate(string) dg){
		return e.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override PostfixExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new PostfixExp(ne);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto pe=cast(PostfixExp)rhs;
		if(!pe) return false;
		return e.unify(pe.e,subst,meet);
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
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		foreach(x;a) if(auto r=dg(x)) return r;
		return 0;
	}
	override IndexExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto na=a.dup;
		foreach(ref x;na) x=x.substitute(subst);
		if(ne==e&&na==a) return this;
		auto r=new IndexExp(ne,na,trailingComma);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto idx=cast(IndexExp)rhs;
		if(!idx||a.length!=idx.a.length) return false;
		return e.unify(idx.e,subst,meet)&&all!(i=>a[i].unify(idx.a[i],subst,meet))(iota(a.length));
	}
	override bool opEquals(Object rhs){
		auto idx=cast(IndexExp)rhs;
		return idx&&idx.e==e&&idx.a==a;
	}

	override Annotation getAnnotation(){ return reduce!min(e.getAnnotation(), a.map!(x=>x.getAnnotation())); }

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
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto x=dg(e)) return x;
		if(auto x=dg(l)) return x;
		if(auto x=dg(r)) return x;
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
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto sl=cast(SliceExp)rhs;
		return e.unify(sl.e,subst,meet)&&l.unify(sl.l,subst,meet)&&r.unify(sl.r,subst,meet);
	}

	override Annotation getAnnotation(){ return min(e.getAnnotation(), l.getAnnotation(), r.getAnnotation()); }
}

string tupleToString(Expression e,bool isSquare){
	auto d=isSquare?"[]":"()";
	bool isTuple=!!cast(TupleExp)e;
	auto str=e.toString();
	if(isTuple||e.brackets){
		assert(str[0]=='(' && str[$-1]==')');
		str=str[1..$-1];
	}
	return d[0]~str~d[1];
}

class CallExp: Expression{
	Expression e;
	Expression arg;
	bool isSquare;
	bool isClassical_;
	this(Expression exp, Expression arg, bool isSquare, bool isClassical_){
		e=exp; this.arg=arg; this.isSquare=isSquare;
		this.isClassical_=isClassical_;
	}
	override string toString(){
		return _brk((isClassical_?"!":"")~e.toString()~arg.tupleToString(isSquare));
	}
	override int freeVarsImpl(scope int delegate(string) dg){
		if(auto r=e.freeVarsImpl(dg)) return r;
		return arg.freeVarsImpl(dg);
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e)) return r;
		return dg(arg);
	}
	override CallExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		auto narg=arg.substitute(subst);
		if(ne==e&&narg==arg) return this;
		auto r=new CallExp(ne,narg,isSquare,isClassical_);
		r.loc=loc;
		if(sstate==SemState.completed){
			r.type=type.substitute(subst);
			r.sstate=SemState.completed;
		}
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return e.unify(ce.e,subst,meet)&&arg.unify(ce.arg,subst,meet);
	}
	override bool opEquals(Object rhs){
		auto ce=cast(CallExp)rhs;
		if(!ce) return false;
		return e==ce.e&&arg==ce.arg&&isClassical_==ce.isClassical_;
	}
	override bool isSubtypeImpl(Expression rhs){
		if(this == rhs) return true;
		auto rcall = cast(CallExp)rhs;
		if(rcall && type==typeTy && rhs.type==typeTy && e==rcall.e && isSquare==rcall.isSquare){
			if(!isClassical_ && rcall.isClassical_) return false;
			if(auto id=cast(Identifier)e){
				if(id.meaning){
					if(auto dat=cast(DatDecl)id.meaning){
						auto rid=cast(Identifier)rcall.e;
						assert(rid && rid.meaning == dat);
						bool check(Variance variance,Expression t1,Expression t2){
							final switch(variance){
								case Variance.invariant_: return t1==t2;
								case Variance.covariant: return isSubtype(t1,t2);
								case Variance.contravariant: return isSubtype(t2,t1);
							}
						}
						if(!dat.isTuple){
							assert(dat.params.length==1);
							return check(dat.params[0].variance,arg,rcall.arg);
						}
						assert(dat.isTuple);
						auto tup=cast(TupleTy)arg, rtup=cast(TupleTy)rcall.arg;
						if(tup && rtup && tup.types.length==dat.params.length && tup.types.length==rtup.types.length){ // TODO: assert this?
							return iota(tup.types.length).all!(i=>check(dat.params[i].variance,tup.types[i],rtup.types[i]));
						}
					}
				}
			}
		}
		return super.isSubtypeImpl(rhs);
	}
	override Expression combineTypesImpl(Expression rhs, bool meet){
		if(this == rhs) return this;
		auto rcall = cast(CallExp)rhs;
		if(rcall && type==typeTy && rhs.type==typeTy && e==rcall.e && isSquare==rcall.isSquare){
			if(e==rcall.e&&arg==rcall.arg){
				if(isClassical_ && !rcall.isClassical_){
					return meet?this:rcall;
				}else{
					assert(rcall.isClassical && !isClassical_);
					return !meet?this:rcall;
				}
			}
			if(auto id=cast(Identifier)e){
				if(id.meaning){
					if(auto dat=cast(DatDecl)id.meaning){
						auto rid=cast(Identifier)rcall.e;
						assert(rid && rid.meaning == dat);
						Expression combine(Variance variance,Expression t1,Expression t2){
							final switch(variance){
								case Variance.invariant_: return t1==t2 ? t1 : null;
								case Variance.covariant: return combineTypes(t1,t2,meet);
								case Variance.contravariant: return combineTypes(t1,t2,!meet);
							}
						}
						import semantic_: ConstResult, callSemantic; // TODO: get rid of this?
						if(!dat.isTuple){
							assert(dat.params.length==1);
							assert(arg != rcall.arg); // (checked at start of function)
							auto combined=combine(dat.params[0].variance,arg,rcall.arg);
							if(!combined) return null;
							return callSemantic(new CallExp(e,combined,isSquare,isClassical_),null,ConstResult.no);
						}
						assert(dat.isTuple);
						auto tup=cast(TupleTy)arg, rtup=cast(TupleTy)rcall.arg;
						if(tup && rtup && tup.types.length==dat.params.length && tup.types.length==rtup.types.length){ // TODO: assert this?
							auto combined=iota(tup.types.length).map!(i=>combine(dat.params[i].variance,tup.types[i],rtup.types[i])).array;
							if(combined.any!(x=>x is null)) return null;
							auto rarg=new TupleExp(combined);
							return callSemantic(new CallExp(e,rarg,isSquare,isClassical),null,ConstResult.no);
						}
					}
				}
			}
		}
		return super.combineTypesImpl(rhs,meet);
	}
	override bool isClassical(){
		return isClassical_;
	}
	override bool hasClassicalComponent(){
		return isClassical_;
	}
	override Expression getClassical(){
		assert(type==typeTy);
		if(auto r=super.getClassical()) return r;
		auto r=new CallExp(e,arg,isSquare,true);
		r.type=typeTy;
		r.sstate=sstate;
		return r;
	}

	override Annotation getAnnotation(){
		auto fty=cast(FunTy)e.type;
		if(!fty) return Annotation.none;
		return min(fty.annotation,arg.getAnnotation());
	}

	override Expression eval(){
		return this;
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
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(e1)) return r;
		if(auto r=dg(e2)) return r;
		return 0;
	}
	override Annotation getAnnotation(){
		return min(e1.getAnnotation(), e2.getAnnotation());
	}
}

class BinaryExp(TokenType op): ABinaryExp{
	static if(op==Tok!"→"){
		Annotation annotation;
		this(Expression left, Expression right,Annotation annotation){
			super(left,right); this.annotation=annotation;
		}
	}else{
		this(Expression left, Expression right){super(left,right);}
	}
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
		static if(op==Tok!"→"){
			auto r=new BinaryExp!op(ne1,ne2,annotation);
		}else{
			auto r=new BinaryExp!op(ne1,ne2);
		}
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto be=cast(typeof(this))rhs;
		if(!be) return false;
		return e1.unify(be.e1,subst,meet)&&e2.unify(be.e2,subst,meet);
	}
	override bool opEquals(Object o){
		auto be=cast(BinaryExp!op)o;
		return be && e1==be.e1&&e2==be.e2;
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
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
	override FieldExp substituteImpl(Expression[string] subst){
		auto ne=e.substitute(subst);
		if(ne==e) return this;
		auto r=new FieldExp(ne,f);
		r.loc=loc;
		return r;
	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto fe=cast(FieldExp)rhs;
		if(!fe||f!=fe.f) return false;
		return e.unify(rhs,subst,meet);
	}

	override Annotation getAnnotation(){
		return e.getAnnotation();
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
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(cond)) return r;
		if(auto r=dg(then)) return r;
		if(othw) if(auto r=othw.subexpressionsImpl(dg)) return r;
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
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ite=cast(IteExp)rhs;
		if(!ite) return false;
		return cond.unify(ite.cond,subst,meet)&&then.unify(ite.then,subst,meet)
			&&!othw&&!ite.othw||othw&&ite.othw&&othw.unify(ite.othw,subst,meet);
	}
	override Annotation getAnnotation(){
		return min(cond.getAnnotation(), then.getAnnotation(), othw.getAnnotation());
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
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(num)) return r;
		return dg(bdy);
	}
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
	BlockScope fescope_;
	VarDecl loopVar;

	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0; // TODO: ok?
	}
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
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(cond)) return r;
		return dg(bdy);
	}
}

class CompoundExp: Expression{
	Expression[] s;
	this(Expression[] ss){s=ss;}

	override string toString(){return "{\n"~indent(join(map!(a=>a.toString()~(a.isCompound()?"":";"))(s),"\n"))~"\n}";}
	override bool isCompound(){ return true; }

	// semantic information
	BlockScope blscope_;

	override int freeVarsImpl(scope int delegate(string) dg){
		foreach(x;s) if(auto r=x.freeVarsImpl(dg)) return r;
		return 0;
	}
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;s) if(auto r=dg(x)) return r;
		return 0;
	}
	override Expression substituteImpl(Expression[string] subst){
		auto ns=s.dup;
		foreach(ref x;ns) x=x.substitute(subst);
		if(ns==s) return this;
		auto r=new CompoundExp(ns);
		r.loc=loc;
		return r;

	}
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		return false;
	}
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
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;e) if(auto r=dg(x)) return r;
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
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto te=cast(TupleExp)rhs;
		if(!te||e.length!=te.e.length) return false;
		return all!(i=>e[i].unify(te.e[i],subst,meet))(iota(e.length));
	}
	override bool opEquals(Object o){
		auto tpl=cast(TupleExp)o;
		return tpl&&e==tpl.e;
	}
	override Annotation getAnnotation(){
		return reduce!min(Annotation.lifted, e.map!(x=>x.getAnnotation()));
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
	override int componentsImpl(scope int delegate(Expression) dg){
		return 0; // TODO: ok?
	}
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
	override int componentsImpl(scope int delegate(Expression) dg){
		foreach(x;e) if(auto r=dg(x)) return r;
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
	override bool unifyImpl(Expression rhs,ref Expression[string] subst,bool meet){
		auto ae=cast(ArrayExp)rhs;
		if(!ae||e.length!=ae.e.length) return false;
		return all!(i=>e[i].unify(ae.e[i],subst,meet))(iota(e.length));
	}
	override Annotation getAnnotation(){ return reduce!min(Annotation.lifted,e.map!(x=>x.getAnnotation())); }
}

class ReturnExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override string toString(){ return "return"~(e?" "~e.toString():""); }

	string expected;
	mixin VariableFree; // TODO!
	override int componentsImpl(scope int delegate(Expression) dg){ return dg(e); }
}

class AssertExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override string toString(){ return _brk("assert("~e.toString()~")"); }
	mixin VariableFree; // TODO!
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
}

class ObserveExp: Expression{
	Expression e;
	this(Expression e){
		this.e=e;
	}
	override string toString(){ return _brk("observe("~e.toString()~")"); }

	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		return dg(e);
	}
}

class CObserveExp: Expression{
	Expression var;
	Expression val;
	this(Expression var,Expression val){
		this.var=var; this.val=val;
	}
	override string toString(){ return _brk("cobserve("~var.toString()~","~val.toString()~")"); }

	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(var)) return r;
		return dg(val);
	}
}

class ForgetExp: Expression{
	Expression var;
	Expression val;
	this(Expression var,Expression val){
		this.var=var;
		this.val=val;
	}
	override string toString(){ return _brk("forget("~var.toString()~(val?"="~val.toString():"")~")"); }

	mixin VariableFree; // TODO
	override int componentsImpl(scope int delegate(Expression) dg){
		if(auto r=dg(var)) return r;
		return dg(val);
	}
}
