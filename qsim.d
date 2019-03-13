import std.conv: text, to;
import std.string: split;
import std.algorithm;
import std.array: array;
import std.range: iota;
import std.string: startsWith;
import std.typecons: q=tuple,Q=Tuple;
import std.exception: enforce;

import options;
import distrib,error;
import hashtable,util;
import expression,declaration,type;
import semantic_,scope_;

import std.random, sample;
import std.complex, std.math;

class QSim{
	this(string sourceFile){
		this.sourceFile=sourceFile;
	}
	QState run(FunctionDef def,ErrorHandler err){
		enforce(!def.params.length);
		/+DExpr[string] fields;
		foreach(i,a;def.params) fields[a.getName]=dVar(a.getName);
		DExpr init=dRecord(fields);+/
		auto init=QState.unit();
		auto interpreter=Interpreter!QState(def,def.body_,init,false);
		auto ret=QState.empty();
		interpreter.runFun(ret);
		assert(!!def.ftype);
		bool isTuple = !!cast(TupleTy)def.ftype.cod;
		return ret;
	}
private:
	string sourceFile;
}

enum zeroThreshold=1e-8;
struct QState{
	C[Σ] state;
	Value[string] vars;
	QState dup(){
		return QState(state.dup,vars.dup);
	}
	void copyNonState(ref QState rhs){
		this.tupleof[1..$]=rhs.tupleof[1..$];
	}
	void add(Σ k,C v){
		if(k in state) state[k]+=v;
		else state[k]=v;
		if(abs(state[k]) < zeroThreshold) state.remove(k);
	}
	void opOpAssign(string op:"+")(QState r){
		foreach(k,v;r.vars) vars[k]=v;
		foreach(k,v;r.state) add(k,v);
	}
	Q!(QState,QState) split(Value cond){
		QState then,othw;
		then.copyNonState(this);
		othw.copyNonState(this);
		if(cond.type.isClassical()){
			if(cond.asBoolean) then=this;
			else othw=this;
		}else{
			foreach(k,v;state){
				if(cond.classicalValue(k).asBoolean) then.add(k,v);
				else othw.add(k,v);
			}
		}
		return q(then,othw);
	}
	QState map(alias f)(){

	}

	alias R=double;
	alias C=Complex!double;
	abstract class QuVal{
		abstract Value get(Σ);
		abstract Σ forget(Σ);
	}
	struct Closure{
		FunctionDef fun;
		Value* context;
	}
	struct Value{
		Expression type;
		bool opCast(T:bool)(){ return !!type; }
		void opAssign(Value rhs){
			type=rhs.type;
			bits=rhs.bits;
		}
		union{
			Value[] array_;
			Value[string] record;
			Closure closure;
			QuVal quval;
			R fval;
			ℚ qval;
			ℤ zval;
			bool bval;
			ubyte[max(array_.sizeof,record.sizeof,quval.sizeof,fval.sizeof,qval.sizeof,zval.sizeof,bval.sizeof)] bits;
		}
		Value opUnary(string op)(){
			enforce(0,text("TODO: '",op,"' for type ",this.type));
			assert(0);
		}
		Value opBinary(string op)(Value r){
			static if(["+","-","*","/"].canFind(op)){
				if(type==ℝ(true)&&r.type==ℝ(true)) return makeReal(mixin(`fval `~op~` r.fval`));
				if(type==ℚt(true)&&r.type==ℚt(true)) return makeRational(mixin(`qval `~op~` r.qval`));
				if(type==ℤt(true)&&r.type==ℤt(true)) return makeInteger(mixin(`zval `~op~` r.zval`));
			}
			enforce(0,text("TODO: '",op,"' for types ",this.type," and ",r.type));
			assert(0);
		}
		Value opBinary(string op)(long b){
			return mixin(`this `~op~` makeInteger(ℤ(b))`);
		}
		Value opBinary(string op)(ℤ b){
			return mixin(`this `~op~` makeInteger(b)`);
		}
		Value eqZ(){
			enforce(0,text("TODO: 'eqZ' for type ",this.type));
			assert(0);
		}
		Value neqZ(){
			enforce(0,text("TODO: 'eqZ' for type ",this.type));
			assert(0);
		}
		Value lt(Value r){
			if(type==ℝ(true)&&r.type==ℝ(true)) return makeBool(fval<r.fval);
			if(type==ℚt(true)&&r.type==ℚt(true)) return makeBool(qval<r.qval);
			if(type==ℤt(true)&&r.type==ℤt(true)||type==ℕt(true)&&r.type==ℕt(true)) return makeBool(zval<r.zval);
			if(type==Bool(true)&&r.type==Bool(true))
			enforce(0,text("TODO: 'lt' for types ",this.type," ",r.type));
			assert(0);
		}
		Value le(Value r){
			enforce(0,text("TODO: 'le' for types ",this.type," ",r.type));
			assert(0);
		}
		Value gt(Value r){
			enforce(0,text("TODO: 'lt' for types ",this.type," ",r.type));
			assert(0);
		}
		Value ge(Value r){
			enforce(0,text("TODO: 'lt' for types ",this.type," ",r.type));
			assert(0);
		}
		Value eq(Value r){
			enforce(0,text("TODO: 'eq' for types ",this.type," ",r.type));
			assert(0);
		}
		Value neq(Value r){
			enforce(0,text("TODO: 'neq' for types ",this.type," ",r.type));
			assert(0);
		}
		Value floor(){
			enforce(0,text("TODO: floor for type ",this.type));
			assert(0);
		}
		Value ceil(){
			enforce(0,text("TODO: ceil for type ",this.type));
			assert(0);
		}
		Value classicalValue(Σ state){
			if(type.isClassical) return this;
			return quval.get(state);
		}
		bool asBoolean()in{
			assert(type==Bool(true),text(type));
		}do{
			return bval;
		}
		bool isClassicalInteger(){
			return type.isClassical()&&(isInt(type)||isUint(type)||type==ℤt(true));
		}
		ℤ asInteger()in{
			assert(isClassicalInteger());
		}do{
			if(type==ℤt(true)) return zval;
			enforce(0,text("TODO: asInteger for type ",type));
			assert(0);
		}
		string toString(){
			if(type.isClassical()){
				if(type==ℝ(true)) return text(fval,":",type);
				if(type==ℚt(true)) return text(qval,":",type);
				if(type==ℤt(true)) return text(zval,":",type);
				if(type==Bool(true)) return text(bval,":",type);
			}
			return text("_:",type);
		}
	}
	static assert(Value.sizeof==Type.sizeof+Value.bits.sizeof);
	static Value nullValue(){
		return Value.init;
	}
	static Value typeValue(){
		Value r;
		r.type=typeTy;
		return r;
	}
	static Value π(){
		Value r;
		r.type=ℝ(true);
		r.fval=PI;
		return r;
	}
	struct Σ{
		ubyte[] data;
	}
	static QState empty(){ return QState.init; }
	static QState unit(){
		QState qstate;
		qstate.state[Σ.init]=C(1.0);
		return qstate;
	}
	QState pushFrame(){
		Value[string] nvars;
		foreach(name,val;vars) nvars[name]=makeRecord(["`frame":val]);
		return QState(state,nvars);
	}
	QState popFrame(string tmpVar){
		enforce(0,"TODO: function calls");
		assert(0);
	}
	Value call(FunctionDef fun,Value thisExp,Value arg,Scope sc){
		auto ncur=pushFrame();
		enforce(0,"TODO: function calls");
		assert(0);
	}
	QState assertTrue(Value val)in{
		assert(val.type==Bool(true));
	}do{
		if(!val.asBoolean) enforce(0,"TODO: assertion failures");
		return this;
	}
	private QState callImpl(Value fun,Value arg){
		enforce(0,"TODO: function calls");
		assert(0);
	}
	Value call(Value fun,Value arg){
		auto r=callImpl(fun,arg);
		enforce(0,"TODO: function calls");
		assert(0);
	}

	Value readLocal(string s){
		return vars[s];
	}
	static Value makeRecord(Value[string] record){
		Value r;
		r.type=contextTy(false);
		r.record=record;
		return r;
	}
	static Value readField(Value r,string s){
		assert(r.type==contextTy(false));
		return r.record[s];
	}
	static Value makeTuple(Expression type,Value[] tuple)in{
		assert(!!cast(TupleTy)type||cast(ArrayTy)type||cast(VectorTy)type);
	}do{
		Value r;
		r.type=type;
		r.array_=tuple;
		return r;
	}
	alias makeArray=makeTuple;
	alias makeVector=makeTuple;
	Value readIndex(Value r,Value i){
		enforce(0,"TODO: readIndex");
		assert(0);
	}
	Value makeSlice(Value v,Value l,Value r){
		enforce(0,"TODO: makeSlice");
		assert(0);
	}
	static Value makeReal(string value){
		Value r;
		r.type=ℝ(true);
		r.fval=to!R(value);
		return r;
	}
	static Value makeReal(R value){
		Value r;
		r.type=ℝ(true);
		r.fval=value;
		return r;
	}
	static Value makeRational(ℚ value){
		Value r;
		r.type=ℚt(true);
		r.qval=value;
		return r;
	}
	static Value makeInteger(ℤ value){
		Value r;
		r.type=ℤt(true);
		r.zval=value;
		return r;
	}
	static Value makeBool(bool value){
		Value r;
		r.type=Bool(true);
		r.bval=value;
		return r;
	}
	Value makeFunction(FunctionDef fd,Value* context){
		Value r;
		r.type=fd.ftype;
		r.closure=Closure(fd,context);
		return r;
	}
	Value makeFunction(FunctionDef fd,Scope from){
		Value* context=null;
		if(fd.isNested) context=[buildContextFor(this,fd,from)].ptr;
		return makeFunction(fd,context);
	}
	Value readFunction(Identifier id){
		auto fd=cast(FunctionDef)id.meaning;
		assert(!!fd);
		return makeFunction(fd,id.scope_);
	}
	static Value ite(Value cond,Value then,Value othw)in{
		assert(cast(BoolTy)cond.type);
	}do{
		if(cond.type.isClassical) return cond.asBoolean?then:othw;
		static class IteQuVal: QuVal{
			Value cond,then,othw;
			this(Value cond,Value then,Value othw){
				this.cond=cond, this.then=then, this.othw=othw;
			}
			override Value get(Σ s){
				return cond.classicalValue(s)?then.classicalValue(s):othw.classicalValue(s);
			}
			override Σ forget(Σ s){
				enforce(0,"TODO?");
				assert(0);
			}
		}
		enforce(then.type==othw.type,"TODO: ite branches with different types");
		Value r;
		r.type=then.type;
		r.quval=new IteQuVal(cond,then,othw);
		return r;
	}
	void assignTo(string lhs,Value rhs){
		vars[lhs]=rhs;
	}
	void assignTo(Value lhs,Value rhs){
		enforce(0,"TODO: assignTo");
		assert(0);
	}
}


// TODO: move this to semantic_, as a rewrite
QState.Value readVariable(QState)(QState qstate,VarDecl var,Scope from){
	QState.Value r=getContextFor(qstate,var,from);
	if(r) return qstate.readField(r,var.getName);
	return qstate.readLocal(var.getName);
}
QState.Value getContextFor(QState)(QState qstate,Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{
	QState.Value r=QState.nullValue;
	auto meaningScope=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		meaningScope=fd.realScope;
	assert(sc&&sc.isNestedIn(meaningScope));
	for(auto csc=sc;csc !is meaningScope;){
		void add(string name){
			if(!r) r=qstate.readLocal(name);
			else r=qstate.readField(r,name);
			assert(!!cast(NestedScope)csc);
		}
		assert(cast(NestedScope)csc);
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto fsc=cast(FunctionScope)csc){
			auto fd=fsc.getFunction();
			if(fd.isConstructor){
				if(meaning is fd.thisVar) break;
				add(fd.thisVar.getName);
			}else add(fd.contextName);
		}else if(cast(AggregateScope)csc) add(csc.getDatDecl().contextName);
		csc=(cast(NestedScope)csc).parent;
	}
	return r;
}
QState.Value buildContextFor(QState)(QState qstate,Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{ // template, forward references 'doIt'
	if(auto ctx=getContextFor(qstate,meaning,sc)) return ctx;
	QState.Value[string] record;
	auto msc=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		msc=fd.realScope;
	for(auto csc=msc;;csc=(cast(NestedScope)csc).parent){
		if(!cast(NestedScope)csc) break;
		foreach(vd;&csc.all!VarDecl)
			if(auto var=readVariable(qstate,vd,sc))
				record[vd.getName]=var;
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto dsc=cast(DataScope)csc){
			auto name=dsc.decl.contextName;
			record[name]=qstate.readLocal(name);
			break;
		}
		if(auto fsc=cast(FunctionScope)csc){
			auto cname=fsc.getFunction().contextName;
			record[cname]=qstate.readLocal(cname);
			break;
		}
	}
	return QState.makeRecord(record);
}
QState.Value lookupMeaning(QState)(QState qstate,Identifier id)in{assert(id && id.scope_,text(id," ",id.loc));}body{
	if(!id.meaning||!id.scope_||!id.meaning.scope_)
		return qstate.readLocal(id.name);
	if(auto vd=cast(VarDecl)id.meaning){
		auto r=getContextFor(qstate,id.meaning,id.scope_);
		return r?qstate.readField(r,id.name):qstate.readLocal(id.name);
	}
	if(cast(FunctionDef)id.meaning) return qstate.readFunction(id);
	return QState.nullValue;
}

import lexer: Tok;
alias ODefExp=BinaryExp!(Tok!":=");
struct Interpreter(QState){
	FunctionDef functionDef;
	CompoundExp statements;
	QState qstate;
	bool hasFrame=false;
	this(FunctionDef functionDef,CompoundExp statements,QState qstate,bool hasFrame){
		this.functionDef=functionDef;
		this.statements=statements;
		this.qstate=qstate;
		this.hasFrame=hasFrame;
	}
	QState.Value runExp(Expression e){
		// TODO: get rid of code duplication
		QState.Value doIt(Expression e){
			if(e.type == typeTy) return QState.typeValue; // TODO: get rid of this
			if(auto id=cast(Identifier)e){
				if(!id.meaning&&id.name=="π") return QState.π;
				if(auto r=lookupMeaning(qstate,id)) return r;
				assert(0,"unsupported");
			}
			if(auto fe=cast(FieldExp)e){
				if(isBuiltIn(fe)){
					if(auto at=cast(ArrayTy)fe.e.type){
						assert(fe.f.name=="length");
					}
				}
				return qstate.readField(doIt(fe.e),fe.f.name);
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
			if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
			if(cast(DivExp)e||cast(IDivExp)e){
				auto de=cast(ABinaryExp)e;
				auto e1=doIt(de.e1);
				auto e2=doIt(de.e2);
				enforce(0,text("TODO: ",e));
				assert(0);
			}
			if(auto me=cast(ModExp)e) return doIt(me.e1)%doIt(me.e2);
			if(auto pe=cast(PowExp)e) return doIt(pe.e1)^^doIt(pe.e2);
			if(auto ce=cast(CatExp)e) return doIt(ce.e1)~doIt(ce.e2);
			if(auto ce=cast(BitOrExp)e) return doIt(ce.e1)|doIt(ce.e2);
			if(auto ce=cast(BitXorExp)e) return doIt(ce.e1)^doIt(ce.e2);
			if(auto ce=cast(BitAndExp)e) return doIt(ce.e1)&doIt(ce.e2);
			if(auto ume=cast(UMinusExp)e) return -doIt(ume.e);
			if(auto ume=cast(UNotExp)e) return doIt(ume.e).eqZ;
			if(auto ume=cast(UBitNotExp)e) return ~doIt(ume.e);
			if(auto le=cast(LambdaExp)e) return qstate.makeFunction(le.fd,le.fd.scope_);
			if(auto ce=cast(CallExp)e){
				auto id=cast(Identifier)ce.e;
				auto fe=cast(FieldExp)ce.e;
				QState.Value thisExp=QState.nullValue;
				if(fe){
					id=fe.f;
					thisExp=doIt(fe.e);
				}
				if(id){
					if(auto fun=cast(FunctionDef)id.meaning){
						auto arg=doIt(ce.arg); // TODO: allow temporaries within arguments
						return qstate.call(fun,thisExp,arg,id.scope_);
					}
					if(!fe && isBuiltIn(id)){
						switch(id.name){
							default:
								enforce(0,text("TODO: ",id.name));
								assert(0);
						}
					}
				}
				auto fun=doIt(ce.e), arg=doIt(ce.arg);
				return qstate.call(fun,arg);
			}
			if(auto idx=cast(IndexExp)e) return qstate.readIndex(doIt(idx.e),doIt(idx.a[0])); // TODO: bounds checking
			if(auto sl=cast(SliceExp)e) return qstate.makeSlice(doIt(sl.e),doIt(sl.l),doIt(sl.r)); // TODO: bounds checking
			if(auto le=cast(LiteralExp)e){
				if(util.among(le.lit.type,Tok!"0",Tok!".0")){
					if(le.type==ℚt(true)){
						auto n=le.lit.str.split(".");
						if(n.length==1) n~="";
						return QState.makeRational(ℚ((n[0]~n[1]).ℤ,ℤ(10)^^n[1].length));
					}else if(util.among(le.type,ℤt(true),ℕt(true))){
						return QState.makeInteger(ℤ(le.lit.str));
					}else if(le.type==ℝ(true)){
						return QState.makeReal(le.lit.str);
					}else if(le.type==Bool(true)){
						return QState.makeBool(le.lit.str=="1");
					}
				}
			}
			if(auto cmp=cast(CompoundExp)e){
				if(cmp.s.length==1)
					return doIt(cmp.s[0]);
			}else if(auto ite=cast(IteExp)e){
				auto cond=runExp(ite.cond);
				auto thenElse=qstate.split(cond);
				qstate=thenElse[0];
				auto othw=thenElse[1];
				auto thenIntp=Interpreter!QState(functionDef,ite.then,qstate,hasFrame);
				assert(!!ite.othw);
				auto othwIntp=Interpreter(functionDef,ite.othw,othw,hasFrame);
				qstate=thenIntp.qstate;
				qstate+=othwIntp.qstate;
				return QState.ite(cond,thenIntp.runExp(ite.then.s[0]),othwIntp.runExp(ite.othw));
			}else if(auto tpl=cast(TupleExp)e){
				auto values=tpl.e.map!doIt.array;
				return QState.makeTuple(e.type,values);
			}else if(auto arr=cast(ArrayExp)e){
				auto values=arr.e.map!doIt.array;
				return QState.makeArray(e.type,values);
			}else if(auto ae=cast(AssertExp)e){
				if(auto c=runExp(ae.e)){
					qstate=qstate.assertTrue(c);
					return qstate.makeTuple(unit,[]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)e){
				return doIt(tae.e);
			}else if(cast(Type)e)
				return qstate.makeTuple(unit,[]); // 'erase' types
			else{
				enum common=q{
					auto e1=doIt(b.e1),e2=doIt(b.e2);
				};
				if(auto b=cast(AndExp)e){
					mixin(common);
					return e1&e2;
				}else if(auto b=cast(OrExp)e){
					mixin(common);
					return e1|e2;
				}else if(auto b=cast(LtExp)e){
					mixin(common);
					return e1.lt(e2);
				}else if(auto b=cast(LeExp)e){
					mixin(common);
					return e1.le(e2);
				}else if(auto b=cast(GtExp)e){
					mixin(common);
					return e1.gt(e2);
				}else if(auto b=cast(GeExp)e){
					mixin(common);
					return e1.ge(e2);
				}else if(auto b=cast(EqExp)e){
					mixin(common);
					return e1.eq(e2);
				}else if(auto b=cast(NeqExp)e){
					mixin(common);
					return e1.neq(e2);
				}
			}
			enforce(0,text("TODO: ",e," ",e.type));
			assert(0);
		}
		return doIt(e);
	}
	void assignTo(Expression lhs,QState.Value rhs){
		if(auto id=cast(Identifier)lhs){
			qstate.assignTo(id.name,rhs);
		}else enforce(0,"TODO: unpacking assignments");
	}
	void runStm(Expression e,ref QState retState){
		if(!qstate.state.length) return;
		if(opt.trace) writeln("statement: ",e);
		if(auto nde=cast(DefExp)e){
			auto de=cast(ODefExp)nde.initializer;
			assert(!!de);
			auto lhs=de.e1, rhs=runExp(de.e2);
			assignTo(lhs,rhs);
		}else if(auto ae=cast(AssignExp)e){
			auto lhs=ae.e1,rhs=runExp(ae.e2);
			assignTo(lhs,rhs);
		}else if(isOpAssignExp(e)){
			QState.Value perform(QState.Value a,QState.Value b){
				if(cast(OrAssignExp)e) return a|b;
				if(cast(AndAssignExp)e) return a&b;
				if(cast(AddAssignExp)e) return a+b;
				if(cast(SubAssignExp)e) return a-b;
				if(cast(MulAssignExp)e) return a*b;
				if(cast(DivAssignExp)e||cast(IDivAssignExp)e){
					qstate=qstate.assertTrue(b.neqZ);
					return cast(IDivAssignExp)e?(a/b).floor():a/b;
				}
				if(cast(ModAssignExp)e) return a%b;
				if(cast(PowAssignExp)e){
					// TODO: enforce constraints on domain
					return a^^b;
				}
				if(cast(CatAssignExp)e) return a~b;
				if(cast(BitOrAssignExp)e) return a|b;
				if(cast(BitXorAssignExp)e) return a^b;
				if(cast(BitAndAssignExp)e) return a&b;
				assert(0);
			}
			auto be=cast(ABinaryExp)e;
			assert(!!be);
			auto lhs=runExp(be.e1),rhs=runExp(be.e2);
			assignTo(be.e1,perform(lhs,rhs));
		}else if(auto call=cast(CallExp)e){
			runExp(call);
		}else if(auto ite=cast(IteExp)e){
			auto cond=runExp(ite.cond);
			auto thenOthw=qstate.split(cond);
			qstate=thenOthw[0];
			auto othw=thenOthw[1];
			auto thenIntp=Interpreter(functionDef,ite.then,qstate,hasFrame);
			thenIntp.run(retState);
			qstate=thenIntp.qstate;
			if(ite.othw){
				auto othwIntp=Interpreter(functionDef,ite.othw,othw,hasFrame);
				othwIntp.run(retState);
				othw=othwIntp.qstate;
			}
			qstate+=othw;
		}else if(auto re=cast(RepeatExp)e){
			auto rep=runExp(re.num);
			if(rep.isClassicalInteger()){
				auto z=rep.asInteger();
				auto intp=Interpreter(functionDef,re.bdy,qstate,hasFrame);
				foreach(x;0.ℤ..z){
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retState);
					// TODO: marginalize locals
				}
				qstate=intp.qstate;
			}else{
				auto bound=rep.floor();
				auto intp=Interpreter(functionDef,re.bdy,QState.empty(),hasFrame);
				intp.qstate.state = qstate.state;
				qstate.state=typeof(qstate.state).init;
				for(ℤ x=0;;++x){
					auto thenOthw=intp.qstate.split(bound.le(QState.makeInteger(x)));
					qstate += thenOthw[0];
					intp.qstate = thenOthw[1];
					//intp.qstate.error = zero;
					if(!intp.qstate.state.length) break;
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retState);
				}
			}
		}else if(auto fe=cast(ForExp)e){
			auto l=runExp(fe.left), r=runExp(fe.right);
			if(l.isClassicalInteger()&&r.isClassicalInteger()){
				auto lz=l.asInteger(),rz=r.asInteger();
				auto intp=Interpreter(functionDef,fe.bdy,qstate,hasFrame);
				for(ℤ j=lz+cast(int)fe.leftExclusive;j+cast(int)fe.rightExclusive<=rz;j++){
					if(opt.trace) writeln("loop-index: ",j);
					intp.qstate.assignTo(fe.var.name,qstate.makeInteger(j));
					intp.run(retState);
					// TODO: marginalize locals
				}
				qstate=intp.qstate;
			}else{
				auto loopIndex=fe.leftExclusive?l.floor()+1:l.ceil();
				auto bound=fe.rightExclusive?r.ceil()-1:r.floor();
				auto intp=Interpreter(functionDef,fe.bdy,QState.empty(),hasFrame);
				intp.qstate.state = qstate.state;
				qstate.state=typeof(qstate.state).init;
				for(int x=0;;++x){
					auto ncond=bound.lt(loopIndex+x);
					auto othwThen=intp.qstate.split(ncond);
					qstate += othwThen[0];
					intp.qstate = othwThen[1];
					//intp.qstate.error = zero;
					if(!intp.qstate.state.length) break;
					intp.qstate.assignTo(fe.var.name,loopIndex+x);
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retState);
				}
			}
		}else if(auto we=cast(WhileExp)e){
			auto intp=Interpreter(functionDef,we.bdy,qstate,hasFrame);
			qstate.state=typeof(qstate.state).init;
			while(intp.qstate.state.length){
				auto cond = intp.runExp(we.cond);
				auto thenOthw=intp.qstate.split(cond);
				qstate += thenOthw[1];
				intp.qstate = thenOthw[0];
				//intp.qstate.error = zero;
				intp.run(retState);
				// TODO: marginalize locals
			}
		}else if(auto re=cast(ReturnExp)e){
			auto value = runExp(re.e);
			if(functionDef.context&&functionDef.contextName.startsWith("this"))
				value = QState.makeTuple(tupleTy([re.e.type,contextTy(true)]),[value,qstate.readLocal(functionDef.contextName)]);
			qstate.assignTo("`value",value);
			if(hasFrame){
				assert("`frame" in qstate.vars);
				//assert(qstate.vars.length==2); // `value and `frame
			}//else assert(qstate.vars.length==1); // only `value
			retState += qstate; // TODO: compute distributions?
			qstate=QState.empty();
		}else if(auto ae=cast(AssertExp)e){
			auto cond=runExp(ae.e);
			qstate=qstate.assertTrue(cond);
		}else if(auto oe=cast(ObserveExp)e){
			enforce(0,"TODO: observe?");
			assert(0);
		}else if(auto ce=cast(CommaExp)e){
			runStm(ce.e1,retState);
			runStm(ce.e2,retState);
		}else if(cast(Declaration)e){
			// do nothing
		}else{
			enforce(0,text("TODO: ",e));
		}
	}
	void run(ref QState retState){
		foreach(s;statements.s){
			runStm(s,retState);
			// writeln("cur: ",cur);
		}
	}
	void runFun(ref QState retState){
		run(retState);
		retState+=qstate;
		qstate=QState.empty();
	}
}
