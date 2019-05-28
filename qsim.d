import std.conv: text, to;
import std.string: split;
import std.algorithm;
import std.array: array;
import std.range: iota, zip, repeat;
import std.string: startsWith,join;
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

string formatQValue(QState qs,QState.Value value){ // (only makes sense if value contains the full quantum state)
	if(value.type.isClassical()) return value.toString();
	string r;
	foreach(k,v;qs.state){
		if(r.length) r~="+";
		r~=text("(",v,")·|",value.classicalValue(k),"⟩");
	}
	return r;
}

enum zeroThreshold=1e-8;
bool isToplevelClassical(Expression ty){
	return ty.isClassical()||cast(TupleTy)ty||cast(ArrayTy)ty||cast(VectorTy)ty||cast(ContextTy)ty||cast(ProductTy)ty;
}

void hadamardUnitary(alias add,QState)(QState.Value c){
	alias C=QState.C;
	enforce(c.tag==QState.Value.Tag.bval);
	enum norm=C(sqrt(1.0/2.0));
	if(!c.bval){ add(c,norm); add(c.eqZ,norm); }
	else{    add(c.eqZ,norm);    add(c,-norm); }
}
struct QState{
	MapX!(Σ,C) state;
	Record vars;
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
	QState map(alias f,T...)(T args){
		QState new_;
		new_.copyNonState(this);
		foreach(k,v;state){
			auto nk=f(k,args);
			enforce(nk !in new_.state);
			new_.state[nk]=v;
		}
		return new_;
	}
	alias R=double;
	alias C=Complex!double;
	static abstract class QVal{
		override string toString(){ return "_"; }
		abstract Value get(Σ);
		void assign(ref QState state,Value rhs){
			enforce(0,text("can't assign to quval ",this));
		}
		void removeVar(ref Σ σ){}
		final Value applyUnitary(alias unitary)(ref QState qs,Expression type){
			QState nstate;
			nstate.copyNonState(qs);
			auto ref_=Σ.curRef++; // TODO: reuse reference of x if possible
			foreach(k,v;qs.state){
				void add(Value nk,C nv){
					auto σ=k.dup;
					σ.assign(ref_,nk);
					removeVar(σ);
					nstate.add(σ,nv*v);
				}
				unitary!add(get(k));
			}
			Value r;
			r.type=type;
			r.quval=new QVar(ref_);
			qs=nstate;
			return r;
		}
	}
	static class QConst: QVal{
		Value constant;
		override string toString(){ return constant.toStringImpl(); }
		this(Value constant){ this.constant=constant; }
		override Value get(Σ){ return constant; }
	}
	static class QVar: QVal{
		Σ.Ref ref_;
		override string toString(){ return text("ref(",ref_,")"); }
		this(Σ.Ref ref_){ this.ref_=ref_; }
		override Value get(Σ s){
			return s.qvars[ref_];
		}
		override void removeVar(ref Σ s){
			s.qvars.remove(ref_);
		}
		override void assign(ref QState state,Value rhs){
			state.assignTo(ref_,rhs);
		}
	}
	static class ConvertQVal: QVal{
		QVal value;
		Expression ntype;
		this(QVal value,Expression ntype){ this.value=value; }
		override Value get(Σ σ){ return value.get(σ).convertTo(ntype); }
		override void removeVar(ref Σ σ){
			// TODO: some conversions need variables to be removed
		}
	}
	alias Record=HashMap!(string,Value,(a,b)=>a==b,(a)=>typeid(a).getHash(&a));
	struct Closure{
		FunctionDef fun;
		Value* context;
		hash_t toHash(){ return context?tuplex(fun,*context).toHash():fun.toHash(); }
		bool opEquals(Closure rhs){ return fun==rhs.fun && (context is rhs.context || context&&rhs.context&&*context==*rhs.context); }
	}
	struct Value{
		Expression type;
		enum Tag{
			array_,
			record,
			closure,
			quval,
			fval,
			qval,
			zval,
			bval,
		}
		static Tag getTag(Expression type){
			assert(!!type);
			if(cast(ArrayTy)type||cast(VectorTy)type||cast(TupleTy)type) return Tag.array_;
			if(cast(ContextTy)type) return Tag.record;
			if(cast(ProductTy)type) return Tag.closure;
			if(!type.isClassical()){
				assert(!type.isToplevelClassical());
				return Tag.quval;
			}
			if(type==ℝ(true)) return Tag.fval;
			if(type==ℚt(true)) return Tag.qval;
			if(type==ℤt(true)) return Tag.zval;
			if(type==Bool(true)) return Tag.bval;
			if(type==typeTy) return Tag.bval; // TODO: ok?
			enforce(0,text("TODO: representation for type ",type));
			assert(0);
		}
		@property Tag tag(){
			return getTag(type);
		}
		bool opCast(T:bool)(){ return !!type; }
		void opAssign(Value rhs){
			// TODO: make safe
			type=rhs.type;
			Lswitch:final switch(tag){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag)
				case t: mixin(`this.`~text(t)~`=rhs.`~text(t)~`;`); break Lswitch;
			}
		}
		bool opEquals(Value rhs){
			if(type!=rhs.type) return false;
			if(!type) return true;
			assert(tag==rhs.tag);
			final switch(tag){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag){
					case t: return mixin(`this.`~text(t)~`==rhs.`~text(t));
				}
			}
		}
		hash_t toHash(){
			if(!type) return 0;
			final switch(tag){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag)
				case t: return tuplex(type,mixin(text(t))).toHash();
			}
		}
		this(this){
			if(!type) return;
			auto tt=tag;
			Lswitch:final switch(tt){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag)
				case t: static if(__traits(hasMember,mixin(text(t)),"__postblit")) mixin(`this.`~text(t)~`.__postblit();`);
			}
			if(tt==Tag.array_) array_=array_.dup;
			if(tt==Tag.record) record=record.dup; // TODO: necessary?
		}
		void assign(ref QState state,Value rhs){
			assert(type==rhs.type);
			assert(!type.isToplevelClassical);
			assert(tag==Tag.quval);
			quval.assign(state,rhs);
		}
		Value applyUnitary(alias unitary)(ref QState qs,Expression type){
			enforce(tag==Tag.quval);
			return quval.applyUnitary!unitary(qs,type);
		}
		union{
			Value[] array_;
			Record record;
			Closure closure;
			QVal quval;
			R fval;
			ℚ qval;
			ℤ zval;
			bool bval;
			ubyte[max(array_.sizeof,record.sizeof,quval.sizeof,fval.sizeof,qval.sizeof,zval.sizeof,bval.sizeof)] bits;
		}

		Value convertTo(Expression ntype){
			if(type==ntype) return this;
			auto otag=tag, ntag=getTag(ntype);
			if(otag==Tag.quval){
				enforce(ntag==Tag.quval);
				Value r;
				r.type=ntype;
				r.quval=new ConvertQVal(quval,ntype);
				return r;
			}else if(ntag==Tag.quval){
				auto constant=convertTo(ntype.getClassical());
				Value r;
				r.type=ntype;
				r.quval=new QConst(convertTo(ntype.getClassical()));
				return r;
			}
			final switch(otag){
				case Tag.array_:
					if(ntag==Tag.array_){
						Value r;
						r.type=ntype;
						break; // TODO
					}
					break;
				case Tag.record:
					break;
				case Tag.closure:
					assert(ntag==Tag.closure);
					Value r=this;
					r.type=ntype;
					return r;
					break;
				case Tag.quval:
					break; // TODO
				case Tag.fval:
					break;
				case Tag.qval:
					if(ntag==Tag.fval){
						Value r;
						r.type=ntype;
						r.fval=to!R(text(qval.num))/to!R(text(qval.den)); // TODO: better?
						return r;
					}
					break;
				case Tag.zval:
					if(ntag==Tag.qval){
						Value r;
						r.type=ntype;
						r.qval=ℚ(zval);
						return r;
					}
					if(ntag==Tag.fval){
						Value r;
						r.type=ntype;
						r.fval=to!R(text(zval)); // TODO: better?
						return r;
					}
					break;
				case Tag.bval:
					if(ntag==Tag.zval){
						Value r;
						r.type=ntype;
						r.zval=ℤ(cast(int)bval);
						return r;
					}
					if(ntag==Tag.qval){
						Value r;
						r.type=ntype;
						r.qval=ℚ(bval);
						return r;
					}
					if(ntag==Tag.fval){
						Value r;
						r.type=ntype;
						r.fval=to!R(bval);
						return r;
					}
			}
			if(ntag==Tag.bval) return neqZ;
			enforce(0,text("TODO: convert ",type," to ",ntype));
			assert(0);
		}
		
		Value inFrame(){
			return this;
			/+Value r;
			r.type=type;
			final switch(tag){
				case Tag.array_:
					r.array_=array_.map!(v=>v.inFrame).array;
					break;
				case Tag.record:
					Value[string] nr;
					foreach(k,v;record)
						nr[k]=v.inFrame();
					r.record=nr;
					break;
				case Tag.closure:
					r.closure=Closure(closure.fun,[closure.context.inFrame()].ptr);
					break;
				case Tag.quval:
					r.quval=quval.inFrame();
					break;
				case Tag.fval: r.fval=fval; break;
				case Tag.qval: r.qval=qval; break;
				case Tag.zval: r.zval=zval; break;
				case Tag.bval: r.bval=bval; break;
			}
			return r;+/
		}
		Value opIndex(size_t i)in{
			assert(tag==Tag.array_);
		}do{
			return array_[i];
		}
		Value opIndex(Value i){
			if(i.isClassicalInteger()) return this[to!size_t(i.asInteger())];
			enforce(0,text("TODO: indexing for types ",this.type," and ",i.type));
			assert(0);
		}
		Value opSlice(size_t l,size_t r)in{
			assert(tag==Tag.array_);
		}do{
			Value res;
			res.type=type;
			res.array_=array_[l..r];
			return res;
		}
		Value opSlice(Value l,Value r){
			if(l.isClassicalInteger()&&r.isClassicalInteger()) return this[to!size_t(l.asInteger())..to!size_t(r.asInteger())];
			enforce(0,text("TODO: slicing for types ",this.type,", ",l.type," and ",r.type));
			assert(0);
		}
		Value opUnary(string op)(){
			static if(op=="-"){
				if(type==ℝ(true)) return makeReal(mixin(op~` fval`));
				if(type==ℚt(true)) return makeRational(mixin(op~` qval`));
				if(type==ℤt(true)) return makeInteger(mixin(op~` zval`));
			}
			enforce(0,text("TODO: '",op,"' for type ",this.type));
			assert(0);
		}
		Value opBinary(string op)(Value r){
			static if(["+","-","*","/"].canFind(op)){
				Expression ntype=null;
				if(type!=r.type){
					ntype=joinTypes(type,r.type);
					if(ntype){
						if(op=="/"&&isSubtype(ntype,ℚt(false)))
							ntype=ℚt(ntype.isClassical());
						return mixin(`this.convertTo(ntype) `~op~` r.convertTo(ntype)`);
					}
				}else{
					if(type==ℝ(true)) return makeReal(mixin(`fval `~op~` r.fval`));
					if(type==ℚt(true)) return makeRational(mixin(`qval `~op~` r.qval`));
					if(type==ℤt(true)) return makeInteger(mixin(`zval `~op~` r.zval`));
				}
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
		bool eqZImpl(){
			if(type==ℝ(true)) return fval==0;
			if(type==ℚt(true)) return qval==0;
			if(type==ℤt(true)) return zval==0;
			if(type==Bool(true)) return bval==0;
			enforce(0,text("TODO: 'eqZ'/'neqZ' for type ",this.type));
			assert(0);
		}
		Value eqZ(){
			return makeBool(eqZImpl());
		}
		Value neqZ(){
			return makeBool(!eqZImpl());
		}
		Value compare(string op)(Value r){
			if(type!=r.type){
				auto ntype=joinTypes(type,r.type);
				if(ntype) return this.convertTo(ntype).compare!op(r.convertTo(ntype));
			}else{
				if(type==ℝ(true)) return makeBool(mixin(`fval `~op~` r.fval`));
				if(type==ℚt(true)) return makeBool(mixin(`qval `~op~` r.qval`));
				if(type==ℤt(true)||type==ℕt(true)) return makeBool(mixin(`zval `~op~` r.zval`));
				if(type==Bool(true)&&r.type==Bool(true)) return makeBool(mixin(`bval `~op~` r.bval`));
			}
			enforce(0,text("TODO: '",op,"' for types ",this.type," ",r.type));
			assert(0);
		}
		Value lt(Value r){ return compare!"<"(r); }
		Value le(Value r){ return compare!"<="(r); }
		Value gt(Value r){ return compare!">"(r); }
		Value ge(Value r){ return compare!">="(r); }
		Value eq(Value r){ return compare!"=="(r); }
		Value neq(Value r){ return compare!"!="(r); }
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
			return type.isClassical()&&(isInt(type)||isUint(type)||type==ℤt(true)||type==Bool(true));
		}
		ℤ asInteger()in{
			assert(isClassicalInteger());
		}do{
			if(type==ℤt(true)) return zval;
			if(type==Bool(true)) return ℤ(cast(int)bval);
			enforce(0,text("TODO: asInteger for type ",type));
			assert(0);
		}
		string toStringImpl(){
			if(!type) return "Value.init";
			if(type==typeTy) return "_";
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval])
				case t: return text(mixin(text(t)));
				case Tag.bval: return bval?"1":"0";
				case Tag.closure: return text("⟨",closure.fun,",",*closure.context,"⟩");
				case Tag.array_: return text("[",array_.map!text.join(","),"]");
				case Tag.record:
					auto r="{";
					foreach(k,v;record) r~=text(".",k," ↦ ",v,",");
					return r.length!=1?r[0..$-1]~"}":"{}";
				case Tag.quval: return quval.toString();
			}
		}
		string toString(){
			return text(toStringImpl(),":",type);
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
		alias Ref=size_t;
		HashMap!(Ref,Value,(a,b)=>a==b,a=>a) qvars;
		Σ dup(){ return Σ(qvars.dup); }
		static Ref curRef=0;
		Ref assign(Ref ref_,Value v){
			qvars[ref_]=v.classicalValue(this);
			return ref_;
		}
		void forget(Ref ref_){
			qvars.remove(ref_);
		}
		hash_t toHash(){ return qvars.toHash(); }
	}
	static QState empty(){ return QState.init; }
	static QState unit(){
		QState qstate;
		qstate.state[Σ.init]=C(1.0);
		return qstate;
	}
	QState pushFrame(){
		Record nvars,nnvars;
		foreach(k,v;vars) nvars[k]=v.inFrame();
		nnvars["`frame"]=makeRecord(nvars);
		return QState(state,nnvars);
	}
	QState popFrame(){
		auto frame=vars["`frame"];
		enforce(frame.tag==Value.Tag.record);
		Record nvars=frame.record.dup;
		return QState(state,nvars);
	}
	static Value inFrame(Value v){
		return v.inFrame();
	}
	Value call(FunctionDef fun,Value thisExp,Value arg,Scope sc,Value* context=null){
		enforce(fun.body_,text("error: need function body to simulate function ",fun));
		auto ncur=pushFrame();
		enforce(!thisExp,"TODO: method calls");
		enforce(!fun.isConstructor,"TODO: constructors");
		if(fun.isNested){
			assert(context||sc);
			ncur.passParameter(fun.contextName,context?*context:inFrame(buildContextFor(this,fun,sc)));
		}
		if(fun.isTuple){
			auto args=iota(fun.params.length).map!(i=>inFrame(arg[i]));
			foreach(i,prm;fun.params)
				ncur.passParameter(prm.getName,inFrame(arg[i])); // TODO: faster: parallel assignment to parameters
		}else{
			assert(fun.params.length==1);
			ncur.passParameter(fun.params[0].getName,inFrame(arg));
		}
		auto intp=Interpreter!QState(fun,fun.body_,ncur,true);
		auto nnstate=QState.empty();
		intp.runFun(nnstate);
		this=nnstate.popFrame();
		return nnstate.vars["`value"];
	}
	QState assertTrue(Value val)in{
		assert(val.type==Bool(true));
	}do{
		if(!val.asBoolean) enforce(0,"TODO: assertion failures");
		return this;
	}
	Value call(Value fun,Value arg){
		enforce(fun.tag==Value.Tag.closure);
		return call(fun.closure.fun,nullValue,arg,null,fun.closure.context);
	}

	Value readLocal(string s,bool constLookup){
		auto r=vars[s];
		if(!constLookup&&!r.type.isClassical()) vars.remove(s);
		return r;
	}
	static Value makeRecord(Record record){
		Value r;
		r.type=contextTy(false);
		r.record=record;
		return r;
	}
	static Value readField(Value r,string s,bool constLookup){
		assert(r.type==contextTy(false));
		auto res=r.record[s];
		if(!constLookup&&!res.type.isClassical()) r.record.remove(s); // TODO: ok?
		return res;
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
		static class IteQVal: QVal{
			Value cond,then,othw;
			this(Value cond,Value then,Value othw){
				this.cond=cond, this.then=then, this.othw=othw;
			}
			override Value get(Σ s){
				return cond.classicalValue(s)?then.classicalValue(s):othw.classicalValue(s);
			}
		}
		enforce(then.type==othw.type,"TODO: ite branches with different types");
		Value r;
		r.type=then.type;
		r.quval=new IteQVal(cond,then,othw);
		return r;
	}
	Value makeQVar(Value v)in{
		assert(!v.type.isClassical());
	}do{
		Value r;
		r.type=v.type;
		auto ref_=Σ.curRef++;
		static Σ addVariable(Σ s,Σ.Ref ref_,Value v){
			enforce(ref_ !in s.qvars);
			s.assign(ref_,v);
			return s;
		}
		this=map!addVariable(ref_,v);
		r.quval=new QVar(ref_);
		return r;
	}
	private void assignTo(Σ.Ref var,Value rhs){
		static Σ assign(Σ s,Σ.Ref var,Value rhs){
			s.assign(var,rhs);
			return s;
		}
		this=map!assign(var,rhs);
	}
	void assignTo(string lhs,Value rhs){
		if(rhs.type.isToplevelClassical()){
			vars[lhs]=rhs;
			return;
		}
		if(lhs in vars){
			auto var=vars[lhs];
			enforce(!var.type.isToplevelClassical());
			enforce(var.type==rhs.type);
			var.assign(this,rhs);
		}else{
			enforce(rhs.tag==Value.Tag.quval);
			Value qvar=rhs;
			if(!cast(QVar)qvar.quval) qvar=makeQVar(rhs);
			vars[lhs]=qvar;
		}
	}
	void passParameter(string prm,Value rhs){
		enforce(prm!in vars);
		vars[prm]=rhs;
	}
	void assignTo(Value lhs,Value rhs){
		enforce(0,"TODO: assignTo");
		assert(0);
	}
	Value H(Value x){
		return x.applyUnitary!hadamardUnitary(this,x.type);
	}
	Value X(Value x){
		enforce(0,"TODO: X");
		assert(0);
	}
	Value Y(Value x){
		enforce(0,"TODO: Y");
		assert(0);
	}
	Value Z(Value x){
		enforce(0,"TODO: Z");
		assert(0);
	}
	Value phase(Value φ){
		enforce(0,"TODO: Z");
		assert(0);
	}
	Value rX(Value args){
		enforce(0,"TODO: rX");
		assert(0);
	}
	Value rY(Value args){
		enforce(0,"TODO: rY");
		assert(0);
	}
	Value rZ(Value args){
		enforce(0,"TODO: rY");
		assert(0);
	}
	Value array_(Expression type,Value arg){
		enforce(arg.tag==Value.Tag.array_);
		enforce(arg.array_.length==2);
		enforce(arg.array_[0].isClassicalInteger());
		return makeArray(type,arg.array_[1].repeat(to!size_t(arg.array_[0].asInteger)).array);
	}
	alias vector=array_;
	Value measure(Value arg){
		MapX!(Value,C) candidates;
		foreach(k,v;state){
			auto candidate=arg.classicalValue(k);
			if(candidate!in candidates) candidates[candidate]=v;
			else candidates[candidate]+=v;
		}
		Value result;
		R random=uniform!"[]"(R(0),R(1));
		R current=0.0;
		foreach(k,v;candidates){
			current+=sqAbs(v);
			if(current>=random){
				result=k;
				break;
			}
		}
		MapX!(Σ,C) nstate;
		R total=0.0f;
		foreach(k,v;state){
			auto candidate=arg.classicalValue(k);
			if(candidate!=result) continue;
			total+=v.sqAbs();
			nstate[k]=v;
		}
		total=sqrt(total);
		foreach(k,ref v;nstate) v/=total;
		state=nstate;
		return result;
	}
}


// TODO: move this to semantic_, as a rewrite
QState.Value readVariable(QState)(ref QState qstate,VarDecl var,Scope from,bool constLookup){
	QState.Value r=getContextFor(qstate,var,from);
	if(r) return qstate.readField(r,var.getName,constLookup);
	return qstate.readLocal(var.getName,constLookup);
}
QState.Value getContextFor(QState)(ref QState qstate,Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{
	QState.Value r=QState.nullValue;
	auto meaningScope=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		meaningScope=fd.realScope;
	assert(sc&&sc.isNestedIn(meaningScope));
	for(auto csc=sc;csc !is meaningScope;){
		void add(string name){
			if(!r) r=qstate.readLocal(name,true);
			else r=qstate.readField(r,name,true);
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
QState.Value buildContextFor(QState)(ref QState qstate,Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{ // TODO: callers of this should only read the required context (and possibly consume)
	if(auto ctx=getContextFor(qstate,meaning,sc)) return ctx;
	QState.Record record;
	auto msc=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		msc=fd.realScope;
	for(auto csc=msc;;csc=(cast(NestedScope)csc).parent){
		if(!cast(NestedScope)csc) break;
		record=qstate.vars.dup;
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto dsc=cast(DataScope)csc){
			auto name=dsc.decl.contextName;
			record[name]=qstate.readLocal(name,true);
			break;
		}
		if(auto fsc=cast(FunctionScope)csc){
			auto cname=fsc.getFunction().contextName;
			record[cname]=qstate.readLocal(cname,true);
			break;
		}
	}
	return QState.makeRecord(record);
}
QState.Value lookupMeaning(QState)(ref QState qstate,Identifier id)in{assert(id && id.scope_,text(id," ",id.loc));}body{
	if(!id.meaning||!id.scope_||!id.meaning.scope_)
		return qstate.readLocal(id.name,id.constLookup);
	if(auto vd=cast(VarDecl)id.meaning){
		auto r=getContextFor(qstate,id.meaning,id.scope_);
		if(r) return qstate.readField(r,id.name,id.constLookup);
		return qstate.readLocal(id.name,id.constLookup);
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
				static assert(!__traits(compiles,fe.constLookup));
				// TODO: non-constant field lookup
				return qstate.readField(doIt(fe.e),fe.f.name,true);
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
			if(auto me=cast(NSubExp)e){
				auto a=doIt(me.e1),b=doIt(me.e2);
				enforce(a.ge(b).bval,"result of sub is negative");
				return a-b;
			}if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
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
				static Expression unwrap(Expression e){
					if(auto tae=cast(TypeAnnotationExp)e)
						return unwrap(tae.e);
					return e;
				}
				static string getQuantumOp(Expression qpArg){
					auto opExp=qpArg;
					if(auto tpl=cast(TupleExp)opExp){
						enforce(tpl.e.length==1);
						opExp=tpl.e[0];
					}
					auto opLit=cast(LiteralExp)opExp;
					enforce(!!opLit&&opLit.lit.type==Tok!"``");
					return opLit.lit.str;
				}
				auto id=cast(Identifier)unwrap(ce.e);
				auto fe=cast(FieldExp)unwrap(ce.e);
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
							case "quantumPrimitive":
								enforce(0,"quantum primitive cannot be used as first-class value");
								assert(0);
							default:
								enforce(0,text("TODO: ",id.name));
								assert(0);
						}
					}
				}else if(auto ce2=cast(CallExp)unwrap(ce.e)){
					if(auto id2=cast(Identifier)unwrap(ce2.e)){
						if(isBuiltIn(id2)){
							switch(id2.name){
								case "quantumPrimitive":
									switch(getQuantumOp(ce2.arg)){
										case "dup": enforce(0,"quantumPrimitive(\"dup\")[τ] cannot be used as first-class value"); assert(0);
										case "array": enforce(0,"quantumPrimitive(\"array\")[τ] cannot be used as first-class value"); assert(0);
										case "vector": enforce(0,"quantumPrimitive(\"vector\")[τ] cannot be used as first-class value"); assert(0);
										case "reverse":  enforce(0,"quantumPrimitive(\"reverse\")[τ] cannot be used as first-class value"); assert(0);
										case "M": enforce(0,"quantumPrimitive(\"M\")[τ] cannot be used as first-class value"); assert(0);
										case "H": return qstate.H(doIt(ce.arg));
										case "X": return qstate.X(doIt(ce.arg));
										case "Y": return qstate.Y(doIt(ce.arg));
										case "Z": return qstate.Z(doIt(ce.arg));
										case "P": return qstate.phase(doIt(ce.arg));
										case "rX": return qstate.rX(doIt(ce.arg));
										case "rY": return qstate.rY(doIt(ce.arg));
										case "rZ": return qstate.rZ(doIt(ce.arg));
										default: break;
									}
									break;
								default:
									break;
							}
						}
					}else if(auto ce3=cast(CallExp)unwrap(ce2.e)){
						if(auto id3=cast(Identifier)unwrap(ce3.e)){
							if(isBuiltIn(id3)){
								switch(id3.name){
									case "quantumPrimitive":
										switch(getQuantumOp(ce3.arg)){
											case "dup": return doIt(ce.arg);
											case "array": return qstate.array_(ce.type,doIt(ce.arg));
											case "vector": return qstate.vector(ce.type,doIt(ce.arg));
											case "reverse": enforce(0,"TODO: reverse"); assert(0);
											case "M": return qstate.measure(doIt(ce.arg));
											default: break;
										}
										break;
									default:
										break;
								}
							}
						}
					}
				}
				auto fun=doIt(ce.e), arg=doIt(ce.arg);
				return qstate.call(fun,arg);
			}
			if(auto idx=cast(IndexExp)e) return doIt(idx.e)[doIt(idx.a[0])]; // TODO: bounds checking
			if(auto sl=cast(SliceExp)e) return doIt(sl.e)[doIt(sl.l)..doIt(sl.r)]; // TODO: bounds checking
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
				auto et=arr.type.elementType;
				assert(!!et);
				auto values=arr.e.map!(v=>doIt(v).convertTo(et)).array;
				return QState.makeArray(e.type,values);
			}else if(auto ae=cast(AssertExp)e){
				if(auto c=runExp(ae.e)){
					qstate=qstate.assertTrue(c);
					return qstate.makeTuple(unit,[]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)e){
				return doIt(tae.e).convertTo(tae.type);
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
		}else enforce(0,"TODO: assignments to non-variables");
	}
	void runStm(Expression e,ref QState retState){
		if(!qstate.state.length) return;
		if(opt.trace){
			writeln("state: ",qstate);
			writeln("statement: ",e);
		}
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
				value = QState.makeTuple(tupleTy([re.e.type,contextTy(true)]),[value,qstate.readLocal(functionDef.contextName,false)]);
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
