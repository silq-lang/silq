import std.conv: text, to;
import std.format: format;
import std.string: split;
import std.algorithm, std.range;
import std.array: array;
import std.range: iota, repeat, walkLength;
import util.range: zip;
import std.string: startsWith,join;
import util.tuple: q=tuple,Q=Tuple;
import std.exception: enforce;

import options;
import astopt;
import util.hashtable,util;
import ast.expression,ast.declaration,ast.type;
import ast.lexer,ast.semantic_,ast.reverse,ast.scope_,ast.error;
import util, util.io;

import std.random;
import std.complex;
import util.math;

struct FrameInfo {
	FunctionDef fd;
	Location loc; // location within caller, not `fd`
}

class LocalizedException: Exception{
	Location loc;
	FrameInfo[] stackTrace;
	this(Exception e,Location loc){
		super(e.msg,e.file,e.line,e);
		this.loc=loc;
	}
}
LocalizedException localizedException(Exception e,Location loc){
	if(auto r=cast(LocalizedException)e) return r;
	return new LocalizedException(e,loc);
}
version=LOCALIZE;
version(LOCALIZE){}else pragma(msg,"NOTE: error messages not formatted");

class QSim{
	this(string sourceFile){
		this.sourceFile=sourceFile;
	}
	QState run(FunctionDef def,ErrorHandler err){
		if(def.params.length){
			err.run_error("use `--run-on=args` or `--run-on-each=[args_1,...,args_n]` to run main function with parameters",def.loc);
			return QState.empty();
		}
		/+DExpr[string] fields;
		foreach(i,a;def.params) fields[a.getName]=dVar(a.getName);
		DExpr init=dRecord(fields);+/
		auto init=QState.unit();
		auto interpreter=Interpreter!QState(def,def.body_,init,false);
		auto ret=QState.empty();
		try{
			interpreter.runFun(ret);
		}catch(LocalizedException ex){
			Location loc = ex.loc;
			size_t i=0;
			// Suppress stack frames in prelude
			while(i<ex.stackTrace.length && ex.stackTrace[i].fd.boolAttribute(Id.s!"artificial")) {
				loc=ex.stackTrace[i].loc;
				i++;
			}
			err.run_error(ex.msg,loc);
			for(;i<ex.stackTrace.length;i++){
				err.note("called from here",ex.stackTrace[i].loc);
			}
			return QState.empty();
		}
		assert(!!def.ftype);
		bool isTuple = !!def.ftype.cod.isTupleTy;
		return ret;
	}
private:
	string sourceFile;
}

private alias FormattingOptions=QState.Value.FormattingOptions;
private alias FormattingType=QState.Value.FormattingOptions.FormattingType;
string formatQValue(QState qs,QState.Value value){ // (only makes sense if value contains the full quantum state)
	if(value.isClassical()) return value.toStringImpl(FormattingOptions.init);
	string r;
	foreach(k,v;qs.state){
		if(r.length) r~="+";
		r~=text("(",v,")·",value.classicalValue(k).toBasisStringImpl());
	}
	if(!r.length) return "0";
	return r;
}

long smallValue(ℤ value){
	if(long.min<=value&&value<=long.max) return to!long(value);
	enforce(0,"value too large");
	assert(0);
}

enum zeroThreshold=1e-15; // TODO: make configurable
bool isToplevelClassical(Expression ty)in{
	assert(!!ty);
}do{
	return ty.isClassical()||cast(TupleTy)ty||cast(ArrayTy)ty||cast(VectorTy)ty||cast(ContextTy)ty||cast(ProductTy)ty;
}

void hadamardUnitary(alias add,QState)(QState.Value x){
	alias C=QState.C;
	enforce(x.tag==QState.Value.Tag.bval,"bad input for H");
	enum norm=C(sqrt(1.0/2.0));
	if(!x.bval){ add(x,norm); add(x.eqZ,norm); }
	else{    add(x.eqZ,norm);    add(x,-norm); }
}
void xUnitary(alias add,QState)(QState.Value x){
	alias C=QState.C;
	enforce(x.tag==QState.Value.Tag.bval,"bad input for X");
	add(x.eqZ,C(1.0));
}
void yUnitary(alias add,QState)(QState.Value x){
	alias C=QState.C;
	enforce(x.tag==QState.Value.Tag.bval,"bad input for Y");
	add(x.eqZ,C(0.0,x.eqZImpl?1.0:-1.0));
}
void zUnitary(alias add,QState)(QState.Value x){
	alias C=QState.C;
	enforce(x.tag==QState.Value.Tag.bval,"bad input for Z");
	add(x,C(x.eqZImpl?1.0:-1.0));
}
// (string mixin as workaround for DMD compiler bug)
enum rotUnitary(string D)=mixin(X!q{
	void r@(D)Unitary(alias add,QState)(QState.Value x,QState.R φ){
		alias C=QState.C;
		enforce(x.tag==QState.Value.Tag.bval,"bad input for rot@(D)");
		add(x,C(cos(0.5*φ),0.0));
		@(lowerf(D))Unitary!((k,v)=>add(k,C(0.0,-sin(0.5*φ))*v))(x);
	}
});
mixin(rotUnitary!"X");
mixin(rotUnitary!"Y");
mixin(rotUnitary!"Z");

struct QState{
	MapX!(Σ,C) state;
	Record vars;
	QVar[] popFrameCleanup;

	static Value dupValue(Value v){
		if(!v.type) return Value.init;
		auto tt=v.tag;
		if(tt==QState.Value.Tag.array_) v.array_=dupValue(v.array_);
		if(tt==QState.Value.Tag.record) v.record=dupValue(v.record);
		return v;
	}
	static Value[] dupValue(QState.Value[] r){
		r=r.dup;
		foreach(ref v;r) v=dupValue(v);
		return r;
	}
	static Record dupValue(Record r){
		r=r.dup;
		foreach(k,ref v;r) v=dupValue(v);
		return r;
	}

	string toString(int skipFrames=0){
		FormattingOptions opt={type: FormattingType.dump};
		string r="/────────\nQUANTUM STATE\n";
		Q!(string,Σ.Sortable)[] vk;
		foreach(k,v;state)
			vk~=q(text("(",v,")·"),k.toSortable());
		sort!"a[1]<b[1]"(vk);
		if(state.length){
			auto maxlen=vk.map!(x=>x[0].displayWidth).reduce!max;
			foreach(ref t;vk) t[0]=text(' '.repeat(maxlen-t[0].displayWidth),t[0]);
		}
		bool first=true;
		foreach(t;vk){
			if(first){
				first=false;
				if(state.length>1) r~=" ";
			}else r~="\n+";
			r~=text(t[0],t[1].toStringImpl(opt));
		}
		r~="\n\nVARIABLES\n";
		alias Mapping=Q!(string,Value);
		Mapping[] mappings;
		Record nvars=vars;
		foreach(i;0..skipFrames){
			if("`parent" in nvars){
				auto frame=vars["`parent"];
				if(frame.tag!=Value.Tag.record) break;
				nvars=frame.record;
			}
		}
		foreach(var,val;nvars) mappings~=q(var,val);
		bool special(string name){
			return name.length&&name[0]=='`';
		}
		bool compare(Mapping a,Mapping b){
			return q(special(a[0]),a[0])<q(special(b[0]),b[0]);
		}
		sort!compare(mappings);
		foreach(i,t;mappings){
			if(i&&special(t[0])&&!special(mappings[i-1][0]))
				r~="\n";
			r~=text(t[0]," ↦ ",t[1].toStringImpl(opt),"\n");
		}
		r~="────────/";
		return r;
	}

	void dump(int skipFrames){
		writeln(toString(skipFrames));
	}

	QState dup(){
		return QState(state.dup,dupValue(vars),popFrameCleanup);
	}
	void copyNonState(ref QState rhs){
		this.tupleof[1..$]=rhs.tupleof[1..$];
	}
	void add(Σ k,C v){
		if(k in state) state[k]+=v;
		else state[k]=v;
		if(abs(state[k]) <= zeroThreshold) state.remove(k);
	}
	void updateRelabeling(ref Σ.Ref[Σ.Ref] relabeling,Value to,Value from){
		if(!to.type) return;
		auto tag=to.tag;
		
		enforce(tag==from.tag,"value type mismatch on merge");
		final switch(tag){
			case Value.Tag.array_:
				enforce(to.array_.length==from.array_.length,"encountered quantum-dependent tuple length");
				foreach(i;0..to.array_.length)
					updateRelabeling(relabeling,to.array_[i],from.array_[i]);
				break;
			case Value.Tag.record:
				foreach(k,v;to.record)
					updateRelabeling(relabeling,v,from.record[k]);
				break;
			case Value.Tag.quval:
				auto tquvar=cast(QVar)to.quval;
				auto fquvar=cast(QVar)from.quval;
				if(tquvar&&fquvar&&fquvar.ref_!=tquvar.ref_) relabeling[fquvar.ref_]=tquvar.ref_;
				break;
			case Value.Tag.closure:
				/+if(to.closure.context&&from.closure.context)
					updateRelabeling(relabeling,*to.closure.context,*from.closure.context);+/
				break;
			case Value.Tag.fval,Value.Tag.qval,Value.Tag.zval,Value.Tag.uintval,Value.Tag.intval,Value.Tag.bval:
				break;
		}
	}
	void opOpAssign(string op:"+")(QState r){
		if(!r.state.length) return; // TODO: ideally would not be needed
		if(!state.length){ this=r; return; } // TODO: ideally would not be needed
		Σ.Ref[Σ.Ref] relabeling;
		foreach(k,ref v;r.vars){
			if(k in vars) updateRelabeling(relabeling,vars[k],v);
			else vars[k]=v;
		}
		foreach(k,v;r.state){
			k.relabel(relabeling);
			add(k,v);
		}
	}
	Q!(QState,QState) split(Value cond){
		QState then,othw;
		then.copyNonState(this);
		othw.copyNonState(this);
		othw.vars=dupValue(othw.vars);
		if(cond.isClassical()){
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
	QState project(Value cond){ return split(cond)[0]; }
	R totalProb(){ return state.values.map!sqAbs.sum; }
	QState map(alias f,bool checkInterference=true,T...)(T args){
		QState new_;
		new_.copyNonState(this);
		if(!opt.projectForget){
			foreach(k,v;state){
				auto nk=f(k,args);
				static if(checkInterference){
					enforce(nk !in new_.state,"bad forget"); // TODO: good error reporting, e.g. for forget
					new_.state[nk]=v;
				}else new_.add(nk,v);
			}
		}else{
			foreach(k,v;state){
				auto nk=f(k,args);
				static if(checkInterference){
					if(nk !in new_.state||abs(new_.state[nk])<abs(v))
						new_.state[nk]=v;
				}else new_.add(nk,v);
			}			
		}
		return new_;
	}
	alias R=double;
	alias C=Complex!double;
	static abstract class QVal{
		override string toString(){ return text("_ (",typeid(this),")"); }
		abstract Value get(ref Σ);
		QVar dup(ref QState state,Value self){
			auto nref_=Σ.curRef++;
			state.assignTo(nref_,self);
			return new QVar(nref_);
		}
		void forget(ref QState state,Value rhs){ }
		void forget(ref QState state){ }
		QVal consumeOnRead(){
			return this;
		}
		Value toVar(ref QState state,Value self,bool cleanUp){
			auto r=state.makeQVar(self);
			if(cleanUp){
				auto var=cast(QVar)r.quval;
				assert(!!var);
				state.popFrameCleanup~=var;
			}
			return r;
		}
		void removeVar(ref Σ σ){}
		final Value applyUnitary(alias unitary,T...)(ref QState qs,Expression type,T controls){
			// TODO: get rid of code duplication
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
				unitary!(add,QState)(get(k),controls);
			}
			auto r=makeQuval(type,new QVar(ref_));
			qs=nstate;
			return r;
		}
		static Value applyUnitaryToClassical(alias unitary,T...)(ref QState qs,Value value,Expression type,T controls){
			// TODO: get rid of code duplication
			QState nstate;
			nstate.copyNonState(qs);
			auto ref_=Σ.curRef++; // TODO: reuse reference of x if possible
			foreach(k,v;qs.state){
				void add(Value nk,C nv){
					auto σ=k.dup;
					σ.assign(ref_,nk);
					nstate.add(σ,nv*v);
				}
				unitary!(add,QState)(value,controls);
			}
			auto r=makeQuval(type,new QVar(ref_));
			qs=nstate;
			return r;
		}
	}
	static class QConst: QVal{
		Value constant;
		override string toString(){ return constant.toStringImpl(FormattingOptions.init); }
		this(Value constant){ this.constant=constant; }
		override Value get(ref Σ){ return constant; }
	}
	static class QVar: QVal{
		Σ.Ref ref_;
		bool consumedOnRead=false;
		override string toString(){ return text("ref(",ref_,")"); }
		this(Σ.Ref ref_){ this.ref_=ref_; }
		override Value get(ref Σ s){
			if(astopt.allowUnsafeCaptureConst) enforce(ref_ in s.qvars, "dangling reference");
			auto r=s.qvars[ref_];
			if(consumedOnRead) removeVar(s);
			return r;
		}
		override void removeVar(ref Σ s){
			s.qvars.remove(ref_);
		}
		void assign(ref QState state,Value rhs){
			state.assignTo(ref_,rhs);
		}
		override QVar dup(ref QState state,Value self){
			if(consumedOnRead){ consumedOnRead=false; return this; }
			return super.dup(state,self);
		}
		override void forget(ref QState state,Value rhs){
			state.forget(ref_,rhs);
		}
		override void forget(ref QState state){
			state.forget(ref_);
		}
		override QVar consumeOnRead(){
			consumedOnRead=true;
			return this;
		}
		override Value toVar(ref QState state,Value self,bool cleanUp){
			if(consumedOnRead){
				consumedOnRead=false;
				if(cleanUp) state.popFrameCleanup~=this;
			}
			return self;
		}
	}
	static class ConvertQVal: QVal{
		Value value;
		Expression ntype;
		this(Value value,Expression ntype){ this.value=value; this.ntype=ntype.getClassical(); }
		override Value get(ref Σ σ){ return value.classicalValue(σ).convertTo(ntype); }
		override void removeVar(ref Σ σ){
			value.removeVar(σ);
		}
		override void forget(ref QState state,Value rhs){
			value.forget(state,rhs);
		}
		override void forget(ref QState state){
			value.forget(state);
		}
	}
	static class IndexQVal: QVal{
		Value value,i;
		this(Value value,Value i){ this.value=value; this.i=i; }
		override Value get(ref Σ σ){ return value.classicalValue(σ)[i.classicalValue(σ)]; }
	}
	static class UnOpQVal(string op):QVal{
		Value value;
		this(Value value){ this.value=value; }
		override Value get(ref Σ σ){ return value.classicalValue(σ).opUnary!op; }
	}
	static class BinOpQVal(string op):QVal{
		Value l,r;
		this(Value l,Value r){ this.l=l; this.r=r; }
		override Value get(ref Σ σ){ return l.classicalValue(σ).opBinary!op(r.classicalValue(σ)); }
	}
	static class MemberFunctionQVal(string fun,T...):QVal{
		Value value;
		T args;
		this(Value value,T args){ this.value=value; this.args=args; }
		override Value get(ref Σ σ){ return mixin(`value.classicalValue(σ).`~fun)(args); }
	}
	static class FunctionQVal(alias fun,T...):QVal{
		Value value;
		T args;
		this(Value value,T args){ this.value=value; this.args=args; }
		override Value get(ref Σ σ){ return fun(value.classicalValue(σ),args); }
	}
	static class CompareQVal(string op):QVal{
		Value l,r;
		this(Value l,Value r){ this.l=l; this.r=r; }
		override Value get(ref Σ σ){ return l.classicalValue(σ).compare!op(r.classicalValue(σ)); }
	}
	alias Record=HashMap!(string,Value,(a,b)=>a==b,(a)=>typeid(a).getHash(&a));
	struct Closure{
		FunctionDef fun;
		Value* context;
		this(FunctionDef fun,Value* context){
			this.fun=fun; this.context=context;
		}
		hash_t toHash(){ return context?q(fun,*context).toHash():fun.toHash(); }
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
			intval,
			uintval,
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
			if(auto intTy=isFixedIntTy(type)) return intTy.isSigned ? Tag.intval : Tag.uintval;
			if(type==typeTy||type==ctypeTy||type==qtypeTy) return Tag.bval; // (optimization)
			if(isTypeTy(type)||isQNumericTy(type)) return Tag.bval; // TODO: ok?
			enforce(0,text("TODO: representation for type ",type," ",typeid(type)));
			assert(0);
		}
		@property Tag tag(){
			return getTag(type);
		}
		bool isValid(){ return !!type; }
		void opAssign(Value rhs){
			// TODO: make safe
			type=rhs.type;
			if(!type) return;
			Lswitch:final switch(tag){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag){
					case t: mixin(`this.`~text(t)~`=rhs.`~text(t)~`;`); break Lswitch;
				}
			}
		}
		Value dup(ref QState state){
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						return this;
				}
				case Tag.closure:
					return state.makeClosure(type,Closure(closure.fun,closure.context?[closure.context.dup(state)].ptr:null));
				case Tag.array_: return state.makeArray(type,array_.map!(x=>x.dup(state)).array);
				case Tag.record:
					Record nrecord;
					foreach(k,v;record) nrecord[k]=v.dup(state);
					return state.makeRecord(type,nrecord);
				case Tag.quval: return state.makeQuval(type,quval.dup(state,this));
			}
		}
		Value toVar(ref QState state,bool cleanUp){
			if(isClassical) return this;
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						assert(0);
				}
				case Tag.closure:
					return state.makeClosure(type,Closure(closure.fun,closure.context?[closure.context.toVar(state,cleanUp)].ptr:null));
				case Tag.array_:
					return makeArray(type,array_.map!(v=>v.toVar(state,cleanUp)).array); // TODO: this can be inefficient, avoid
				case Tag.record: // TODO: get rid of this
					Record nrecord;
					foreach(k,v;record) nrecord[k]=v.toVar(state,cleanUp);
					return state.makeRecord(type,nrecord);
				case Tag.quval: return quval.toVar(state,this,cleanUp);
			}
		}
		bool opEquals(Value rhs){
			if(type!=rhs.type) return false;
			if(!type) return true;
			assert(tag==rhs.tag);
			final switch(tag){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag){
					case t:
						return mixin(`this.`~text(t)~`==rhs.`~text(t));
				}
			}
		}
		hash_t toHash(){
			if(!type) return 0;
			final switch(tag){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag){
					case t:
						return q(t,mixin(text(t))).toHash();
				}
			}
		}
		this(this){
			if(!type) return;
			auto tt=tag;
			Lswitch:final switch(tt){
				import std.traits:EnumMembers;
				static foreach(t;EnumMembers!Tag){
					case t:
						static if(__traits(hasMember,mixin(text(t)),"__postblit"))
							mixin(`this.`~text(t)~`.__postblit();`);
						break Lswitch;
				}
			}
		}
		void assign(ref QState state,Value rhs){
			if(!type){ this=rhs; return; }
			if(isClassical()){
				if(rhs.isClassical) this=rhs;
				else this=rhs.toVar(state,false);
				return;
			}
			if(rhs.isClassical()){
				forget(state);
				this=rhs;
				return;
			}
			assert(tag==rhs.tag);
			enforce(rhs.tag==rhs.tag,"incompatible values for assignment");
			Lswitch: final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						this=rhs;
						break Lswitch;
				}
				case Tag.closure:
					enforce(rhs.tag==Tag.closure,"incompatible values for closure assignment");
					closure.fun=rhs.closure.fun;
					if(closure.context&&rhs.closure.context&&closure.context!is rhs.closure.context)
						(*closure.context).assign(state,*rhs.closure.context);
					return;
				case Tag.array_:
					enforce(rhs.tag==Tag.array_,"incompatible values for array assignment");
					if(array_.length==rhs.array_.length){
						if(array_ !is rhs.array_)
							foreach(i;0..array_.length)
								array_[i].assign(state,rhs.array_[i]);
					}else{
						forget(state);
						this=rhs;
					}
					return;
				case Tag.record:
					enforce(rhs.tag==Tag.record,"incompatible values for record assignment");
					if(record is rhs.record) return;
					bool ok=true;
					foreach(k,v;rhs.record) if(k !in record) ok=false;
					foreach(k,v;record) if(k !in rhs.record) ok=false;
					if(ok) foreach(k,v;record) v.assign(state,rhs.record[k]);
					else{
						forget(state);
						this=rhs;
					}
					return;
				case Tag.quval:
					if(rhs.tag==Tag.quval&&quval is rhs.quval) return;
					if(auto quvar=cast(QVar)quval){ // TODO: ok?
						scope(success) rhs.forget(state);
						return quvar.assign(state,rhs);
					}
			}
			assert(0,text("can't assign to constant ",this," ",rhs));
		}
		void removeVar(ref Σ σ){
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						assert(isClassical);
						return;
				}
				case Tag.closure:
					if(closure.context) return closure.context.removeVar(σ);
					return;
				case Tag.array_:
					foreach(i,ref x;array_) x.removeVar(σ);
					return;
				case Tag.record:
					foreach(k,v;record) v.removeVar(σ);
					return;
				case Tag.quval:
					return quval.removeVar(σ);
			}
		}
		void forget(ref QState state,Value rhs){
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						assert(isClassical);
						return;
				}
				case Tag.closure:
					enforce(rhs.tag==Tag.closure,"incompatible values for closure forget");
					if(closure.context) return closure.context.forget(state,*rhs.closure.context);
					return;
				case Tag.array_:
					assert(rhs.tag==Tag.array_,"incompatible values for array forget");
					enforce(array_.length==rhs.array_.length,"inconsistent array lengths for forget"); // TODO: good error reporting
					foreach(i,ref x;array_) x.forget(state,rhs.array_[i]);
					return;
				case Tag.record:
					enforce(rhs.tag==Tag.record,"incompatible values for record forget");
					foreach(k,v;rhs.record) enforce(k in record,format("missing key `%s` for record forget",k));
					foreach(k,v;record) v.forget(state,rhs.record[k]);
					return;
				case Tag.quval:
					return quval.forget(state,rhs);
			}
		}
		void forget(ref QState state){
			// TODO: get rid of code duplication
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						assert(isClassical);
						return;
				}
				case Tag.closure:
					if(closure.context) return closure.context.forget(state);
					return;
				case Tag.array_:
					foreach(i,ref x;array_) x.forget(state);
					return;
				case Tag.record:
					foreach(k,v;record) v.forget(state);
					return;
				case Tag.quval:
					return quval.forget(state);
			}
		}
		Value consumeOnRead(){ // TODO: do this in-place
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						assert(isClassical);
						return this;
				}
				case Tag.closure:
					Closure nclosure=this.closure;
					if(nclosure.context) *nclosure.context=(*closure.context).consumeOnRead();
					return makeClosure(type,nclosure);
				case Tag.array_: return makeArray(type,array_.map!(x=>x.consumeOnRead()).array);
				case Tag.record:
					Record nrecord;
					foreach(k,v;record) nrecord[k]=v.consumeOnRead();
					return makeRecord(type,nrecord);
				case Tag.quval: return makeQuval(type,quval.consumeOnRead());
			}
		}
		Value applyUnitary(alias unitary,T...)(ref QState qs,Expression type,T controls){
			if(this.isClassical()) return QVal.applyUnitaryToClassical!unitary(qs,this,type,controls);
			enforce(tag==Tag.quval,"bad value type for unitary application");
			return quval.applyUnitary!unitary(qs,type,controls);
		}
		union{
			Value[] array_;
			Record record;
			Closure closure;
			QVal quval;
			R fval;
			ℚ qval;
			ℤ zval;
			BitInt!true intval;
			BitInt!false uintval;
			bool bval;
			ubyte[max(array_.sizeof,record.sizeof,quval.sizeof,fval.sizeof,qval.sizeof,zval.sizeof,bval.sizeof)] bits;
		}
		bool isClassical(){
			if(!type) return true; // TODO: can we get rid of this?
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						return true;
				}
				case Tag.closure:
					if(closure.context) return (*closure.context).isClassical();
					return true;
				case Tag.array_: return array_.all!(x=>x.isClassical());
				case Tag.record:
					foreach(k,v;record) if(!v.isClassical()) return false;
					return true;
				case Tag.quval: return false;
			}
		}
		bool isToplevelClassical(){
			return type.isToplevelClassical();
		}

		Value convertTo(Expression ntype){
			if(ntype==ℕt(true)) ntype=ℤt(true);
			try{ getTag(ntype); }catch(Exception){ ntype=type; } // TODO: get rid of this
			// TODO: do this in-place?
			auto otag=tag, ntag=getTag(ntype);
			if(ntag==tag.quval){
				if(isClassical()){
					auto constant=convertTo(ntype.getClassical());
					return makeQuval(ntype,new QConst(constant));
				}else return makeQuval(ntype,new ConvertQVal(this,ntype));
			}else if(isClassical()&&type==ntype) return this;
			final switch(otag){
				case Tag.array_:
					if(ntag==Tag.array_){
						if(auto tpl=ntype.isTupleTy()){
							assert(array_.length==tpl.length);
							return makeArray(ntype,iota(array_.length).map!(i=>array_[i].convertTo(tpl[i])).array);
						}else if(auto arr=cast(ArrayTy)ntype){
							return makeArray(ntype,array_.map!(v=>v.convertTo(arr.next)).array);
						}else if(auto vec=cast(VectorTy)ntype){
							return makeArray(ntype,array_.map!(v=>v.convertTo(vec.next)).array);
						}else assert(0);
					}
					if(ntag==Tag.intval||ntag==Tag.uintval){
						ℤ r=0;
						foreach(i,ref v;array_){
							assert(v.tag==Tag.bval);
							if(v.bval) r+=ℤ(1)<<i;
						}
						if(ntag==Tag.intval) return makeInt(ntype,BitInt!true(array_.length,r));
						return makeUint(ntype,BitInt!false(array_.length,r));
					}
					break;
				case Tag.record:
					break;
				case Tag.closure:
					assert(ntag==Tag.closure);
					return makeClosure(ntype,closure);
				case Tag.quval:
					// can happen when converting from int[n]/uint[n] to array (TODO: store n classically?)
					break;
				case Tag.fval:
					if(ntag==Tag.bval) return neqZ;
					if(ntag==Tag.zval||ntag==Tag.qval){
						static assert(R.sizeof*8==64);
						auto r=fval.toℚ;
						if(ntag==Tag.qval) return makeRational(r);
						if(ntag==Tag.zval) return makeInteger(.floor(r));
					}
					if(ntag==Tag.fval) return this;
					break;
				case Tag.qval:
					if(ntag==Tag.bval) return neqZ;
					if(ntag==Tag.zval) return makeInteger(.floor(qval));
					if(ntag==Tag.qval) return this;
					if(ntag==Tag.fval) return makeReal(toReal(qval));
					break;
				case Tag.zval:
					if(ntag==Tag.bval) return neqZ;
					if(ntag==Tag.zval) return this;
					if(ntag==Tag.qval) return makeRational(ℚ(zval));
					if(ntag==Tag.fval) return makeReal(toReal(zval));
					break;
				case Tag.intval,Tag.uintval:
					if(ntag==Tag.bval) return neqZ;
					if(ntag==Tag.zval) return makeInteger(otag==Tag.intval?intval.val:uintval.val);
					if(ntag==Tag.qval) return makeRational(ℚ(otag==Tag.intval?intval.val:uintval.val));
					if(ntag==Tag.fval) return makeReal(toReal(otag==Tag.intval?intval.val:uintval.val));
					if(ntag==tag){
						auto r=this;
						r.type=ntype;
						return r;
					}
					if(ntag==Tag.array_||ntag==Tag.intval||ntag==Tag.uintval){
						size_t nbits=0;
						ℤ val=0;
						if(otag==Tag.intval){
							nbits=intval.nbits;
							val=intval.val;
						}else{
							nbits=uintval.nbits;
							val=uintval.val;
						}
						if(ntag==Tag.array_)
							return makeArray(ntype.getClassical(),iota(nbits).map!(i=>makeBool(!!(val&(ℤ(1)<<i)))).array).convertTo(ntype);
						if(ntag==Tag.intval) return makeInt(ntype,BitInt!true(nbits,val));
						assert(ntag==Tag.uintval);
						return makeUint(ntype,BitInt!false(nbits,val));
					}
					break;
				case Tag.bval:
					if(ntag==Tag.bval) return this;
					if(ntag==Tag.zval) return makeInteger(ℤ(cast(int)bval));
					if(ntag==Tag.qval) return makeRational(ℚ(cast(int)bval));
					if(ntag==Tag.fval) return makeReal(to!R(bval));
			}
			if(ntag==Tag.bval) return neqZ;
			enforce(0,text("converting ",type," to ",ntype," not yet supported"));
			assert(0);
		}

		Value inFrame(){
			return this;
		}
		Value opIndex(ℤ i)in{
			assert(tag==Tag.array_||isFixedIntTy(type));
		}do{
			final switch(tag){
				case Tag.array_: enforce(0<=i&&i<array_.length,"index out of bounds"); return array_[to!size_t(i)];
				case Tag.quval:
					assert(isFixedIntTy(type));
					return makeQuval(Bool(false),new IndexQVal(this,makeInteger(ℤ(i))));
				case Tag.uintval:
					enforce(0<=i&&i<uintval.nbits,"index out of bounds");
					return makeBool((uintval.val&(ℤ(1)<<to!size_t(i)))!=0);
				case Tag.intval:
					enforce(0<=i&&i<intval.nbits,"index out of bounds");
					return makeBool((intval.val&(ℤ(1)<<to!size_t(i)))!=0);
				case Tag.fval,Tag.qval,Tag.zval,Tag.bval: enforce(0,"bad aggregate type for index"); assert(0);
				case Tag.record,Tag.closure: enforce(0,"bad aggregate type for index"); assert(0);
			}
		}
		Value opIndex(Value i){
			if(i.isℤ()) return this[i.asℤ()];
			if(cast(ArrayTy)i.type||cast(VectorTy)i.type||cast(TupleTy)i.type){
				if(cast(TupleTy)type){
					auto values=i.array_.map!(v=>this[v]).array;
					auto ntype=tupleTy(values.map!(v=>v.type).array);
					return makeTuple(ntype,values);
				}
				auto values=i.array_.map!(v=>this[v]).array;
				auto ntype=!values.length?ast.type.unit:values.map!(v=>v.type).fold!joinTypes;
				if(cast(ArrayTy)i.type) ntype=arrayTy(ntype);
				if(auto vt=cast(VectorTy)i.type) ntype=vectorTy(ntype,vt.num);
				return makeArray(arrayTy(ntype),values);
			}
			final switch(tag){
				case Tag.array_:
					// TODO: bounds checking
					Value build(Value[] array_,size_t offset){ // TODO: this is a hack
						if(array_.length==1) return array_[0];
						auto cond=i.compare!"<"(makeInteger(ℤ(offset+array_.length/2)));
						return ite(cond,build(array_[0..$/2],offset),build(array_[$/2..$],offset+array_.length/2));
					}
					enforce(array_.length,"array index out of bounds");
					return build(array_,0);
				case Tag.uintval,Tag.intval,Tag.quval:
					assert(isFixedIntTy(type));
					return makeQuval(Bool(false),new IndexQVal(this,i));
				case Tag.fval,Tag.qval,Tag.zval,Tag.bval: enforce(0,"bad aggregate type for index"); assert(0);
				case Tag.record,Tag.closure: enforce(0,"bad aggregate type for index"); assert(0);
			}
		}
		Value opSlice(ℤ l,ℤ r)in{
			assert(tag==Tag.array_);
		}do{
			enforce(r<=array_.length,"slice upper bound exceeds array length");
			enforce(l<=r,"slice lower bound exceeds slice upper bound");
			return makeArray(type,array_[to!size_t(l)..to!size_t(r)]);
		}
		Value opSlice(Value l,Value r){
			if(l.isℤ()&&r.isℤ()) return this[l.asℤ()..r.asℤ()];
			enforce(0,text("slicing for types ",this.type,", ",l.type," and ",r.type," is not yet supported"));
			assert(0);
		}
		static Expression unaryType(string op)(Expression t){
			static if(op=="-") return minusType(t);
			else static if(op=="~") return bitNotType(t);
			else static if(op=="!") return handleUnary!notType(t);
			else{
				enforce(0,text("`",op,"` for type ",t," is not yet supported"));
				assert(0);
			}
		}
		Value opUnary(string op)(){
			auto ntype=unaryType!op(type);
			if(!ntype.isToplevelClassical()) return makeQuval(ntype,new UnOpQVal!op(this));
			static if(op=="-"||op=="~"){
				static if(is(typeof(mixin(op~` fval`))))
					if(type==ℝ(true)) return makeReal(mixin(op~` fval`));
				static if(is(typeof(mixin(op~` qval`))))
					if(type==ℚt(true)) return makeRational(mixin(op~` qval`));
				static if(is(typeof(mixin(op~` zval`))))
					if(type==ℤt(true))
						return makeInteger(mixin(op~` zval`)); // TODO: wraparound
				if(auto intTy=isFixedIntTy(type)){
					if(intTy.isSigned) return makeInt(type,mixin(op~` intval`));
					else return makeUint(type,mixin(op~` uintval`));
				}
				if(type==Bool(true)){
					static if(op=="~") return makeBool(!bval);
					else return makeInteger(mixin(op~` ℤ(cast(int)bval)`));
				}
			}else static if(op=="!"){
				if(type==ℝ(true)) return makeBool(mixin(op~` fval`));
				if(type==ℚt(true)) return makeBool(mixin(op~` qval`));
				if(type==ℤt(true)) return makeBool(mixin(op~` zval`));
				if(type==Bool(true)) return makeBool(mixin(op~` bval`));
			}
			enforce(0,text("`",op,"` for type ",this.type," is not yet supported"));
			assert(0);
		}
		static Expression binaryType(string op)(Expression t1,Expression t2){
			static if(op=="+") return arithmeticType!false(t1,t2);
			else static if(op=="-") return subtractionType(t1,t2);
			else static if(op=="sub") return nSubType(t1,t2);
			else static if(op=="*") return arithmeticType!true(t1,t2);
			else static if(op=="/") return divisionType(t1,t2);
			else static if(op=="div"){
				if(t1==ℤt(true)){
					if(auto ft=isFixedIntTy(t2))
						if(!ft.isSigned)
							t1=ℕt(true); // TODO: this is a hack
				}
				return iDivType(t1,t2);
			}else static if(op=="%"){
				if(t2==ℤt(true)){
					if(auto ft=isFixedIntTy(t1))
						if(!ft.isSigned)
							t2=ℕt(true); // TODO: this is a hack
				}
				return moduloType(t1,t2);
			}else static if(op=="^^") return powerType(t1,t2);
			else static if(op=="|") return bitwiseType(t1,t2);
			else static if(op=="^") return bitwiseType(t1,t2);
			else static if(op=="&") return bitAndType(t1,t2);
			else static if(op=="~") return t1; // TODO: add function to semantic instead
			else static if(op=="<<"||op==">>") return arithmeticType!false(arithmeticType!false(t1,t1),t2); // TODO: add function to semantic instead
			else{
				enforce(0,text("`",op,"` for types ",t1," and ",t2," is not yet supported"));
				assert(0);
			}
		}
		Value opBinary(string op)(Value r){
			// % does not work for ℚ
			// |,& don't work for ℚ, ℝ
			// ^^ needs special handling
			// ~ needs special handling
			auto ntype=binaryType!op(type,r.type);
			if(!ntype){
				// TODO: this is a hack
				ntype=type;
				if(!r.type.isClassical){
					if(ntype.isClassical){
						if(ntype==ℕt(true)) ntype=ℕt(false);
						else if(ntype==ℤt(true)) ntype=ℤt(false);
						else if(ntype==ℚt(true)) ntype=ℚt(false);
						else if(ntype==ℂ(true)) ntype=ℂ(false);
						else ntype=ntype.getQuantum();
						enforce(!!ntype,text("`",op,"` for types ",type," and ",r.type," is not supported"));
					}
				}
			}
			if(ntype==ℕt(true)) ntype=ℤt(true);
			if(!ntype.isToplevelClassical()) return makeQuval(ntype,new BinOpQVal!op(this,r));
			assert(!!ntype);
			static if(op=="sub"){
				enforce(this.ge(r).neqZImpl,"result of sub is negative");
				if(isNumericTy(ntype)==NumericType.Bool) return this.gt(r);
				return this-r;
			}else static if(op=="^^"){
				auto t1=type,t2=r.type;
				if(t1==Bool(true)&&isSubtype(t2,ℕt(true))) return makeBool(asBoolean||!r.asBoolean);
				//if(cast(ℂTy)t1||cast(ℂTy)t2) return t1^^t2; // ?
				if(util.among(t1,Bool(true),ℕt(true),ℤt(true),ℚt(true))&&isSubtype(t2,ℤt(false))){
					auto p=r.asℤ();
					if(t1!=ℚt(true)&&p>=0) return makeInteger(pow(asℤ(),p)); // TODO: this is a hack
					return makeRational(pow(asℚ(),p));
				}
				if(type==Bool(true)) return makeBool(asBoolean||r.asBoolean);
				if(t1!=ℝ(true)||t2!=ℝ(true))
					return convertTo(ℝ(true))^^r.convertTo(ℝ(true));
				auto res=fval^^r.fval;
				enforce(!isNaN(res),text("cannot take `",fval,"` to the power of `",r.fval,"`"));
				return makeReal(res);
			}else static if(op=="~"){
				enforce(tag==Tag.array_&&r.tag==Tag.array_,"incompatible values for concatentation");
				return makeArray(ntype,array_~r.array_);
			}else static if(op=="<<"||op==">>"){
				if(type==ℤt(true)) return makeInteger(mixin(`zval `~op~` smallValue(r.asℤ())`));
				if(type==Bool(true)) return makeInteger(mixin(`ℤ(cast(int)bval) `~op~` smallValue(r.asℤ())`));
				if(auto intTy=isFixedIntTy(type)){
					if(intTy.isSigned) return makeInt(type,mixin(`intval `~op~` smallValue(r.asℤ())`));
					else return makeUint(type,mixin(`uintval `~op~` smallValue(r.asℤ())`));
				}
			}else{
				static if(op=="/"||op=="div"||op=="%") enforce(!r.eqZImpl,"division by zero");
				if(type!=ntype||r.type!=ntype){
					static if(op=="%"||op=="div"){
						size_t nbits=0;
						if(r.tag==Tag.intval) nbits=r.intval.nbits;
						else if(r.tag==Tag.uintval) nbits=r.uintval.nbits;
						if(nbits==0){
							if(tag==Tag.intval) nbits=intval.nbits;
							else if(tag==Tag.uintval) nbits=uintval.nbits;
						}
						static if(op=="%"){
							if(auto intTy=isFixedIntTy(ntype)){
								if(intTy.isSigned) return makeInt(ntype,BitInt!true(nbits, floormod(asℤ, r.asℤ)));
								else return makeUint(ntype,BitInt!false(nbits, floormod(asℤ, r.asℤ)));
							}else if(ntype==Bool(true)) return makeBool(!!floormod(asℤ, r.asℤ));
						}else static if(op=="div"){
							if(isℚ&&r.isℚ){
								if(auto intTy=isFixedIntTy(ntype)){
									if(intTy.isSigned) return makeInt(ntype,BitInt!true(nbits, .floor(asℚ/r.asℚ)));
									else return makeUint(ntype,BitInt!false(nbits, .floor(asℚ/r.asℚ)));
								}else if(ntype==Bool(true)) return makeBool(!!.floor(asℚ/r.asℚ));
								else return makeInteger(.floor(asℚ/r.asℚ));
							}else if(isℝ&&r.isℝ){
								return makeReal(.floor(asℝ/r.asℝ));
							}
						}
					}else{
						if(type==ntype&&util.among(r.type,Bool(true),ℕt(true),ℤt(true))){
							if(auto intTy=isFixedIntTy(type)){
								if(intTy.isSigned) return this.opBinary!op(makeInt(ntype,BitInt!true(intval.nbits,r.asℤ())));
								else return this.opBinary!op(makeUint(ntype,BitInt!false(uintval.nbits,r.asℤ())));
							}
						}else if(util.among(type,Bool(true),ℕt(true),ℤt(true))&&r.type==ntype){
							if(auto intTy=isFixedIntTy(r.type)){
								if(intTy.isSigned) return makeInt(ntype,BitInt!true(r.intval.nbits,asℤ())).opBinary!op(r);
								else return makeUint(ntype,BitInt!false(r.uintval.nbits,asℤ())).opBinary!op(r);
							}
							// TODO: rat
						}
					}
					return this.convertTo(ntype).opBinary!op(r.convertTo(ntype));
				}
				static if(op=="%"){ // TODO: make more efficient
					if(type==ℝ(true)) return makeReal(((fval%r.fval)+r.fval)%r.fval); // TODO: make numerically sound
					alias abs=util.abs;
					alias floor=util.floor;
					if(type==ℚt(true)) return makeRational(qval-ℚ(floor(qval/r.qval))*r.qval);
					if(type==ℤt(true)) return makeInteger(floormod(zval, r.zval));
					if(auto intTy=isFixedIntTy(type)){
						if(intTy.isSigned) return makeInt(ntype,floormod(intval,r.intval));
						else{
							if(r.eqZImpl) return this;
							return makeUint(ntype,uintval%r.uintval);
						}
					}
				}else{
					static if(is(typeof(mixin(`fval `~op~` r.fval`))))
						if(type==ℝ(true)) return makeReal(mixin(`fval `~op~` r.fval`));
					static if(is(typeof(mixin(`qval `~op~` r.qval`))))
						if(type==ℚt(true)) return makeRational(mixin(`qval `~op~` r.qval`));
					static if(is(typeof(mixin(`zval `~op~` r.zval`))))
						if(type==ℤt(true)) return makeInteger(mixin(`zval `~op~` r.zval`));
					static if(is(typeof(mixin(`intval `~op~` r.intval`))))
						if(isInt(type)) return makeInt(ntype,mixin(`intval `~op~` r.intval`));
					static if(is(typeof(mixin(`uintval `~op~` r.uintval`))))
						if(isUint(type)) return makeUint(ntype,mixin(`uintval `~op~` r.uintval`));
				}
				static if(op=="div"){
					final switch(tag){
						case Tag.fval: return (this/r).floor();
						case Tag.qval: return makeInteger(.floor(qval/r.qval));
						case Tag.zval: return makeInteger(floordiv(zval,r.zval));
						case Tag.intval: return makeInt(type,BitInt!true(intval.nbits,floordiv(intval.val,r.intval.val)));
						case Tag.uintval: return makeUint(ntype,uintval/r.uintval);
						case Tag.bval: return makeBool(bval/r.bval);
						case Tag.closure,Tag.array_,Tag.record,Tag.quval: break;
					}
				}
				static if(is(typeof((bool a,bool b){ bool c=mixin(`a `~op~` b`); })))
					if(type==Bool(true)&&r.type==Bool(true)) return makeBool(mixin(`bval `~op~` r.bval`));
			}
			enforce(0,text("`",op,"` for types ",this.type," and ",r.type," is not yet supported"));
			assert(0);
		}
		Value opBinary(string op)(long b){
			return mixin(`this `~op~` makeInteger(ℤ(b))`);
		}
		Value opBinary(string op)(ℤ b){
			return mixin(`this `~op~` makeInteger(b)`);
		}
		bool eqZImpl(){
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.uintval,Tag.intval,Tag.bval]){
					case t:
						return mixin(text(t,`==0`));
				}
				case Tag.array_,Tag.record,Tag.closure: break;
				case Tag.quval: break;
			}
			enforce(0,text("`=0`/`≠0` for type ",this.type," is not yet supported"));
			assert(0);
		}
		Value eqZ(){
			if(!isClassical()) return makeQuval(Bool(false),new MemberFunctionQVal!"eqZ"(this));
			return makeBool(eqZImpl());
		}
		bool neqZImpl(){ return !eqZImpl(); }
		Value neqZ(){
			if(!isClassical()) return makeQuval(Bool(false),new MemberFunctionQVal!"neqZ"(this));
			return makeBool(neqZImpl());
		}
		Value compare(string op)(Value r){
			if(!isClassical()||!r.isClassical()) return makeQuval(Bool(false),new CompareQVal!op(this,r));
			if(tag==Tag.array_&&r.tag==Tag.array_){
				static if(op=="==") if(array_.length!=r.array_.length) return makeBool(false);
				static if(op=="!=") if(array_.length!=r.array_.length) return makeBool(true);
				int equalPrefix=0;
				for(;equalPrefix<min(array_.length,r.array_.length);equalPrefix++)
					if(array_[equalPrefix].compare!"!="(r.array_[equalPrefix]).neqZImpl) break;
				static if(op!="=="&&op!="!="){
					if(util.among(equalPrefix,array_.length,r.array_.length)){
						if(array_.length==r.array_.length){
							enum equalAllowed=op=="<="||op==">=";
							return makeBool(equalAllowed);
						}else return makeBool(mixin(`array_.length `~op~` r.array_.length`));
					}else return array_[equalPrefix].compare!op(r.array_[equalPrefix]);
				}else{
					static if(op=="==") return makeBool(equalPrefix==array_.length);
					else return makeBool(equalPrefix!=array_.length);
				}
			}
			enum supportedTags=[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval];
			enum unsupportedTags=[Tag.closure,Tag.array_,Tag.record,Tag.quval];
			static bool compareImpl(S,T)(S a,T b){
				static if(is(S==T)||(is(S==ℚ)&&is(T==ℤ)||is(S==ℤ)&&is(T==ℚ))||
				          is(S==BitInt!true)||is(S==BitInt!false)||
				          is(T==BitInt!true)||is(T==BitInt!false))
					return mixin(text(`a `,op,` b`));
				else static if(is(S==double)){
					static if(is(T==ℚ)||is(T==ℤ)) return mixin(text(`a `,op,` toReal(b)`)); // TODO: improve
					else static if(is(T==bool)) return mixin(text(`a `,op,` to!R(b)`));
					else static assert(0);
				}else static if(is(T==double)){
					static if(is(S==ℚ)||is(S==ℤ)) return mixin(text(`toReal(a) `,op,` b`));
					else static if(is(S==bool)) return mixin(text(`to!R(a) `,op,` b`));
					else static assert(0);
				}else static if(is(S==bool)) return compareImpl(ℤ(cast(int)a),b);
				else static if(is(T==bool)) return compareImpl(a,ℤ(cast(int)b));
				else static assert(0);
			}
			Louter: final switch(tag){
				static foreach(ltag;supportedTags){
					case ltag:
						final switch(r.tag){
							static foreach(rtag;supportedTags){
								case rtag: return makeBool(mixin(text(`compareImpl(`,ltag,`,r.`,rtag,`)`)));
							}
							static foreach(rtag;unsupportedTags){
								case rtag: break Louter;
							}
						}
				}
				static foreach(tag;unsupportedTags){
					case tag: break Louter;
				}
			}
			enforce(0,text("`",op,"` for types ",this.type," ",r.type," is not yet supported"));
			assert(0);
		}
		Value lt(Value r){ return compare!"<"(r); }
		Value le(Value r){ return compare!"<="(r); }
		Value gt(Value r){ return compare!">"(r); }
		Value ge(Value r){ return compare!">="(r); }
		Value eq(Value r){ return compare!"=="(r); }
		Value neq(Value r){ return compare!"!="(r); }
		Value floor(){
			final switch(tag){
				case Tag.qval: return makeInteger(.floor(qval));
				case Tag.zval,Tag.bval: return this;
				case Tag.intval,Tag.uintval: break;
				case Tag.fval: return makeInteger(.floor(fval.toℚ));
				case Tag.closure,Tag.array_,Tag.record: break;
				case Tag.quval: return makeQuval(type==ℝ(true)?ℤt(true):type,new MemberFunctionQVal!"floor"(this));
			}
			enforce(0,text("`floor` for type ",this.type," is not yet supported"));
			assert(0);
		}
		Value ceil(){
			final switch(tag){
				case Tag.qval: return makeInteger(.ceil(qval));
				case Tag.zval,Tag.bval: return this;
				case Tag.intval,Tag.uintval: break;
				case Tag.fval: return makeInteger(.ceil(fval.toℚ)); // TODO: more efficient variant?
				case Tag.closure,Tag.array_,Tag.record: break;
				case Tag.quval: return makeQuval(type==ℝ(true)?ℤt(true):type,new MemberFunctionQVal!"ceil"(this));
			}
			enforce(0,text("̈`ceil` for type ",this.type," is not yet supported"));
			assert(0);
		}
		Value realFunction(alias f)(){
			final switch(tag){
				case Tag.qval,Tag.zval,Tag.bval: return convertTo(ℝ(true)).realFunction!f();
				case Tag.fval: return makeReal(f(fval));
				case Tag.intval,Tag.uintval: break;
				case Tag.closure,Tag.array_,Tag.record: break;
				case Tag.quval: return makeQuval(type==ℝ(true)?ℤt(true):type,new FunctionQVal!(v=>v.realFunction!f())(this));
			}
			enforce(0,text("real functions for type ",this.type," are not yet supported"));
			assert(0);
		}
		Value realFunction2(alias f)(Value b){
			auto a=this;
			if(!util.among(a.tag,Tag.qval,Tag.zval,Tag.bval,Tag.fval)||
			   !util.among(b.tag,Tag.qval,Tag.zval,Tag.bval,Tag.fval)){
				enforce(0,text("real binary functions for types `",a.type,"` and `",b.type,"` are not yet supported"));
			}
			if(a.tag!=Tag.fval) a=a.convertTo(ℝ(true));
			if(b.tag!=Tag.fval) b=b.convertTo(ℝ(true));
			enforce(a.tag==Tag.fval&&b.tag==Tag.fval,"cannot convert arguments to real numbers");
			return makeReal(f(a.fval,b.fval));
		}
		Value realFunction3(alias f)(Value b,Value c){
			auto a=this;
			if(!util.among(a.tag,Tag.qval,Tag.zval,Tag.bval,Tag.fval)||
			   !util.among(b.tag,Tag.qval,Tag.zval,Tag.bval,Tag.fval)||
			   !util.among(c.tag,Tag.qval,Tag.zval,Tag.bval,Tag.fval)){
				enforce(0,text("real ternary functions for types `",a.type,"`, `",b.type,"` and `",c.type,"` are not yet supported"));
			}
			if(a.tag!=Tag.fval) a=a.convertTo(ℝ(true));
			if(b.tag!=Tag.fval) b=b.convertTo(ℝ(true));
			if(c.tag!=Tag.fval) c=c.convertTo(ℝ(true));
			enforce(a.tag==Tag.fval&&b.tag==Tag.fval&&c.tag==Tag.fval,"cannot convert arguments to real numbers");
			return makeReal(f(a.fval,b.fval,c.fval));
		}
		Value sqrt(){ return realFunction!(.sqrt)(); }
		Value cbrt(){ return realFunction!(.cbrt)(); }
		Value hypot2(Value b){ return realFunction2!(.hypot)(b); }
		Value hypot3(Value b,Value c){ return realFunction3!(.hypot)(b,c); }
		Value exp(){ return realFunction!(.exp)(); }
		Value exp2(){ return realFunction!(.exp2)(); }
		Value expm1(){ return realFunction!(.expm1)(); }
		Value log(){ return realFunction!(.log)(); }
		Value log1p(){ return realFunction!(.log1p)(); }
		Value log10(){ return realFunction!(.log10)(); }
		Value log2(){ return realFunction!(.log2)(); }
		Value sin(){ return realFunction!(.sin)(); }
		Value asin(){ return realFunction!(.asin)(); }
		//Value csc(){ return realFunction!(.csc)(); }
		//Value acsc(){ return realFunction!(.acsc)(); }
		Value cos(){ return realFunction!(.cos)(); }
		Value acos(){ return realFunction!(.acos)(); }
		//Value sec(){ return realFunction!(.sec)(); }
		//Value asec(){ return realFunction!(.asec)(); }
		Value tan(){ return realFunction!(.tan)(); }
		Value atan(){ return realFunction!(.atan)(); }
		Value atan2(Value x){ return realFunction2!(.atan2)(x); }
		//Value cot(){ return realFunction!(.cot)(); }
		//Value acot(){ return realFunction!(.acot)(); }
		Value sinh(){ return realFunction!(.sinh)(); }
		Value asinh(){ return realFunction!(.asinh)(); }
		Value cosh(){ return realFunction!(.cosh)(); }
		Value acosh(){ return realFunction!(.acosh)(); }
		Value tanh(){ return realFunction!(.tanh)(); }
		Value atanh(){ return realFunction!(.atanh)(); }
		Value erf(){ return realFunction!(.erf)(); }
		Value erfc(){ return realFunction!(.erfc)(); }
		Value tgamma(){ return realFunction!(.tgamma)(); }
		Value lgamma(){ return realFunction!(.lgamma)(); }

		Value realFunctionFP(alias f,bool circular1,R a,R b,bool circular2,R c,R d,T...)(ℤ size,Expression type,T args){
			final switch(tag){
				case Tag.intval:
					enforce(circular1,"signed non-circular fixed-point functions are not yet supported");
					auto m=intval.nbits;
					enforce(0<=size&&size<=size_t.max,"number of bits is too large");
					auto n=size.to!size_t;
					static assert(is(R==double));
					enforce(a==0&&b==2*PI,"input ranges other than [0,2π) are not yet supported for circular signed fixed-point functions");
					auto x=a+intval.val.toDouble()/(2.0^^m-!circular1)*(b-a);
					static if(circular1){
						while(x<a) x+=b-a;
						while(x>b) x-=b-a;
					}
					if(x<a) x=a;
					if(x>b) x=b;
					if(isInt(type)){
						enforce(circular2&&c==0&&d==2*PI,"output ranges other than circular [0,2π) are not yet supported for signed fixed-point functions ");
						return makeInt(type.getClassical(),BitInt!true(n,.round(toℚ((f(x,args)-c)/(d-c))*ℚ(ℤ(2)^^n-ℤ(cast(int)!circular2)))));
					}else return makeUint(type.getClassical(),BitInt!false(n,.round(toℚ((f(x,args)-c)/(d-c))*ℚ(ℤ(2)^^n-ℤ(cast(int)!circular2)))));
				case Tag.uintval:
					auto m=uintval.nbits;
					enforce(0<=size&&size<=size_t.max,"number of bits is too large");
					auto n=size.to!size_t;
					static assert(is(R==double));
					auto x=a+uintval.val.toDouble()/(2.0^^m-!circular1)*(b-a);
					static if(circular1){
						while(x<a) x+=b-a;
						while(x>b) x-=b-a;
					}
					if(x<a) x=a;
					if(x>b) x=b;
					if(isInt(type)){
						enforce(circular2&&c==0&&d==2*PI,"output ranges other than circular [0,2π) are not yet supported for signed fixed-point functions ");
						return makeInt(type.getClassical(),BitInt!true(n,.round(toℚ((f(x,args)-c)/(d-c))*ℚ(ℤ(2)^^n-ℤ(cast(int)!circular2)))));
					}else return makeUint(type.getClassical(),BitInt!false(n,.round(toℚ((f(x,args)-c)/(d-c))*ℚ(ℤ(2)^^n-ℤ(cast(int)!circular2)))));
				case Tag.quval:
					static fun(T...)(Value v,T args){ return v.realFunctionFP!(f,circular1,a,b,circular2,c,d)(args); }
					return makeQuval(type,new FunctionQVal!(fun,ℤ,Expression,T)(this,size,type.getClassical(),args));
				case Tag.qval,Tag.zval,Tag.bval,Tag.fval: break;
				case Tag.closure,Tag.array_,Tag.record: break;
			}
			enforce(0,text("fixed-point functions for type ",this.type," are not yet supported"));
			assert(0);
		}
		enum zeroToOne=Seq!(false,0.0,1.0);
		enum minusOneToOne=Seq!(false,-1.0,1.0);
		enum angleRange=Seq!(true,0.0,2*PI);
		Value sinQ(ℤ size,Expression type){ return realFunctionFP!(.sin,angleRange,minusOneToOne)(size,type); }
		Value asinQ(ℤ size,Expression type){ return realFunctionFP!(.asin,minusOneToOne,angleRange)(size,type); }
		Value cosQ(ℤ size,Expression type){ return realFunctionFP!(.cos,angleRange,minusOneToOne)(size,type); }
		Value acosQ(ℤ size,Expression type){ return realFunctionFP!(.acos,minusOneToOne,angleRange)(size,type); }

		Value invQ(ℤ size,Expression type,R c){
			static R divQ(R x,R c){
				if(x<=c) return 1;
				return c/x;
			}
			return realFunctionFP!(divQ,zeroToOne,zeroToOne)(size,type,c);
		}

		Value classicalValue(Σ state){
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval,Tag.bval]){
					case t:
						assert(isClassical);
						return this;
				}
				case Tag.closure:
					return makeClosure(type.getClassical(),Closure(closure.fun,closure.context?[closure.context.classicalValue(state)].ptr:null));
				case Tag.array_:
					return makeArray(type.getClassical(),array_.map!(x=>x.classicalValue(state)).array);
				case Tag.record:
					Record nrecord;
					foreach(k,v;record) nrecord[k]=v.classicalValue(state);
					return makeRecord(type.getClassical(),nrecord);
				case Tag.quval: return quval.get(state);
			}
		}
		bool asBoolean()in{
			assert(type==Bool(true),text(type));
		}do{
			return bval;
		}
		bool isℤ(){
			return isClassical()&&(isFixedIntTy(type)||type==ℤt(true)||type==Bool(true));
		}
		ℤ asℤ()in{
			assert(isℤ());
		}do{
			if(type==ℤt(true)) return zval;
			if(auto intTy=isFixedIntTy(type)) return intTy.isSigned ? intval.val : uintval.val;
			if(type==Bool(true)) return ℤ(cast(int)bval);
			enforce(0,text("converting `",type,"` to `!ℤ` not yet supported"));
			assert(0);
		}
		bool isℚ(){
			return isℤ()||type==ℚt(true);
		}
		ℚ asℚ()in{
			assert(isℚ());
		}do{
			if(type==ℚt(true)) return qval;
			return ℚ(asℤ());
		}
		bool isℝ(){
			return isℚ()||type==ℝ(true);
		}
		R asℝ()in{
			assert(isℝ());
		}do{
			if(type==ℝ(true)) return fval;
			static assert(is(R==double));
			return toDouble(asℚ());
		}
		struct FormattingOptions{
			enum FormattingType{
				default_,
				dump,
			}
			FormattingType type;
		}
		string toStringImpl(FormattingOptions opt){
			if(!type) return "Value.init";
			if(isTypeTy(type)||isQNumericTy(type)) return "_";
			final switch(tag){
				static foreach(t;[Tag.fval,Tag.qval,Tag.zval,Tag.intval,Tag.uintval]){
					case t:
						return text(mixin(text(t)));
				}
				case Tag.bval: return bval?"1":"0";
				case Tag.closure: return text("⟨",text(closure.fun)[4..$],(closure.context?text(",",closure.context.toStringImpl(opt)):""),"⟩");
				case Tag.array_:
					string prn="()";
					if(cast(ArrayTy)type) prn="[]";
					return text(prn[0],array_.map!(x=>x.toStringImpl(opt)).join(","),(array_.length==1&&prn=="()"?",":""),prn[1]);
				case Tag.record:
					auto r="{";
					foreach(k,v;record) r~=text(k," ↦ ",v.toStringImpl(opt),",");
					return r.length!=1?r[0..$-1]~"}":"{}";
				case Tag.quval: return quval.toString();
			}
		}
		string toBasisStringImpl()in{
			assert(isClassical(),text(this));
		}do{
			return text("|",toStringImpl(FormattingOptions.init),"⟩");
		}
		string toString(){
			return text(toStringImpl(FormattingOptions.init),":",type);
		}
	}
	static assert(Value.sizeof==Type.sizeof+Value.bits.sizeof);
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
		static Value makeRecord(Record record){
		Value r;
		r.type=contextTy(false);
		r.record=record;
		return r;
	}
	static Value makeRecord(Expression type,Record record){
		Value r;
		r.type=type;
		enforce(r.tag==Value.Tag.record);
		r.record=record;
		return r;
	}
	static Value makeClosure(Expression type,Closure closure){
		Value r;
		r.type=type;
		enforce(r.tag==Value.Tag.closure);
		r.closure=closure;
		return r;
	}
	static Value makeQuval(Expression type,QVal quval){
		Value r;
		r.type=type;
		enforce(r.tag==Value.Tag.quval);
		r.quval=quval;
		return r;
	}
	static Value makeReal(R value){
		enforce(!isNaN(value),text("invalid argument"));
		enforce(value<R.infinity,text("positive floating point overflow"));
		enforce(value>-R.infinity,text("negative floating point overflow"));
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
	static Value makeInt(Expression type,BitInt!true value){
		Value r;
		r.type=type;
		assert(r.tag==Value.Tag.intval,text(type));
		r.intval=value;
		return r;
	}
	static Value makeUint(Expression type,BitInt!false value){
		Value r;
		r.type=type;
		assert(r.tag==Value.Tag.uintval);
		r.uintval=value;
		return r;
	}
	static Value makeBool(bool value){
		Value r;
		r.type=Bool(true);
		r.bval=value;
		return r;
	}
	static Value nullValue(){
		return Value.init;
	}
	static Value typeValue(Expression value)in{
		assert(isType(value)||isQNumeric(value));
	}do{
		Value r;
		r.type=value.type;
		return r;
	}
	static Value π(){ return makeReal(PI); }

	alias Σ=Sigma;
	struct Sigma{
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
		void forget(Ref ref_,Value v){
			auto val=qvars[ref_];
			enforce(val==v.classicalValue(this).convertTo(val.type),"bad forget"); // TODO: better error reporting
			forget(ref_);
		}
		hash_t toHash(){ return qvars.toHash(); }
		void relabel(Ref[Ref] relabeling){
			typeof(qvars) nqvars; // TODO: apply permutation in place
			foreach(ref_,qvar;qvars){
				if(auto to=ref_ in relabeling) nqvars[*to]=qvar;
				else nqvars[ref_]=qvar;
			}
			qvars=nqvars;
		}
		struct Sortable{
			Q!(Ref,Value)[] values;
			private static int cmp(Value a,Value b){
				enforce(a.type==b.type,"encountered incomparable values for output sorting");
				if(util.among(a.tag,Value.Tag.closure,Value.Tag.record)) return 0; // TODO: compare those
				return a.lt(b).neqZImpl?-1:a.eq(b).neqZImpl?0:1;
			}
			int opCmp(Sortable rhs){
				if(values.length!=rhs.values.length) return 0;
				//enforce(values.length==rhs.values.length);
				foreach(i;0..values.length){
					enforce(values[i][0]==rhs.values[i][0],"encountered incompatible locations for output sorting");
					int current=cmp(values[i][1],rhs.values[i][1]);
					if(current!=0) return current;
				}
				return 0;
			}
			string toStringImpl(FormattingOptions opt){
				if(!values.length) return "|⟩";
				return values.map!(t=>text("|",t[1].toStringImpl(opt),"⟩",lowNum(t[0]))).join("⊗");
			}
		}
		Sortable toSortable(){
			Q!(Ref,Value)[] values;
			foreach(k,v;qvars) values~=q(k,v);
			sort!"a[0]<b[0]"(values);
			return Sortable(values);
		}
		string toStringImpl(FormattingOptions opt){
			return toSortable().toStringImpl(opt);
		}
		string toString(){ return toStringImpl(FormattingOptions.init); }
	}
	static QState empty(){
		return QState.init;
	}
	static QState unit(){
		QState qstate;
		qstate.state[Σ.init]=C(1.0);
		return qstate;
	}
	QState pushFrame(){
		Record nvars,nnvars;
		foreach(k,v;vars) nvars[k]=v.inFrame();
		nnvars["`parent"]=makeRecord(nvars);
		return QState(state,nnvars);
	}
	QState popFrame(QVar[] previousPopFrameCleanup){
		foreach(qvar;popFrameCleanup) qvar.forget(this);
		auto frame=vars["`parent"];
		enforce(frame.tag==Value.Tag.record,"frame is a bad value");
		Record nvars=frame.record.dup;
		return QState(state,nvars,previousPopFrameCleanup);
	}
	static Value inFrame(Value v){
		return v.inFrame();
	}
	void passParameter(string prm,bool isConst,Value rhs){
		enforce(prm!in vars,"parameter already defined");
		bool cleanUp=isConst;
		vars[prm]=rhs.toVar(this,cleanUp); // TODO: this may be inefficient (it iterates over arrays to check whether components are variables)
	}
	void passContext(FunctionDef fd,Value rhs){
		enforce(!!fd.ftype);
		auto captureAnnotation=fd.ftype.captureAnnotation;
		bool isMoved=captureAnnotation==CaptureAnnotation.moved||captureAnnotation==CaptureAnnotation.once;
		enforce(rhs.tag==Value.Tag.record);
		foreach(meaning,_;fd.captures){
			auto name=meaning.getName;
			enforce(name in rhs.record,text("missing capture ",name," in ",rhs.record));
			auto val=rhs.record[name];
			if(isMoved&&fd.isConsumedCapture(meaning))
				rhs.record.remove(name);
			vars[name]=val;
		}
		auto ctx=fd.contextName;
		enforce(ctx!in vars,"context already defined");
		vars[ctx]=rhs;
	}
	Value call(FunctionDef fun,Value thisExp,Value arg,Scope sc,Value* context,Expression type,Location loc){
		Value fix(Value arg){
			if(type.isClassical()&&!arg.isClassical()) return measure(arg,false); // TODO: improve simulator so this is not needed
			return arg;
		}
		enforce(!thisExp.isValid,"method calls not yet supported");
		if(string prim=isPrimitive(fun)){
			return callPrimitive(prim, arg, type, loc);
		}
		enforce(fun.body_,text("need function body to simulate function ",fun));
		auto ncur=pushFrame();
		enforce(!fun.isConstructor,"constructor calls not yet supported");
		if(fun.boolAttribute(Id.s!"trace")){
			string[2] paren = fun.isSquare ? ["[", "]"] : arg.tag==Value.Tag.array_ ? ["", ""] : ["(", ")"];
			string name = fun.getName;
			if(name.length==0) {
				auto parent = fun;
				while(parent && parent.getName.length==0) parent = parent.scope_.getFunction();
				name = (parent ? parent.getName : "") ~ ".lambda";
			}
			FormattingOptions opt = {type: FormattingType.dump};
			writeln(name ~ paren[0] ~ arg.toStringImpl(opt) ~ paren[1]);
			stdout.flush();
		}
		if(fun.isNested){
			assert(!!context);
			ncur.passContext(fun,*context);
		}else assert(!context);
		if(fun.isTuple){
			enforce(arg.tag==Value.Tag.array_,"argument is not a tuple");
			auto args=iota(fun.params.length).map!(i=>inFrame(arg.array_[i]));
			foreach(i,prm;fun.params)
				ncur.passParameter(prm.getName,prm.isConst,inFrame(arg.array_[i])); // TODO: faster: parallel assignment to parameters
		}else{
			assert(fun.params.length==1,"encountered wrong number of parameters");
			ncur.passParameter(fun.params[0].getName,fun.params[0].isConst,inFrame(arg));
		}
		auto intp=Interpreter!QState(fun,fun.body_,ncur,true);
		auto nnstate=QState.empty();
		nnstate.popFrameCleanup=ncur.popFrameCleanup;
		try{
			intp.runFun(nnstate);
		}catch(LocalizedException ex){
			ex.stackTrace~=FrameInfo(fun, loc);
			throw ex;
		}
		this=nnstate.popFrame(this.popFrameCleanup);
		return fix(nnstate.vars["`value"]);
	}
	Value callPrimitive(string prim, Value arg, Expression type, Location loc){
		switch(prim){
			case "dump":
				dump(0);
				stdout.flush();
				return makeTuple(.unit,[]);
			case "exit":
				enforce(0, "terminated by exit call");
				assert(0);
			case "dup":
				return arg.dup(this);
			case "vector":
				enforce(arg.tag==Value.Tag.array_ && arg.array_.length==2,"wrong number of arguments passed to `vector`");
				return vector(type, arg[ℤ(0)], arg[ℤ(1)]);
			case "M":
				return measure(arg);
			case "H":
				return H(arg);
			case "X":
				return X(arg);
			case "Y":
				return Y(arg);
			case "Z":
				return Z(arg);
			case "P":
				return phase(arg);
			case "rX":
				enforce(arg.tag==Value.Tag.array_ && arg.array_.length==2,"wrong number of arguments passed to `rX`");
				return rX(arg[ℤ(0)], arg[ℤ(1)]);
			case "rY":
				enforce(arg.tag==Value.Tag.array_ && arg.array_.length==2,"wrong number of arguments passed to `rY`");
				return rY(arg[ℤ(0)], arg[ℤ(1)]);
			case "rZ":
				enforce(arg.tag==Value.Tag.array_ && arg.array_.length==2,"wrong number of arguments passed to `rZ`");
				rZ(arg[ℤ(0)], arg[ℤ(1)].dup(this)).forget(this);
				return makeTuple(.unit,[]);
			case "print": {
				FormattingOptions opt={type: FormattingType.dump};
				writeln(arg.toStringImpl(opt)); stdout.flush();
				return makeTuple(.unit,[]);
			}
				static foreach(f;["floor","ceil","sqrt","cbrt","exp","exp2","expm1","log","log1p","log10","log2","sin","asin","cos","acos","tan","atan","sinh","asinh","cosh","acosh","tanh","atanh","erf","erfc","tgamma","lgamma"]){
				case "real." ~ f:
					return mixin(`arg.`~f)();
			}
			static foreach(f;["atan2","hypot2"]){
				case "real." ~ f:
					enforce(arg.tag==Value.Tag.array_ && arg.array_.length==2,"wrong number of arguments passed to `"~f~"`");
					return mixin(`arg[ℤ(0)].`~f)(arg[ℤ(1)]);
			}
			static foreach(f;["hypot3"]){
				case "real." ~ f:
					enforce(arg.tag==Value.Tag.array_ && arg.array_.length==3,"wrong number of arguments passed to `"~f~"`");
					return mixin(`arg[ℤ(0)].`~f)(arg[ℤ(1)],arg[ℤ(2)]);
			}
			static foreach(f;["sin","asin","cos","acos"]){
				case "qfixed."~f:
					enforce(arg.tag==Value.Tag.array_ && arg.array_.length==2,"wrong number of arguments passed to `rZ`");
					return mixin(`arg[ℤ(1)].`~f~`Q`)(arg[ℤ(0)].asℤ(), type);
			}
			case "qfixed.inv": {
				enforce(arg.tag==Value.Tag.array_ && arg.array_.length==3,"wrong number of arguments passed to `qfixed.inv`");
				QState.Value n = arg[ℤ(0)];
				QState.Value x = arg[ℤ(1)];
				auto c = arg[ℤ(2)].asℝ();
				enforce(0 <= c, "`invQ` argument negative");
				return x.invQ(n.asℤ(), type, c);
			}
			default:
				enforce(0, text("primitive `",prim,"` not supported"));
				assert(0);
		}
	}
	Value call(Value fun,Value arg,Expression type,Location loc){
		enforce(fun.tag==Value.Tag.closure,"bad value for function in call");
		bool cleanup=false;
		if(auto ft=cast(FunTy)fun.type){
			auto context=fun.closure.context;
			if(context&&ft.captureAnnotation==CaptureAnnotation.const_){ // non-linear function
				if(auto cvar=fun.closure.fun.context){ // can be null if function has no body
					fun=fun.dup(this); // TODO: avoid this
					cleanup=true;
				}
			}
		}
		scope(exit) if(cleanup) fun.forget(this); // TODO: avoid this
		return call(fun.closure.fun,nullValue,arg,null,fun.closure.context,type,loc);
	}
	QState assertTrue(Value val)in{
		assert(val.type==Bool(true));
	}do{
		if(!val.asBoolean) enforce(0,"assertion failure");
		return this;
	}
	Value readLocal(string s,bool constLookup){
		enforce(s in vars,text("variable `",s,"` not found"));
		auto r=vars[s];
		if(!constLookup) vars.remove(s);
		return r;
	}
	static Value readField(Value r,string s,bool constLookup){
		assert(r.type==contextTy(false));
		auto res=r.record[s];
		if(!constLookup&&!res.isClassical()) r.record.remove(s); // TODO: ok?
		return res;
	}
	Value makeFunction(FunctionDef fd,Value* context){
		return makeClosure(fd.ftype,Closure(fd,context));
	}
	Value makeFunction(FunctionDef fd,Scope sc){
		Value* context=null;
		if(fd.isNested) context=[buildContextFor(this,fd,sc)].ptr;
		return makeFunction(fd,context);
	}
	void declareFunction(FunctionDef fd){
		vars[fd.getName]=nullValue;
		auto result=makeFunction(fd,fd.scope_);
		assert(result.tag==Value.Tag.closure);
		if(result.closure.context){
			assert(result.closure.context.tag==Value.Tag.record);
			foreach(k,ref v;result.closure.context.record)
				if(!v.isValid) enforce(0,"invalid nested function");
		}
		vars[fd.getName]=result;
	}
	static Value ite(Value cond,Value then,Value othw)in{
		assert(then.type.getClassical==othw.type.getClassical);
		assert(cond.type is Bool(false));
	}do{
		static class IteQVal: QVal{
			Value cond,then,othw;
			this(Value cond,Value then,Value othw){
				this.cond=cond, this.then=then, this.othw=othw;
			}
			override Value get(ref Σ s){
				return cond.classicalValue(s).asBoolean?then.classicalValue(s):othw.classicalValue(s);
			}
		}
		auto type=then.type;
		final switch(Value.getTag(type)){
			case Value.Tag.array_:
				enforce(then.tag==Value.Tag.array_&&othw.tag==Value.Tag.array_,"incompatible values in branches of quantum if-then-else expression");
				enforce(then.array_.length==othw.array_.length,"encountered quantum-dependent tuples lengths");
				return makeArray(type,zip(then.array_,othw.array_).map!(x=>ite(cond,x[0],x[1])).array);
			case Value.Tag.closure: enforce(0,"quantum-conditional closures not yet supported"); assert(0);
			case Value.Tag.record: enforce(0,"quantum-conditional closures not yet supported"); assert(0);
			case Value.Tag.uintval,Value.Tag.intval,Value.Tag.bval:
				type=type.getQuantum();
				enforce(isQuantum(type));
				goto case;
			case Value.Tag.quval: return makeQuval(type,new IteQVal(cond,then.convertTo(type),othw.convertTo(type)));
			case Value.Tag.fval,Value.Tag.qval,Value.Tag.zval:
				enforce(0,"bad type for quantum if-then-else expression");
				assert(0);
		}
	}
	Value makeQVar(Value v)in{
		assert(!v.isClassical());
	}do{
		v=v.consumeOnRead();
		auto ref_=Σ.curRef++;
		static Σ addVariable(Σ s,Σ.Ref ref_,Value v){
			enforce(ref_ !in s.qvars,text("tried to redefine variable at location `%s`",ref_));
			s.assign(ref_,v);
			return s;
		}
		this=map!addVariable(ref_,v);
		return makeQuval(v.type,new QVar(ref_));
	}
	private void assignTo(Σ.Ref var,Value rhs){
		static Σ assign(Σ s,Σ.Ref var,Value rhs){
			s.assign(var,rhs);
			return s;
		}
		this=map!(assign,false)(var,rhs);
	}
	private void forget(Σ.Ref var,Value rhs){
		static Σ forgetImpl(Σ s,Σ.Ref var,Value rhs){
			s.forget(var,rhs);
			return s;
		}
		this=map!forgetImpl(var,rhs);
	}
	private void forget(Σ.Ref var){
		static Σ forgetImpl(Σ s,Σ.Ref var){
			s.forget(var);
			return s;
		}
		this=map!forgetImpl(var);
	}
	static if(language==silq){
		void forgetVars(Declaration[] forgottenVars){
			if(!state.length) return;
			foreach(var;forgottenVars){
				auto name=var.getName;
				vars[name].forget(this);
				vars.remove(name);
			}
		}
	}
	void assignTo(ref Value var,Value rhs){
		var.assign(this,rhs);
	}
	void catAssignTo(ref Value var,Value rhs){
		enforce(var.tag==QState.Value.Tag.array_&&rhs.tag==QState.Value.Tag.array_,"bad values for concat assignment");
		var.array_~=rhs.array_;
	}
	void assignTo(string lhs,Value rhs){
		if(lhs in vars) assignTo(vars[lhs],rhs);
		else vars[lhs]=rhs.toVar(this,false);
	}
	void catAssignTo(string lhs,Value rhs){
		enforce(lhs in vars);
		enforce(vars[lhs].tag==QState.Value.Tag.array_&&rhs.tag==QState.Value.Tag.array_,"bad values for concat assignment");
		vars[lhs].array_~=rhs.array_;
	}
	Value H(Value x){
		return x.applyUnitary!hadamardUnitary(this,Bool(false));
	}
	Value X(Value x){
		if(x.isClassical()) return x.eqZ;
		return x.applyUnitary!xUnitary(this,Bool(false));
	}
	Value Y(Value x){
		return x.applyUnitary!yUnitary(this,Bool(false));
	}
	Value Z(Value x){
		return x.applyUnitary!zUnitary(this,Bool(false));
	}
	Value phase(Value φ){
		φ=φ.convertTo(ℝ(true));
		typeof(state) new_;
		foreach(k,v;state){
			new_[k]=cast(C)std.complex.expi(φ.fval)*v;
		}
		state=new_;
		return makeTuple(ast.type.unit,[]);
	}
	Value rot(alias unitary)(Value φ, Value x){
		φ=φ.convertTo(ℝ(true));
		return x.applyUnitary!unitary(this,Bool(false),φ.fval);
	}
	Value rX(Value φ, Value x){
		return rot!rXUnitary(φ, x);
	}
	Value rY(Value φ, Value x){
		return rot!rYUnitary(φ, x);
	}
	Value rZ(Value φ, Value x){
		return rot!rZUnitary(φ, x);
	}
	Value array_(Expression type, Value len, Value val){
		enforce(len.isℤ(),"bad array length");
		return makeArray(type,iota(smallValue(len.asℤ)).map!(_=>val.dup(this)).array);
	}
	alias vector=array_;
	Value reverse(ref QState qstate,Expression type,Value arg){
		import ast.reverse;
		enforce(arg.tag==Value.Tag.closure,text("bad value for reverse: ",arg));
		return makeClosure(type,Closure(reverseFunction(arg.closure.fun),arg.closure.context));
		//return qstate.makeFunction(reverseFunction(arg.closure.fun));
	}
	Value measure(Value arg,bool renormalize=true){
		MapX!(Value,R) candidates;
		R one=0;
		foreach(k,v;state){
			auto candidate=arg.classicalValue(k);
			if(candidate!in candidates) candidates[candidate]=sqAbs(v);
			else candidates[candidate]+=sqAbs(v);
			one+=sqAbs(v);
		}
		Value result;
		R random=uniform!"[]"(R(0),one);
		R current=0.0;
		bool ok=false;
		foreach(k,v;candidates){
			current+=v;
			if(current>=random){
				result=k;
				ok=true;
				break;
			}
		}
		if(!ok){
			foreach(k,v;candidates){
				result=k; // TODO: distribute rounding error equally among candidates?
				break;
			}
		}
		MapX!(Σ,C) nstate;
		R total=0.0f;
		foreach(k,v;state){
			auto candidate=arg.classicalValue(k);
			if(candidate!=result) continue;
			total+=sqAbs(v);
			nstate[k]=v;
		}
		if(renormalize){
			total=sqrt(total);
			foreach(k,ref v;nstate) v/=total;
			state=nstate;
		}
		arg.forget(this);
		return result;
	}
}


// TODO: move this to semantic_, as a rewrite
QState.Value readVariable(QState)(ref QState qstate,VarDecl var,Scope from,bool constLookup){
	QState.Value r=getContextFor(qstate,var,from);
	if(r) return qstate.readField(r,var.getName,constLookup);
	return qstate.readLocal(var.getName,constLookup);
}
QState.Value getContextFor(QState)(ref QState qstate,Declaration meaning,Scope sc)in{assert(meaning&&sc);}do{
	if(meaning.getName in qstate.vars) return QState.nullValue;
	if(auto fd=sc.getFunction())
		if(fd.context && fd.contextName in qstate.vars)
			return qstate.readLocal(fd.contextName,true);
	return QState.nullValue;
}
QState.Value buildContextFor(QState)(ref QState qstate,FunctionDef fd,Scope sc)in{assert(fd&&fd.scope_);}do{
	QState.Record record;
	foreach(decl;fd.capturedDecls){
		auto name=decl.getName;
		auto constLookup=!fd.isConsumedCapture(decl);
		auto val=lookupMeaning(qstate,decl,constLookup,sc);
		if(constLookup) val=val.dup(qstate);
		record[name]=val;
	}
	return QState.makeRecord(record);
}

QState.Value lookupMeaning(QState)(ref QState qstate,Identifier id,Scope sc=null)in{assert(id && id.scope_,text(id," ",id.loc));}do{
	auto meaning=id.meaning;
	auto constLookup=id.constLookup||id.implicitDup;
	if(!sc) sc=id.scope_;
	if(!meaning||!sc||!meaning.scope_)
		return qstate.readLocal(id.name,constLookup);
	if(id.lazyCapture)
		if(auto fd=cast(FunctionDef)meaning)
			return qstate.makeFunction(fd,sc);
	return lookupMeaning(qstate,meaning,constLookup,sc);
}

QState.Value lookupMeaning(QState)(ref QState qstate,Declaration meaning,bool constLookup,Scope sc)in{assert(!!meaning);}do{
	auto name=meaning.getName;
	if(auto dd=cast(DatDecl)meaning)
		meaning=dd.toFunctionDef();
	auto r=getContextFor(qstate,meaning,sc);
	if(r.isValid){
		assert(r.tag==QState.Value.Tag.record);
		if(name in r.record)
			return qstate.readField(r,name,constLookup);
	}
	if(auto fd=cast(FunctionDef)meaning)
		if(!fd.isNested()||name !in qstate.vars)
			return qstate.makeFunction(fd,sc);
	return qstate.readLocal(name,constLookup);
}

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
	bool consumeConst(Expression e){
		return !cast(Identifier)e&&!cast(TupleExp)e&&!cast(VectorExp)e&&!cast(IndexExp)e&&!cast(SliceExp)e&&!cast(CatExp)e&&!cast(TypeAnnotationExp)e&&e.isQfree();
	}
	QState.Value convertTo(Expression e,Expression type){
		auto value=runExp(e);
		if(value.isValid) value=convertTo(value,type,!e.constLookup);
		return value;
	}
	QState.Value convertTo(QState.Value value,Expression type,bool consumeArg){
		assert(value.type.isSemEvaluated());
		type=type.eval();
		assert(type.isSemEvaluated());
		if(value.type==type||cast(Identifier)type){
			if(consumeArg) return value;
			return value.dup(qstate);
		}
		if(auto intTy=isFixedIntTy(type)){
			auto len=runExp(intTy.bits);
			if(!cast(LiteralExp)intTy.bits){ // TODO: this is a hack, store integer bit lengths classically instead
				auto llen=LiteralExp.makeInteger(len.asℤ);
				llen.loc=intTy.bits.loc;
				auto ce=cast(CallExp)type;
				auto ntype=new CallExp(ce.e,llen,ce.isSquare,ce.isClassical_);
				ntype.type=type.type;
				ntype.sstate=SemState.completed;
				ntype.loc=type.loc;
				type=ntype.eval();
			}
		}
		QState.Value default_(){
			if(consumeArg) value.consumeOnRead(); // TODO: ok?
			if(auto intTy=isFixedIntTy(type)){
				if(value.tag==QState.Value.Tag.array_)
					enforce(qstate.makeInteger(ℤ(value.array_.length)).compare!"=="(runExp(intTy.bits)).neqZImpl,"length mismatch for conversion to fixed-size integer");
			}
			if(type==ℕt(true)) enforce(value.compare!">="(qstate.makeInteger(ℤ(0))).neqZImpl,"negative value not representable as a natural number");
			return value.convertTo(type);
		}
		if(isSubtype(value.type,type)) return default_();
		if(isSubtype(value.type,ℤt(true))){
			if(auto intTy=isFixedIntTy(type)){
				if(intTy.isSigned)
					return qstate.makeInt(type.getClassical(),BitInt!true(smallValue(runExp(intTy.bits).asℤ()),value.asℤ())).convertTo(type);
				else
					return qstate.makeUint(type.getClassical(),BitInt!false(smallValue(runExp(intTy.bits).asℤ()),value.asℤ())).convertTo(type);
			}
		}
		if(isUint(value.type)&&isSubtype(ℕt(true),type)){
			assert(value.tag==QState.Value.Tag.uintval);
			return qstate.makeInteger(value.uintval.val).convertTo(type);
		}
		if(isInt(value.type)&&isSubtype(ℤt(true),type)){
			assert(value.tag==QState.Value.Tag.intval);
			return qstate.makeInteger(value.intval.val).convertTo(type);
		}
		// TODO: rat
		if(auto tpl=cast(TupleTy)type){
			if(value.tag==QState.Value.Tag.array_){
				enforce(value.array_.length==tpl.length,"length mismatch for conversion to tuple");
				return qstate.makeTuple(type,iota(tpl.length).map!(i=>convertTo(value.array_[i],tpl[i],consumeArg)).array);
			}
		}else if(auto arr=cast(ArrayTy)type){
			if(value.tag==QState.Value.Tag.array_)
				return qstate.makeTuple(type,value.array_.map!(v=>convertTo(v,arr.next,consumeArg)).array);
		}else if(auto vec=cast(VectorTy)type){
			if(value.tag==QState.Value.Tag.array_){
				enforce(qstate.makeInteger(ℤ(value.array_.length)).compare!"=="(runExp(vec.num)).neqZImpl,"length mismatch for conversion to vector");
				return qstate.makeTuple(type,value.array_.map!(v=>convertTo(v,vec.next,consumeArg)).array);
			}
		}
		if(auto intTy=isFixedIntTy(value.type)){
			if(!intTy.isClassical&&QState.Value.getTag(type)==QState.Value.Tag.array_){
				assert(!type.isClassical);
				auto len=runExp(intTy.bits); // TODO: maybe store lengths classically instead
				enforce(len.isℤ(),"fixed-width integer width is not an integer");
				auto nbits=smallValue(len.asℤ());
				enforce(nbits>=0,"fixed-with integer width is negative");
				auto tmp=value.dup(qstate); // TODO: don't do this if value is already a variable
				auto r=qstate.makeTuple(arrayTy(Bool(false)),iota(nbits).map!(i=>(tmp&qstate.makeInteger(ℤ(1)<<i)).neqZ).array).convertTo(type).toVar(qstate,false);
				tmp.forget(qstate);
				if(consumeArg) value.forget(qstate);
				else r.consumeOnRead();
				return r;
			}
		}
		if(consumeArg) value.consumeOnRead(); // TODO: ok?
		return default_();
	}
	void closeScope(Scope sc){
		if(!qstate.state.length) return;
		foreach(merged;sc.mergedVars){
			auto name=merged.getName;
			if(name !in qstate.vars) continue; // TODO: get rid of this
			assert(!!merged.mergedInto);
			import ast.semantic_:typeForDecl;
			auto type=typeForDecl(merged.mergedInto);
			enforce(name in qstate.vars,text("missing variable `",name,"` when closing scope"));
			if(qstate.vars[name].type !is type)
				qstate.vars[name]=convertTo(qstate.vars[name],type,true).toVar(qstate,false);
		}
	}
	QState.Value runExp(Expression e){
		if(!qstate.state.length) return QState.Value.init;
		QState.Value doIt()(Expression e){
			try{
				auto r=doIt2(e);
				if((e.constLookup||e.implicitDup)&&consumeConst(e))
					r=r.consumeOnRead();
				if(e.implicitDup) r=r.dup(qstate);
				return r;
			}catch(Exception ex){
				version(LOCALIZE) throw localizedException(ex,e.loc);
				else throw ex;
			}
		}
		// TODO: get rid of code duplication
		QState.Value doIt2(Expression e){
			if(auto id=cast(Identifier)e){
				if(!id.meaning&&util.among(id.name,"π","pi")) return QState.π;
				if(auto init=id.getInitializer()){
					return doIt2(init);
				}
				auto r=lookupMeaning(qstate,id);
				enforce(r.isValid,"this identifier lookup is not yet supported");
				if(id.consumedDuringBorrow){ r=r.dup(qstate).consumeOnRead(); }
				return r;
			}
			if(auto fe=cast(FieldExp)e){
				enforce(fe.type.isClassical||fe.constLookup,"consuming fields is not yet supported");
				if(isBuiltIn(fe)){
					if(cast(ArrayTy)fe.e.type||cast(VectorTy)fe.e.type||cast(TupleTy)fe.e.type){
						assert(fe.f.name=="length");
						auto r=doIt(fe.e);
						enforce(r.tag==QState.Value.Tag.array_,"bad value for length lookup");
						return qstate.makeInteger(ℤ(r.array_.length));
					}
				}
				// TODO: non-constant field lookup
				return qstate.readField(doIt(fe.e),fe.f.name,true);
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
			if(auto se=cast(NSubExp)e) return doIt(se.e1).opBinary!"sub"(doIt(se.e2));
			if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
			if(auto de=cast(DivExp)e) return doIt(de.e1)/doIt(de.e2);
			if(auto de=cast(IDivExp)e) return doIt(de.e1).opBinary!"div"(doIt(de.e2));
			if(auto me=cast(ModExp)e) return doIt(me.e1)%doIt(me.e2);
			if(auto pe=cast(PowExp)e) return doIt(pe.e1)^^doIt(pe.e2);
			if(auto ce=cast(CatExp)e) return doIt(ce.e1)~doIt(ce.e2);
			if(auto ce=cast(BitOrExp)e) return doIt(ce.e1)|doIt(ce.e2);
			if(auto ce=cast(BitXorExp)e) return doIt(ce.e1)^doIt(ce.e2);
			if(auto ce=cast(BitAndExp)e) return doIt(ce.e1)&doIt(ce.e2);
			if(auto ume=cast(UMinusExp)e) return -doIt(ume.e);
			if(auto ume=cast(UNotExp)e) return doIt(ume.e).eqZ;
			if(auto ume=cast(UBitNotExp)e) return ~doIt(ume.e);
			if(auto let=cast(LetExp)e){
				auto ret=QState.empty();
				runStm(let.s,ret);
				enforce(!ret.state.length,"early returns from `let` statement not supported yet");
				return doIt(let.e);
			}
			if(auto le=cast(LambdaExp)e) return qstate.makeFunction(le.fd,le.fd.scope_);
			if(auto ce=cast(CallExp)e){
				auto target=unwrap(ce.e);
				auto id=cast(Identifier)target;
				auto fe=cast(FieldExp)target;
				QState.Value thisExp=QState.nullValue;
				if(fe){
					id=fe.f;
					thisExp=doIt(fe.e);
					enforce(0, "method calls not yet supported");
					assert(0);
				} else {
					final switch(isBuiltIn(id)){
						case BuiltIn.none:
							break;
						case BuiltIn.show,BuiltIn.query:
							return qstate.makeTuple(ast.type.unit,[]);
						case BuiltIn.pi:
							enforce(0,text("built-in `",id.name,"` not yet supported"));
							assert(0);
					}
					if(id&&cast(DatDecl)id.meaning) return QState.typeValue(ce); // TODO: get rid of this
				}
				auto fun=doIt(ce.e);
				auto arg=doIt(ce.arg);
				auto r=qstate.call(fun,arg,ce.type,ce.loc);
				if(ce.newFunctionVar) qstate.assignTo(ce.newFunctionVar.getName,fun);
				return r;
			}
			if(auto fe=cast(ForgetExp)e){
				forget(fe);
				return qstate.makeTuple(unit,[]);
			}
			if(auto idx=cast(IndexExp)e){
				auto a=doIt2(idx.e),i=doIt(idx.a);
				auto r=a[i];
				if(!idx.constLookup&&!idx.implicitDup){
					if(idx.byRef){
						if(a.tag==QState.Value.Tag.array_&&i.isℤ()){
							a.array_[i.asℤ.to!size_t]=QState.Value.init;
						}else{
							r=r.dup(qstate).consumeOnRead();
							getAssignable!false(idx,[]).assign(qstate,QState.makeBool(false)); // TODO: a bit hacky
						}
					}else r=r.dup(qstate);
				}
				return r;
			}
			if(auto sl=cast(SliceExp)e){
				auto r=doIt(sl.e)[doIt(sl.l)..doIt(sl.r)];
				if(!sl.constLookup) r=r.dup(qstate);
				return r;
			}
			if(auto le=cast(LiteralExp)e){
				QState.Value val;
				if(auto v = le.asIntegerConstant()) {
					if(le.type==Bool(true)){
						val = QState.makeBool(v.get() != 0);
					} else {
						val = QState.makeInteger(v.get());
					}
				} else if(auto v = le.asRationalConstant()) {
					auto t = v.get();
					auto num = t[0];
					auto den = t[1];
					if(t[3] < 0) {
						den *= ℤ(t[2])^^(-t[3]);
					} else {
						num *= ℤ(t[2])^^t[3];
					}
					val = QState.makeRational(ℚ(num, den));
				}
				if(val.isValid()) {
					return convertTo(val, le.type, false);
				}
			}
			if(auto ite=cast(IteExp)e){
				auto cond=runExp(ite.cond);
				if(cond.isClassical()){
					if(cond.neqZImpl){
						auto thenIntp=Interpreter!QState(functionDef,ite.then,qstate,hasFrame);
						auto then=thenIntp.convertTo(ite.then.s[0],ite.type);
						thenIntp.closeScope(ite.then.blscope_);
						qstate=thenIntp.qstate;
						return then;
					}else{
						auto othwIntp=Interpreter!QState(functionDef,ite.othw,qstate,hasFrame);
						auto othw=othwIntp.convertTo(ite.othw.s[0],ite.type);
						othwIntp.closeScope(ite.othw.blscope_);
						qstate=othwIntp.qstate;
						return othw;
					}
				}else{
					auto thenElse=qstate.split(cond);
					qstate=thenElse[0];
					auto thenIntp=Interpreter!QState(functionDef,ite.then,qstate,hasFrame);
					auto then=thenIntp.convertTo(ite.then.s[0],ite.type);
					thenIntp.closeScope(ite.then.blscope_);
					auto constLookup=ite.constLookup;
					assert(!!ite.othw);
					assert(ite.then.s[0].constLookup==constLookup&&ite.othw.s[0].constLookup==constLookup);
					auto othwState=thenElse[1];
					auto othwIntp=Interpreter(functionDef,ite.othw,othwState,hasFrame);
					auto othw=othwIntp.convertTo(ite.othw.s[0],ite.type);
					othwIntp.closeScope(ite.othw.blscope_);
					if(!then.isValid){ qstate=othwIntp.qstate; return othw; } // constant conditions
					if(!othw.isValid){ qstate=thenIntp.qstate; return then; }
					thenIntp.qstate.assignTo("`result",then);
					othwIntp.qstate.assignTo("`result",othw);
					qstate=thenIntp.qstate;
					qstate+=othwIntp.qstate;
					auto var=qstate.vars["`result"];
					qstate.vars.remove("`result");
					return var;
				}
			}else if(auto tpl=cast(TupleExp)e){
				auto values=tpl.e.map!(e=>doIt(e)).array; // DMD bug: map!doIt does not work
				return QState.makeTuple(e.type,values);
			}else if(auto vec=cast(VectorExp)e){
				auto et=vec.type.elementType;
				assert(!!et);
				auto values=vec.e.map!((e){
					auto value=doIt(e);
					if(e.type!=et) value=convertTo(value,et,!e.constLookup);
					return value;
				}).array;
				return QState.makeArray(e.type,values);
			}else if(auto ae=cast(AssertExp)e){
				auto c=runExp(ae.e);
				if(c.isValid){
					qstate=qstate.assertTrue(c);
					return qstate.makeTuple(unit,[]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)e){
				if(tae.e.type==tae.type||tae.annotationType==TypeAnnotationType.punning) return doIt(tae.e);
				bool consume=!tae.constLookup;
				auto r=convertTo(doIt(tae.e),tae.type,consume);
				if(tae.constLookup) r=r.consumeOnRead();
				return r;
			} else if(auto te=cast(VectorTy)e){
				runExp(te.next);
				runExp(te.num);
				return qstate.typeValue(te);
			} else if(auto te=cast(ArrayTy)e){
				runExp(te.next);
				return qstate.typeValue(te);
			} else if(auto te=cast(TupleTy)e){
				foreach(sub; te.types) {
					runExp(sub);
				}
				return qstate.typeValue(te);
			} else if(auto te=cast(VariadicTy)e){
				runExp(te.next);
				return qstate.typeValue(te);
			} else if(auto te=cast(ClassicalTy)e){
				runExp(te.inner);
				return qstate.typeValue(te);
			} else if(auto te=cast(ProductTy)e){
				foreach(p; te.params) {
					runExp(p.dtype);
				}
				return qstate.typeValue(te);
			} else if(cast(NumericTy)e || cast(TypeTy)e || cast(QNumericTy)e || cast(BottomTy)e){
				return qstate.typeValue(e);
			}else{
				enum common=q{
					auto e1=doIt(b.e1),e2=doIt(b.e2);
				};
				if(auto b=cast(AndExp)e){
					auto e1=doIt(b.e1);
					if(e1.isClassical()&&e1.eqZImpl) return e1;
					auto e2=doIt(b.e2);
					return e1&e2;
				}else if(auto b=cast(OrExp)e){
					auto e1=doIt(b.e1);
					if(e1.isClassical()&&e1.neqZImpl) return e1;
					auto e2=doIt(b.e2);
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
			enforce(0,text("expression `",e,"` of type `",e.type,"` not yet supported"));
			assert(0);
		}
		return doIt(e);
	}
	static struct Assignable(bool isCat){
		string readName;
		string writeName;
		QState.Value[] indices;
		Location[] locations;
		QState.Value read(ref QState state){
			enforce(readName in state.vars,format("missing variable `%s`",readName));
			auto var=state.vars[readName];
			enforce(indices.all!(x=>x.isClassical()),"assignment to quantum index not yet supported");
			QState.Value doIt(ref QState.Value value,QState.Value[] indices,Location[] locations){
				if(!indices.length) return value;
				switch(value.tag){
					case QState.Value.Tag.array_:
						auto index=indices[0].asℤ;
						if(!(0<=index&&index<value.array_.length)){
							auto ex=new Exception("index out of bounds");
							version(LOCALIZE) ex=new LocalizedException(ex,locations[0]);
							throw ex;
						}
						return doIt(value.array_[to!size_t(index)],indices[1..$],locations[1..$]);
					case QState.Value.Tag.intval,QState.Value.Tag.uintval,QState.Value.Tag.quval:
						enforce(indices.length==1);
						auto index=indices[0].asℤ;
						return value[index];
					default: enforce(0,text("TODO: ",value.tag)); assert(0);
				}
			}
			return doIt(var,indices,locations);
		}
		void assign(ref QState state,QState.Value rhs){
			enforce(readName in state.vars,format("missing variable `%s` for assignment",readName,));
			auto var=state.vars[readName];
			void doIt(ref QState.Value value,QState.Value[] indices,Location[] locations,QState.Value condition){
				if(!indices.length){
					if(value.isValid) rhs.consumeOnRead();
					auto nrhs=rhs;
					if(condition.isValid)
						nrhs=state.ite(condition,nrhs,value);
					static if(isCat) state.catAssignTo(value,nrhs);
					else state.assignTo(value,nrhs);
					return;
				}
				noreturn outOfBounds(){
					auto ex=new Exception("index out of bounds");
					version(LOCALIZE) ex=new LocalizedException(ex,locations[0]);
					throw ex;
				}
				auto tag=value.tag;
				switch(tag){
					case QState.Value.Tag.array_:
						if(indices[0].isClassical()){
							auto index=indices[0].asℤ;
							if(index<0||index>=value.array_.length) outOfBounds();
							doIt(value.array_[to!size_t(index)],indices[1..$],locations[1..$],condition);
						}else{
							foreach(i;0..value.array_.length){
								auto ncond=indices[0].compare!"=="(qstate.makeInteger(ℤ(i)));
								doIt(value.array_[i],indices[1..$],locations[1..$],condition.isValid?condition&ncond:ncond);
							}
							auto check=indices[0].compare!"<"(qstate.makeInteger(ℤ(0)))|indices[0].compare!">="(qstate.makeInteger(ℤ(value.array_.length)));
							auto ccheck=condition.isValid?condition&check:check;
							foreach(k,v;state.state) // TODO: this is very inefficient
								if(ccheck.classicalValue(k).neqZImpl)
									outOfBounds();
						}
						return;
					case QState.Value.Tag.intval,QState.Value.Tag.uintval,QState.Value.Tag.quval:
						enforce(indices.length==1,"wrong number of indices for indexing fixed-width integer");
						size_t nbits=size_t.max;
						switch(tag){
							case QState.Value.Tag.intval:
								nbits=value.intval.nbits;
								break;
							case QState.Value.Tag.uintval:
								nbits=value.uintval.nbits;
								break;
							case QState.Value.Tag.quval:
								// TODO: store number of bits classically?
								foreach(k,v;state.state){
									auto cvalue=value.quval.get(k);
									if(cvalue.tag==QState.Value.Tag.intval)
										nbits=cvalue.intval.nbits;
									else if(cvalue.tag==QState.Value.Tag.uintval)
										nbits=cvalue.uintval.nbits;
									break;
								}
								break;
							default: break;
						}
						if(indices[0].isClassical()){
							auto index=indices[0].asℤ;
							if(index<0||index>=nbits) outOfBounds();
						}else{
							auto check=indices[0].compare!"<"(qstate.makeInteger(ℤ(0)))|indices[0].compare!">="(qstate.makeInteger(ℤ(nbits)));
							auto ccheck=condition.isValid?condition&check:check;
							foreach(k,v;state.state) // TODO: this is very inefficient
								if(ccheck.classicalValue(k).neqZImpl)
									outOfBounds();
						}
						auto index=indices[0];
						rhs.consumeOnRead();
						auto nrhsz=value&~(state.makeInteger(ℤ(1))<<index);
						auto nrhso=nrhsz|state.makeInteger(ℤ(1))<<index;
						auto nrhs=rhs.isClassical()?(rhs.neqZImpl?nrhso:nrhsz):state.ite(rhs,nrhso,nrhsz);
						if(condition.isValid) nrhs=state.ite(condition,nrhs,value);
						value.assign(state,nrhs);
						return;
					default: enforce(0,text("bad value for assignment"));
				}
			}
			doIt(var,indices,locations,state.nullValue);
			state.vars[writeName]=var;
			if(readName!=writeName)
				state.vars.remove(readName);
		}
	}
	Assignable!isCat getAssignable(bool isCat)(Expression lhs,AAssignExp.Replacement[] replacements){
		if(auto id=cast(Identifier)lhs){
			auto readName=id.name,writeName=readName;
			foreach(r;replacements){
				if(id.meaning is r.previous){
					writeName=r.new_.getName;
					break;
				}
			}
			return Assignable!isCat(readName,writeName,[]);
		}
		if(auto idx=cast(IndexExp)lhs){
			auto a=getAssignable!isCat(idx.e,replacements);
			auto index=runExp(idx.a);
			a.indices~=index;
			a.locations~=idx.loc;
			return a;
		}
		enforce(0,text("assigning to `",lhs,"` not yet supported"));
		assert(0);
	}
	QState.Value canonicalValue(Expression type){
		if(!isUnit(type)) return QState.Value.init;
		if(auto tt=cast(TupleTy)type){
			auto next=tt.types.map!(ty=>canonicalValue(ty)).array;
			if(next.any!(v=>!v.isValid)) return QState.Value.init;
			return qstate.makeTuple(tt,next);
		}
		if(auto vt=cast(VectorTy)type){
			auto num=vt.num.asIntegerConstant();
			if(!num)
				return QState.Value.init;
			auto next=iota(to!size_t(num.get())).map!(i=>canonicalValue(vt.next)).array;
			return qstate.makeTuple(vt,next);
		}
		if(auto at=cast(ArrayTy)type){
			if(!isEmpty(at.next)) return QState.Value.init;
			return qstate.makeTuple(at,[]);
		}
		return QState.Value.init;
	}
	void assignTo(bool isCat=false)(Expression lhs,QState.Value rhs,AAssignExp.Replacement[] replacements){
		if(auto id=cast(Identifier)lhs){
			static if(isCat){
				qstate.catAssignTo(id.name,rhs);
				foreach(r;replacements){
					if(id.meaning is r.previous){
						enforce(id.name in qstate.vars,format("missing variable `%s` for assignment",id.name));
						auto writeName=r.new_.getName;
						if(id.name!=writeName){
							qstate.vars[writeName]=qstate.vars[id.name];
							qstate.vars.remove(id.name);
						}
						break;
					}
				}
			}else qstate.assignTo(id.name,rhs);
		}else if(auto tpl=cast(TupleExp)lhs){
			enforce(!isCat,"cannot concat assign to tuple expression");
			enforce(rhs.tag==QState.Value.Tag.array_,"bad value for assignment");
			enforce(tpl.e.length==rhs.array_.length,"length mismatch for pattern matching against array");
			foreach(i;0..tpl.e.length)
				assignTo!isCat(tpl.e[i],rhs.array_[i],replacements);
		}else if(auto idx=cast(IndexExp)lhs){
			getAssignable!isCat(lhs,replacements).assign(qstate,rhs);
		}else if(auto ce=cast(CallExp)lhs){
			enforce(!isCat,"cannot concat assign to function call expression");
			auto f=ce.e,oft=cast(ProductTy)f.type;
			enforce(!!oft,"reversed function call not yet supported");
			auto fv=runExp(f);
			if(fv.tag==QState.Value.Tag.closure){
				auto ft=fv.closure.fun.ftype;
				enforce(fv.closure.fun.scope_&&ft&&ft.captureAnnotation==CaptureAnnotation.const_&&ft.annotation>=Annotation.mfree,"reversed function call not yet supported");
				auto rf=reverseFunction(fv.closure.fun), rft=rf.ftype;
				auto context=fv.closure.context;
				auto rfv=qstate.makeClosure(rft,QState.Closure(rf,context));
				//auto rfv=qstate.makeFunction(rf);
				auto rfret=rft.cod; // TODO: probably semantic analysis has to explicitly compute this
				auto r=reverseCallRewriter(ft,ce.loc); // TODO: would be nice to not require this
				QState.Value constArg;
				void handleUnitArg(Expression arg,Expression type){
					enforce(isUnit(type),"reversed function call not yet supported");
					auto val=canonicalValue(type);
					enforce(val.isValid,"reversed function call not yet supported");
					assignTo(arg,val,[]);
				}
				if(oft.nargs&&oft.isConstForReverse.all){
					constArg=runExp(ce.arg);
				}else if(!oft.isConstForReverse.any&&!ft.isConstForReverse.any){
					// no const arg
					enforce(rf.params.length==1&&equal(rft.isConstForReverse,only(false))&&!rft.isTuple,"reversed function call not yet supported");
				}else if(!ft.isTuple){
					assert(ft.nargs==1);
					if(ft.isConstForReverse[0]){
						assert(!oft.isConstForReverse.any);
						handleUnitArg(ce.arg,ft.dom);
						constArg=runExp(ce.arg);
					}else{
						enforce(0,"reversed function call not yet supported");
					}
				}else{
					enforce(oft.dom.isTupleTy,"reversed function call not yet supported");
					oft=oft.setTuple(true);
					auto tpl=cast(TupleExp)ce.arg;
					enforce(!!tpl&&tpl.length==oft.isConst.length,"reversed function call not yet supported");
					QState.Value[] cargs;
					if(r.constTuple){
						foreach(i,arg;tpl.e){
							if(ft.isConstForReverse[i]){
								if(!oft.isConstForReverse[i])
									handleUnitArg(arg,ft.argTy(i));
								cargs~=runExp(arg);
							}
						}
					}else{
						enforce(ft.isConstForReverse.count!(x=>x)==1);
						foreach(i,arg;tpl.e){
							if(ft.isConstForReverse[i]){
								if(!oft.isConstForReverse[i])
									handleUnitArg(arg,ft.argTy(i));
								constArg=runExp(arg);
								break;
							}
						}
					}
					if(r.constTuple) constArg=qstate.makeTuple(r.constType,cargs);
				}
				void assignMoved(QState.Value result){
					if(!oft.isConstForReverse.any) return assignTo(ce.arg,result,replacements);
					if(oft.nargs&&oft.isConstForReverse.all){ // TODO: remove?
						assert(rft.cod is unit);
						return;
					}
					auto tpl=cast(TupleExp)ce.arg;
					enforce(!!tpl);
					if(r.movedTuple){
						enforce(result.tag==QState.Value.Tag.array_,"wrong number of moved arguments to reversed call");
						enforce(ft.isConstForReverse.count!(x=>!x)==result.array_.length);
						size_t j=0;
						foreach(i,arg;tpl.e){
							if(!ft.isConstForReverse[i])
								assignTo(arg,result.array_[j++],replacements);
						}
					}else{
						enforce(ft.isConstForReverse.count!(x=>!x)==1,"wrong number of moved arguments to reversed call");
						foreach(i,arg;tpl.e){
							if(!ft.isConstForReverse[i]){
								assignTo(arg,result,replacements);
								break;
							}
						}
					}
				}
				if(rft.nargs&&rft.isConst.all){
					enforce(rhs.tag==QState.Value.Tag.array_&&rhs.array_.length==0,"bad right-hand side for reversed call");
					// assignment is on unit. can just drop rhs.
					auto result=qstate.call(rfv,constArg,rfret,ce.loc);
					assignMoved(result);
				}else if(!rft.isConst.any){
					assert(!rft.isConst.any);
					auto result=qstate.call(rfv,rhs,rfret,ce.loc);
					assignMoved(result);
				}else if(rf.params.length==2){
					enforce(rft.isConst[0]!=rft.isConst[1],"reversed call not yet supported");
					auto constLast=rft.isConst[1];
					auto args=constLast?[rhs,constArg]:[constArg,rhs];
					auto aty=tupleTy(constLast?[r.movedType,r.constType]:[r.constType,r.movedType]); // TODO: get rid of this
					auto arg=qstate.makeTuple(aty,args);
					auto result=qstate.call(rfv,arg,rfret,ce.loc);
					assignMoved(result);
				}else enforce(0,"reversed call not yet supported");
			}
		}else if(auto ce=cast(CatExp)lhs){
			enforce(!isCat);
			enforce(rhs.tag==QState.Value.Tag.array_, "split not supported in simulator");
			auto len=rhs.array_.length;
			ℤ mid;
			import util.maybe:Maybe,just;
			Maybe!ℤ a,b;
			if(auto l1=knownLength(ce.e1,false)){
				auto len1=runExp(l1).asℤ;
				a=just(len1);
				mid=len1;
			}
			if(auto l2=knownLength(ce.e2,false)){
				auto len2=runExp(l2).asℤ;
				b=just(len2);
				if(!a) mid=len-len2;
			}
			if(!a&&!b) enforce(0, "this split is not yet supported");
			import std.format:format;
			if(a&&!b) enforce(a.get<=len, format("need at least %s elements to split, only got %s",a.get,len));
			if(!a&&b) enforce(b.get<=len, format("need at least %s elements to split, only got %s",b.get,len));
			if(a&&b) enforce(a.get+b.get==len, format("incompatible lengths for split: %s + %s ≠ %s",a.get,b.get,len));
			auto e1=rhs[0.ℤ..mid],e2=rhs[mid.ℤ..len.ℤ];
			assignTo(unwrap(ce.e1),convertTo(e1,ce.e1.type,true),replacements);
			assignTo(unwrap(ce.e2),convertTo(e2,ce.e2.type,true),replacements);
		}else enforce(0,text("assignment to `",lhs,"` is not yet supported"));
	}
	void catAssignTo(Expression lhs,QState.Value rhs,AAssignExp.Replacement[] replacements){
		return assignTo!true(lhs,rhs,replacements);
	}
	void swap(Expression e1,Expression e2,AAssignExp.Replacement[] replacements){ // TODO: swap Values directly if supported
		auto a1=getAssignable!false(e1,replacements);
		auto a2=getAssignable!false(e2,replacements);
		auto tmp=a1.read(qstate).dup(qstate);
		a1.assign(qstate,a2.read(qstate).dup(qstate));
		tmp.consumeOnRead();
		a2.assign(qstate,tmp);
	}
	void forget(QState.Value lhs,QState.Value rhs){
		if(opt.projectForget) qstate=qstate.project(lhs.eq(rhs));
		lhs.forget(qstate,rhs);
	}
	void forget(QState.Value lhs){
		lhs.forget(qstate);
	}
	void forget(ForgetExp fe){
		if(fe.var.type&&fe.var.type.isClassical){
			auto var=runExp(fe.var);
			if(fe.val){
				auto val=runExp(fe.val);
				enforce(var==val,"bad forget");
			}
			void doForget(Expression e){
				if(auto id=cast(Identifier)e){
					if(!id.implicitDup){
						assert(id.name !in qstate.vars,text(id));
						//qstate.vars.remove(id.name);
					}
				}else if(auto tpl=cast(TupleExp)e){
					foreach(t;tpl.e)
						doForget(t);
				}
			}
			doForget(fe.var);
		}else{
			if(fe.val) forget(runExp(fe.var),runExp(fe.val));
			else forget(runExp(fe.var));
		}
	}
	void runStm(Expression e,ref QState retState){
		try{
			runStm2(e,retState);
		}catch(Exception ex){
			version(LOCALIZE) throw localizedException(ex,e.loc);
			else throw ex;
		}
	}
	void runStm2(Expression e,ref QState retState){
		if(!qstate.state.length) return;
		if(opt.trace && !functionDef.boolAttribute(Id.s!"artificial")){
			writeln(qstate);
			writeln();
			writeln("STATEMENT");
			writeln(e);
			writeln();
		}
		if(auto ae=cast(AssignExp)e){
			auto lhs=ae.e1,rhs=runExp(ae.e2);
			assignTo(lhs,rhs,ae.replacements);
		}else if(auto ae=cast(DefineExp)e){
			if(ae.isSwap){
				auto tpl=cast(TupleExp)unwrap(ae.e2);
				enforce(!!tpl);
				swap(tpl.e[0],tpl.e[1],[]);
			}else{
				auto lhs=ae.e1,rhs=runExp(ae.e2);
				assignTo(lhs,rhs,[]);
			}
		}else if(auto ce=cast(CatAssignExp)e){
			auto lhs=ce.e1,rhs=runExp(ce.e2);
			catAssignTo(lhs,rhs,ce.replacements);
		}else if(isOpAssignExp(e)){
			QState.Value perform(QState.Value a,QState.Value b){
				if(cast(OrAssignExp)e) return a|b;
				if(cast(AndAssignExp)e) return a&b;
				if(cast(AddAssignExp)e) return a+b;
				if(cast(SubAssignExp)e) return a-b;
				if(cast(NSubAssignExp)e) return a.opBinary!"sub"(b);
				if(cast(MulAssignExp)e) return a*b;
				if(cast(DivAssignExp)e) return a/b;
				if(cast(IDivAssignExp)e) return a.opBinary!"div"(b);
				if(cast(ModAssignExp)e) return a%b;
				if(cast(PowAssignExp)e){
					// TODO: enforce constraints on domain
					return a^^b;
				}
				if(cast(BitOrAssignExp)e) return a|b;
				if(cast(BitXorAssignExp)e) return a^b;
				if(cast(BitAndAssignExp)e) return a&b;
				assert(0);
			}
			auto ae=cast(AAssignExp)e;
			assert(!!ae);
			auto ass=getAssignable!false(ae.e1,ae.replacements);
			if(cast(OrAssignExp)e&&ae.e1.type.isClassical()){
				auto lhs=ass.read(qstate);
				enforce(lhs.isClassical(),"unexpected quantum condition");
				if(!lhs.neqZImpl) ass.assign(qstate,runExp(ae.e2));
			}else if(cast(AndAssignExp)e&&ae.e1.type.isClassical()){
				auto lhs=ass.read(qstate);
				enforce(lhs.isClassical(),"unexpected quantum condition");
				if(lhs.neqZImpl) ass.assign(qstate,runExp(ae.e2));				
			}else{
				auto lhs=ass.read(qstate),rhs=runExp(ae.e2);
				ass.assign(qstate,perform(lhs,rhs));
			}
		}else if(auto call=cast(CallExp)e){
			runExp(call).forget(qstate);
		}else if(auto ce=cast(CompoundExp)e){
			foreach(s;ce.s) runStm(s,retState);
		}else if(auto ite=cast(IteExp)e){
			auto cond=runExp(ite.cond);
			if(cond.isClassical()){
				if(cond.neqZImpl){
					auto thenIntp=Interpreter!QState(functionDef,ite.then,qstate,hasFrame);
					thenIntp.run(retState);
					thenIntp.closeScope(ite.then.blscope_);
					qstate=thenIntp.qstate;
				}else{
					auto othwIntp=Interpreter!QState(functionDef,ite.othw,qstate,hasFrame);
					othwIntp.run(retState);
					othwIntp.closeScope(ite.othw.blscope_);
					qstate=othwIntp.qstate;
				}
			}else{
				auto thenOthw=qstate.split(cond);
				qstate=thenOthw[0];
				auto othw=thenOthw[1];
				auto thenIntp=Interpreter(functionDef,ite.then,qstate,hasFrame);
				thenIntp.run(retState);
				thenIntp.closeScope(ite.then.blscope_);
				qstate=thenIntp.qstate;
				enforce(!!ite.othw);
				auto othwIntp=Interpreter(functionDef,ite.othw,othw,hasFrame);
				othwIntp.run(retState);
				othwIntp.closeScope(ite.othw.blscope_);
				othw=othwIntp.qstate;
				qstate+=othw;
			}
		}else if(auto with_=cast(WithExp)e){
			runStm(with_.trans,retState);
			runStm(with_.bdy,retState);
			runStm(with_.itrans,retState);
		}else if(auto re=cast(RepeatExp)e){
			auto rep=runExp(re.num);
			if(rep.isℤ()){
				auto z=rep.asℤ();
				auto intp=Interpreter(functionDef,re.bdy,qstate,hasFrame);
				foreach(x;0.ℤ..z){
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retState);
					intp.closeScope(re.bdy.blscope_);
				}
				qstate=intp.qstate;
			}else{
				enforce(0,"TODO?");
				/+auto bound=rep.floor();
				auto intp=Interpreter(functionDef,re.bdy,qstate,hasFrame);
				qstate.state=typeof(qstate.state).init;
				for(ℤ x=0;;++x){
					auto thenOthw=intp.qstate.split(bound.le(QState.makeInteger(x)));
					qstate += thenOthw[0];
					intp.qstate = thenOthw[1];
					//intp.qstate.error = zero;
					if(!intp.qstate.state.length) break;
					if(opt.trace) writeln("repetition: ",x+1);
					intp.run(retState);
					intp.closeScope(re.bdy.blscope_);
				}+/
			}
		}else if(auto fe=cast(ForExp)e){
			auto l=runExp(fe.left), r=runExp(fe.right), s=fe.step?runExp(fe.step):qstate.makeInteger(ℤ(1));
			if(l.isℤ()&&r.isℤ()&&s.isℤ()){
				auto lz=l.asℤ(),rz=r.asℤ(),sz=s.asℤ();
				auto intp=Interpreter(functionDef,fe.bdy,qstate,hasFrame);
				enum body_=q{
					if(opt.trace) writeln("loop-index: ",j);
					intp.qstate.assignTo(fe.var.name,qstate.makeInteger(j).convertTo(fe.loopVar.vtype));
					intp.run(retState);
					intp.closeScope(fe.bdy.blscope_);
				};
				ℤ mz=fe.leftExclusive==fe.rightExclusive?(lz+rz)>>1:fe.leftExclusive?rz:lz;
				auto adj=floormod(mz-lz,sz);
				if(fe.leftExclusive&&adj==0) adj=sz;
				lz+=adj;
				if(sz>=0){
					for(ℤ j=lz;j+cast(int)fe.rightExclusive<=rz;j+=sz) mixin(body_);
				}else{
					for(ℤ j=lz;j-cast(int)fe.rightExclusive>=rz;j+=sz) mixin(body_);
				}
				qstate=intp.qstate;
			}else{
				enforce(0,"TODO?");
				/+auto loopIndex=fe.leftExclusive?l.floor()+1:l.ceil();
				auto bound=fe.rightExclusive?r.ceil()-1:r.floor();
				auto intp=Interpreter(functionDef,fe.bdy,qstate,hasFrame);
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
					intp.closeScope(fe.bdy.blscope_);
				}+/
			}
		}else if(auto we=cast(WhileExp)e){
			auto intp=Interpreter(functionDef,we.bdy,qstate,hasFrame);
			for(;;){
				if(!intp.qstate.state.length) break;
				auto cond=intp.runExp(we.cond);
				if(!cond.asBoolean) break;
				intp.run(retState);
				intp.closeScope(we.bdy.blscope_);
			}
			qstate=intp.qstate;
		}else if(auto re=cast(ReturnExp)e){
			auto value = convertTo(re.e,functionDef.ret);
			if(functionDef.context&&functionDef.contextName.startsWith("this"))
				value = QState.makeTuple(tupleTy([re.e.type,contextTy(true)]),[value,qstate.readLocal(functionDef.contextName,false)]);
			qstate.assignTo("`value",value);
			static if(language==silq) qstate.forgetVars(re.forgottenVars);
			//closeScope(re.scope_);
			if(functionDef.isNested) // caller takes care of context
				qstate.vars.remove(functionDef.contextName);
			if(hasFrame){
				assert("`parent" in qstate.vars);
				//assert(qstate.vars.length==2); // `value and `parent
			}//else assert(qstate.vars.length==1); // only `value
			retState += qstate; // TODO: compute distributions?
			qstate=QState.empty();
		}else if(auto ae=cast(AssertExp)e){
			auto cond=runExp(ae.e);
			qstate=qstate.assertTrue(cond);
		}else if(auto oe=cast(ObserveExp)e){
			enforce(0,"TODO: observe?");
			assert(0);
		}else if(auto fe=cast(ForgetExp)e){
			forget(fe);
		}else if(auto ce=cast(CommaExp)e){
			runStm(ce.e1,retState);
			runStm(ce.e2,retState);
		}else if(auto fd=cast(FunctionDef)e){
			qstate.declareFunction(fd);
		}else if(cast(Declaration)e){
			// do nothing
		}else{
			enforce(0,text("statement `",e,"` is not yet supported"));
		}
	}
	void run(ref QState retState){
		static if(language==silq){
			if(statements.blscope_)
				qstate.forgetVars(statements.blscope_.forgottenVarsOnEntry);
		}
		foreach(s;statements.s){
			runStm(s,retState);
			// writeln("cur: ",cur);
		}
		static if(language==silq){
			if(statements.blscope_)
				qstate.forgetVars(statements.blscope_.forgottenVars);
		}
	}
	void runFun(ref QState retState){
		foreach(p;functionDef.params){
			runExp(p.dtype);
		}
		if(functionDef.rret) runExp(functionDef.rret);
		run(retState);
		retState+=qstate;
		qstate=QState.empty();
	}
}
