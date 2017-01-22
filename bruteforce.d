import std.conv: text;
import std.string: split;
import std.algorithm: map;
import std.array: array;

import backend;
import distrib,error;
import dexpr,hashtable,util;
import expression,declaration,type;
import semantic_;

class Bruteforce: Backend{
	this(string sourceFile){
		this.sourceFile=sourceFile;
	}
	override Distribution analyze(FunctionDef def,ErrorHandler err){
		auto interpreter=Interpreter(def.body_);
		Dist ret;
		interpreter.run(ret);
		return ret.toDistribution();
	}
private:
	string sourceFile;
}

struct Dist{
	void add(DExpr k,DExpr v){
		if(k in state) state[k]=(state[k]+v).simplify(one);
		else state[k]=v;
		if(state[k] is zero) state.remove(k);
	}
	void opOpAssign(string op:"+")(Dist r){
		foreach(k,v;r.state)
			add(k,v);
	}
	Dist map(DLambda lambda){
		Dist r;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			auto err=dField(k,"`error").simplify(one);
			assert(err is one || err is zero);
			if(err is one) r.add(k,v);
			else r.add(dApply(lambda,k).simplify(one),v);
		}
		return r;
	}
	Dist flatMap(DLambda[] lambdas){
		Dist r;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			auto err=dField(k,"`error").simplify(one);
			assert(err is one || err is zero);
			if(err is one) r.add(k,v);
			else{
				foreach(lambda;lambdas){
					auto app=dApply(lambda,k).simplify(one);
					auto val=app[0.dℤ].simplify(one),scale=app[1.dℤ].simplify(one);
					r.add(val,(v*scale).simplify(one));
				}
			}
		}
		return r;
	}
	Dist assertTrue(DLambda lambda){
		Dist r;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			auto cond=dApply(lambda,k).simplify(one);
			assert(cond is one || cond is zero);
			if(dField(k,"`error").simplify(one) is one || cond is zero){
				r.add(dRecord(["`error":one]),v);
			}else{
				r.add(k,v);
			}
		}
		return r;
	}
	Dist eraseErrors(){
		Dist r;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			auto cond=dField(k,"`error").simplify(one);
			assert(cond is one || cond is zero);
			if(cond is one) continue;
			r.add(k,v);
		}
		return r;
	}
	Dist observe(DLambda lambda){
		Dist r;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			auto err=dField(k,"`error").simplify(one);
			assert(err is one || err is zero);
			if(err is one) r.add(k,v);
			else{
				auto cond=dApply(lambda,k).simplify(one);
				assert(cond is one || cond is zero,text(cond));
				if(cond is one) r.add(k,v);
			}
		}
		return r;
	}
	Distribution toDistribution(){
		auto r=new Distribution();
		auto var=r.declareVar("r");
		r.distribution=zero;
		r.error=zero;
		foreach(k,v;state){
			auto err=dField(k,"`error").simplify(one);
			assert(err is one || err is zero);
			if(err is one) r.error=r.error+v;
			else r.distribution=r.distribution+v*dDiscDelta(var,dField(k,"`value"));
		}
		r.simplify();
		r.orderFreeVars([var],false);
		return r;
	}
	MapX!(DExpr,DExpr) state;	
	SetX!string tmpVars;
	this(MapX!(DExpr,DExpr) state,SetX!string tmpVars){
		this.state=state;
		this.tmpVars=tmpVars;
	}
	Dist dup(){ return Dist(state.dup,tmpVars.dup); static assert(this.tupleof.length==2); }
	void addTmpVar(string var){ tmpVars.insert(var); }
	Dist marginalizeTemporaries(){
		if(!tmpVars.length) return this;
		Dist r;
		foreach(k,v;state){
			auto err=dField(k,"`error").simplify(one);
			assert(err is one || err is zero);
			if(err is one) r.add(k,v);
			else{
				auto rec=cast(DRecord)k;
				assert(!!rec);
				auto val=rec.values.dup;
				foreach(x;tmpVars) val.remove(x);
				r.add(dRecord(val),v);
			}
		}
		tmpVars.clear();
		return r;
	}
}

import lexer: Tok;
alias ODefExp=BinaryExp!(Tok!":=");
auto db1(){ return dDeBruijnVar(1); }
struct Interpreter{
	CompoundExp statements;
	Dist cur;
	this(CompoundExp statements){
		MapX!(DExpr,DExpr) state;
		state[dRecord(["`error":zero])]=one;
		this(statements,Dist(state,SetX!string.init));
	}
	this(CompoundExp statements,Dist cur){
		this.statements=statements;
		this.cur=cur;
	}
	DExpr runExp(Expression e){
		DExpr doIt(Expression e){
			if(auto pl=cast(PlaceholderExp)e) return dVar(pl.ident.name);
			if(auto id=cast(Identifier)e){
				if(!id.meaning&&id.name=="π") return dΠ;
				return dField(db1,id.name);
			}
			if(auto fe=cast(FieldExp)e){
				if(isBuiltIn(fe)){
					assert(0,"TODO");
				}
				return dField(doIt(fe.e),fe.f.name);
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
			if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
			if(cast(DivExp)e||cast(IDivExp)e){
				auto de=cast(ABinaryExp)e;
				auto e1=doIt(de.e1);
				auto e2=doIt(de.e2);
				cur=cur.assertTrue(dLambda(dIvr(DIvr.Type.neqZ,e2)));
				return cast(IDivExp)e?dFloor(e1/e2):e1/e2;
			}
			if(auto me=cast(ModExp)e) return doIt(me.e1)%doIt(me.e2);
			if(auto pe=cast(PowExp)e) return doIt(pe.e1)^^doIt(pe.e2);
			if(auto ce=cast(CatExp)e) return doIt(ce.e1)~doIt(ce.e2);
			if(auto ce=cast(BitOrExp)e) return dBitOr(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitXorExp)e) return dBitXor(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitAndExp)e) return dBitAnd(doIt(ce.e1),doIt(ce.e2));
			if(auto ume=cast(UMinusExp)e) return -doIt(ume.e);
			if(auto ume=cast(UNotExp)e) return dIvr(DIvr.Type.eqZ,doIt(ume.e));
			if(auto ume=cast(UBitNotExp)e) return -doIt(ume.e)-1;
			if(auto le=cast(LambdaExp)e){
				assert(0,"TODO: lambdas");
			}
			if(auto ce=cast(CallExp)e){
				auto id=cast(Identifier)ce.e;
				auto fe=cast(FieldExp)ce.e;
				DExpr thisExp=null;
				if(fe){
					id=fe.f;
					thisExp=doIt(fe.e);
				}
				if(auto fun=cast(FunctionDef)id.meaning){
					assert(0,text("TODO: ",ce));
				}
				switch(id.name){
					case "flip":
						// TODO: check that p is in [0,1]
						auto p=doIt(ce.arg);
						static int unique=0;
						auto tmp="`flip"~lowNum(++unique);
						cur.addTmpVar(tmp);
						cur=cur.flatMap(
							[dLambda(dTuple([dRUpdate(db1,tmp,zero),(one-p).simplify(one)])),
							 dLambda(dTuple([dRUpdate(db1,tmp,one),p]))]);
						return dField(db1,tmp);
					case "uniformInt": assert(0,text("TODO: ",ce));
					case "categorical": assert(0,text("TODO: ",ce));
					default: assert(0,text("TODO: ",ce));
				}
			}
			if(auto idx=cast(IndexExp)e) return dIndex(doIt(idx.e),doIt(idx.a[0])); // TODO: bounds checking
			if(auto sl=cast(SliceExp)e) return dSlice(doIt(sl.e),doIt(sl.l),doIt(sl.r)); // TODO: bounds checking
			if(auto le=cast(LiteralExp)e){
				if(le.lit.type==Tok!"0"){
					auto n=le.lit.str.split(".");
					if(n.length==1) n~="";
					return (dℤ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length)).simplify(one);
				}
			}
			if(auto cmp=cast(CompoundExp)e){
				if(cmp.s.length==1)
					return doIt(cmp.s[0]);
			}else if(auto ite=cast(IteExp)e){
				auto cond=runExp(ite.cond);
				auto curP=cur.eraseErrors();
				cur=cur.observe(dLambda(dIvr(DIvr.Type.neqZ,cond).simplify(one)));
				curP=curP.observe(dLambda(dIvr(DIvr.Type.eqZ,cond).simplify(one)));
				auto thenIntp=Interpreter(ite.then,cur);
				auto r=dIvr(DIvr.Type.neqZ,cond)*thenIntp.runExp(ite.then.s[0]);
				cur=thenIntp.cur;
				assert(!!ite.othw);
				auto othwIntp=Interpreter(ite.othw,curP);
				r=r+dIvr(DIvr.Type.eqZ,cond)*othwIntp.runExp(ite.othw);
				curP=othwIntp.cur;
				cur+=curP;
				return r;
			}else if(auto tpl=cast(TupleExp)e){
				auto dexprs=tpl.e.map!doIt.array;
				return dTuple(dexprs);
			}else if(auto arr=cast(ArrayExp)e){
				auto dexprs=arr.e.map!doIt.array;
				return dArray(dexprs);
			}else if(auto ae=cast(AssertExp)e){
				if(auto c=runExp(ae.e)){
					cur=cur.assertTrue(dLambda(dIvr(DIvr.Type.neqZ,c)));
					return dTuple([]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)e){
				return doIt(tae.e);
			}else if(cast(Type)e)
				return dTuple([]); // 'erase' types
			else{
				enum common=q{
					auto e1=doIt(b.e1),e2=doIt(b.e2);
				};
				if(auto b=cast(AndExp)e){
					auto e1=doIt(b.e1), e2=doIt(b.e2);
					return e1*e2;
				}else if(auto b=cast(OrExp)e){
					auto e1=doIt(b.e1), e2=doIt(b.e2);
					return dIvr(DIvr.Type.neqZ,e1+e2);
				}else with(DIvr.Type)if(auto b=cast(LtExp)e){
					mixin(common);
					return dIvr(lZ,e1-e2);
				}else if(auto b=cast(LeExp)e){
					mixin(common);
					return dIvr(leZ,e1-e2);
				}else if(auto b=cast(GtExp)e){
					mixin(common);
					return dIvr(lZ,e2-e1);
				}else if(auto b=cast(GeExp)e){
					mixin(common);
					return dIvr(leZ,e2-e1);
				}else if(auto b=cast(EqExp)e){
					mixin(common);
					return dIvr(eqZ,e2-e1);
				}else if(auto b=cast(NeqExp)e){
					mixin(common);
					return dIvr(neqZ,e2-e1);
				}
			}
			assert(0,text("TODO: ",e));
		}
		return doIt(e);
	}
	void assignTo(Expression to,DExpr val){
		if(auto id=cast(Identifier)to){
			auto lambda=dLambda(dRUpdate(db1,id.name,val));
			cur=cur.map(lambda);
		}else{
			assert(0,text("TODO: assign to ",to));
		}
	}
	void runStm(Expression e,ref Dist retDist){
		if(auto nde=cast(DefExp)e){
			auto de=cast(ODefExp)nde.initializer;
			assert(!!de);
			if(auto id=cast(Identifier)de.e1){
				auto lambda=dLambda(dRUpdate(db1,id.name,runExp(de.e2)));
				cur=cur.map(lambda);
				cur=cur.marginalizeTemporaries();
			}else{
				assert(0,text("TODO: ",e));
			}
		}else if(auto ae=cast(AssignExp)e){
			assignTo(ae.e1,runExp(ae.e2));
			cur=cur.marginalizeTemporaries();
		}else if(isOpAssignExp(e)){
						DExpr perform(DExpr a,DExpr b){
				if(cast(OrAssignExp)e) return dIvr(DIvr.Type.neqZ,dIvr(DIvr.Type.neqZ,a)+dIvr(DIvr.Type.neqZ,b));
				if(cast(AndAssignExp)e) return dIvr(DIvr.Type.neqZ,a)*dIvr(DIvr.Type.neqZ,b);
				if(cast(AddAssignExp)e) return a+b;
				if(cast(SubAssignExp)e) return a-b;
				if(cast(MulAssignExp)e) return a*b;
				if(cast(DivAssignExp)e||cast(IDivAssignExp)e){
					cur=cur.assertTrue(dLambda(dIvr(DIvr.Type.neqZ,b)));
					return cast(IDivAssignExp)e?dFloor(a/b):a/b;
				}
				if(cast(ModAssignExp)e) return a%b;
				if(cast(PowAssignExp)e){
					// TODO: enforce constraints on domain
					return a^^b;
				}
				if(cast(CatAssignExp)e) return a~b;
				if(cast(BitOrAssignExp)e) return dBitOr(a,b);
				if(cast(BitXorAssignExp)e) return dBitXor(a,b);
				if(cast(BitAndAssignExp)e) return dBitAnd(a,b);
				assert(0);
			}
			auto be=cast(ABinaryExp)e;
			assert(!!be);
			auto lhs=runExp(be.e1);
			auto rhs=runExp(be.e2);
			assignTo(be.e1,perform(lhs,rhs));
			cur=cur.marginalizeTemporaries();
		}else if(auto call=cast(CallExp)e){
			runExp(call);
		}else if(auto ite=cast(IteExp)e){
			auto cond=runExp(ite.cond);
			auto curP=cur.eraseErrors();
			cur=cur.observe(dLambda(dIvr(DIvr.Type.neqZ,cond)));
			curP=curP.observe(dLambda(dIvr(DIvr.Type.eqZ,cond).simplify(one)));
			auto thenIntp=Interpreter(ite.then,cur);
			thenIntp.run(retDist);
			cur=thenIntp.cur;
			if(ite.othw){
				auto othwIntp=Interpreter(ite.othw,curP);
				othwIntp.run(retDist);
				curP=othwIntp.cur;
			}
			cur+=curP;
		}else if(auto re=cast(RepeatExp)e){
			auto rep=runExp(re.num);
			rep=dApply(rep,dTuple([])).simplify(one);
			assert(0,text("TODO: ",re));
		}else if(auto fe=cast(ForExp)e){
			assert(0,text("TODO: ",fe));
		}else if(auto re=cast(ReturnExp)e){
			auto value = runExp(re.e);
			retDist += cur.map(dLambda(dRecord(["`error":dField(db1,"`error"),"`value":value])));
			cur=Dist.init;
		}else if(auto ae=cast(AssertExp)e){
			auto cond=dIvr(DIvr.Type.neqZ,runExp(ae.e));
			cur=cur.assertTrue(dLambda(cond));
		}else if(auto oe=cast(ObserveExp)e){
			auto cond=dIvr(DIvr.Type.neqZ,runExp(oe.e));
			cur=cur.observe(dLambda(cond));
		}else if(auto ce=cast(CommaExp)e){
			runStm(ce.e1,retDist);
			runStm(ce.e2,retDist);
		}else{
			assert(0,text("TODO: ",e));
		}
	}
	void run(ref Dist retDist){
		foreach(s;statements.s){
			runStm(s,retDist);
			// writeln("cur: ",cur);
		}
	}
}
