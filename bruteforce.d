import std.conv: text;
import std.string: split;
import std.algorithm: map;
import std.array: array;
import std.string: startsWith;

import backend,options;
import distrib,error;
import dexpr,hashtable,util;
import expression,declaration,type;
import semantic_;

class Bruteforce: Backend{
	this(string sourceFile){
		this.sourceFile=sourceFile;
	}
	override Distribution analyze(FunctionDef def,ErrorHandler err){
		auto interpreter=Interpreter(def,def.body_,false);
		auto ret=distInit();
		interpreter.run(ret);
		return ret.toDistribution();
	}
private:
	string sourceFile;
}

auto distInit(){
	return Dist(MapX!(DExpr,DExpr).init,zero,SetX!string.init);
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
		error=(error+r.error).simplify(one);
	}
	Dist map(DLambda lambda){
		auto r=distInit;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state) r.add(dApply(lambda,k).simplify(one),v);
		return r;
	}
	DExpr expectation(DLambda lambda){
		DExpr r=zero;
		foreach(k,v;state) r=(r+v*dApply(lambda,k)).simplify(one);
		return r;
	}
	Dist pushFrame(){
		return map(dLambda(dRecord(["`frame":db1])));
	}
	Dist popFrame(string tmpVar){
		addTmpVar(tmpVar);
		return map(dLambda(dRUpdate(dField(db1,"`frame"),tmpVar,dField(db1,"`value"))));
	}
	Dist flatMap(DLambda[] lambdas){
		auto r=distInit;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			foreach(lambda;lambdas){
				auto app=dApply(lambda,k).simplify(one);
				auto val=app[0.dℤ].simplify(one),scale=app[1.dℤ].simplify(one);
				r.add(val,(v*scale).simplify(one));
			}
		}
		return r;
	}
	Dist assertTrue(DLambda lambda){
		auto r=distInit;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			auto cond=dApply(lambda,k).simplify(one);
			if(cond is one || cond is zero){
				if(cond is zero){
					r.error = (r.error + v).simplify(one);
				}else{
					r.add(k,v);
				}
			}else{
				r.error = (r.error + v*dIvr(DIvr.Type.eqZ,cond)).simplify(one);
				r.add(k,(v*cond).simplify(one));
			}
		}
		return r;
	}
	Dist eraseErrors(){
		auto r=dup();
		error=zero;
		return r;
	}
	Dist observe(DLambda lambda){
		auto r=distInit;
		r.tupleof[1..$]=this.tupleof[1..$];
		foreach(k,v;state){
			auto cond=dApply(lambda,k).simplify(one);
			if(cond is one || cond is zero){
				if(cond is one) r.add(k,v);
			}else{
				r.add(k,(v*cond).simplify(one));
			}
		}
		return r;
	}
	Distribution toDistribution(){
		auto r=new Distribution();
		auto var=r.declareVar("r");
		r.distribution=zero;
		foreach(k,v;state) r.distribution=r.distribution+v*dDiscDelta(var,dField(k,"`value"));
		r.error=error;
		r.simplify();
		r.orderFreeVars([var],false);
		return r;
	}
	MapX!(DExpr,DExpr) state;
	DExpr error;
	SetX!string tmpVars;
	@disable this();
	this(MapX!(DExpr,DExpr) state,DExpr error,SetX!string tmpVars){
		this.state=state;
		this.error=error;
		this.tmpVars=tmpVars;
	}
	Dist dup(){ return Dist(state.dup,error,tmpVars.dup); static assert(this.tupleof.length==3); }
	void addTmpVar(string var){ tmpVars.insert(var); }
	Dist marginalizeTemporaries(){
		if(!tmpVars.length) return this;
		auto r=distInit;
		r.error=error;
		foreach(k,v;state){
			auto rec=cast(DRecord)k;
			assert(!!rec,text(k));
			auto val=rec.values.dup;
			foreach(x;tmpVars) val.remove(x);
			r.add(dRecord(val),v);
		}
		tmpVars.clear();
		return r;
	}
	DExpr flip(DExpr p){
		// TODO: check that p is in [0,1]
		static int unique=0;
		auto tmp="`flip"~lowNum(++unique);
		addTmpVar(tmp);
		this=flatMap(
			[dLambda(dTuple([dRUpdate(db1,tmp,zero),(one-p).simplify(one)])),
			 dLambda(dTuple([dRUpdate(db1,tmp,one),p]))]);
		return dField(db1,tmp);
	}
	DExpr uniformInt(DExpr arg){
		// TODO: check constraints on arguments
		auto r=distInit;
		r.tupleof[1..$]=this.tupleof[1..$];
		auto lambda=dLambda(arg);
		static int unique=0;
		auto tmp="`uniformInt"~lowNum(++unique);
		addTmpVar(tmp);
		foreach(k,v;state){
			auto ab=dApply(lambda,k).simplify(one);
			auto a=ab[0.dℤ].simplify(one), b=ab[1.dℤ].simplify(one);
			auto az=cast(Dℤ)a, bz=cast(Dℤ)b;
			assert(az&&bz,"TODO");
			auto num=dℤ(bz.c-az.c+1);
			if(num.c<=0) assert(0,"TODO");
			auto nv=(v/num).simplify(one);
			for(ℤ i=az.c;i<=bz.c;++i) r.add(dRUpdate(k,tmp,i.dℤ).simplify(one),nv);
		}
		this=r;
		return dField(db1,tmp);
	}
}

import lexer: Tok;
alias ODefExp=BinaryExp!(Tok!":=");
auto db1(){ return dDeBruijnVar(1); }
struct Interpreter{
	FunctionDef functionDef;
	CompoundExp statements;
	Dist cur;
	bool hasFrame=false;
	this(FunctionDef functionDef,CompoundExp statements,bool hasFrame){
		auto cur=distInit;
		cur.state[dRecord()]=one;
		this(functionDef,statements,cur,hasFrame);
	}
	this(FunctionDef functionDef,CompoundExp statements,Dist cur,bool hasFrame){
		this.functionDef=functionDef;
		this.statements=statements;
		this.cur=cur;
		this.hasFrame=hasFrame;
	}
	DExpr runExp(Expression e){
		if(!cur.state.length) return zero;
		DExpr doIt(Expression e){
			if(auto pl=cast(PlaceholderExp)e) return dVar(pl.ident.name);
			if(auto id=cast(Identifier)e){
				if(!id.meaning&&id.name=="π") return dΠ;
				return dField(db1,id.name);
			}
			if(auto fe=cast(FieldExp)e){
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
					auto arg=doIt(ce.arg); // TODO: allow temporaries within arguments
					auto ncur=cur.pushFrame();
					DExpr inFrame(DExpr arg){
						return arg.substitute(db1,dField(db1,"`frame"));
					}
					if(fun.isConstructor){
						assert(!thisExp,"TODO");
						ncur=ncur.map(dLambda(dRUpdate(db1,"this",dRecord())));
					}else if(thisExp) ncur=ncur.map(dLambda(dRUpdate(db1,"this",inFrame(thisExp))));
					if(fun.isTuple){
						DExpr updates=db1;
						foreach(i,prm;fun.params){
							updates=dRUpdate(updates,prm.getName,inFrame(arg[i.dℤ]));
						}
						if(updates !is db1) ncur=ncur.map(dLambda(updates));
					}else{
						assert(fun.params.length==1);
						ncur=ncur.map(dLambda(dRUpdate(db1,fun.params[0].getName,inFrame(arg))));
					}
					auto intp=Interpreter(fun,fun.body_,ncur,true);
					auto nndist = distInit();
					intp.run(nndist);
					static uniq=0;
					string tmp="`call"~lowNum(++uniq);
					cur=nndist.popFrame(tmp);
					if(thisExp&&!fun.isConstructor){
						assignTo(thisExp,dField(db1,tmp)[1.dℤ]);
						assignTo(dVar(tmp),dField(db1,tmp)[0.dℤ]);
					}
					return dField(db1,tmp);
				}
				switch(id.name){
					case "flip":
						auto arg=doIt(ce.arg);
						return cur.flip(arg);
					case "uniformInt":
						auto arg=doIt(ce.arg);
						return cur.uniformInt(arg);
					case "categorical": assert(0,text("TODO: ",ce));
					case "Expectation": // TODO: condition on frame
						auto arg=doIt(ce.arg);
						return cur.expectation(dLambda(arg));
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
				auto thenIntp=Interpreter(functionDef,ite.then,cur,hasFrame);
				auto r=dIvr(DIvr.Type.neqZ,cond)*thenIntp.runExp(ite.then.s[0]);
				cur=thenIntp.cur;
				assert(!!ite.othw);
				auto othwIntp=Interpreter(functionDef,ite.othw,curP,hasFrame);
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
					DExprSet disjuncts;
					void collect(Expression e){
						if(auto or=cast(OrExp)e){
							collect(or.e1);
							collect(or.e2);
						}else disjuncts.insert(doIt(e));
					}
					collect(e);
					return dIvr(DIvr.Type.neqZ,dPlus(disjuncts));
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
	void assignTo(DExpr lhs,DExpr rhs){
		if(auto id=cast(DVar)lhs){
			auto lambda=dLambda(dRUpdate(db1,id.name,rhs));
			cur=cur.map(lambda);
		}else if(auto idx=cast(DIndex)lhs){
			assignTo(idx.e,dIUpdate(idx.e,idx.i,rhs));
		}else if(auto fe=cast(DField)lhs){
			if(fe.e is db1){
				assignTo(dVar(fe.f),rhs);
				return;
			}
			assignTo(fe.e,dRUpdate(fe.e,fe.f,rhs));
		}else if(auto tpl=cast(DTuple)lhs){
			foreach(i;0..tpl.values.length)
				assignTo(tpl[i],rhs[i.dℤ].simplify(one));
		}else if(cast(DPlus)lhs||cast(DMult)lhs){
			// TODO: this could be the case (if cond { a } else { b }) = c;
			// (this is also not handled in the symbolic backend at the moment)
		}else{
			assert(0,text("TODO: ",lhs," = ",rhs));
		}
	}
	void runStm(Expression e,ref Dist retDist){
		if(!cur.state.length) return;
		if(opt.trace) writeln("statement: ",e);
		if(auto nde=cast(DefExp)e){
			auto de=cast(ODefExp)nde.initializer;
			assert(!!de);
			auto lhs=runExp(de.e1).simplify(one), rhs=runExp(de.e2).simplify(one);
			assignTo(lhs,rhs);
			cur=cur.marginalizeTemporaries();
		}else if(auto ae=cast(AssignExp)e){
			auto lhs=runExp(ae.e1),rhs=runExp(ae.e2);
			assignTo(lhs,rhs);
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
			auto lhs=runExp(be.e1); // TODO: keep lhs stable!
			auto rhs=runExp(be.e2);
			assignTo(lhs,perform(lhs,rhs));
			cur=cur.marginalizeTemporaries();
		}else if(auto call=cast(CallExp)e){
			runExp(call);
		}else if(auto ite=cast(IteExp)e){
			auto cond=runExp(ite.cond);
			auto curP=cur.eraseErrors();
			cur=cur.observe(dLambda(dIvr(DIvr.Type.neqZ,cond)));
			curP=curP.observe(dLambda(dIvr(DIvr.Type.eqZ,cond).simplify(one)));
			auto thenIntp=Interpreter(functionDef,ite.then,cur,hasFrame);
			thenIntp.run(retDist);
			cur=thenIntp.cur;
			if(ite.othw){
				auto othwIntp=Interpreter(functionDef,ite.othw,curP,hasFrame);
				othwIntp.run(retDist);
				curP=othwIntp.cur;
			}
			cur+=curP;
		}else if(auto re=cast(RepeatExp)e){
			auto rep=runExp(re.num);
			if(auto z=cast(Dℤ)rep){
				auto intp=Interpreter(functionDef,re.bdy,cur,hasFrame);
				foreach(x;0.ℤ..z.c){
					intp.run(retDist);
					// TODO: marginalize locals
				}
				cur=intp.cur;
			}else assert(0,text("TODO: ",re));
		}else if(auto fe=cast(ForExp)e){
			auto l=runExp(fe.left), r=runExp(fe.right);
			auto lz=cast(Dℤ)l,rz=cast(Dℤ)r;
			if(lz&&rz){
				auto intp=Interpreter(functionDef,fe.bdy,cur,hasFrame);
				for(ℤ j=lz.c+cast(int)fe.leftExclusive;j+cast(int)fe.rightExclusive<=rz.c;j++){
					intp.assignTo(dVar(fe.var.name),dℤ(j));
					intp.run(retDist);
					// TODO: marginalize locals
				}
				cur=intp.cur;
			}else assert(0,text("TODO: ",fe));
		}else if(auto re=cast(ReturnExp)e){
			auto value = runExp(re.e);
			if(functionDef.context&&functionDef.contextName.startsWith("this")){
				value = dTuple([value,dField(db1,"this")]);
			}
			auto rec=["`value":value];
			if(hasFrame) rec["`frame"]=dField(db1,"`frame");
			retDist += cur.map(dLambda(dRecord(rec)));
			cur=distInit;
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
