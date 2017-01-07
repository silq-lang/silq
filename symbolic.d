// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.stdio, std.conv, std.format, std.string, std.range, std.algorithm;

import options, backend;
import lexer, expression, declaration, type, semantic_, error;
import distrib, dexpr, util;

class Symbolic: Backend{
	this(string sourceFile){
		this.sourceFile=sourceFile;
	}
	override Distribution analyze(FunctionDef def,ErrorHandler err){
		auto dist=new Distribution();
		DExpr[] args;
		foreach(a;def.params) args~=dist.declareVar(a.getName);
		DVar ctx=null;
		if(def.context){
			ctx=dist.declareVar(def.contextName);
			if(def.isConstructor){
				auto dd=def.scope_.getDatDecl();
				assert(dd && dd.dtype);
				dist.initialize(ctx,dRecord(),dd.dtype);
				ctx=null;
			}
		}
		if(!def.name||def.getName!="main"||args.length||def.isNested) // TODO: move this decision to caller
			dist.addArgs(args,def.isTuple,ctx);
		return analyzeWith(def,dist,err);
	}

	Distribution analyzeWith(FunctionDef def,Distribution dist,ErrorHandler err){
		auto a=Analyzer(this,dist,err);
		Distribution retDist=null;
		a.analyze(def.body_,retDist,def);
		a.applyRetDist(def,retDist);
		a.dist.simplify();
		// dw(def," ",a.dist);
		return a.dist;
	}


	Distribution getSummary(FunctionDef fun,Location loc,ErrorHandler err){
		if(fun !in summaries){
			summaries[fun]=new Distribution();
			summaries[fun].distribute(mone);
			summaries[fun]=analyze(fun,err);
		}else if(summaries[fun].distribution is mone){
			// TODO: support special cases.
			err.error("recursive dependencies unsupported",loc);
			return null;
		}
		return summaries[fun];
	}
private:
	Distribution[FunctionDef] summaries;
	string sourceFile;
}


alias ODefExp=BinaryExp!(Tok!":=");

private struct Analyzer{
	Symbolic be;
	Distribution dist;
	ErrorHandler err;
	DExpr[][string] arrays;
	DExpr[DVar] deterministic;
	DExpr transformExp(Exp e){
		class Unwind: Exception{ this(){ super(""); } }
		void unwind(){ throw new Unwind(); }
		import scope_;
		DExpr getContextFor(Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{
			DExpr r=null;
			auto meaningScope=meaning.scope_;
			if(auto fd=cast(FunctionDef)meaning)
				meaningScope=fd.realScope;
			assert(sc&&sc.isNestedIn(meaningScope));
			for(auto csc=sc;csc !is meaningScope;csc=(cast(NestedScope)csc).parent){
				void add(string name){
					if(!r) r=dVar(name);
					else r=dField(r,name);
					assert(!!cast(NestedScope)csc);
				}
				assert(cast(NestedScope)csc);
				if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
				if(cast(AggregateScope)csc) add("outer");
				else if(auto fsc=cast(FunctionScope)csc) add(fsc.getFunction().contextName); // TODO: shouldn't be able to clash with user defined variables
			}
			return r;
		}
		DExpr readVariable(VarDecl var,Scope from){
			DExpr r=getContextFor(var,from);
			if(r) return dField(r,var.getName);
			auto v=dVar(var.getName);
			if(v in dist.freeVars) return v;
			return null;
		}
		DExpr buildContextFor()(Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{ // template, forward references 'doIt'
			if(meaning.scope_ !is sc) return getContextFor(meaning,sc);
			DExpr[string] record;
			foreach(vd;&sc.all!VarDecl)
				if(auto var=readVariable(vd,sc))
					record[vd.getName]=var;
			for(auto csc=sc;;csc=(cast(NestedScope)csc).parent){
				if(auto fsc=cast(FunctionScope)csc)
					foreach(p;fsc.getFunction().params)
						record[p.getName]=dVar(p.getName);
				if(!cast(NestedScope)csc) break;
				if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
				if(cast(AggregateScope)csc){
					record["outer"]=dVar("outer");
					break;
				}
				if(auto fsc=cast(FunctionScope)csc){
					auto cname=fsc.getFunction().contextName;
					record[cname]=dVar(cname);
					break;
				}
			}
			return dRecord(record);
		}
		DExpr lookupMeaning(Identifier id)in{assert(id && id.scope_,text(id," ",id.loc));}body{
			if(!id.meaning||!id.scope_||!id.meaning.scope_){
				if(isBuiltIn(id)){ // TODO: this is somewhat hacky
					static DExpr[string] builtIn;
					auto fty=cast(FunTy)id.type;
					assert(!!fty);
					if(id.name !in builtIn){
						auto bdist=new Distribution();
						auto names=iota(fty.nargs).map!(i=>new Identifier("x"~lowNum(i+1))).array;
						auto arg=fty.isTuple?new TupleExp(cast(Expression[])names):names[0];
						auto params=new Parameter[](names.length);
						foreach(i,ref p;params) p=new Parameter(names[i],fty.argTy(i));
						auto call=new CallExp(id,arg,fty.isSquare);
						auto bdy=new CompoundExp([new ReturnExp(call)]);
						auto fdef=new FunctionDef(null,params,fty.isTuple,null,bdy);
						fdef.isSquare=fty.isSquare;
						auto sc=new TopScope(err);
						fdef.scope_=sc;
						fdef=cast(FunctionDef)presemantic(fdef,sc);
						assert(!!fdef);
						bdist=be.analyze(functionDefSemantic(fdef,sc),err);
						builtIn[id.name]=bdist.toDExpr();
					}
					return builtIn[id.name];
				}
				err.error("undefined variable '"~id.name~"'",id.loc);
				return null;
			}
			if(auto vd=cast(VarDecl)id.meaning){
				DExpr r=getContextFor(id.meaning,id.scope_);
				return r?dField(r,id.name):dVar(id.name);
			}
			if(auto fd=cast(FunctionDef)id.meaning){
				auto summary=be.getSummary(fd,id.loc,err);
				if(fd.isNested)
					return summary.toDExprWithContext(buildContextFor(fd,id.scope_));
				return summary.toDExpr();
			}
			err.error("unsupported",id.loc);
			return null;
		}
		DExpr doIt(Exp e){
			if(e.type == typeTy) return dTuple([]); // TODO: get rid of this
			if(cast(Declaration)e||cast(BinaryExp!(Tok!":="))e){
				err.error("definition must be at top level",e.loc);
				unwind();
			}
			if(auto pl=cast(PlaceholderExp)e)
				return dVar(pl.ident.name);
			if(auto id=cast(Identifier)e){
				if(!id.meaning&&id.name=="π") return dΠ;
				if(id.name in arrays){
					err.error("missing array index",id.loc);
					unwind();
				}
				if(auto r=lookupMeaning(id)) return r;
				unwind();
			}
			if(auto fe=cast(FieldExp)e){
				if(auto id=cast(Identifier)fe.e){
					if(id.name in arrays && fe.f.name=="length")
						return ℤ(arrays[id.name].length).dℤ;
				}
				if(isBuiltIn(fe)){
					bool ok=false;
					if(auto at=cast(ArrayTy)fe.e.type){
						assert(fe.f.name=="length");
						ok=true;
					}else if(auto ce=cast(CallExp)fe.e.type){
						if(auto id=cast(Identifier)ce.e){
							assert(ce.arg.type == typeTy);
							auto tt=ce.arg;
							if(id.name=="Distribution"){
								static DExpr get(DExpr distr,Expression tt,Expression type,string name){
									switch(name){
										case "sample":
											auto idist=new Distribution();
											idist.addArgs([],true,null);
											auto d=idist.declareVar("`d");
											auto dist=dDistApply(distr,d);
											idist.distribute(dist*dIvr(DIvr.Type.eqZ,dField(d,"tag")-one));
											idist.error=dInt(d,dIvr(DIvr.Type.eqZ,dField(d,"tag"))*dist);
											auto r=idist.declareVar("`r");
											idist.initialize(r,dField(d,"val"),tt);
											idist.marginalize(d);
											idist.orderFreeVars([r],false);
											return idist.toDExpr().simplify(one);
										case "then": // d.then(f) <-> infer(()=>f(d.sample()))
											auto idist=new Distribution();
											auto f=idist.declareVar("`f");
											idist.addArgs([f],false,null);
											auto rdist=new Distribution();
											rdist.addArgs([],true,null);
											auto d=rdist.declareVar("`d");
											auto dist=dDistApply(distr,d);
											rdist.distribute(dist*dIvr(DIvr.Type.eqZ,dField(d,"tag")-one));
											rdist.error=dInt(d,dIvr(DIvr.Type.eqZ,dField(d,"tag"))*dist);
											auto x=rdist.declareVar("`x");
											rdist.initialize(x,dField(d,"val"),tt);
											auto faty=cast(ForallTy)type;
											assert(!!faty);
											auto fety=cast(FunTy)faty.cod;
											assert(!!fety);
											auto fty=cast(FunTy)fety.dom;
											assert(!!fty);
											auto summary=Distribution.fromDExpr(f,1,["`r".dVar],false,[fty.cod]);
											auto db1=dDeBruijnVar(1);
											auto tmp=rdist.call(summary,x,fty.dom);
											auto r=rdist.declareVar("`r");
											rdist.initialize(r,tmp,tt);
											rdist.marginalize(d);
											rdist.marginalize(x);
											rdist.marginalizeTemporaries();
											rdist.orderFreeVars([r],false);
											rdist.renormalize();
											auto res=idist.declareVar("`res");
											idist.initialize(res,dDistApply(rdist.toDExpr(),dLambda(one)),fety.cod);
											idist.marginalize(f);
											idist.orderFreeVars([res],false);
											auto gdist=new Distribution(); // generic argument
											auto a=gdist.declareVar("`a");
											gdist.addArgs([a],false,null);
											auto fun=gdist.declareVar("`fun");
											gdist.initialize(fun,idist.toDExpr(),faty.cod);
											gdist.marginalize(a);
											gdist.orderFreeVars([fun],false);
											return gdist.toDExpr().simplify(one);
										case "expectation": // TODO: handle non-convergence
											assert(tt == ℝ);
											auto d="`d".dVar,x="`x".dVar;
											auto pdf=dInt(d,dDistApply(distr,d)*dIvr(DIvr.Type.eqZ,dField(d,"tag")-one)*dDelta(x,dField(d,"val"),ℝ));
											auto total=dInt(x,pdf),expct=dInt(x,x*pdf);
											auto idist=new Distribution();
											idist.addArgs([],true,null);
											idist.assertTrue(dIvr(DIvr.Type.neqZ,total),"cannot compute conditional expectation");
											auto r=idist.declareVar("`r");
											idist.initialize(r,expct/total,ℝ);
											idist.orderFreeVars([r],false);
											return idist.toDExpr().simplify(one);
										default: assert(0);
									}
								}
								import std.functional: memoize;
								return memoize!get(doIt(fe.e),tt,fe.type,fe.f.name);
							}
						}
					}
				}else if(auto fd=cast(FunctionDef)fe.f.meaning){
					assert(fe.f.scope_&&fe.f.meaning.scope_);
					auto summary=be.getSummary(fd,fe.f.loc,err);
					return summary.toDExprWithContext(doIt(fe.e),true);
				}else assert(cast(VarDecl)fe.f.meaning&&fe.f.scope_&&fe.f.meaning.scope_);
				return dField(doIt(fe.e),fe.f.name);
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
			if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
			if(cast(DivExp)e||cast(IDivExp)e){
				auto de=cast(ABinaryExp)e;
				auto e1=doIt(de.e1);
				auto e2=doIt(de.e2);
				dist.assertTrue(dIvr(DIvr.Type.neqZ,e2),formatError("division by zero",e.loc));
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
				auto summary=be.getSummary(le.fd,le.loc,err);
				if(le.fd.isNested)
					return summary.toDExprWithContext(buildContextFor(le.fd,le.fd.scope_));
				return summary.toDExpr();
			}
			if(auto ce=cast(CallExp)e){
				auto id=cast(Identifier)ce.e;
				auto fe=cast(FieldExp)ce.e;
				DExpr thisExp=null;
				if(fe){
					id=fe.f;
					thisExp=doIt(fe.e);
				}
				if(id){
					if(auto fun=cast(FunctionDef)id.meaning){
						auto summary=be.getSummary(fun,ce.loc,err);
						if(!summary) unwind();
						DExpr arg=doIt(ce.arg);
						if(!arg) unwind();
						auto funty=cast(FunTy)ce.e.type;
						assert(!!funty);
						auto argty=ce.arg.type;
						assert(argty == funty.dom,text(argty," ",funty.dom));
						if(thisExp&&!fun.isConstructor){
							arg=dTuple([arg,thisExp]);
							argty=tupleTy([argty,fe.e.type]);
						}
						if(!thisExp)if(fun.isNested){ // nested function calls
							assert(id.scope_,text(id," ",id.loc));
							auto ctx=buildContextFor(fun,id.scope_);
							assert(!!ctx);
							arg=dTuple([arg,ctx]);
							argty=tupleTy([argty,contextTy]);
						}
						auto r=dist.call(summary,arg,argty);
						if(thisExp&&!fun.isConstructor){
							DExpr thisr;
							auto tpl=cast(DTuple)r;
							assert(!!tpl);
							r=tpl.values[0];
							thisr=tpl.values[1];
							assert(thisr&&fe);
							assignTo(thisExp,thisr,fe.e.type,ce.loc);
						}
						return r;
					}
					auto arg=util.among(id.name,"categorical","dirac","Dirac","SampleFrom")?null:doIt(ce.arg);
					switch(id.name){
					case "array": // TODO: make polymorphic
						assert(ce.arg.type==typeTy);
						auto idist=new Distribution();
						auto len=idist.declareVar("`len"),init=idist.declareVar("`init");
						idist.addArgs([len,init],true,null);
						auto r=idist.declareVar("`r");
						idist.initialize(r,dConstArray(len,init),arrayTy(ce.arg));
						idist.marginalize(init);
						idist.marginalize(len);
						idist.orderFreeVars([r],false);
						return idist.toDExpr();
					case "readCSV":
						err.error(text("call to 'readCSV' only supported as the right hand side of an assignment"),ce.loc);
						unwind();
						assert(0);
					case "exp":
						if(ce.arg.type!=ℝ)
							err.error("expected one real argument to exp",ce.loc);
						return dE^^arg;
					case "log":
						if(ce.arg.type!=ℝ)
							err.error("expected one real argument to log",ce.loc);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-arg),formatError("nonpositive argument to log",e.loc));
						return dLog(arg);
					case "abs":
						if(ce.arg.type!=ℝ)
							err.error("expected one argument to abs",ce.loc);
						return dAbs(doIt(ce.arg));
					case "floor":
						if(ce.arg.type!=ℝ)
							err.error("expected one real argument to floor",ce.loc);
						return dFloor(arg);
					case "ceil":
						if(ce.arg.type!=ℝ)
							err.error("expected one real argument to floor",ce.loc);
						return dCeil(arg);
					case "cosUnifDist": // TODO: Remove
						auto var=dist.getTmpVar("__g");
						dist.distribute(one/dΠ*(1-var^^2)^^-(one/2) * dBounded!"[]"(var,-one, one) * dIvr(DIvr.Type.neqZ,var-one)*dIvr(DIvr.Type.neqZ,var+one));
						return var;
					case "categorical":
						if(ce.arg.type!=arrayTy(ℝ)){
							err.error("expected one argument (ps: ℝ[]) to categorical",ce.loc);
							unwind();
						}
						auto idd=cast(Identifier)ce.arg;
						if(idd && idd.name in arrays){
							// DExpr sum=zero;
							auto array=arrays[idd.name];

							foreach(x;array){
								dist.assertTrue(dIvr(DIvr.Type.leZ,-x),"probability of category should be non-negative");
								// sum=sum+x;
							}
							// dist.assertTrue(dIvr(DIvr.Type.eqZ,sum-1),"probabilities should sum up to 1"); // TODO: don't enforce this to vigorously for floats
							DExpr d=zero;
							auto var=dist.getTmpVar("__c");
							foreach(i,x;array) d=d+x*dDelta(var,dℤ(i),ℝ);
							dist.distribute(d);
							return var;
						}else{
							auto p=doIt(ce.arg);
							auto dbv=dDeBruijnVar(1);
							dist.assertTrue(dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length")*dIvr(DIvr.Type.lZ,p[dbv])))),"probability of category should be non-negative"); // TODO: dProd?
							dist.assertTrue(dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv])-1),"probabilities should sum up to 1");
							auto var=dist.getTmpVar("__c");
							dist.distribute(categoricalPDF(var,p));
							return var;
							//err.error("argument to categorical should be an array",ce.loc);
							//unwind();
						}
					case "dirac":
						assert(ce.arg.type == typeTy);
						auto idist=new Distribution();
						auto x=idist.declareVar("`x");
						idist.addArgs([x],false,null);
						idist.orderFreeVars([x],false);
						return idist.toDExpr();
					case "Dirac":
						assert(ce.arg.type == typeTy);
						auto idist=new Distribution();
						auto x=idist.declareVar("`x");
						auto darg=idist.declareVar("`arg");
						idist.addArgs([darg],false,null);
						idist.distribute(pdf!"dirac"(x,[darg]));
						idist.marginalize(darg);
						idist.orderFreeVars([x],false);
						auto rdist=new Distribution();
						auto varg=rdist.declareVar("`varg");
						rdist.addArgs([varg],false,null);
						auto r=rdist.declareVar("`r");
						auto db1=dDeBruijnVar(1);
						auto res=dApply(idist.toDExpr(),dLambda(dDelta(db1,varg,ce.arg.type)));
						auto fty=cast(FunTy)ce.type;
						assert(!!fty);
						rdist.initialize(r,res,fty.cod);
						rdist.marginalize(varg);
						rdist.orderFreeVars([r],false);
						return rdist.toDExpr();
					case "bernoulli": goto case "flip";
					case "Bernoulli": goto case "Flip";
					foreach(name;ToTuple!distribNames){
						static if(!util.among(name,"categorical","dirac")){
							case name:
								auto nargs=paramNames!name.length;
								auto args=nargs==1?[arg]:iota(nargs).map!(i=>arg[i.dℤ]).array;
								foreach(c;cond!name(args))
									dist.assertTrue(c.cond,formatError(c.error,e.loc));
								auto var=dist.getTmpVar("__"~name[0]);
								dist.distribute(pdf!name(var,args));
								return var;
						}
						static if(!util.among(name,"dirac")){
							case util.capitalize(name):
								auto nargs=paramNames!name.length;
								auto args=nargs==1?[arg]:iota(nargs).map!(i=>arg[i.dℤ]).array;
								foreach(c;cond!name(args))
									dist.assertTrue(c.cond,formatError(c.error,e.loc));

								auto idist=new Distribution();
								auto argv=idist.declareVar("`arg");
								idist.addArgs([argv],false,null);
								auto vargs=nargs==1?[cast(DExpr)argv]:iota(nargs).map!(i=>argv[i.dℤ]).array;
								auto x=idist.declareVar("`x");
								idist.distribute(pdf!name(x,vargs));
								idist.marginalize(argv);
								idist.orderFreeVars([x],false);
								auto db1=dDeBruijnVar(1);
								return dApply(idist.toDExpr(),dLambda(dDelta(db1,arg,ce.arg.type)));
						}
					}
					case "Marginal":
						auto idist=dist.dup();
						auto r=idist.getVar("`r");
						idist.addArgs([],true,null);
						idist.initialize(r,arg,ce.arg.type);
						foreach(v;idist.freeVars)
							if(v !is r) idist.marginalize(v);
						idist.orderFreeVars([r],false);
						return dApply(idist.toDExpr(),dLambda(one));
					case "FromMarginal":
						auto tmp=dist.getTmpVar("__mrg");
						auto ndist=dist.dup();
						ndist.initialize(tmp,arg,ce.arg.type);
						foreach(v;dist.freeVars)
							if(v !is tmp) ndist.marginalize(v);
						ndist.simplify();
						dist.distribute(ndist.distribution);
						return tmp;
					case "SampleFrom":
						Expression[] args;
						if(auto tpl=cast(TupleExp)ce.arg) args=tpl.e;
						else args=[ce.arg];
						auto info=analyzeSampleFrom(ce,err,dist);
						if(info.error) unwind();
						auto retVars=info.retVars,paramVars=info.paramVars,newDist=info.newDist;
						foreach(i,pvar;paramVars){
							auto expr=doIt(args[1+i]);
							newDist=newDist.substitute(pvar,expr);
						}
						dist.distribute(newDist);
						return retVars.length==1?retVars[0].tmp:dTuple(cast(DExpr[])retVars.map!(v=>v.tmp).array);
					case "Expectation":
						if(ce.arg.type!=ℝ){
							err.error("expected one real argument (e) to Expectation",ce.loc);
							unwind();
						}
						auto total=dist.distribution;
						auto expct=dist.distribution*arg;
						foreach(v;dist.freeVars){ // TODO: handle non-convergence
							total=dInt(v,total);
							expct=dInt(v,expct);
						}
						// for obvious reasons, this will never fail:
						dist.assertTrue(dIvr(DIvr.Type.neqZ,total),"expectation can be computed only in feasible path");
						auto tmp=dist.getTmpVar("__exp");
						dist.distribute(dDelta(tmp,expct/total,ℝ));
						return tmp;
					case "infer":
						if(ce.arg.type!=typeTy){
							err.error("expected one type argument [a] to infer",ce.loc);
							unwind();
						}
						auto fty=cast(ForallTy)ce.type;
						auto dfty=cast(ForallTy)fty.dom;
						assert(dfty&&dfty.dom==unit);
						auto idist=new Distribution();
						auto f=idist.declareVar("`f");
						idist.addArgs([f],false,null);
						auto fdist=Distribution.fromDExpr(f,0,["`val".dVar],false,[dfty.cod]);
						fdist.renormalize();
						auto r=idist.declareVar("`dist");
						idist.initialize(r,dApply(fdist.toDExpr(),dLambda(one)),fty.cod);
						idist.marginalize(f);
						idist.orderFreeVars([r],false);
						return idist.toDExpr();
					default: break;
					}
				}
				auto funty=cast(FunTy)ce.e.type;
				assert(!!funty);
				Expression[] resty;
				bool isTuple=true;
				if(auto tplres=cast(TupleTy)funty.cod) resty=tplres.types;
				else{ resty=[funty.cod]; isTuple=false; }
				size_t nargs=funty.nargs;
				auto fun=doIt(ce.e);
				DVar[] results=iota(0,resty.length).map!(x=>dist.getTmpVar("__r")).array;
				auto summary=Distribution.fromDExpr(fun,nargs,results,isTuple,resty);
				foreach(r;results) dist.freeVars.remove(r), dist.tmpVars.remove(r);
				auto argty=funty.dom;
				assert(ce.arg.type == argty);
				auto r=dist.call(summary,doIt(ce.arg),argty);
				return r;
			}
			if(auto idx=cast(IndexExp)e){
				if(idx.e.type == arrayTy(ℝ)){
					if(auto id=cast(Identifier)idx.e) if(id.name in arrays){
						auto r=indexArray(idx);
						if(r) return r;
						unwind();
					}
				}
				if(cast(ArrayTy)idx.e.type){
					assert(idx.a.length==1);
					auto de=doIt(idx.e);
					auto di=doIt(idx.a[0]);
					if(!opt.noBoundsCheck) dist.assertTrue(dIvr(DIvr.Type.leZ,-di)*dIvr(DIvr.Type.lZ,di-dField(de,"length")),"array access out of bounds"); // TODO: check that index is an integer.
					auto r=dIndex(de,di);
					return r;
				}else if(auto tt=cast(TupleTy)idx.e.type){
					assert(idx.a.length==1);
					return doIt(idx.e)[doIt(idx.a[0])];
				}
				assert(0,text(idx," ",idx.e.type));
			}
			if(auto le=cast(LiteralExp)e){
				if(le.lit.type==Tok!"0"){
					auto n=le.lit.str.split(".");
					if(n.length==1) n~="";
					return dℤ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length);
				}
			}
			if(auto cmp=cast(CompoundExp)e){
				if(cmp.s.length==1)
					return doIt(cmp.s[0]);
			}else if(auto ite=cast(IteExp)e){
				auto cond=transformConstr(ite.cond);
				if(!cond) throw new Unwind();
				auto var=dist.getTmpVar("__ite");
				dist.initialize(var,dTuple([]),unit); // TODO: get rid of this?
				auto dthen=dist.dupNoErr();
				dthen.distribution=dthen.distribution*dIvr(DIvr.Type.neqZ,cond);
				auto dothw=dist.dupNoErr();
				dothw.distribution=dothw.distribution*dIvr(DIvr.Type.eqZ,cond);
				auto athen=Analyzer(be,dthen,err,arrays.dup,deterministic.dup);
				auto then=athen.transformExp(ite.then);
				if(!then) unwind();
				athen.dist.assign(var,then,ite.then.s[0].type);
				if(!ite.othw){
					err.error("missing else for if expression",ite.loc);
					unwind();
				}
				auto aothw=Analyzer(be,dothw,err,arrays.dup,deterministic.dup);
				auto othw=aothw.transformExp(ite.othw);
				if(!othw) unwind();
				aothw.dist.assign(var,othw,ite.othw.s[0].type);
				athen.dist.simplify(), aothw.dist.simplify();
				dist=athen.dist.join(dist,aothw.dist);
				foreach(k,v;deterministic){
					if(k in athen.deterministic && k in aothw.deterministic
						&& athen.deterministic[k] is aothw.deterministic[k]){
						deterministic[k]=athen.deterministic[k];
					}else deterministic.remove(k);
				}
				return var;
			}else if(auto tpl=cast(TupleExp)e){
				auto dexprs=tpl.e.map!doIt.array;
				return dTuple(dexprs);
			}else if(auto arr=cast(ArrayExp)e){
				auto dexprs=arr.e.map!doIt.array;
				return dArray(dexprs);
			}else if(auto tae=cast(TypeAnnotationExp)e){
				return doIt(tae.e);
			}else if(cast(Type)e)
				return dTuple([]); // 'erase' types
			else if(auto c=transformConstr(e))
				return c;
			err.error("unsupported",e.loc);
			throw new Unwind();
		}
		try return doIt(e);
		catch(Unwind){ return null; }
	}

	DExpr transformConstr(Exp e){
		class Unwind: Exception{ this(){ super(""); } }
		void unwind(){ throw new Unwind(); }
		DExpr doIt(Exp e){
			enum common=q{
				auto e1=transformExp(b.e1),e2=transformExp(b.e2);
				if(!e1||!e2) unwind();
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
			}else{
				auto cond=transformExp(e);
				if(!cond) unwind();
				return dIvr(DIvr.Type.neqZ,cond);
			}
			err.error("unsupported",e.loc);
			throw new Unwind();
		}
		try return doIt(e);
		catch(Unwind){ return null; }
	}

	void trackDeterministic(DVar var,DExpr rhs,Expression ty){
		if(ty != ℝ) return;
		if(rhs){
			if(auto nrhs=isObviouslyDeterministic(rhs)){
				deterministic[var]=nrhs;
				return;
			}
		}
		deterministic.remove(var);
	}

	DExpr isObviouslyDeterministic(DExpr e){
		foreach(v;e.freeVars.setx){
			if(v in deterministic){
				e=e.substitute(v,deterministic[v]);
			}else return null;
		}
		return e.simplify(one);
	}

	DExpr isDeterministic(DExpr e,Expression ty){ // TODO: track deterministic values for more complex datatypes than 'ℝ"?
		if(ty != ℝ) return null;
		if(auto r=isObviouslyDeterministic(e))
			return r;
		// TODO: this is a glorious hack:
		auto ndist=dist.dup();
		auto tmp=ndist.getVar("tmp");
		ndist.initialize(tmp,e,ℝ);
		foreach(v;dist.freeVars) ndist.marginalize(v);
		ndist.simplify();
		foreach(f;ndist.distribution.factors)
			if(!cast(DDelta)f&&!f.isFraction())
				return null;
		auto norm=dIntSmp(tmp,ndist.distribution,one);
		if(norm is zero || (!norm.isFraction()&&!cast(DFloat)norm))
			return null;
		auto r=(dIntSmp(tmp,tmp*ndist.distribution,one)/norm).simplify(one);
		if(r.hasAny!DInt) return null;
		return r;
	}

	Dℤ isDeterministicInteger(DExpr e){
		auto r=isDeterministic(e,ℝ);
		if(auto num=cast(Dℤ)r) return num;
		return null;
	}

	DExpr indexArray(IndexExp idx){
		if(idx.a.length!=1){
			err.error("multidimensional arrays not supported",idx.loc);
			return null;
		}
		auto id=cast(Identifier)idx.e;
		if(!id){
			err.error("indexed expression should be identifier",idx.e.loc);
			return null;
		}
		if(id.name !in arrays){
			err.error("undefined variable '"~id.name~"'",id.loc);
			return null;
		}
		auto arr=arrays[id.name];
		if(auto index=transformExp(idx.a[0])){
			auto cidx=isDeterministicInteger(index);
			if(!cidx){
				err.error("index expression should be provably deterministic integer",idx.a[0].loc);
				return null;
			}
			if(!(0<=cidx.c&&cidx.c<arr.length)){
				err.error(text("index ",cidx.c," is outside array bounds [0..",arr.length,")"),idx.loc);
				return null;
			}
			return arr[cast(size_t)cidx.c.toLong()];
		}else return null;
	}

	void evaluateArrayCall(Identifier id,CallExp call){
		if(call.arg.type!=ℝ){
			err.error("expected one real argument to array",call.loc);
			return;
		}
		auto ae=transformExp(call.arg);
		if(!ae) return;
		auto num=isDeterministicInteger(ae);
		if(!num){
			err.error("array length should be provably deterministic integer",call.loc);
			return;
		}
		if(num.c<0){
			err.error("array length should be non-negative",call.loc);
			return;
		}
		if(num.c>int.max){
			err.error("array length too high",call.loc);
			return;
		}
		if(id.name in arrays){
			err.error("array already exists",id.loc);
			return;
		}
		foreach(k;0..num.c.toLong()){
			auto var=dist.getVar(id.name);
			dist.initialize(var,zero,ℝ);
			arrays[id.name]~=var;
		}
	}

	void evaluateReadCSVCall(Identifier id,CallExp call){
		if(call.arg.type!=stringTy){
			err.error("expected one string argument (filename) to 'readCSV'",call.loc);
			return;
		}
		auto lit=cast(LiteralExp)call.arg;
		if(!lit||lit.lit.type != Tok!"``"){
			err.error("argument to 'readCSV' must be string constant",call.arg.loc);
			return;
		}
		auto filename=lit.lit.str;
		import std.path, std.file;
		auto path=buildPath(dirName(be.sourceFile),filename);
		File f;
		try{
			f=File(path,"r");
		}catch(Exception){
			err.error(text(`could not open file "`,path,`"`),call.loc);
			return;
		}
		try{
			static DExpr parseNum(string s){
				auto n=s.split(".");
				if(n.length==1) n~="";
				import std.exception;
				enforce(n.length==2);
				if(n[1].length) return dFloat((n[0]~"."~n[1]).to!real);
				return dℤ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length);
			}
			auto arr=f.readln().strip().split(",").map!strip.map!parseNum.array;
			//enforce(f.eof);
			arrays[id.name]=arr;
			// dw("len: ",arr.length);
		}catch(Exception e){
			err.error(text("not a comma-separated list of numbers: `",path,"`"),call.loc);
			return;
		}
	}

	void assignTo(DExpr lhs,DExpr rhs,Expression ty,Location loc){
		void assignVar(DVar var,DExpr rhs,Expression ty){
			if(var.name !in arrays){
				dist.assign(var,rhs,ty);
				trackDeterministic(var,rhs,ty);
			}else err.error("reassigning array unsupported",loc);
		}
		if(auto var=cast(DVar)lhs){
			assignVar(var,rhs,ty);
		}else if(auto idx=cast(DIndex)lhs){
			if(auto id=cast(DVar)idx.e){
				if(id.name in arrays){
					err.error("unsupported",loc);
					return;
				}
			}
			assignTo(idx.e,dIUpdate(idx.e,idx.i,rhs),unit,loc); // TODO: 'unit' ok?
		}else if(auto fe=cast(DField)lhs){
			assignTo(fe.e,dRUpdate(fe.e,fe.f,rhs),unit,loc); // TODO: 'unit' ok?
		}else{
			err.error("unsupported assignment",loc);
		}
	}
	
	void assignTo(Expression lhs,DExpr rhs,Expression ty,Location loc){
		if(!rhs) return;
		void assignVar(Identifier id,DExpr rhs,Expression ty){
			if(id.name !in arrays){
				auto v=dVar(id.name);
				dist.assign(v,rhs,ty);
				trackDeterministic(v,rhs,ty);
			}else err.error("reassigning array unsupported",lhs.loc);
		}
		if(auto id=cast(Identifier)lhs){
			assignVar(id,rhs,ty);
		}else if(auto idx=cast(IndexExp)lhs){
			if(auto id=cast(Identifier)idx.e){
				if(id.name in arrays){
					if(auto cidx=indexArray(idx)){
						if(auto v=cast(DVar)cidx){
							dist.assign(v,rhs?rhs:zero,ty);
							trackDeterministic(v,rhs,ty);
						}else{
							err.error(text("array is not writeable"),lhs.loc);
						}
					}
					return;
				}
			}
			if(cast(TupleTy)idx.e.type||cast(ArrayTy)idx.e.type){
				auto old=transformExp(idx.e);
				assert(idx.a.length==1);
				auto index=transformExp(idx.a[0]);
				if(old&&index&&rhs){
					if(!opt.noBoundsCheck) dist.assertTrue(dIvr(DIvr.Type.leZ,-index)*dIvr(DIvr.Type.lZ,index-dField(old,"length")),"array access out of bounds"); // TODO: check that index is an integer.
					assignTo(idx.e,dIUpdate(old,index,rhs),idx.e.type,loc);
				}
			}else{
				err.error(text("unsupported type '",idx.e.type,"' for index expression"),lhs.loc);
			}
		}else if(auto fe=cast(FieldExp)lhs){
			if(!cast(ArrayTy)fe.e.type){
				auto old=transformExp(fe.e);
				if(old) assignTo(fe.e,dRUpdate(old,fe.f.name,rhs),fe.e.type,loc);
			}
		}else if(auto tpl=cast(TupleExp)lhs){
			auto tt=cast(TupleTy)ty;
			assert(!!tt);
			assert(tpl.e.length==tt.types.length);
			foreach(k,exp;tpl.e) assignTo(exp,rhs[k.dℤ],tt.types[k],loc);
		}else{
		LbadAssgnmLhs:
			err.error("invalid left hand side for assignment",lhs.loc);
		}
	}

	private void analyzeStatement(Expression e,ref Distribution retDist,FunctionDef functionDef)in{assert(!!e);}body{
		if(opt.trace) writeln("statement: ",e);
		/+writeln("before: ",dist);
		 scope(success) writeln("after: ",dist);+/
		// TODO: visitor?
		if(auto nde=cast(DefExp)e){
			auto de=cast(ODefExp)nde.initializer;
			assert(!!de);
			// TODO: no real need to repeat checks done by semantic
			scope(exit) dist.marginalizeTemporaries();
			void defineVar(Identifier id,DExpr rhs,Expression ty){
				DVar var=null;
				if(id.name !in arrays) var=dist.declareVar(id.name);
				if(var){
					dist.distribute(dDelta(var,rhs?rhs:zero,rhs?ty:ℝ)); // TODO: zero is not a good default value for types other than ℝ.
					trackDeterministic(var,rhs,ty);
				}else err.error("variable already exists",id.loc);
			}
			if(auto id=cast(Identifier)de.e1){
				bool isSpecial=false;
				if(auto call=cast(CallExp)de.e2){
					if(auto cid=cast(Identifier)call.e){
						switch(cid.name){
							case "array":
								if(call.arg.type==ℝ){
									isSpecial=true;
									evaluateArrayCall(id,call);
								}
								break;
							case "readCSV":
								isSpecial=true;
								evaluateReadCSVCall(id,call);
								break;
							default: break;
						}
					}
				}
				if(!isSpecial){
					auto rhs=transformExp(de.e2);
					defineVar(id,rhs,de.e2.type);
					dist.marginalizeTemporaries();
				}
			}else if(auto tpl=cast(TupleExp)de.e1){
				auto rhs=transformExp(de.e2);
				auto tt=cast(TupleTy)de.e2.type;
				assert(!!tt);
				assert(tpl.e.length==tt.types.length);
				foreach(k,exp;tpl.e){
					auto id=cast(Identifier)exp;
					if(!id) goto LbadDefLhs;
					defineVar(id,rhs[k.dℤ],tt.types[k]);
				}
			}else{
			LbadDefLhs:
				err.error("left hand side of definition should be identifier or tuple of identifiers",de.e1.loc);
			}
		}else if(auto ae=cast(AssignExp)e){
			assignTo(ae.e1,transformExp(ae.e2),ae.e2.type,ae.loc);
			dist.marginalizeTemporaries();
		}else if(isOpAssignExp(e)){
			DExpr perform(DExpr a,DExpr b){
				if(cast(OrAssignExp)e) return dIvr(DIvr.Type.neqZ,dIvr(DIvr.Type.neqZ,a)+dIvr(DIvr.Type.neqZ,b));
				if(cast(AndAssignExp)e) return dIvr(DIvr.Type.neqZ,a)*dIvr(DIvr.Type.neqZ,b);
				if(cast(AddAssignExp)e) return a+b;
				if(cast(SubAssignExp)e) return a-b;
				if(cast(MulAssignExp)e) return a*b;
				if(cast(DivAssignExp)e||cast(IDivAssignExp)e){
					dist.assertTrue(dIvr(DIvr.Type.neqZ,b),"division by zero");
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
			auto lhs=transformExp(be.e1);
			auto rhs=transformExp(be.e2);
			assignTo(lhs,perform(lhs,rhs),be.e2.type,be.loc);
			dist.marginalizeTemporaries();
		}else if(auto call=cast(CallExp)e){
			transformExp(call);
			dist.marginalizeTemporaries();
		}else if(auto ite=cast(IteExp)e){
			if(auto c=transformConstr(ite.cond)){
				auto dthen=dist.dupNoErr();
				dthen.distribution=dthen.distribution*dIvr(DIvr.Type.neqZ,c);
				auto dothw=dist.dupNoErr();
				dothw.distribution=dothw.distribution*dIvr(DIvr.Type.eqZ,c);
				auto athen=Analyzer(be,dthen,err,arrays.dup,deterministic.dup);
				dthen=athen.analyze(ite.then,retDist,functionDef);
				auto aothw=Analyzer(be,dothw,err,arrays.dup,deterministic.dup);
				if(ite.othw) dothw=aothw.analyze(ite.othw,retDist,functionDef);
				dist=dthen.join(dist,dothw);
				foreach(k,v;deterministic){
					if(k in athen.deterministic && k in aothw.deterministic
						&& athen.deterministic[k] is aothw.deterministic[k]){
						deterministic[k]=athen.deterministic[k];
					}else deterministic.remove(k);
				}
			}
		}else if(auto re=cast(RepeatExp)e){
			if(auto exp=transformExp(re.num)){
				if(auto num=isDeterministicInteger(exp)){
					int nerrors=err.nerrors;
					for(ℤ j=0;j<num.c;j++){
						auto anext=Analyzer(be,dist.dup(),err,arrays.dup,deterministic);
						auto dnext=anext.analyze(re.bdy,retDist,functionDef);
						dnext.marginalizeLocals(dist);
						dist=dnext;
						deterministic=anext.deterministic;
						if(err.nerrors>nerrors) break;
					}
				}else err.error("repeat expression should be provably deterministic integer",re.num.loc);
			}
		}else if(auto fe=cast(ForExp)e){
			auto lexp=transformExp(fe.left), rexp=transformExp(fe.right);
			if(lexp&&rexp){
				auto l=isDeterministicInteger(lexp), r=isDeterministicInteger(rexp);
				if(l&&r){
					int nerrors=err.nerrors;
					for(ℤ j=l.c+cast(int)fe.leftExclusive;j+cast(int)fe.rightExclusive<=r.c;j++){
						auto cdist=dist.dup();
						auto anext=Analyzer(be,cdist,err,arrays.dup,deterministic);
						auto var=cdist.declareVar(fe.var.name);
						if(var){
							auto rhs=dℤ(j);
							cdist.initialize(var,rhs,ℝ);
							anext.trackDeterministic(var,rhs,ℝ);
						}else{
							err.error("variable already exists",fe.var.loc);
							break;
						}
						auto dnext=anext.analyze(fe.bdy,retDist,functionDef);
						dnext.marginalizeLocals(dist,(v){ anext.deterministic.remove(v); });
						dist=dnext;
						deterministic=anext.deterministic;
						deterministic.remove(var);
						if(err.nerrors>nerrors) break;
					}
				}else{
					err.error("for bounds should be provably deterministic integers",
					          l?fe.right.loc:r?fe.left.loc:fe.left.loc.to(fe.right.loc));
				}
			}
		}else if(auto re=cast(ReturnExp)e){
			auto odist=dist.dup;
			odist.distribution=odist.error=zero; // code after return is unreachable
			SetX!DVar vars;
			DVar[] orderedVars;
			bool isTuple=true;
			Expression[] returns;
			dist.freeVar("r");
			if(!cast(TupleTy)re.e.type||cast(TupleExp)re.e){
				if(auto tpl=cast(TupleExp)re.e) returns=tpl.e;
				else{ returns=[re.e]; isTuple=false; }
				foreach(ret;returns){
					if(auto id=cast(Identifier)ret){ // TODO: this hack should be removed
						if(id.name in arrays){
							foreach(expr;arrays[id.name]){
								if(auto var=cast(DVar)expr){
									vars.insert(var);
									orderedVars~=var;
								}
							}
							continue;
						}
					}
					auto exp=transformExp(ret);
					if(!exp) exp=dTuple([]); // TODO: is there a better way?
					DVar var=cast(DVar)exp;
					if(var && !var.name.startsWith("__")){
						if(var in vars||functionDef.context&&!functionDef.isConstructor&&var.name==functionDef.contextName){
							dist.freeVar(var.name);
							auto vv=dist.getVar(var.name);
							dist.initialize(vv,var,ret.type);
							var=vv;
						}
						vars.insert(var);
						orderedVars~=var;
					}else{
						if(auto fe=cast(FieldExp)ret){
							dist.freeVar(fe.f.name);
							var=dist.declareVar(fe.f.name);
							if(!var) var=dist.getVar(fe.f.name);
						}else var=dist.getVar("r");
						dist.initialize(var,exp,ret.type);
						vars.insert(var);
						orderedVars~=var;
					}
				}
			}else{
				auto tty=cast(TupleTy)re.e.type;
				assert(!!tty);
				auto r=transformExp(re.e);
				auto id=cast(Identifier)re.e;
				auto name=id?id.name:"r";
				dist.freeVar(name);
				foreach(i,ty;tty.types){
					auto var=dist.getVar(name);
					dist.initialize(var,dIndex(r,i.dℤ),ty);
					vars.insert(var);
					orderedVars~=var;
				}
			}
			if(functionDef.context&&functionDef.contextName=="this"&&!functionDef.isConstructor){
				// TODO: if this happens, the above is quite pointless. refactor.
				assert(isTuple||orderedVars.length==1);
				auto res=isTuple?dTuple(cast(DExpr[])orderedVars):orderedVars[0];
				auto resv=dist.getVar("__r"),ctxv=dVar(functionDef.contextName);
				dist.initialize(resv,res,re.e.type);
				vars.clear();
				vars.insert(resv);
				vars.insert(ctxv);
				orderedVars=[resv,ctxv];
				isTuple=true;
			}
			import hashtable:  setMinus;
			foreach(w;dist.freeVars.setMinus(vars)){
				dist.marginalize(w);
			}
			dist.orderFreeVars(orderedVars,isTuple);
			dist.simplify();
			if(!retDist) retDist=dist;
			else retDist=dist.orderedJoin(retDist);
			dist=odist;
			if(re.expected.length){
				import dparse;
				bool todo=false;
				import std.string: strip;
				auto ex=re.expected.strip;
				if(ex.strip.startsWith("TODO:")){
					todo=true;
					ex=ex["TODO:".length..$].strip;
				}
				if(!expected.exists){
					expected=Expected(true,todo,ex);
				}else err.error("can only have one 'expected' annotation, in 'main'.",re.loc);
			}
		}else if(auto ae=cast(AssertExp)e){
			if(auto c=transformConstr(ae.e)){
				dist.assertTrue(c,text("assertion '",ae.e,"' failed"));
			}
		}else if(auto oe=cast(ObserveExp)e){
			if(auto c=transformConstr(oe.e)){
				dist.observe(c);
			}
		}else if(auto co=cast(CObserveExp)e){
			if(auto var=transformExp(co.var))
				if(auto ex=transformExp(co.val))
					dist.distribution=dist.distribution*dDelta(var-ex);
		}else if(auto ce=cast(CommaExp)e){
			analyzeStatement(ce.e1,retDist,functionDef);
			analyzeStatement(ce.e2,retDist,functionDef);
		}else if(cast(Declaration)e){
			// skip
		}else if(!cast(ErrorExp)e) err.error(text("unsupported"),e.loc);
	}
	
	Distribution analyze(CompoundExp ce,ref Distribution retDist,FunctionDef functionDef)in{assert(!!ce);}body{
		foreach(e;ce.s){
			analyzeStatement(e,retDist,functionDef);
		}
		return dist;
	}
	void applyRetDist(FunctionDef fd,Distribution retDist){
		if(!retDist) return;
		dist.simplify();
		if(dist.distribution is zero){
			retDist.error=retDist.error+dist.error;
			dist=retDist;
		}else err.error("not all paths return",fd.loc); // TODO: check during semantic
	}
}
