import std.stdio, std.conv, std.format, std.string, std.range, std.algorithm;

import lexer, expression, declaration, type, semantic_, error;
import distrib, dexpr, util;

FunctionDef[string] functions; // TODO: get rid of globals
Distribution[FunctionDef] summaries;
string sourceFile;

alias ODefExp=BinaryExp!(Tok!":=");

struct Expected{
	bool exists;
	bool todo;
	string ex;
}
Expected expected;

private struct Analyzer{
	Distribution dist;
	ErrorHandler err;
	DExpr[][string] arrays;
	DExpr[DVar] deterministic;
	DExpr transformExp(Exp e){
		class Unwind: Exception{ this(){ super(""); } }
		void unwind(){ throw new Unwind(); }
		DExpr doIt(Exp e){
			if(cast(Declaration)e||cast(BinaryExp!(Tok!":="))e){
				err.error("definition must be at top level",e.loc);
				unwind();
			}
			if(auto id=cast(Identifier)e){
				if(auto v=dist.lookupVar(id.name))
					return v;
				if(id.name in arrays){
					err.error("missing array index",id.loc);
				}else{
					err.error("undefined variable '"~id.name~"'",id.loc);
				}
				unwind();
			}
			if(auto fe=cast(FieldExp)e){
				if(auto id=cast(Identifier)fe.e){
					if(id.name in arrays && fe.f.name=="length")
						return ℕ(arrays[id.name].length).dℕ;
				}
				return dField(doIt(fe.e),fe.f.name);
				unwind();
			}
			if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
			if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
			if(auto me=cast(MulExp)e) return doIt(me.e1)*doIt(me.e2);
			if(auto de=cast(DivExp)e){
				auto e1=doIt(de.e1);
				auto e2=doIt(de.e2);
				dist.assertTrue(dIvr(DIvr.Type.neqZ,e2),formatError("division by zero",e.loc));
				return e1/e2;
			}
			if(auto pe=cast(PowExp)e) return doIt(pe.e1)^^doIt(pe.e2);
			if(auto ce=cast(CatExp)e) return doIt(ce.e1)~doIt(ce.e2);
			if(auto ume=cast(UMinusExp)e) return -doIt(ume.e);
			if(auto ume=cast(UNegExp)e) return dIvr(DIvr.Type.eqZ,doIt(ume.e));
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
						if(fun !in summaries){
							summaries[fun]=new Distribution();
							summaries[fun].distribute(mone);
							summaries[fun]=.analyze(fun,err);
						}else if(summaries[fun].distribution is mone){
							// TODO: support special cases.
							err.error("recursive dependencies unsupported",ce.loc);
							unwind();
						}
						auto summary=summaries[fun];
						if(ce.args.length != fun.params.length){
							err.error(format("expected %s arguments to '%s', received %s",fun.params.length,id.name,ce.args.length),ce.loc);
							unwind();
						}
						DExpr[] args;
						foreach(i,arg;ce.args){
							if(auto a=doIt(arg)){
								args~=a;
							}else unwind();
						}
						if(thisExp&&!fun.isConstructor) args~=thisExp;
						auto funty=cast(FunTy)ce.e.type;
						assert(!!funty);
						auto tuplety=cast(TupleTy)funty.dom;
						assert(!!tuplety);
						auto types=tuplety.types;
						if(thisExp&&!fun.isConstructor)
							types~=fe.e.type; // TODO: this is wasteful
						auto r=dist.call(summary,args,types);
						if(thisExp&&!fun.isConstructor){
							DExpr thisr;
							if(auto tpl=cast(DTuple)r){
								thisr=tpl.values[$-1];
								if(tpl.length==2) r=tpl.values[0];
								else r=dTuple(tpl.values[0..$-1]);
							}else{
								thisr=r;
								r=dTuple([]);
							}
							assert(thisr&&fe);
							assignTo(thisExp,thisr,fe.e.type,ce.loc);
						}
						if(!cast(DTuple)r&&cast(TupleTy)funty.cod) r=dTuple([r]);
						return r;
					}
					switch(id.name){
					case "array":
						if(ce.args.length==1)
							return dArray(doIt(ce.args[0]));
						assert(ce.args.length==2);
						return dConstArray(doIt(ce.args[0]),doIt(ce.args[1]));
					case "readCSV":
						err.error(text("call to 'readCSV' only supported as the right hand side of an assignment"),ce.loc);
						unwind();
					case "Gauss":
						if(ce.args.length!=2){
							err.error("expected two arguments (μ,σ²) to Gauss",ce.loc);
							unwind();
						}
						auto μ=doIt(ce.args[0]), σsq=doIt(ce.args[1]);
						dist.assertTrue(dIvr(DIvr.Type.leZ,-σsq),formatError("negative variance",e.loc));
						auto var=dist.getTmpVar("__g");
						dist.distribute(gaussianPDF(var,μ,σsq));
						//import approximate;
						//dist.distribute(approxGaussianPDF(var,μ,σsq));
						return var;
					case "TruncatedGauss":
						if(ce.args.length!=4){
							err.error("expected four arguments (μ,σ²,a,b) to TruncatedGauss",ce.loc);
							unwind();
						}
						auto μ=doIt(ce.args[0]), σsq=doIt(ce.args[1]), a = doIt(ce.args[2]), b = doIt(ce.args[3]);
						dist.assertTrue(dIvr(DIvr.Type.leZ,-σsq),formatError("negative variance",e.loc));
						auto var=dist.getTmpVar("__g");
						dist.distribute(truncGaussianPDF(var,μ,σsq, a, b));
						return var;
					case "Pareto":
						if(ce.args.length!=2){
							err.error("expected two arguments (a,b) to Pareto",ce.loc);
							unwind();
						}
						auto a = doIt(ce.args[0]), b = doIt(ce.args[1]);
						dist.assertTrue(dIvr(DIvr.Type.leZ,-a), formatError("negative scale",e.loc));
						dist.assertTrue(dIvr(DIvr.Type.leZ,-b), formatError("negative shape",e.loc));
						auto var=dist.getTmpVar("__g");
						dist.distribute(paretoPDF(var,a,b));
						return var;
					case "Rayleigh":
						if(ce.args.length!=1){
							err.error("expected one argument (σ²) to Rayleigh",ce.loc);
							unwind();
						}
						auto σsq=doIt(ce.args[0]);
						dist.assertTrue(dIvr(DIvr.Type.leZ,-σsq),formatError("negative scale",e.loc));
						auto var=dist.getTmpVar("__g");
						dist.distribute(rayleighPDF(var,σsq));
						return var;
					case "CosUnifDist": // TODO: Remove
						auto var=dist.getTmpVar("__g");
						dist.distribute(one/dΠ*(1-var^^2)^^-(one/2) * dBounded!"[]"(var,-one, one) * dIvr(DIvr.Type.neqZ,var-one)*dIvr(DIvr.Type.neqZ,var+one));
						return var;
					case "Uniform":
						if(ce.args.length!=2){
							err.error("expected two arguments (a,b) to Uniform",ce.loc);
							unwind();
						}
						auto a=doIt(ce.args[0]),b=doIt(ce.args[1]);
						dist.assertTrue(dIvr(DIvr.Type.leZ,a-b),formatError("empty range",e.loc));
						auto var=dist.getTmpVar("__u");
						dist.distribute(uniformPDF(var,a,b));
						return var;
					case "Bernoulli":
						if(ce.args.length!=1){
							err.error("expected one argument (p) to Bernoulli",ce.loc);
							unwind();
						}
						auto p=doIt(ce.args[0]);
						dist.assertTrue(dIvr(DIvr.Type.leZ,-p)*dIvr(DIvr.Type.leZ,p-1),"parameter ouside range [0..1]");
						auto var=dist.getTmpVar("__b");
						dist.distribute(bernoulliPDF(var,p));
						return var;
					case "UniformInt":
						if(ce.args.length!=2){
							err.error("expected two arguments (a,b) to UniformInt",ce.loc);
							unwind();
						}
						auto a=doIt(ce.args[0]),b=doIt(ce.args[1]);
						auto tmp=freshVar(); // TODO: get rid of this
						auto nnorm=uniformIntPDFNnorm(tmp,a,b);
						auto norm=dIntSmp(tmp,nnorm,one);
						dist.assertTrue(dIvr(DIvr.Type.neqZ,norm),"no integers in range");
						auto var=dist.getTmpVar("__u");
						dist.distribute(nnorm.substitute(tmp,var)/norm);
						return var;
					case "Poisson":
						if(ce.args.length!=1){
							err.error("expected one argument (λ) to Poisson",ce.loc);
							unwind();
						}
						auto λ=doIt(ce.args[0]);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-λ),"λ must be positive");
						auto var=dist.getTmpVar("__p");
						dist.distribute(poissonPDF(var,λ));
						return var;
					case "Categorical":
						if(ce.args.length!=1){
							err.error("expected one argument (ps) to Categorical",ce.loc);
							unwind();
						}
						assert(ce.args[0].type is arrayTy(ℝ));
						auto idd=cast(Identifier)ce.args[0];
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
							foreach(i,x;array) d=d+x*dDelta(var,dℕ(i),ℝ);
							dist.distribute(d);
							return var;
						}else{
							auto p=doIt(ce.args[0]);
							auto dbv=dDeBruijnVar(1);
							dist.assertTrue(dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length")*dIvr(DIvr.Type.lZ,p[dbv])))),"probability of category should be non-negative"); // TODO: dProd?
							dist.assertTrue(dIvr(DIvr.Type.eqZ,dSum(dBounded!"[)"(dbv,zero,dField(p,"length"))*p[dbv])-1),"probabilities should sum up to 1");
							auto var=dist.getTmpVar("__c");
							dist.distribute(categoricalPDF(var,p));
							return var;
							//err.error("argument to Categorical should be an array",ce.loc);
							//unwind();
						}
					case "Beta":
						if(ce.args.length!=2){
							err.error("expected two arguments (α,β) to Beta",ce.loc);
							unwind();
						}
						auto α=doIt(ce.args[0]),β=doIt(ce.args[1]);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-α)*dIvr(DIvr.Type.lZ,-β),"α and β must be positive");
						auto var=dist.getTmpVar("__β");
						dist.distribute(betaPDF(var,α,β));
						return var;
					case "Gamma":
						if(ce.args.length!=2){
							err.error("expected two arguments (α,β) to Gamma",ce.loc);
							unwind();
						}
						auto α=doIt(ce.args[0]),β=doIt(ce.args[1]);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-α)*dIvr(DIvr.Type.lZ,-β),"α and β must be positive");
						auto var=dist.getTmpVar("__γ");
						dist.distribute(gammaPDF(var,α,β));
						return var;
					case "Laplace":
						if(ce.args.length!=2){
							err.error("expected two arguments (μ,b) to Laplace",ce.loc);
							unwind();
						}
						auto μ=doIt(ce.args[0]),b=doIt(ce.args[1]);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-b),"b must be positive");
						auto var=dist.getTmpVar("__γ");
						dist.distribute(laplacePDF(var,μ,b));
						return var;
					case "Exp","Exponential":
						if(ce.args.length!=1){
							err.error(text("expected one argument (λ) to ",id.name),ce.loc);
							unwind();
						}
						auto λ=doIt(ce.args[0]);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-λ),"λ must be positive");
						auto var=dist.getTmpVar("__e");
						dist.distribute(expPDF(var,λ));
						return var;
					case "StudentT":
						if(ce.args.length!=1){
							err.error("expected one argument (ν) to StudentT",ce.loc);
							unwind();
						}
						auto ν=doIt(ce.args[0]);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-ν),"ν must be positive");
						auto var=dist.getTmpVar("__t");
						dist.distribute(studentTPDF(var,ν));
						return var;
					case "Weibull":
						if(ce.args.length!=2){
							err.error("expected two arguments (λ,k) to Weibull",ce.loc);
							unwind();
						}
						auto λ=doIt(ce.args[0]), k=doIt(ce.args[1]);
						dist.assertTrue(dIvr(DIvr.Type.lZ,-λ),"λ must be positive");
						dist.assertTrue(dIvr(DIvr.Type.lZ,-k),"k must be positive");
						auto var=dist.getTmpVar("__w");
						dist.distribute(weibullPDF(var,λ,k));
						return var;
					case "FromMarginal":
						auto exp=ce.args.map!doIt.array;
						auto tmp=ce.args.map!(_=>dist.getTmpVar("__mrg")).array;
						auto ndist=dist.dup();
						foreach(i;0..exp.length)
							ndist.initialize(tmp[i],exp[i],ce.args[i].type);
						SetX!DVar tmpset;
						foreach(var;tmp) tmpset.insert(var);
						foreach(v;dist.freeVars){
							if(v !in tmpset)
								ndist.marginalize(v);
						}
						ndist.simplify();
						dist.distribute(ndist.distribution);
						return tmp.length==1?tmp[0]:dTuple(cast(DExpr[])tmp);
					case "SampleFrom":
						auto info=analyzeSampleFrom(ce,err,dist);
						if(info.error) unwind();
						auto retVars=info.retVars,paramVars=info.paramVars,newDist=info.newDist;
						foreach(i,pvar;paramVars){
							auto expr=doIt(ce.args[1+i]);
							newDist=newDist.substitute(pvar,expr);
						}
						dist.distribute(newDist);
						return retVars.length==1?retVars[0].tmp:dTuple(cast(DExpr[])retVars.map!(v=>v.tmp).array);
					case "Expectation":
						if(ce.args.length!=1){
							err.error("expected one argument (e) to Expectation",ce.loc);
							unwind();
						}
						assert(ce.args[0].type is ℝ);
						auto exp=doIt(ce.args[0]);
						auto total=dist.distribution;
						auto expct=dist.distribution*exp;
						foreach(v;dist.freeVars){
							total=dInt(v,total);
							expct=dInt(v,expct);
						}
						if(auto ctx=dist.context){
							total=dInt(ctx,total);
							expct=dInt(ctx,expct);
						}
						// for obvious reasons, this will never fail:
						dist.assertTrue(dIvr(DIvr.Type.neqZ,total),"expectation can be computed only in feasible path");
						auto tmp=dist.getTmpVar("__exp");
						dist.distribute(dDelta(tmp,expct/total,ℝ));
						return tmp;
					default: break;
					}
					err.error("undefined function '"~id.name~"'",ce.loc);
					unwind();
				}
			}
			if(auto idx=cast(IndexExp)e){
				if(idx.e.type is arrayTy(ℝ)){
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
					dist.assertTrue(dIvr(DIvr.Type.lZ,di-dField(de,"length")),"array access out of bounds"); // TODO: check that index is an integer.
					auto r=dIndex(de,di);
					return r;
				}else if(auto tt=cast(TupleTy)idx.e.type){
					assert(idx.a.length==1);
					return doIt(idx.e)[doIt(idx.a[0])];
				}
				assert(0,text(idx.e.type));
			}
			if(auto le=cast(LiteralExp)e){
				if(le.lit.type==Tok!"0"){
					auto n=le.lit.str.split(".");
					if(n.length==1) n~="";
					return dℕ((n[0]~n[1]).ℕ)/(ℕ(10)^^n[1].length);
				}
			}
			if(auto cmp=cast(CompoundExp)e){
				if(cmp.s.length==1)
					return doIt(cmp.s[0]);
			}else if(auto ite=cast(IteExp)e){
				auto cond=transformConstr(ite.cond);
				if(!cond) throw new Unwind();
				auto var=dist.getTmpVar("__ite");
				auto dthen=dist.dupNoErr();
				dthen.distribution=dthen.distribution*dIvr(DIvr.Type.neqZ,cond);
				auto dothw=dist.dupNoErr();
				dothw.distribution=dothw.distribution*dIvr(DIvr.Type.eqZ,cond);
				auto athen=Analyzer(dthen,err,arrays.dup,deterministic.dup);
				auto then=athen.transformExp(ite.then);
				if(!then) unwind();
				athen.dist.initialize(var,then,ite.then.s[0].type);
				if(!ite.othw){
					err.error("missing else for if expression",ite.loc);
					unwind();
				}
				auto aothw=Analyzer(dothw,err,arrays.dup,deterministic.dup);
				auto othw=aothw.transformExp(ite.othw);
				if(!othw) unwind();
				aothw.dist.initialize(var,othw,ite.othw.s[0].type);
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
			}else if(auto c=transformConstr(e))
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

	void trackDeterministic(DVar var,DExpr rhs,Type ty){
		if(ty !is ℝ) return;
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

	DExpr isDeterministic(DExpr e,Type ty){ // TODO: track deterministic values for more complex datatypes than 'ℝ"?
		if(ty !is ℝ) return null;
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

	Dℕ isDeterministicInteger(DExpr e){
		auto r=isDeterministic(e,ℝ);
		if(auto num=cast(Dℕ)r) return num;
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
		if(call.args.length!=1){
			err.error("multidimensional arrays not supported",call.loc);
			return;
		}
		auto ae=transformExp(call.args[0]);
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
		if(call.args.length!=1){
			err.error("expected one argument (filename) to 'readCSV'",call.loc);
			return;
		}
		auto lit=cast(LiteralExp)call.args[0];
		if(!lit||lit.lit.type != Tok!"``"){
			err.error("argument to 'readCSV' must be string constant",call.args[0].loc);
			return;
		}
		auto filename=lit.lit.str;
		import std.path, std.file;
		auto path=buildPath(dirName(sourceFile),filename);
		File f;
		try{
			f=File(path,"r");
		}catch{
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
				return dℕ((n[0]~n[1]).ℕ)/(ℕ(10)^^n[1].length);
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

	void assignTo(DExpr lhs,DExpr rhs,Type ty,Location loc){
		void assignVar(DVar var,DExpr rhs,Type ty){
			if(var.name !in arrays){
				dist.assign(var,rhs,ty,true);
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
	
	void assignTo(Expression lhs,DExpr rhs,Type ty,Location loc){
		if(!rhs) return;
		void assignVar(Identifier id,DExpr rhs,Type ty){
			if(id.name !in arrays){
				if(auto v=dist.lookupVar(id.name)){
					dist.assign(v,rhs,ty);
					trackDeterministic(v,rhs,ty);
				}else err.error("undefined variable '"~id.name~"'",id.loc);
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
					dist.assertTrue(dIvr(DIvr.Type.lZ,index-dField(old,"length")),"array access out of bounds"); // TODO: check that index is an integer.
					assignTo(idx.e,dIUpdate(old,index,rhs),idx.e.type,loc);
				}
			}else{
				err.error(text("unsupported type '",idx.e.type,"' for index expression"),lhs.loc);
			}
		}else if(auto fe=cast(FieldExp)lhs){
			if(cast(AggregateTy)fe.e.type){
				auto old=transformExp(fe.e);
				if(old) assignTo(fe.e,dRUpdate(old,fe.f.name,rhs),fe.e.type,loc);
			}
		}else if(auto tpl=cast(TupleExp)lhs){
			auto tt=cast(TupleTy)ty;
			assert(!!tt);
			auto dtpl=cast(DTuple)rhs;
			if(rhs&&(!dtpl||dtpl.length!=tpl.length)){
				err.error(text("inconsistent number of tuple entries for assignment: ",tpl.length," vs. ",(dtpl?dtpl.length:1)),loc);
				rhs=dtpl=null;
			}
			if(dtpl){
				auto tmp=iota(tpl.e.length).map!(_=>dist.getVar("__tpltmp")).array;
				foreach(k,de;dtpl.values) dist.initialize(tmp[k],de,tt.types[k]);
				foreach(k,exp;tpl.e) assignTo(exp,tmp[k],tt.types[k],loc);
			}
		}else{
		LbadAssgnmLhs:
			err.error("invalid left hand side for assignment",lhs.loc);
		}
	}

	Distribution analyze(CompoundExp ce,FunctionDef isMethodBody=null)in{assert(!!ce);}body{
		foreach(i,e;ce.s){
			/+writeln("statement: ",e);
			 writeln("before: ",dist);
			 scope(success) writeln("after: ",dist);+/
			// TODO: visitor?
			if(auto nde=cast(DefExp)e){
				auto de=cast(ODefExp)nde.init;
				assert(!!de);
				// TODO: no real need to repeat checks done by semantic
				scope(exit) dist.marginalizeTemporaries();
				void defineVar(Identifier id,DExpr rhs,Type ty){
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
								if(call.args.length==1){
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
					}
				}else if(auto tpl=cast(TupleExp)de.e1){
					auto rhs=transformExp(de.e2);
					auto tt=cast(TupleTy)de.e2.type;
					assert(!!tt);
					auto dtpl=cast(DTuple)rhs;
					if(rhs&&(!dtpl||dtpl.length!=tpl.length)){
						err.error(text("inconsistent number of tuple entries for definition: ",tpl.length," vs. ",(dtpl?dtpl.length:1)),de.loc);
						rhs=dtpl=null;
					}
					if(dtpl){
						foreach(k,exp;tpl.e){
							auto id=cast(Identifier)exp;
							if(!id) goto LbadDefLhs;
							defineVar(id,dtpl[k],tt.types[k]);
						}
					}
				}else{
				LbadDefLhs:
					err.error("left hand side of definition should be identifier or tuple of identifiers",de.e1.loc);
				}
			}else if(auto ae=cast(AssignExp)e){
				assignTo(ae.e1,transformExp(ae.e2),ae.e2.type,ae.loc);
				dist.marginalizeTemporaries();
			}else if(cast(AddAssignExp)e||cast(SubAssignExp)e||cast(MulAssignExp)e||cast(DivAssignExp)e||cast(PowAssignExp)e||cast(CatAssignExp)e){
				DExpr perform(DExpr a,DExpr b){
					if(cast(AddAssignExp)e) return a+b;
					if(cast(SubAssignExp)e) return a-b;
					if(cast(MulAssignExp)e) return a*b;
					if(cast(DivAssignExp)e){
						dist.assertTrue(dIvr(DIvr.Type.neqZ,b),"division by zero");
						return a/b;
					}
					if(cast(PowAssignExp)e){
						// TODO: enforce constraints on domain
						return a^^b;
					}
					if(cast(CatAssignExp)e) return a~b;
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
					auto athen=Analyzer(dthen,err,arrays.dup,deterministic.dup);
					dthen=athen.analyze(ite.then);
					auto aothw=Analyzer(dothw,err,arrays.dup,deterministic.dup);
					if(ite.othw) dothw=aothw.analyze(ite.othw);
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
						for(ℕ j=0;j<num.c;j++){
							auto anext=Analyzer(dist.dup(),err,arrays.dup,deterministic);
							auto dnext=anext.analyze(re.bdy);
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
						for(ℕ j=l.c+cast(int)fe.leftExclusive;j+cast(int)fe.rightExclusive<=r.c;j++){
							auto cdist=dist.dup();
							auto anext=Analyzer(cdist,err,arrays.dup,deterministic);
							auto var=cdist.declareVar(fe.var.name);
							if(var){
								auto rhs=dℕ(j);
								cdist.initialize(var,rhs,ℝ);
								anext.trackDeterministic(var,rhs,ℝ);
							}else{
								err.error("variable already exists",fe.var.loc);
								break;
							}
							auto dnext=anext.analyze(fe.bdy);
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
				if(isMethodBody&&i+1==ce.s.length){
					Expression[] returns;
					if(auto tpl=cast(TupleExp)re.e) returns=tpl.e;
					else returns=[re.e];
					import hashtable;
					SetX!DVar vars;
					DVar[] orderedVars;
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
						DVar var=cast(DVar)exp;
						if(var && !var.name.startsWith("__")){
							if(var in vars){
								auto vv=dist.getVar(var.name);
								dist.initialize(vv,var,ret.type);
								var=vv;
							}
							vars.insert(var);
							orderedVars~=var;
						}else if(exp){
							if(auto fe=cast(FieldExp)ret){
								var=dist.declareVar(fe.f.name,false);
								if(!var) var=dist.getVar(fe.f.name);
							}else var=dist.getVar("r");
							dist.initialize(var,exp,ret.type);
							vars.insert(var);
							orderedVars~=var;
						}
					}
					if(isMethodBody.thisRef&&!isMethodBody.isConstructor){
						vars.insert(dVar("this"));
						orderedVars~=dVar("this");
					}
					foreach(w;dist.freeVars.setMinus(vars)){
						dist.marginalize(w);
					}
					dist.orderFreeVars(orderedVars);
					dist.simplify();
				}else err.error("return statement must be last statement in function",re.loc);
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
				static bool warned=false;
				if(!warned){
					err.note("warning: cobserve will be removed",co.loc);
					warned=true;
				}
				if(auto var=transformExp(co.var)){
					if(cast(DVar)var){
						if(auto ex=transformExp(co.val)){
							dist.distribution=dist.distribution*dDelta(var-ex);
						}
					}else err.error("observed quantity must be a variable",co.loc);
				}
			}else if(!cast(ErrorExp)e) err.error(text("unsupported"),e.loc);
		}
		return dist;
	}
}

Distribution analyze(FunctionDef def,ErrorHandler err){
	auto dist=new Distribution();
	DExpr[] args;
	foreach(a;def.params) args~=dist.declareVar(a.name.name);
	if(def.thisRef){
		auto this_=dist.declareVar("this");
		if(!def.isConstructor) args~=this_;
		else{
			auto dd=def.scope_.getDatDecl();
			assert(dd && dd.dtype);
			dist.initialize(this_,dRecord(),dd.dtype);
		}
	}
	if(def.name.name!="main"||args.length) // TODO: move this decision to caller
		dist.addArgsWithContext(args);
	return analyzeWith(def,dist,err);
}

Distribution analyzeWith(FunctionDef def,Distribution dist,ErrorHandler err){
	auto a=Analyzer(dist,err);
	a.analyze(def.body_,def);
	a.dist.simplify();
	return a.dist;
}
