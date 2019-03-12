/+// Written in the D programming language
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
		DNVar[] args;
		foreach(i,a;def.params) args~=dist.declareVar(a.getName);
		DNVar ctx=null;
		if(def.context){
			assert(!!def.contextVal,text(def));
			ctx=dist.declareVar(def.contextVal.getName);
			if(def.contextName!=ctx.name)
				dist.initialize(dist.declareVar(def.contextName),ctx,def.context.vtype);
		}
		if(def.isConstructor){
			assert(!!def.thisVar);
			auto thisVar=dist.declareVar(def.thisVar.getName);
			auto dd=def.scope_.getDatDecl();
			assert(dd && dd.dtype);
			DExpr[string] fields;
			if(def.context) fields[def.contextName]=ctx;
			dist.initialize(thisVar,dRecord(fields),dd.dtype);
		}
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
		}else if(summaries[fun].distribution == mone){
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

	static class Unwind: Exception{ this(){ super(""); } }
	static void unwind(){ throw new Unwind(); }
	DExpr transformIte(Expression iteCond,CompoundExp iteThen,CompoundExp iteOthw,bool isConstr=false){
		auto cond=transformConstr(iteCond);
		if(!cond) throw new Unwind();
		auto dthen=dist.dupNoErr();
		auto var=dthen.getTmpVar("__ite");
		dthen.initialize(var,dTuple([]),tupleTy([])); // TODO: get rid of this?
		dthen.distribution=dthen.distribution*dNeqZ(cond);
		auto dothw=dist.dupNoErr();
		auto ovar=dothw.getTmpVar("__ite");
		assert(var==ovar);
		dothw.initialize(var,dTuple([]),tupleTy([])); // TODO: get rid of this?
		dothw.distribution=dothw.distribution*dEqZ(cond);
		auto athen=Analyzer(be,dthen,err,arrays.dup,deterministic.dup);
		auto tprior=dthen.distribution;
		auto then=isConstr?athen.transformConstr(iteThen):athen.transformExp(iteThen);
		if(!then) unwind();
		if(!iteOthw) unwind();
		auto aothw=Analyzer(be,dothw,err,arrays.dup,deterministic.dup);
		auto oprior=dothw.distribution;
		auto othw=isConstr?aothw.transformConstr(iteOthw):aothw.transformExp(iteOthw);
		if(!othw) unwind();
		if(isConstr && aothw.dist.distribution==oprior && aothw.dist.error==zero &&
		   athen.dist.distribution==tprior && athen.dist.error==zero){
			auto e1=transformConstr(iteThen), e2=transformConstr(iteOthw);
			return cond*e1+dEqZ(cond)*e2;
		}
		athen.dist.assign(var,then,iteThen.s[0].type);
		aothw.dist.assign(var,othw,iteOthw.s[0].type);
		auto dvar=dist.getTmpVar("__ite");
		dist.initialize(dvar,dTuple([]),tupleTy([]));
		dist=athen.dist.join(dist,aothw.dist);
		foreach(k,v;deterministic){
			if(k in athen.deterministic && k in aothw.deterministic
				&& athen.deterministic[k] == aothw.deterministic[k]){
				deterministic[k]=athen.deterministic[k];
			}else deterministic.remove(k);
		}
		return var;
	}
	DExpr transformExp(Exp e){
		import scope_,context;
		DExpr readLocal(string name){
			auto v=dVar(name);
			if(v in dist.freeVars||dist.hasArg(v)) return v;
			return null;
		}
		DExpr readFunction(Identifier id)in{ assert(id && id.scope_ && cast(FunctionDef)id.meaning); }body{
			auto fd=cast(FunctionDef)id.meaning;
			assert(!!fd);
			auto summary=be.getSummary(fd,id.loc,err);
			if(fd.isNested)
				return summary.toDExprWithContext(buildContextFor!readLocal(fd,id.scope_));
			return summary.toDExpr();
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
				if(id.name in arrays) return dArray(arrays[id.name]);
				if(auto r=lookupMeaning!(readLocal,readFunction)(id)) return r;
				err.error("undefined variable '"~id.name~"'",id.loc);
				unwind();
			}
			if(auto fe=cast(FieldExp)e){
				if(auto id=cast(Identifier)fe.e){
					if(id.name in arrays && fe.f.name=="length")
						return ℤ(arrays[id.name].length).dℚ;
				}
				if(isBuiltIn(fe)){
					if(auto at=cast(ArrayTy)fe.e.type){
						assert(fe.f.name=="length");
					}else{ assert(0); }
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
				dist.assertTrue(dNeqZ(e2),formatError("division by zero",e.loc));
				return cast(IDivExp)e?dFloor(e1/e2):e1/e2;
			}
			if(auto me=cast(ModExp)e) return doIt(me.e1)%doIt(me.e2);
			if(auto pe=cast(PowExp)e){
				auto e1=doIt(pe.e1), e2=doIt(pe.e2);
				// e1>=0 or e2∈ ℤ.
				auto c1=dNeqZ(dGeZ(e1)+dIsℤ(e2));
				// e1!=0 or e2>=0
				auto c2=dNeqZ(dNeqZ(e1)+dGeZ(e2));
				dist.assertTrue(c1*c2, "arguments outside domain of ^");
				return e1^^e2;
			}
			if(auto ce=cast(CatExp)e) return doIt(ce.e1)~doIt(ce.e2);
			if(auto ce=cast(BitOrExp)e) return dBitOr(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitXorExp)e) return dBitXor(doIt(ce.e1),doIt(ce.e2));
			if(auto ce=cast(BitAndExp)e) return dBitAnd(doIt(ce.e1),doIt(ce.e2));
			if(auto ume=cast(UMinusExp)e) return -doIt(ume.e);
			if(auto ume=cast(UNotExp)e) return dEqZ(doIt(ume.e));
			if(auto ume=cast(UBitNotExp)e) return -doIt(ume.e)-1;
			if(auto le=cast(LambdaExp)e){
				auto summary=be.getSummary(le.fd,le.loc,err);
				if(le.fd.isNested)
					return summary.toDExprWithContext(buildContextFor!readLocal(le.fd,le.fd.scope_));
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
						assert(isSubtype(argty,funty.dom),text(argty," ",funty.dom));
						if(thisExp){
							arg=dTuple([arg,thisExp]);
							argty=tupleTy([argty,fe.e.type]);
						}
						if(!thisExp)if(fun.isNested){ // nested function calls
							assert(id.scope_,text(id," ",id.loc));
							auto ctx=buildContextFor!readLocal(fun,id.scope_);
							assert(!!ctx);
							arg=dTuple([arg,ctx]);
							argty=tupleTy([argty,contextTy(false)]);
						}
						auto r=dist.call(summary,arg,argty);
						if(thisExp&&!fun.isConstructor){
							auto thisr=r[1.dℚ];
							r=r[0.dℚ];
							assignTo(thisExp,thisr,fe.e.type,ce.loc);
						}
						return r;
					}
					auto arg=util.among(id.name,"categorical","dirac","Dirac","sampleFrom","readCSV")?null:doIt(ce.arg);
					if(isBuiltIn(id)) switch(id.name){
					case "readCSV":
						err.error(text("call to 'readCSV' only supported as the right hand side of an assignment"),ce.loc);
						unwind();
						assert(0);
					case "Marginal":
						auto idist=dist.dup();
						auto r=idist.getVar("`r");
						idist.hasArgs=false;
						idist.addArgs([],true,null);
						idist.initialize(r,arg,ce.arg.type);
						foreach(v;dist.freeVars)
							idist.marginalize(v);
						idist.orderFreeVars([r],false);
						idist.renormalize();
						return dApply(idist.toDExpr(),dTuple([]));
					case "sampleFrom":
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
						auto total=dist.distribution;
						auto expct=dist.distribution*arg;
						foreach(v;dist.freeVars){ // TODO: handle non-convergence
							total=dInt(v,total);
							expct=dInt(v,expct);
						}
						// for obvious reasons, this will never fail:
						dist.assertTrue(dNeqZ(total),"expectation can be computed only in feasible path");
						auto tmp=dist.getTmpVar("__exp");
						dist.distribute(dDelta(expct/total,tmp,ℝ(true)));
						return tmp;
					default: break;
					}
				}
				auto funty=cast(FunTy)ce.e.type;
				assert(!!funty);
				Expression[] resty;
				bool isTuple=true;
				if(auto tplres=cast(TupleTy)funty.cod) resty=tplres.types;
				else{ resty=[funty.cod]; isTuple=false; }
				auto fun=doIt(ce.e);
				DNVar[] results=iota(0,resty.length).map!(x=>dist.getTmpVar("__r")).array;
				auto summary=Distribution.fromDExpr(fun,1,false,results,isTuple,resty);
				foreach(r;results) dist.freeVars.remove(r), dist.tmpVars.remove(r);
				auto argty=funty.dom;
				assert(isSubtype(ce.arg.type, argty));
				auto r=dist.call(summary,doIt(ce.arg),argty);
				return r;
			}
			if(auto idx=cast(IndexExp)e){
				if(idx.e.type == arrayTy(ℝ(true))){
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
					if(!opt.noBoundsCheck) dist.assertTrue(dIsℤ(di)*dGeZ(di)*dLt(di,dField(de,"length")),formatError("array access out of bounds",idx.loc));
					auto r=dIndex(de,di);
					return r;
				}else if(auto tt=cast(TupleTy)idx.e.type){
					assert(idx.a.length==1);
					return doIt(idx.e)[doIt(idx.a[0])];
				}
				assert(0,text(idx," ",idx.e.type));
			}
			if(auto sl=cast(SliceExp)e){
				auto de=doIt(sl.e),dl=doIt(sl.l),dr=doIt(sl.r);
				if(!opt.noBoundsCheck){
					dist.assertTrue(dIsℤ(dl)*dGeZ(dl),formatError("slice lower bound out of bounds",sl.loc));
					dist.assertTrue(dLe(dl,dr),formatError("slice lower bound exceeds upper bound",sl.loc));
					dist.assertTrue(dIsℤ(dr)*dLe(dr,dField(de,"length")),formatError("slice upper bound out of bounds",sl.loc));
				}
				return dSlice(de,dl,dr);
			}
			if(auto le=cast(LiteralExp)e){
				if(le.lit.type==Tok!"0"||le.lit.type==Tok!".0"){
					auto x=le.lit.str.split("e");
					auto n=x[0].split(".");
					if(n.length==1) n~="";
					auto r=dℚ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length);
					if(x.length==2) r=x[1][0]=='-'?r/pow(ℤ(10),-ℤ(x[1])):r*pow(ℤ(10),ℤ(x[1]));
					return r;
				}
			}
			if(auto cmp=cast(CompoundExp)e){
				if(cmp.s.length==1)
					return doIt(cmp.s[0]);
			}else if(auto ite=cast(IteExp)e){
				return transformIte(ite.cond,ite.then,ite.othw);
			}else if(auto tpl=cast(TupleExp)e){
				auto dexprs=tpl.e.map!doIt.array;
				return dTuple(dexprs);
			}else if(auto arr=cast(ArrayExp)e){
				auto dexprs=arr.e.map!doIt.array;
				return dArray(dexprs);
			}else if(auto ae=cast(AssertExp)e){
				if(auto c=transformConstr(ae.e)){
					dist.assertTrue(c,text("assertion '",ae.e,"' failed"));
					return dTuple([]);
				}
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
				auto zeroExp=new LiteralExp(Token(Tok!"0","0"));
				zeroExp.type = ℝ(true);
				return transformIte(b.e1,new CompoundExp([b.e2]),new CompoundExp([zeroExp]),true);
			}else if(auto b=cast(OrExp)e){
				auto oneExp=new LiteralExp(Token(Tok!"0","1"));
				oneExp.type = ℝ(true);
				return transformIte(b.e1,new CompoundExp([oneExp]),new CompoundExp([b.e2]),true);
			}else if(auto i=cast(IteExp)e){
				return transformIte(i.cond,i.then,i.othw,true);
			}else with(DIvr.Type)if(auto b=cast(LtExp)e){
				mixin(common);
				return dLt(e1,e2);
			}else if(auto b=cast(LeExp)e){
				mixin(common);
				return dLe(e1,e2);
			}else if(auto b=cast(GtExp)e){
				mixin(common);
				return dGt(e1,e2);
			}else if(auto b=cast(GeExp)e){
				mixin(common);
				return dGe(e1,e2);
			}else if(auto b=cast(EqExp)e){
				mixin(common);
				return dEq(e1,e2);
			}else if(auto b=cast(NeqExp)e){
				mixin(common);
				return dNeq(e1,e2);
			}else{
				auto cond=transformExp(e);
				if(!cond) unwind();
				return dNeqZ(cond);
			}
			err.error("unsupported",e.loc);
			throw new Unwind();
		}
		try return doIt(e);
		catch(Unwind){ return null; }
	}

	void trackDeterministic(DVar var,DExpr rhs,Expression ty){
		if(ty != ℝ(true)) return;
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

	DExpr isDeterministic(DExpr e,Expression ty){ // TODO: track deterministic values for more complex datatypes than 'ℝ(true)"?
		if(ty != ℝ(true)) return null;
		if(auto r=isObviouslyDeterministic(e))
			return r;
		// TODO: this is a glorious hack:
		auto ndist=dist.dup();
		auto tmp=ndist.getVar("tmp");
		ndist.initialize(tmp,e,ℝ(true));
		foreach(v;dist.freeVars) ndist.marginalize(v);
		foreach(f;ndist.distribution.factors)
			if(!cast(DDelta)f&&!cast(Dℚ)f)
				return null;
		auto norm=dIntSmp(tmp,ndist.distribution,one);
		if(norm == zero || (!cast(Dℚ)norm&&!cast(DFloat)norm))
			return null;
		auto r=(dIntSmp(tmp,tmp*ndist.distribution,one)/norm).simplify(one);
		if(r.hasAny!DInt) return null;
		return r;
	}

	Dℚ isDeterministicInteger(DExpr e){
		if(auto r=isDeterministic(e,ℝ(true)))
			if(auto num=r.isInteger()) return num;
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
			assert(cidx.c.den==1);
			return arr[cast(size_t)cidx.c.num.toLong()];
		}else return null;
	}

	void evaluateArrayCall(Identifier id,CallExp call){
		if(!isSubtype(call.arg.type,ℝ(true))){
			err.error("expected one real argument to array",call.loc);
			return;
		}
		auto ae=transformExp(call.arg);
		if(!ae) return;
		auto num=isDeterministicInteger(ae);
		assert(num.c.den==1);
		if(!num){
			err.error("array length should be provably deterministic integer",call.loc);
			return;
		}
		if(num.c.num<0){
			err.error("array length should be non-negative",call.loc);
			return;
		}
		if(num.c.num>int.max){
			err.error("array length too high",call.loc);
			return;
		}
		if(id.name in arrays){
			err.error("array already exists",id.loc);
			return;
		}
		foreach(k;0..num.c.num.toLong()){
			auto var=dist.getVar(id.name);
			dist.initialize(var,zero,ℝ(true));
			arrays[id.name]~=var;
		}
	}

	void evaluateReadCSVCall(Identifier id,CallExp call){
		if(call.arg.type!=stringTy(true)){
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
				return dℚ((n[0]~n[1]).ℤ)/(ℤ(10)^^n[1].length);
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
		void assignVar(DNVar var,DExpr rhs,Expression ty){
			if(var.name !in arrays){
				dist.assign(var,rhs,ty);
				trackDeterministic(var,rhs,ty);
			}else err.error("reassigning array unsupported",loc);
		}
		if(auto var=cast(DNVar)lhs){
			assignVar(var,rhs,ty);
		}else if(auto idx=cast(DIndex)lhs){
			if(auto id=cast(DNVar)idx.e){
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
		/+if(!cast(Identifier)lhs&&!cast(FieldExp)lhs){ // TODO
			auto tmp=dist.getTmpVar("tmp");
			dist.initialize(tmp,rhs,ty);
			rhs=tmp;
		}+/
		void assignToImpl(Expression lhs,DExpr rhs,Expression ty){
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
							if(auto v=cast(DNVar)cidx){
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
						if(!opt.noBoundsCheck) dist.assertTrue(dGeZ(index)*dLt(index,dField(old,"length")),"array access out of bounds"); // TODO: check that index is an integer.
						assignToImpl(idx.e,dIUpdate(old,index,rhs),idx.e.type);
					}
				}else{
					err.error(text("unsupported type '",idx.e.type,"' for index expression"),lhs.loc);
				}
			}else if(auto fe=cast(FieldExp)lhs){
				if(!cast(ArrayTy)fe.e.type){
					auto old=transformExp(fe.e);
					if(old) assignToImpl(fe.e,dRUpdate(old,fe.f.name,rhs),fe.e.type);
				}
			}else if(auto tpl=cast(TupleExp)lhs){
				if(!cast(DVar)rhs){
					auto tmp=dist.getTmpVar("__tpl");
					dist.initialize(tmp,rhs,ty);
					assignTo(lhs,tmp,ty,loc);
				}else{
					auto tt=cast(TupleTy)ty;
					assert(!!tt);
					assert(tpl.e.length==tt.types.length);
					foreach(k,exp;tpl.e) assignToImpl(exp,rhs[k.dℚ],tt.types[k]);
				}
			}else if(auto tae=cast(TypeAnnotationExp)lhs){
				assignToImpl(tae.e,rhs,ty);
			}else{
			LbadAssgnmLhs:
				err.error("invalid left hand side for assignment",lhs.loc);
			}
		}
		assignToImpl(lhs,rhs,ty);
	}

	private void analyzeStatement(Expression e,ref Distribution retDist,FunctionDef functionDef)in{assert(!!e);}body{
		if(opt.trace) writeln("statement: ",e);
		/+writeln("before: ",dist);
		 scope(success) writeln("after: ",dist);+/
		// TODO: visitor?
		void analyzeIte(Expression iteCond,CompoundExp iteThen,CompoundExp iteOthw){
			if(auto c=transformConstr(iteCond)){
				auto dthen=dist.dupNoErr();
				dthen.distribution=dthen.distribution*dNeqZ(c);
				auto dothw=dist.dupNoErr();
				dothw.distribution=dothw.distribution*dEqZ(c);
				auto athen=Analyzer(be,dthen,err,arrays.dup,deterministic.dup);
				dthen=athen.analyze(iteThen,retDist,functionDef);
				auto aothw=Analyzer(be,dothw,err,arrays.dup,deterministic.dup);
				if(iteOthw) dothw=aothw.analyze(iteOthw,retDist,functionDef);
				dist=dthen.join(dist,dothw);
				foreach(k,v;deterministic){
					if(k in athen.deterministic && k in aothw.deterministic
						&& athen.deterministic[k] == aothw.deterministic[k]){
						deterministic[k]=athen.deterministic[k];
					}else deterministic.remove(k);
				}
			}
		}
		if(auto nde=cast(DefExp)e){
			auto de=cast(ODefExp)nde.initializer;
			assert(!!de);
			// TODO: no real need to repeat checks done by semantic
			scope(exit) dist.marginalizeTemporaries();
			void defineVar(Identifier id,DExpr rhs,Expression ty){
				DVar var=null;
				if(id.name !in arrays) var=dist.declareVar(id.name);
				if(var){
					dist.distribute(dDelta(rhs?rhs:zero,var,rhs?ty:ℝ(true))); // TODO: zero is not a good default value for types other than ℝ(true).
					trackDeterministic(var,rhs,ty);
				}else err.error("variable already exists",id.loc);
			}
			if(auto id=cast(Identifier)de.e1){
				bool isSpecial=false;
				if(auto call=cast(CallExp)de.e2){
					if(auto cid=cast(Identifier)call.e){
						switch(cid.name){
							case "array":
								if(isSubtype(call.arg.type,ℝ(true))){
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
					defineVar(id,rhs[k.dℚ],tt.types[k]);
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
				//if(cast(OrAssignExp)e) return dNeqZ(dNeqZ(a)+dNeqZ(b));
				//if(cast(AndAssignExp)e) return dNeqZ(a)*dNeqZ(b);
				if(cast(AddAssignExp)e) return a+b;
				if(cast(SubAssignExp)e) return a-b;
				if(cast(MulAssignExp)e) return a*b;
				if(cast(DivAssignExp)e||cast(IDivAssignExp)e){
					dist.assertTrue(dNeqZ(b),"division by zero");
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
			Expression setℝ(Expression e){
				e.type = ℝ(true);
				return e;
			}
			if(cast(AndAssignExp)be){
				auto zeroExp=setℝ(new LiteralExp(Token(Tok!"0","0")));
				analyzeIte(be.e1, new CompoundExp([new AssignExp(be.e1,setℝ(new NeqExp(be.e2,zeroExp)))]), new CompoundExp([new AssignExp(be.e1,setℝ(new NeqExp(be.e1,zeroExp)))]));
			}else if(cast(OrAssignExp)be){
				auto zeroExp=setℝ(new LiteralExp(Token(Tok!"0","0")));
				auto oneExp=setℝ(new LiteralExp(Token(Tok!"0","1")));
				analyzeIte(be.e1, new CompoundExp([new AssignExp(be.e1,oneExp)]), new CompoundExp([new AssignExp(be.e1,setℝ(new NeqExp(be.e2,zeroExp)))]));
			}else{
				auto lhs=transformExp(be.e1);
				auto rhs=transformExp(be.e2);
				assignTo(lhs,perform(lhs,rhs),be.e2.type,be.loc);
			}
			dist.marginalizeTemporaries();
		}else if(auto call=cast(CallExp)e){
			transformExp(call);
			dist.marginalizeTemporaries();
		}else if(auto ite=cast(IteExp)e){
			analyzeIte(ite.cond,ite.then,ite.othw);
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
					assert(l.c.den==1 && r.c.den==1);
					for(ℤ j=l.c.num+cast(int)fe.leftExclusive;j+cast(int)fe.rightExclusive<=r.c.num;j++){
						auto cdist=dist.dup();
						auto anext=Analyzer(be,cdist,err,arrays.dup,deterministic);
						auto var=cdist.declareVar(fe.var.name);
						if(var){
							auto rhs=dℚ(j);
							cdist.initialize(var,rhs,ℝ(true));
							anext.trackDeterministic(var,rhs,ℝ(true));
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
			auto exp = transformExp(re.e);
			auto tty=cast(TupleTy)re.e.type;
			DNVar[] orderedVars;
			bool isTuple=!!tty, needIndex=tty&&tty.types.length!=0;
			void keepOnly(SetX!DNVar keep){
				foreach(w;dist.freeVars.dup){
					if(w in keep) continue;
					dist.marginalize(w);
				}
			}
			if(!exp){ dist=odist; return; }
			if(functionDef.context&&functionDef.contextName.startsWith("this")){
				auto resv=dist.getVar("__r"),ctxv=dVar(functionDef.contextName);
				dist.initialize(resv,exp,re.e.type);
				orderedVars=[resv,ctxv];
				keepOnly(setx(orderedVars));
				isTuple=true;
			}else{
				foreach(n;functionDef.retNames){
					auto var=dVar(n);
					assert(!dist.hasArg(var));
					if(var in dist.freeVars){
						auto nvar=dist.getVar(var.name);
						dist.distribution=dist.distribution.substitute(var,nvar);
						exp=exp.substitute(var,nvar);
						dist.freeVars.remove(var);
						dist.freeVars.insert(nvar);
					}
				}
				orderedVars=functionDef.retNames.map!(n=>dist.declareVar(n)).array;
				foreach(i,var;orderedVars){
					assert(!!var);
					dist.initialize(var,needIndex?dIndex(exp,i.dℚ):exp,needIndex?tty.types[i]:re.e.type);
				}
				keepOnly(setx(orderedVars));
			}
			assert(isTuple||orderedVars.length==1);
			dist.orderFreeVars(orderedVars,isTuple);
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
				}else if(expected != Expected(true,todo,ex))
					err.error("can only have one 'expected' annotation, in 'main'.",re.loc);
			}
		}else if(auto ae=cast(AssertExp)e){
			if(auto c=transformConstr(ae.e))
				dist.assertTrue(c,text("assertion '",ae.e,"' failed"));
		}else if(auto oe=cast(ObserveExp)e){
			if(auto c=transformConstr(oe.e))
				dist.observe(c);
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
		if(retDist){
			dist.simplify();
			if(dist.distribution == zero){
				retDist.error=retDist.error+dist.error;
				dist=retDist;
			}else err.error("not all paths return",fd.loc); // TODO: check during semantic
		}
		if(!dist.freeVarsOrdered) dist.orderFreeVars(dist.freeVars.array,dist.freeVars.length!=1);
	}
}
+/
