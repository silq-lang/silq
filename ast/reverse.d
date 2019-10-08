// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.reverse;

import std.stdio,std.conv,std.format,std.algorithm,std.range,std.exception;
import ast.lexer,ast.scope_,ast.expression,ast.type,ast.declaration,ast.semantic_,ast.error,util;

bool isReverse(Expression e){
	auto id=cast(Identifier)e;
	if(!id) return false;
	if(id.name!="reverse") return false;
	return id.meaning&&isReverse(id.meaning);
}
bool isReverse(Declaration decl){
	import ast.parser: preludePath;
	if(preludePath() !in modules) return false;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	if(!decl||decl.scope_ !is sc) return false;
	if(!decl.name) return false;
	return decl.getName=="reverse";
}
string freshName(){
	static int counter=0;
	return text("__tmp",counter++);
}

Expression constantExp(size_t l){
	Token tok;
	tok.type=Tok!"0";
	tok.str=to!string(l);
	return new LiteralExp(tok);
}

Identifier getPreludeSymbol(string name,Location loc,Scope isc){
	import ast.parser: preludePath;
	import ast.semantic_: modules;
	if(preludePath() !in modules) return null;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	auto res=new Identifier(name);
	res.loc=loc;
	res.scope_=isc;
	res.meaning=sc.lookup(res,false,false,Lookup.consuming);
	if(!res.meaning){
		res.sstate=SemState.error;
	}else{
		res.type=typeForDecl(res.meaning);
		res.constLookup=false;
		res.sstate=SemState.completed;
	}
	return res;
}


Identifier getReverse(Location loc,Scope isc){
	return getPreludeSymbol("reverse",loc,isc);
}
Identifier getDup(Location loc,Scope isc){
	return getPreludeSymbol("dup",loc,isc);
}

bool isClassicalExp(Expression e){
	return e.type&&e.subexpressions.all!(x=>!x.type||x.type.isClassical())&&e.isQfree()&&!e.consumes;
}
bool hasImplicitDup(Expression olhs,Scope sc){
	if(olhs.byRef) return false;
	if(auto idx=cast(IndexExp)olhs)
		return true;
	if(auto id=cast(Identifier)olhs){
		if(isClassicalExp(olhs)) return true;
		if(id.meaning){
			if(typeForDecl(id.meaning).isClassical())
				return true;
			if(auto vd=cast(VarDecl)id.meaning){
				if(vd.isConst)
					return true;
			}
		}
	}
	// TODO: get rid of this
	if(auto id=cast(Identifier)olhs){
		if(auto meaning=cast(VarDecl)sc.lookup(id,false,false,Lookup.probing)){
			if(meaning.isConst||typeForDecl(meaning).isClassical)
				return true;
		}
	}
	return false;
}

bool validDefLhs(bool analyzed)(Expression olhs,Scope sc){
	bool validDefEntry(Expression e){
		static if(analyzed) if(hasImplicitDup(e,sc)) return false;
		return cast(Identifier)e||cast(IndexExp)e;
	}
	if(auto tpl=cast(TupleExp)olhs) return tpl.e.all!validDefEntry;
	return validDefEntry(olhs);
}

Expression lowerDefine(bool analyzed)(Expression olhs,Expression orhs,Location loc,Scope sc)in{
	assert(loc.line);
}do{
	Expression res;
	scope(success) if(res){ res.loc=loc; }
	static if(analyzed) Expression nlhs;
	Expression lhs(){
		static if(analyzed){
			if(!nlhs) nlhs=olhs.copy();
			return nlhs;
		}else return olhs;
	}
	static if(analyzed) Expression nrhs;
	Expression rhs(){
		static if(analyzed){
			if(!nrhs) nrhs=orhs.copy();
			return nrhs;
		}else return orhs;
	}
	Expression error(){
		res=new DefineExp(lhs,rhs);
		res.sstate=SemState.error;
		return res;
	}
	if(validDefLhs!analyzed(olhs,sc)){
		if(auto tpl=cast(TupleExp)lhs) if(!tpl.e.length&&(cast(CallExp)rhs||cast(ForgetExp)rhs)) return rhs;
		return res=new DefineExp(lhs,rhs);
	}
	Expression forget(){ return res=new ForgetExp(rhs,lhs); }
	static if(analyzed){
		if(hasImplicitDup(olhs,sc)) // TODO: automatically synthesize implicit dups in semantic?
			return forget();
	}
	if(auto arr=cast(ArrayExp)olhs){
		auto newLhs=new TupleExp(arr.copy().e);
		newLhs.loc=lhs.loc;
		auto newRhs=orhs;
		if(auto aty=cast(ArrayTy)orhs.type){
			auto tty=tupleTy(aty.next.repeat(arr.e.length).array);
			newRhs=new TypeAnnotationExp(orhs,tty,TypeAnnotationType.coercion);
			newRhs.type=tty;
			newRhs.loc=orhs.loc;
		}
		return lowerDefine!analyzed(newLhs,newRhs,loc,sc);
	}
	if(auto tpll=cast(TupleExp)olhs){
		void handleRhs(R)(){
			if(auto tplr=cast(R)orhs){
				enforce(tpll.e.length==tplr.e.length);
				Expression[] es;
				foreach_reverse(i;0..tpll.e.length){
					es~=lowerDefine!analyzed(tpll.e[i],tplr.e[i],loc,sc); // TODO: evaluation order of rhs okay?
				}
				if(es.any!(x=>!x)) return;
				res=new CompoundExp(es);
			}
		}
		handleRhs!TupleExp();
		handleRhs!ArrayExp();
		if(!res){
			auto tmp=new TupleExp(iota(tpll.e.length).map!(delegate Expression(i){ auto id=new Identifier(freshName); id.loc=orhs.loc; return id; }).array);
			tmp.loc=loc;
			auto d1=lowerDefine!false(tmp,rhs,loc,sc);
			auto d2=lowerDefine!analyzed(olhs,tmp,loc,sc);
			res=new CompoundExp([d1,d2]);
		}
		return res;
	}
	bool isLiftedBuiltIn(Expression e){
		if(cast(AddExp)lhs||cast(SubExp)lhs||cast(NSubExp)lhs||cast(MulExp)lhs||cast(DivExp)lhs||cast(IDivExp)lhs||cast(ModExp)lhs||cast(PowExp)lhs||cast(BitOrExp)lhs||cast(BitXorExp)lhs||cast(BitAndExp)lhs||cast(UMinusExp)lhs||cast(UNotExp)lhs||cast(UBitNotExp)lhs||cast(AndExp)lhs||cast(OrExp)lhs||cast(LtExp)lhs||cast(LeExp)lhs||cast(GtExp)lhs||cast(GeExp)lhs||cast(EqExp)lhs||cast(NeqExp)lhs)
			return true;
		if(cast(LiteralExp)e) return true;
		if(cast(SliceExp)e) return true;
		if(auto tae=cast(TypeAnnotationExp)e)
			return isLiftedBuiltIn(tae.e);
		return false;
	}
	if(isLiftedBuiltIn(lhs)) return forget();
	if(auto tae=cast(TypeAnnotationExp)olhs){
		static if(analyzed){
			if(olhs.type){
				if(!orhs.type||orhs.type!=tae.e.type){
					auto newRhs=new TypeAnnotationExp(rhs,tae.e.type,TypeAnnotationType.coercion);
					newRhs.loc=rhs.loc;
					return lowerDefine!analyzed(tae.e,newRhs,loc,sc);
				}else return lowerDefine!analyzed(tae.e,orhs,loc,sc);
			}
		}
		// TOOD: only do this if lhs is variable
		auto newRhs=new TypeAnnotationExp(rhs,tae.t,tae.annotationType);
		newRhs.loc=rhs.loc;
		return lowerDefine!analyzed(tae.e,newRhs,loc,sc);
	}
	if(auto ce=cast(CatExp)olhs){
		Expression knownLength(Expression e){
			Expression res;
			scope(exit) if(res) res.loc=e.loc;
			if(auto arr=cast(ArrayExp)e) return res=constantExp(arr.e.length);
			if(auto tpl=cast(TupleExp)e) return res=constantExp(tpl.e.length);
			if(auto tae=cast(TypeAnnotationExp)e){
				if(auto vec=cast(VectorTy)tae.t)
					return vec.num.copy();
				if(auto pow=cast(PowExp)tae.t)
					return pow.e2.copy();
				return knownLength(tae.e);
			}
			if(e.type){
				if(auto vec=cast(VectorTy)e.type)
					return vec.num.copy();
			}
			return null;
		}
		auto l1=knownLength(ce.e1),l2=knownLength(ce.e2);
		if(!l1&&!l2){
			sc.error("concatenation of arrays of unknown length not supported as definition left-hand side",ce.loc);
			return error();
		}
		auto tmp=new Identifier(freshName);
		tmp.loc=olhs.loc;
		auto tmpLen(){
			auto id=new Identifier("length");
			id.loc=tmp.loc;
			return new FieldExp(tmp.copy(),id);
		}
		if(!l1){
			auto l=tmpLen();
			l.loc=l2.loc;
			auto s=new NSubExp(l,l2);
			s.loc=l2.loc;
			l1=s;
		}else if(!l2){
			auto l=tmpLen();
			l.loc=l1.loc;
			auto s=new NSubExp(l,l1);
			s.loc=l1.loc;
			l2=s;
		}
		assert(l1&&l2);
		// TODO: nicer runtime error message for inconsistent array lengths?
		auto d1=lowerDefine!analyzed(tmp,orhs,loc,sc);
		auto z=constantExp(0);
		z.loc=olhs.loc;
		auto l=tmpLen();
		l.loc=olhs.loc;
		auto tmp1=tmp.copy();
		tmp1.loc=rhs.loc;
		Expression s1=new SliceExp(tmp1,z,l1);
		s1.loc=tmp1.loc;
		auto tmp2=tmp.copy();
		tmp2.loc=rhs.loc;
		Expression s2=new SliceExp(tmp1,l1.copy(),l);
		s2.loc=tmp2.loc;
		auto d2=lowerDefine!analyzed(ce.e1,s1,loc,sc);
		d2.loc=loc;
		auto d3=lowerDefine!analyzed(ce.e2,s2,loc,sc);
		d3.loc=loc;
		auto tmp3=tmp.copy();
		tmp3.loc=rhs.loc;
		auto fe=new ForgetExp(tmp3,ce.copy());
		fe.loc=loc;
		return res=new CompoundExp([d1,d2,d3,fe]);
	}
	if(auto fe=cast(ForgetExp)olhs){
		if(!fe.val){
			sc.error("reversal of implicit forget not supported yet",fe.loc);
			return error();
		}
		auto tpl=cast(TupleExp)rhs;
		enforce(!tpl||tpl.length==0);
		auto dup=getDup(fe.val.loc,sc);
		auto nval=new CallExp(dup,fe.val.copy(),false,false);
		nval.type=fe.val.type;
		nval.loc=fe.val.loc;
		auto def=lowerDefine!analyzed(fe.var,nval,loc,sc);
		if(!tpl) return res=new CompoundExp([rhs,def]);
		return def;
	}
	if(auto ce=cast(CallExp)olhs){
		if(!ce.e.type) ce.e=expressionSemantic(ce.e,sc,ConstResult.yes);
		if(auto ft=cast(FunTy)ce.e.type){
			if(ft.isSquare&&!ce.isSquare){
				sc.error("implicit function call not supported as definition left-hand side",ce.loc); // TODO
				return error();
			}
			if(ft.annotation<Annotation.mfree){
				sc.error("reversed function must be 'mfree'",ce.e.loc);
				return error;
			}
			if(!ft.isClassical){
				sc.error("quantum function call not supported as definition left-hand side",ce.loc); // TODO: support within reversed functions
				return error();
			}
			auto numConstArgs1=ft.isConst.until!(x=>!x).walkLength;
			auto numArgs=ft.isConst[numConstArgs1..$].until!(x=>x).walkLength;
			auto numConstArgs2=ft.isConst[numConstArgs1+numArgs..$].until!(x=>!x).walkLength;
			if(numConstArgs1+numArgs+numConstArgs2!=ft.nargs){
				sc.error("reversed function cannot mix 'const' and consumed arguments",ce.arg.loc); // TODO: automatically reorder arguments
				return error();
			}
			// if(!numArgs&&rhs.isLifted()) return res=new ForgetExp(rhs,lhs); // TODO?
			Expression newlhs,newarg;
			// TODO: if analyzed, predetermine a type for newlhs
			if(!numArgs){
				if(ft.annotation>=Annotation.qfree) return forget();
				newlhs=new TupleExp([]);
				newlhs.loc=ce.arg.loc;
				newarg=new TupleExp([ce.arg,orhs]);
				newarg.loc=lhs.loc;
			}else if(auto tpl=cast(TupleExp)ce.arg){
				auto newlhss=tpl.e[numConstArgs1..numConstArgs1+numArgs];
				if(newlhss.length==1) newlhs=newlhss[0];
				else newlhs=new TupleExp(newlhss);
				newlhs.loc=ce.arg.loc;
				auto newargs=tpl.e[0..numConstArgs1]~[rhs]~tpl.e[numConstArgs1+numArgs..$];
				if(newargs.length==1) newarg=newargs[0];
				else newarg=new TupleExp(newargs);
				newarg.loc=lhs.loc;
			}else if(numArgs==ft.nargs){
				newlhs=ce.arg;
				newarg=orhs;
				newarg.loc=loc;
			}else{
				sc.error("cannot match single tuple to function with mixed 'const' and consumed parameters",ce.loc);
				return error();
			}
			Expression reversed=null,newrhs=null;
			if(auto ce2=cast(CallExp)unwrap(ce.e)){
				if(auto id=cast(Identifier)unwrap(ce2.e)){
					if(isBuiltIn(id)){
						switch(id.name){
							case "quantumPrimitive":
								auto op=getQuantumOp(ce2.arg);
								switch(op){
									case "H","X","Y","Z": reversed=ce.e; break;
									case "P":
										reversed=ce.e;
										reversed.loc=ce.e.loc;
										auto tpl=cast(TupleExp)newarg;
										enforce(tpl&&tpl.length==2);
										// note: this ignores side-effects of rhs, if any
										auto negated=new UMinusExp(tpl.e[0]);
										negated.loc=newarg.loc;
										newarg=negated;
										break;
									case "rX","rY","rZ":
										reversed=ce.e;
										reversed.loc=ce.e.loc;
										auto tpl=cast(TupleExp)newarg;
										enforce(tpl&&tpl.length==2);
										auto negated=new UMinusExp(tpl.e[0]);
										negated.loc=tpl.e[0].loc;
										auto newtpl=new TupleExp([negated,tpl.e[1]]);
										newtpl.loc=newarg.loc;
										newarg=newtpl;
										break; // DMD bug: does not detect if this is missing
									default:
										sc.error(format("cannot reverse quantum primitive '%s'",op),ce2.loc);
										return error();
								}
								break;
							default: break;
						}
					}
				}else if(auto ce3=cast(CallExp)unwrap(ce2.e)){
						if(auto id3=cast(Identifier)unwrap(ce3.e)){
							if(isBuiltIn(id3)){
								switch(id3.name){
									case "quantumPrimitive":
										auto op=getQuantumOp(ce3.arg);
										switch(op){
											case "dup":
												auto tpl=cast(TupleExp)newarg;
												enforce(tpl&&tpl.length==2);
												newrhs=new ForgetExp(tpl.e[1],tpl.e[0]);
												break;
											default:
												sc.error(format("cannot reverse quantum primitive '%s'",op),ce2.loc);
												return error();
										}
										break;
									default: break;
								}
							}
						}
				}
			}
			if(!reversed&&!newrhs){
				auto rev=getReverse(ce.e.loc,sc);
				if(rev.sstate!=SemState.completed) return error();
				reversed=new CallExp(rev,ce.e,false,false);
				reversed.loc=ce.e.loc;
			}
			if(!newrhs) newrhs=new CallExp(reversed,newarg,ce.isSquare,ce.isClassical);
			newrhs.loc=newarg.loc;
			return lowerDefine!analyzed(newlhs,newrhs,loc,sc);
		}
	}
	sc.error("expression not supported as definition left-hand side",olhs.loc);
	return error();
}
// rev(x:=y;) ⇒ y:=x;
// rev(x:=H(y);) ⇒ H(y):=x; ⇒ y:=reverse(H)(x);
// rev(x:=dup(y);) ⇒ dup(y):=x; ⇒ ():=reverse(dup)(x,y) ⇒ ():=forget(x=dup(y));
// rev(x:=CNOT(a,b);) ⇒ CNOT(a,b):=x; ⇒ a:=reverse(CNOT)(x,b);

Expression lowerDefine(bool analyzed)(DefineExp e,Scope sc){
	if(e.sstate==SemState.error) return e;
	if(validDefLhs!analyzed(e.e1,sc)) return null;
	return lowerDefine!analyzed(e.e1,e.e2,e.loc,sc);
}
FunctionDef reverseFunction(FunctionDef fd)in{
	assert(fd.scope_&&fd.ftype&&fd.ftype.isClassical()&&fd.ftype.annotation>=Annotation.mfree);
}do{
	if(fd.reversed) return fd.reversed;
	auto sc=fd.scope_, ft=fd.ftype;
	auto asc=sc;
	foreach(id;fd.captures){ // TODO: this is a bit hacky
		if(id.meaning&&id.meaning.scope_&&!id.meaning.scope_.lookupHere(id,false,Lookup.probing)){
			auto scope_=id.meaning.scope_;
			id.meaning.scope_=null;
			if(!scope_.insert(id.meaning,true))
				fd.sstate=SemState.error;
		}
	}
	Expression[] constArgTypes1; // TODO: get rid of code dupliction
	Expression[] argTypes;
	Expression[] constArgTypes2;
	Expression returnType;
	if(!ft.isTuple){
		assert(ft.isConst.length==1);
		if(ft.isConst[0]) constArgTypes1=[ft.dom];
		else argTypes=[ft.dom];
	}else{
		auto tpl=ft.dom.isTupleTy;
		assert(!!tpl && tpl.length==ft.isConst.length);
		auto numConstArgs1=ft.isConst.until!(x=>!x).walkLength;
		auto numArgs=ft.isConst[numConstArgs1..$].until!(x=>x).walkLength;
		auto numConstArgs2=ft.isConst[numConstArgs1+numArgs..$].until!(x=>!x).walkLength;
		enforce(numConstArgs1+numArgs+numConstArgs2==tpl.length,"reversed function cannot mix 'const' and consumed arguments");
		constArgTypes1=iota(numConstArgs1).map!(i=>tpl[i]).array;
		argTypes=iota(numConstArgs1,numConstArgs1+numArgs).map!(i=>tpl[i]).array;
		constArgTypes2=iota(numConstArgs1+numArgs,tpl.length).map!(i=>tpl[i]).array;
	}
	enforce(!argTypes.any!(t=>t.hasClassicalComponent()),"reversed function cannot have classical components in consumed arguments");
	returnType=ft.cod;
	auto nargTypes=constArgTypes1~[returnType]~constArgTypes2;
	auto nreturnTypes=argTypes;
	auto dom=nargTypes.length==1?nargTypes[0]:tupleTy(nargTypes);
	auto cod=nreturnTypes.length==1?nreturnTypes[0]:tupleTy(nreturnTypes);
	auto isConst=chain(true.repeat(constArgTypes1.length),only(returnType.impliesConst()),true.repeat(constArgTypes2.length)).array;
	auto annotation=ft.annotation;
	auto ret=fd.body_.s.length?cast(ReturnExp)fd.body_.s[$-1]:null;
	if(!ret){
		sc.error("reversing early returns not supported yet",fd.loc);
		return null;
	}
	string rpname;
	if(auto id=cast(Identifier)ret.e) rpname=(id.meaning&&id.meaning.name?id.meaning.name:id).name;
	else rpname=freshName();
	auto pnames=chain(fd.params[0..constArgTypes1.length].map!(p=>p.name.name),only(rpname),fd.params[chain(constArgTypes1,argTypes).length..$].map!(p=>p.name.name));
	auto params=iota(nargTypes.length).map!((i){
		auto pname=new Identifier(pnames[i]);
		pname.loc=fd.loc;
		auto param=new Parameter(isConst[i],pname,nargTypes[i]);
		param.loc=pname.loc;
		return param;
	}).array;
	auto retRhs=new Identifier(rpname);
	retRhs.loc=ret.loc;
	retRhs.type=returnType;
	retRhs.loc=ret.loc;
	auto body_=new CompoundExp([]);
	body_.loc=fd.body_.loc;
	auto result=new FunctionDef(null,params,params.length!=1,cod,body_);
	result.isSquare=fd.isSquare;
	result.annotation=fd.annotation;
	result.scope_=sc;
	result=cast(FunctionDef)presemantic(result,sc);
	assert(!!result);
	bool retDefNecessary=(returnType!=unit||!cast(TupleExp)ret.e)&&!cast(Identifier)ret.e;
	auto retDef=retDefNecessary?lowerDefine!true(ret.e,retRhs,ret.loc,result.fscope_):null;
	auto argNames=fd.params[constArgTypes1.length..constArgTypes1.length+argTypes.length].map!(p=>p.name.name);
	auto makeArg(size_t i){
		if(argTypes[i]==unit){ // unit is classical yet can be consumed
			Expression r=new TupleExp([]);
			r.loc=ret.loc;
			r.type=unit;
			return r;
		}else{
			Expression id=new Identifier(argNames[i]);
			id.loc=ret.loc;
			id.type=argTypes[i];
			return id;
		}
	}
	auto argExp=argTypes.length==1?makeArg(0):new TupleExp(iota(argTypes.length).map!makeArg.array);
	argExp.loc=fd.loc; // TODO: use precise parameter locations
	Expression argRet=new ReturnExp(argExp);
	argRet.loc=argExp.loc;
	Expression[] statements;
	body_.s=mergeCompound((retDef?[retDef]:[])~reverseStatements(fd.body_.s[0..$-1],fd.fscope_)~[argRet]);
	import options;
	if(opt.dumpReverse){
		writeln(fd);
		writeln("-reverse→");
		writeln(result);
	}
	result=functionDefSemantic(result,sc);
	enforce(result.sstate==SemState.completed,text("semantic errors while reversing function"));
	if(argTypes.length==1) result.reversed=fd;
	fd.reversed=result;
	return result;
}

enum ComputationClass{
	bottom,
	classical,
	quantum,
	mixed,
	unsupported
}

ComputationClass join(ComputationClass a,ComputationClass b){
	with(ComputationClass){
		if(a==bottom) return b;
		if(b==bottom) return a;
		if(a==unsupported) return a;
		if(b==unsupported) return b;
		if(a==b) return a;
		return mixed;
	}
}

ComputationClass classifyExpression(Expression e){
	with(ComputationClass){
		if(isClassicalExp(e)) return classical;
		if(e.type.hasClassicalComponent()) return mixed;
		return quantum;
	}
}

ComputationClass classifyStatement(Expression e){
	with(ComputationClass){
		if(auto ce=cast(CallExp)e) return ComputationClass.quantum; // ok?
		if(auto ce=cast(CompoundExp)e) assert(0);
		if(auto ite=cast(IteExp)e){
			if(!ite.cond.type.isClassical()) return ComputationClass.quantum;
			//return chain(ite.then.s,ite.othw?ite.othw.s:[]).map!classifyStatement.reduce!join(classical); // ???
			auto r=bottom;
			foreach(c;chain(ite.then.s,ite.othw?ite.othw.s:[]).map!classifyStatement) r=join(r,c);
			return r;
		}
		if(auto ret=cast(ReturnExp)e){
			if(ret.e.isClassical()) return classical;
			if(!ret.e.hasClassicalComponent()) return quantum;
			return mixed;
		}
		if(auto fd=cast(FunctionDef)e){
			if(fd.ftype.isClassical()) return classical;
			return mixed;
		}
		// TODO: DatDecl?
		if(auto ce=cast(CommaExp)e) assert(0);
		if(auto de=cast(DefineExp)e){
			assert(!!de.e2.type);
			return classifyExpression(de.e2);
		}
		if(auto de=cast(DefExp)e){
			assert(!!de.initializer);
			return classifyStatement(de.initializer);
		}
		if(auto ae=cast(AssignExp)e) return unsupported;
		if(isOpAssignExp(e)){
			auto be=cast(ABinaryExp)e;
			assert(!!be);
			assert(!!be.e2.type);
			if(be.e2.type.isClassical()) return unsupported;
			if(!be.e2.type.hasClassicalComponent())
				return isInvertibleOpAssignExp(e)?quantum:unsupported;
			return mixed;
		}
		auto classifyBody(CompoundExp e){
			if(e.blscope_&&e.blscope_.forgottenVars.length) return unsupported;
			bool anyQuantum=false;
			bool anyMixed=false;
			bool anyUnsupported=false;
			foreach(c;e.s.map!classifyStatement){
				final switch(c){
					case bottom: assert(0);
					case classical: break;
					case quantum: anyQuantum=true; break;
					case mixed: anyMixed=true; break;
					case unsupported: anyUnsupported=true; break;
				}
			}
			if(anyUnsupported) return unsupported;
			if(anyMixed) return mixed;
			if(anyQuantum) return quantum;
			return classical;
		}
		if(auto fe=cast(ForExp)e) return classifyBody(fe.bdy);
		if(auto we=cast(WhileExp)e) return unsupported;
		if(auto re=cast(RepeatExp)e) return classifyBody(re.bdy);
		if(auto oe=cast(ObserveExp)e) enforce(0);
		if(auto oe=cast(CObserveExp)e) enforce(0);
		if(auto ae=cast(AssertExp)e){
			assert(!!ae.e.type);
			if(ae.e.type.isClassical()) return classical;
			if(!ae.e.type.hasClassicalComponent) return quantum;
			enforce(0);
		}
		if(auto fe=cast(ForgetExp)e) return quantum;
	}
	enforce(0,text("unsupported: ",e));
	assert(0);
}
Expression[] mergeCompound(Expression[] s){
	Expression[] r;
	foreach(e;s){
		if(auto ce=cast(CompoundExp)e){
			assert(!ce.blscope_);
			r~=mergeCompound(ce.s);
			continue;
		}
		if(auto ce=cast(CommaExp)e){
			r~=mergeCompound([ce.e1]);
			r~=mergeCompound([ce.e2]);
		}
		if(auto ite=cast(IteExp)e){
			assert(!!ite.then);
			ite.then.s=mergeCompound(ite.then.s);
			if(ite.othw) ite.othw.s=mergeCompound(ite.othw.s);
		}
		if(auto fe=cast(ForExp)e) fe.bdy.s=mergeCompound(fe.bdy.s);
		if(auto we=cast(WhileExp)e) we.bdy.s=mergeCompound(we.bdy.s);
		if(auto re=cast(RepeatExp)e) re.bdy.s=mergeCompound(re.bdy.s);
		r~=e;
	}
	return r;
}

Expression[] reverseStatements(Expression[] statements,Scope sc){
	statements=mergeCompound(statements);
	Expression[] classicalStatements=statements.filter!(s=>classifyStatement(s)==ComputationClass.classical).array;
	foreach(ref e;classicalStatements){
		if(auto de=cast(DefExp)e) e=de.initializer.copy();
		else e=e.copy();
	}
	Expression[] quantumStatements=statements.retro.filter!(s=>classifyStatement(s)!=ComputationClass.classical).array;
	foreach(ref e;quantumStatements) e=reverseStatement(e,sc);
	return classicalStatements~quantumStatements;
}

Expression reverseStatement(Expression e,Scope sc){
	if(!e) return e;
	Expression error(){
		auto res=e.copy();
		res.sstate=SemState.error;
		return res;
	}
	if(auto ce=cast(CallExp)e){
		auto te=new TupleExp([]);
		te.type=unit;
		return lowerDefine!true(ce,te,ce.loc,sc);
	}
	if(auto ce=cast(CompoundExp)e){
		auto res=new CompoundExp(reverseStatements(ce.s,sc));
		res.loc=ce.loc;
		if(ce.blscope_&&ce.blscope_.forgottenVars.length){
			sc.error("reversal of implicit forget not supported yet",ce.loc);
			res.sstate=SemState.error;
		}
		return res;
	}
	if(auto ite=cast(IteExp)e){
		auto then=cast(CompoundExp)reverseStatement(ite.then,sc);
		assert(!!then);
		auto othw=cast(CompoundExp)reverseStatement(ite.othw,sc);
		assert(!!othw==!!ite.othw);
		auto res=new IteExp(ite.cond.copy(),then,othw);
		res.loc=ite.loc;
		return res;
	}
	if(auto ret=cast(ReturnExp)e){
		sc.error("reversing early returns not supported yet",ret.loc);
		return error();
	}
	if(auto fd=cast(FunctionDef)e){
		sc.error("reversal of quantum variable capturing not supported yet",fd.loc);
		return error();
	}
	// TODO: DatDecl?
	if(auto ce=cast(CommaExp)e) assert(0);
	if(auto de=cast(DefineExp)e) return lowerDefine!true(de.e2,de.e1,de.loc,sc);
	if(auto de=cast(DefExp)e){
		assert(!!de.initializer);
		return reverseStatement(de.initializer,sc);
	}
	if(auto ae=cast(AssignExp)e){
		sc.error("reversal of functions containing assignments not supported yet",ae.loc);
		return error();
	}
	if(isOpAssignExp(e)){
		auto be=cast(ABinaryExp)e;
		assert(!!be);
		assert(!!be.e2.type);
		if(be.e2.type.isClassical()){
			sc.error("reversal of assignments not supported yet",be.loc);
			return error();
		}
		if(be.e2.type.hasClassicalComponent()){
			// TODO: array append is reversible
			sc.error("reversal of assignments not supported yet",be.loc);
			return error();
		}
		if(!isInvertibleOpAssignExp(be)){
			sc.error("reversal of implicit forgets not supported yet",be.loc);
			return error();
		}
		if(auto ae=cast(AddAssignExp)e){
			auto res=new SubAssignExp(ae.e1.copy(),ae.e2.copy());
			res.loc=ae.loc;
			return res;
		}
		if(auto ae=cast(SubAssignExp)e){
			auto res=new AddAssignExp(ae.e1.copy(),ae.e2.copy());
			res.loc=ae.loc;
			return res;
		}
		if(auto ae=cast(CatAssignExp)e){
			sc.error("reversal of concatenation not supported yet",ae.loc);
			return error();
		}
		if(auto ae=cast(BitXorAssignExp)e) return ae.copy();
		sc.error("reversal not supported yet",e.loc);
		return error();
	}
	if(auto fe=cast(ForExp)e){
		auto bdy=cast(CompoundExp)reverseStatement(fe.bdy,sc);
		assert(!!bdy);
		auto leftExclusive=fe.rightExclusive;
		auto left=fe.right.copy();
		auto rightExclusive=fe.leftExclusive;
		auto right=fe.left.copy();
		auto ostep=fe.step?fe.step.copy():null;
		if(!ostep){
			ostep=constantExp(1);
			ostep.loc=left.loc.to(right.loc);
		}
		auto step=new UMinusExp(ostep);
		step.loc=ostep.loc;
		auto res=new ForExp(fe.var.copy(),leftExclusive,left,step,rightExclusive,right,bdy);
		res.loc=fe.loc;
		return res;
	}
	if(auto we=cast(WhileExp)e){
		sc.error("reversal of while loops not supported yet",we.loc);
		return error();
	}
	if(auto re=cast(RepeatExp)e){
		auto bdy=cast(CompoundExp)reverseStatement(re.bdy,sc);
		assert(!!bdy);
		auto res=new RepeatExp(re.num.copy(),bdy);
		res.loc=re.loc;
		return res;
	}
	if(auto oe=cast(ObserveExp)e) enforce(0);
	if(auto oe=cast(CObserveExp)e) enforce(0);
	if(auto ae=cast(AssertExp)e) return ae.copy();
	if(auto fe=cast(ForgetExp)e){
		auto tpl=new TupleExp([]);
		tpl.type=unit;
		tpl.loc=fe.loc;
		return lowerDefine!true(fe,tpl,fe.loc,sc);
	}
	sc.error("reversal unsupported",e.loc);
	return error();
}

