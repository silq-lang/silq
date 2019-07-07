import std.stdio,std.conv,std.algorithm,std.range,std.exception;
import lexer,scope_,expression,type,declaration,semantic_,error,util;

string freshName(){
	static int counter=0;
	return text("__tmp",counter++);
}

Identifier getReverse(Location loc,Scope isc){
	import parser: preludePath;
	import semantic_: modules;
	if(preludePath() !in modules) return null;
	auto exprssc=modules[preludePath()];
	auto sc=exprssc[1];
	auto res=new Identifier("reverse");
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

Expression lowerDefine(Expression lhs,Expression rhs,Location loc,Scope sc){
	Expression res;
	scope(success) if(res) res.loc=loc;
	Expression error(){
		res=new DefineExp(lhs,rhs);
		res.sstate=SemState.error;
		return res;
	}
	bool validDefLhs=!!cast(Identifier)lhs;
	if(auto tpl=cast(TupleExp)lhs) validDefLhs=tpl.e.all!(e=>!!cast(Identifier)e);
	if(validDefLhs) return res=new DefineExp(lhs,rhs);
	if(auto tpll=cast(TupleExp)lhs){
		if(auto tplr=cast(TupleExp)rhs){
			enforce(tpll.e.length==tplr.e.length);
			Expression[] es;
			foreach(i;0..tpll.e.length){
				es~=lowerDefine(tpll.e[i],tplr.e[i],loc,sc); // TODO: evaluation order okay? 
			}
			if(es.any!(x=>!x)) return null;
			return res=new CompoundExp(es);
		}else{
			auto tmp=new TupleExp(iota(tpll.length).map!(delegate Expression(i){ auto id=new Identifier(freshName); id.loc=rhs.loc; return id; }).array);
			tmp.loc=loc;
			auto d1=new DefineExp(tmp,rhs);
			d1.loc=loc;
			auto d2=new DefineExp(lhs,tmp);
			d2.loc=loc;
			return res=new CompoundExp([d1,d2]);
		}
	}
	if(auto ce=cast(CallExp)lhs){
		ce.e=expressionSemantic(ce.e,sc,ConstResult.yes);
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
			if(!numArgs) return res=new ForgetExp(rhs,lhs);
			auto rev=getReverse(ce.e.loc,sc);
			if(rev.sstate!=SemState.completed) return error();
			auto reversed=new CallExp(rev,ce.e,false,false);
			reversed.loc=ce.e.loc;
			Expression newlhs,newarg;
			if(auto tpl=cast(TupleExp)ce.arg){
				newlhs=new TupleExp(tpl.e[numConstArgs1..numConstArgs1+numArgs]);
				newlhs.loc=ce.arg.loc;
				Expression[] erhs;
				if(auto tpll=cast(TupleExp)lhs) erhs=tpll.e;
				else erhs=[rhs];
				newarg=new TupleExp(tpl.e[0..numConstArgs1]~erhs~tpl.e[numConstArgs1+numArgs..$]);
				newarg.loc=lhs.loc;
			}else if(numArgs==ft.nargs){
				newlhs=ce.arg;
				newarg=rhs;
			}else{
				sc.error("cannot match single tuple to function with mixed 'const' and consumed parameters",ce.loc);
				return error();
			}
			auto newrhs=new CallExp(reversed,newarg,ce.isSquare,ce.isClassical);
			newrhs.loc=newarg.loc;
			return lowerDefine(newlhs,newrhs,loc,sc);
		}
	}
	sc.error("expression not supported as definition left-hand side",lhs.loc);
	return error();
}
// rev(x:=y;) ⇒ y:=x;
// rev(x:=H(y);) ⇒ H(y):=x; ⇒ y:=reverse(H)(x);
// rev(x:=dup(y);) ⇒ dup(y):=x; ⇒ ():=reverse(dup)(x,y) ⇒ ():=forget(x=dup(y));
// rev(x:=CNOT(a,b);) ⇒ CNOT(a,b):=x; ⇒ a:=reverse(CNOT)(x,y);

Expression lowerDefine(DefineExp e,Scope sc){
	if(e.sstate==SemState.error) return e;
	bool validDefLhs=!!cast(Identifier)e.e1;
	if(auto tpl=cast(TupleExp)e.e1) validDefLhs=tpl.e.all!(e=>!!cast(Identifier)e);
	if(validDefLhs) return null;
	return lowerDefine(e.e1,e.e2,e.loc,sc);
}
FunctionDef reverseFunction(FunctionDef fd){
	auto sc=fd.scope_;
	auto ret=fd.body_.s.length?cast(ReturnExp)fd.body_.s[$-1]:null;
	if(!ret){
		sc.error("reversing multiple returns not supported yet",fd.loc);
		return null;
	}
	Expression[] statements;
	assert(0,"TODO");
}
