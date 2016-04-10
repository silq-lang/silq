import std.array,std.algorithm;
import std.format, std.conv;
import lexer,scope_,expression,type,declaration,util;

alias CommaExp=BinaryExp!(Tok!",");
alias AssignExp=BinaryExp!(Tok!"=");
alias AddExp=BinaryExp!(Tok!"+");
alias SubExp=BinaryExp!(Tok!"-");
alias MulExp=BinaryExp!(Tok!"*");
alias DivExp=BinaryExp!(Tok!"/");
alias PowExp=BinaryExp!(Tok!"^");
alias UMinusExp=UnaryExp!(Tok!"-");
alias UNegExp=UnaryExp!(Tok!"!");
alias LtExp=BinaryExp!(Tok!"<");
alias LeExp=BinaryExp!(Tok!"<=");
alias GtExp=BinaryExp!(Tok!">");
alias GeExp=BinaryExp!(Tok!">=");
alias EqExp=BinaryExp!(Tok!"==");
alias NeqExp=BinaryExp!(Tok!"!=");
alias OrExp=BinaryExp!(Tok!"||");
alias AndExp=BinaryExp!(Tok!"&&");
alias Exp=Expression;

void propErr(Expression e1,Expression e2){
	if(e1.sstate==SemState.error) e2.sstate=SemState.error;
}

Expression makeDeclaration(Expression expr,ref bool success,Scope sc){
	if(auto dat=cast(DatDecl)expr){
		if(dat.dtype) return expr;
		auto dsc=new DataScope(sc,dat);
		assert(!dat.dscope_);
		dat.dscope_=dsc;
		dat.dtype=new AggregateTy(dat);
		foreach(ref exp;dat.body_.s) exp=makeDeclaration(exp,success,dat.dscope_);
		return dat;
	}
	if(auto decl=cast(Declaration)expr){
		if(!decl.scope_) success&=sc.insert(decl);
		return decl;
	}
	if(auto ce=cast(CommaExp)expr){
		ce.e1=makeDeclaration(ce.e1,success,sc);
		ce.e2=makeDeclaration(ce.e2,success,sc);
		return ce;
	}
	if(auto be=cast(BinaryExp!(Tok!":="))expr){
		if(auto id=cast(Identifier)be.e1){
			auto vd=new VarDecl(id);
			vd.loc=id.loc;
			success&=sc.insert(vd);
			auto de=new SingleDefExp(vd,be);
			de.loc=be.loc;
			propErr(vd,de);
			return de;
		}else if(auto tpl=cast(TupleExp)be.e1){
			VarDecl[] vds;
			foreach(exp;tpl.e){
				auto id=cast(Identifier)exp;
				vds~=new VarDecl(id);
				vds[$-1].loc=id.loc;
				success&=sc.insert(vds[$-1]);
			}
			auto de=new MultiDefExp(vds,be);
			de.loc=be.loc;
			foreach(vd;vds) propErr(vd,de);
			return de;
		}else{
			sc.error("left hand side definition must be identifier or tuple of identifiers",expr.loc);
			success=false;
		}
		success&=expr.sstate==SemState.completed;
	}
	if(auto tae=cast(TypeAnnotationExp)expr){
		if(auto id=cast(Identifier)tae.e){
			auto vd=new VarDecl(id);
			vd.dtype=tae.t;
			vd.loc=id.loc;
			success&=sc.insert(vd);
			return vd;
		}
	}
	sc.error("not a declaration: '"~expr.toString()~"' ",expr.loc);
	expr.sstate=SemState.error;
	success=false;
	return expr;
}

Expression[] semantic(Expression[] exprs,Scope sc){
	bool success=true;
	foreach(ref expr;exprs) expr=makeDeclaration(expr,success,sc);
	foreach(ref expr;exprs){
		expr=semantic(expr,sc);
		success&=expr.sstate==SemState.completed;
	}
	return exprs;
}

Expression semantic(Expression expr,Scope sc){
	if(expr.sstate==SemState.completed||expr.sstate==SemState.error) return expr;
	if(expr.sstate==SemState.started){
		sc.error("cyclic dependency",expr.loc);
		expr.sstate=SemState.error;
		return expr;
	}
	assert(expr.sstate==SemState.initial);
	expr.sstate=SemState.started;
	scope(exit){
		if(expr.sstate!=SemState.error){
			assert(!!expr.type,text(expr));
			expr.sstate=SemState.completed;
		}
	}
	if(auto cd=cast(CompoundDecl)expr){
		auto asc=new AggregateScope(sc);
		cd.ascope_=asc;
		foreach(e;cd.s) if(auto decl=cast(Declaration)e) if(!decl.scope_) asc.insert(decl);
		foreach(ref e;cd.s){
			e=semantic(e,asc);
			propErr(expr,cd);
		}
		cd.type=unit;
		return cd;
	}
	if(auto ce=cast(CompoundExp)expr){
		auto blsc=new BlockScope(sc);
		ce.blscope_=blsc;
		foreach(ref e;ce.s){
			e=semantic(e,blsc);
			propErr(e,ce);
		}
		ce.type=unit;
		return ce;
	}
	if(auto fd=cast(FunctionDef)expr){
		auto fsc=new FunctionScope(sc,fd);
		fd.fscope_=fsc;
		foreach(ref p;fd.params) p=cast(Parameter)semantic(p,fsc);
		auto bdy=cast(CompoundExp)semantic(fd.body_,fsc);
		assert(!!bdy);
		fd.body_=bdy;
		fd.type=unit;
		return fd;
	}
	if(auto dat=cast(DatDecl)expr){
		bool success=true;
		if(!dat.dscope_) makeDeclaration(dat,success,sc);
		auto bdy=cast(CompoundDecl)semantic(dat.body_,dat.dscope_);
		assert(!!bdy);
		dat.body_=bdy;
		dat.type=unit;
		return dat;
	}
	if(auto vd=cast(VarDecl)expr){
		bool success=true;
		if(!vd.scope_) makeDeclaration(vd,success,sc);
		vd.type=unit;
		return vd;
	}
	if(auto be=cast(BinaryExp!(Tok!":="))expr){
		bool success=true;
		auto de=cast(DefExp)makeDeclaration(be,success,sc);
		assert(success || de.sstate==SemState.error);
		assert(!!de);
		assert(de.init is be);
		be.e2=semantic(be.e2,sc);
		if(be.e2.sstate==SemState.completed){
			de.setType(be.e2.type);
			de.type=unit;
		}else de.sstate=SemState.error;
		return expr=de;
	}
	if(auto ae=cast(AssignExp)expr){
		ae.type=unit;
		if(cast(IndexExp)ae.e1){ // TODO
			return ae;
		}
		ae.e1=semantic(ae.e1,sc);
		ae.e2=semantic(ae.e2,sc);
		propErr(ae.e1,ae);
		propErr(ae.e2,ae);
		if(ae.sstate==SemState.error)
			return ae;
		if(auto id=cast(Identifier)ae.e1){
			if(!cast(VarDecl)id.meaning){
				sc.error("can only assign to variables",expr.loc);
				ae.sstate=SemState.error;
				return ae;
			}
			if(!compatible(id.type,ae.e2.type)){
				sc.error(format("cannot assign a '%s' to variable '%s' of type '%s'",ae.e2.type,id,id.type),ae.loc);
				sc.note("declared here",id.meaning.loc);
				ae.sstate=SemState.error;
				return ae;
			}
		}else{
			sc.error("TODO",expr.loc);
			ae.sstate=SemState.error;
		}
		return ae;
	}
	if(auto id=cast(Identifier)expr){
		auto meaning=sc.lookup(id);
		if(!meaning){
			sc.error(format("undefined identifier '%s'",id), id.loc);
			id.sstate=SemState.error;
			return id;
		}
		id.meaning=meaning;
		propErr(meaning,id);
		id.type=typeForDecl(meaning);
		if(!id.type) id.sstate=SemState.error;
		return id;
	}
	if(auto fe=cast(FieldExp)expr){
		fe.e=semantic(fe.e,sc);
		propErr(fe.e,fe);
		if(auto aggrty=cast(AggregateTy)fe.type){
			auto noMember(){
				sc.error(format("no member '%s' for type '%s",fe.f,fe.e.type),fe.loc);
				fe.sstate=SemState.error;
				return fe;
			}
			if(aggrty.decl&&aggrty.decl.dscope_){
				auto meaning=aggrty.decl.dscope_.lookupHere(fe.f);
				if(!meaning) return noMember();
				fe.f.meaning=meaning;
				fe.f.type=typeForDecl(meaning);
				fe.f.sstate=SemState.completed;
				fe.type=fe.f.type;
				return fe;
			}else return noMember();
		}
	}
	if(auto ce=cast(CommaExp)expr){
		ce.e1=semantic(ce.e1,sc);
		ce.e2=semantic(ce.e2,sc);
		ce.type=unit;
		return ce;
	}
	if(auto tpl=cast(TupleExp)expr){
		foreach(ref exp;tpl.e){
			exp=semantic(exp,sc);
			propErr(exp,tpl);
		}
		if(tpl.sstate!=SemState.error)
			tpl.type=tupleTy(tpl.e.map!(e=>e.type).array);
		return tpl;
	}
	if(auto tae=cast(TypeAnnotationExp)expr){
		tae.e=semantic(tae.e,sc);
		tae.type=typeSemantic(tae.t,sc);
		propErr(tae.e,tae);
		propErr(tae.t,tae);
		if(tae.sstate==SemState.error)
			return tae;
		if(tae.e.type !is tae.type){
			sc.error(format("type is '%s' instead of '%s'",tae.e.type,tae.type),tae.loc);
			tae.sstate=SemState.error;
		}
		return tae;
	}
	if(auto lit=cast(LiteralExp)expr){
		switch(lit.lit.type){
		case Tok!"0":
			expr.type=ℝ;
			return expr;
		default: break; // TODO
		}
	}
	sc.error("unsupported "~typeid(expr).to!string,expr.loc);
	expr.sstate=SemState.error;
	return expr;
}

Type typeSemantic(Expression t,Scope sc){
	if(auto id=cast(Identifier)t){
		if(id.name=="R"||id.name=="ℝ") return ℝ;
		if(id.name=="1"||id.name=="𝟙") return unit;
		auto decl=sc.lookup(id);
		if(!decl){
			sc.error(format("undefined identifier '%s'",id),id.loc);
			return null;
		}
		if(auto dat=cast(DatDecl)decl){
			return dat.dtype;
		}else{
			sc.error(format("%s '%s' is not a data type declaration",decl.kind,decl.name),id.loc);
			sc.note("declared here",decl.loc);
			return null;
		}
	}
	return null;
}

Type typeForDecl(Declaration decl){
	if(auto dat=cast(DatDecl)decl){
		assert(cast(AggregateTy)dat.dtype);
		return dat.dtype;
	}
	if(auto vd=cast(VarDecl)decl){
		return vd.type;
	}
	return unit; // TODO
}

bool compatible(Type lhs,Type rhs){
	return lhs is rhs;
}
