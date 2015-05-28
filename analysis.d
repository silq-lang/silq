import std.stdio;

import lexer, expression, error;
import distrib, dexpr;

alias DefExp=BinaryExp!(Tok!":=");
alias AddExp=BinaryExp!(Tok!"+");
alias SubExp=BinaryExp!(Tok!"-");
alias MulExp=BinaryExp!(Tok!"*");
alias DivExp=BinaryExp!(Tok!"/");
alias Exp=Expression;

DExpr transformExp(Exp e,Distribution dist,ErrorHandler err){
	class Unwind: Exception{ this(){ super(""); } }
	void unwind(){ throw new Unwind(); }
	DExpr doIt(Exp e){
		if(auto id=cast(Identifier)e){
			auto v=dist.lookupVar(id.name);
			if(!v){
				err.error("undefined variable '"~id.name~"'",id.loc);
				unwind();
			}
			return v;
		}
		if(auto ae=cast(AddExp)e) return doIt(ae.e1)+doIt(ae.e2);
		if(auto me=cast(SubExp)e) return doIt(me.e1)-doIt(me.e2);
		if(auto me=cast(MulExp)e) return doIt(me.e1)-doIt(me.e2);
		if(auto de=cast(DivExp)e) return doIt(de.e1)/doIt(de.e2);
		if(auto ce=cast(CallExp)e){
			if(auto id=cast(Identifier)ce.e){
				switch(id.name){
				case "Gauss":
					if(ce.args.length!=2){
						err.error("expected two arguments (μ,σ²) to Gauss",ce.loc);
						unwind();
					}
					auto var=dist.getVar("__g");
					// TODO: handle the case when the args are not constant
					dist.distribute(var,gaussianPDF(var,doIt(ce.args[0]),doIt(ce.args[1])));
					return var;
				case "Bernoulli":
					if(ce.args.length!=1){
						err.error("expected one argument (p) to Bernoulli",ce.loc);
						unwind();
					}
					auto var=dist.getVar("__b");
					dist.distribute(var,bernoulliPDF(var,doIt(ce.args[0])));
					return var;
				default: break;
				}
			}
		}
		if(auto le=cast(LiteralExp)e){
			if(le.lit.type==Tok!"0")
				return le.lit.int64.dℕ;
		}
		err.error("unsupported",e.loc);
		throw new Unwind();
	}
	try return doIt(e);
	catch(Unwind){ return null; }
}

void analyze(FunctionDef def,ErrorHandler err){
	auto dist=new Distribution();
	foreach(e;def.body_.s){
		// TODO: visitor?
		if(auto de=cast(DefExp)e){
			if(auto id=cast(Identifier)de.e1){
				if(auto var=dist.declareVar(id.name)){
					auto rhs=transformExp(de.e2,dist,err);
					if(rhs) dist.assign(var,rhs);
			   }else err.error("variable already exists",id.loc);
			}else err.error("left hand side of definition should be identifier",de.e1.loc);
		}else err.error("unsupported",e.loc);
	}
	writeln(dist);
}
