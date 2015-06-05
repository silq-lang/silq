import std.stdio;

import lexer, expression, error;
import distrib, dexpr, util;

alias DefExp=BinaryExp!(Tok!":=");
alias AddExp=BinaryExp!(Tok!"+");
alias SubExp=BinaryExp!(Tok!"-");
alias MulExp=BinaryExp!(Tok!"*");
alias DivExp=BinaryExp!(Tok!"/");
alias LtExp=BinaryExp!(Tok!"<");
alias LeExp=BinaryExp!(Tok!"<=");
alias GtExp=BinaryExp!(Tok!">");
alias GeExp=BinaryExp!(Tok!">=");
alias EqExp=BinaryExp!(Tok!"==");
alias NeqExp=BinaryExp!(Tok!"!=");
alias Exp=Expression;

private struct Analyzer{
	Distribution dist;
	ErrorHandler err;
	SetX!DVar tmp;
	void marginalizeTemporaries(){
		foreach(v;tmp) dist.marginalize(v);
		tmp.clear();
	}
	DExpr transformExp(Exp e){
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
						tmp.insert(var);
						// TODO: handle the case when the args are not constant
						dist.distribute(var,gaussianPDF(var,doIt(ce.args[0]),doIt(ce.args[1])));
						return var;
					case "Bernoulli":
						if(ce.args.length!=1){
							err.error("expected one argument (p) to Bernoulli",ce.loc);
							unwind();
						}
						auto var=dist.getVar("__b");
						tmp.insert(var);
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

	DExpr transformConstr(Exp e){
		class Unwind: Exception{ this(){ super(""); } }
		void unwind(){ throw new Unwind(); }
		DExpr doIt(Exp e){
			enum common=q{
				auto e1=transformExp(b.e1),e2=transformExp(b.e2);
				if(!e1||!e2) unwind();
			};
			with(DIvr.Type)if(auto b=cast(LtExp)e){
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
			err.error("unsupported",e.loc);
			throw new Unwind();
		}
		try return doIt(e);
		catch(Unwind){ return null; }
	}
	void analyze(CompoundExp ce){
		foreach(e;ce.s){
			// TODO: visitor?
			if(auto de=cast(DefExp)e){
				if(auto id=cast(Identifier)de.e1){
					if(auto var=dist.declareVar(id.name)){
						SetX!DVar tmp;
						auto rhs=transformExp(de.e2);
						if(rhs) dist.assign(var,rhs);
						marginalizeTemporaries();
					}else err.error("variable already exists",id.loc);
				}else err.error("left hand side of definition should be identifier",de.e1.loc);
			}else if(auto ite=cast(IteExp)e){
				SetX!DVar tmp;
				if(auto c=transformConstr(ite.cond)){
					// TODO
				}
			}else err.error("unsupported",e.loc);
		}
		writeln(dist);
	}
}

void analyze(FunctionDef def,ErrorHandler err){
	Analyzer(new Distribution,err).analyze(def.body_);
}
