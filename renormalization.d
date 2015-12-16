import dexpr, hashtable, util;

// turns e into an equivalent sum of products where each [e=0] expression
// occurs as a factor in some summand
DExpr expandEqIvrs(DExpr e){
	if(auto p=cast(DPlus)e){
		DExprSet summands;
		bool change=false;
		foreach(s;p.summands){
			auto t=expandEqIvrs(s);
			DPlus.insert(summands,t);
			change|=s !is t;
		}
		if(!change) return e;
		return dPlus(summands).simplify(one);
	}
	if(auto m=cast(DMult)e){
		DExprSet factors;
		bool change=false;
		foreach(f;m.factors){
			auto g=expandEqIvrs(f);
			DMult.insert(factors,g);
			change|=f !is g;
		}
		if(change) e=dMult(factors).simplify(one);
		foreach(f;e.factors){
			bool check(){
				foreach(ivr;f.allOf!DIvr)
					if(ivr.type==DIvr.Type.eqZ)
						return true;
				return false;
			}
			if(cast(DPlus)f && check())
				return expandEqIvrs(dDistributeMult(f,e.withoutFactor(f)));
		}
		return e;
	}
	// TODO: fix the case when dIvr buried in other kind of expression
	return e;
}
/+
DExpr ivrsToDeltas(DExpr dist){
	dist=expandEqIvrs(dist).simplify(one);
	static DExpr doIt(DExpr e){
		if(auto p=cast(DPlus)e){
			DExprSet summands;
			foreach(s;p.summands){
				auto t=ivrsToDeltas(s);
				if(!t) return null;
				DPlus.insert(summands,t);
			}
			return dPlus(summands);
		}
		if(auto m=cast(DMult)e){
			foreach(f;m.factors){
				auto ivr=cast(DIvr)f;
				if(!ivr) continue;
				if(ivr.type!=DIvr.Type.eqZ) continue;
				auto delta=cast(DDelta)dDelta(ivr.e);
				if(!delta) continue;
				foreach(v;ivr.e.freeVars.setx){
					// TODO: figure out how to deal with tautologies and/or contradictions correctly
					// TODO: actually do this substitution right
					if(auto e=DDelta.performSubstitution!false(v,delta,e.withoutFactor(f)*delta,true)){
						auto grad=zero;
						foreach(v;ivr.e.freeVars.setx) grad=grad+dDiff(v,ivr.e)^^2;
						return delta*grad^^(one/2)*e;
					}
				}
			}
			return null;
		}
		return null;
	}
	return doIt(dist);
}


DExpr[2] renormalize(DExpr dist){
	return renormalize(dist,dist.freeVars.setx);
}


DExpr[2] renormalize(DExpr dist,SetX!DVar freeVars){
	dist=dist.simplify(one);
	auto factor=dist;
	foreach(v;freeVars)
		factor=dIntSmp(v,factor);
	auto rdist=dIvr(DIvr.Type.neqZ,factor)*(dist/factor).simplify(one);
	auto err=dIvr(DIvr.Type.eqZ,factor);
	auto isZ=dIvr(DIvr.Type.eqZ,factor).simplify(one);
	/+if(isZ is zero) return [rdist,zero]; // TODO: re-enable after making it correct
	if(isZ is one){
		if(auto ndist=ivrsToDeltas(dist)){
			return renormalize(ndist,freeVars);
		}
	}+/
	// TODO: this should work even in the case where we are unable to prove that an integral is
	// not equal to zero. We also should actually do a good job proving that it is not equal to zero
	//auto renorm=new RenormExp(dist);
	//return [dIvr(DIvr.Type.neqZ,factor)*dist/factor+isZ*renorm,isZ*dIvr(DIvr.Type.eqZ,renorm)];
	return [rdist,isZ];
}
+/
/+class RenormExp: DExpr{
	DExpr expr;
	this(DExpr expr){ this.expr=expr; }
	override string toStringImpl(Precedence prec){
		import std.conv;
		return text("renormalize(",expr,")");
	}

	override int forEachSubExpr(scope int delegate(DExpr) dg){ return 0; } // TODO!
	override int freeVarsImpl(scope int delegate(DVar) dg){ return 0; }
	override DExpr substitute(DVar var,DExpr e){
		return new RenormExp(expr.substitute(var,e)); // TODO
	}
	override DExpr substituteFun(DFunVar fun,DExpr q,DVar[] args){ assert(0); }
	override DExpr incDeBruin(int di){ return new RenormExp(expr.incDeBruin(di)); } // TODO
	override DExpr simplifyImpl(DExpr facts){ return this; } // TODO
}+/
