import std.string, std.range, std.algorithm;

import expression, declaration, type, semantic_, scope_, error;
import dexpr, util;
// TODO: move this to semantic_, as a rewrite

DExpr getContextFor(Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{
	DExpr r=null;
	auto meaningScope=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		meaningScope=fd.realScope;
	assert(sc&&sc.isNestedIn(meaningScope));
	for(auto csc=sc;csc !is meaningScope;){
		void add(string name){
			if(!r) r=dField(db1,name);
			else r=dField(r,name);
			assert(!!cast(NestedScope)csc);
		}
		assert(cast(NestedScope)csc);
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto fsc=cast(FunctionScope)csc) add(fsc.getFunction().contextName);
		else if(cast(AggregateScope)csc) add(csc.getDatDecl().contextName);
		csc=(cast(NestedScope)csc).parent;
		if(csc is meaningScope) break;
		if(auto fsc=cast(FunctionScope)csc){
			auto fd=fsc.getFunction();
			assert(!!fd);
			if(fd.isConstructor){
				csc=fd.scope_;
				assert(!!cast(AggregateScope)csc);
				if(csc is meaningScope) break;
			}
		}
	}
	return r;
}
DExpr buildContextFor(Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{
	if(auto ctx=getContextFor(meaning,sc)) return ctx;
	DExpr[string] record;
	auto msc=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		msc=fd.realScope;
	for(auto csc=msc;;csc=(cast(NestedScope)csc).parent){
		if(!cast(NestedScope)csc) break;
		foreach(vd;&csc.all!VarDecl)
			if(auto var=readVariable(vd,sc))
				record[vd.getName]=var;
		if(auto fsc=cast(FunctionScope)csc)
			foreach(p;fsc.getFunction().params)
				record[p.getName]=dField(db1,p.getName);
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto dsc=cast(DataScope)csc){
			auto name=dsc.decl.contextName;
			record[name]=dField(db1,name);
			break;
		}
		if(auto fsc=cast(FunctionScope)csc){
			auto cname=fsc.getFunction().contextName;
			record[cname]=dField(db1,cname);
			break;
		}
	}
	return dRecord(record);
}
import dp;
DExpr lookupMeaning(Identifier id)in{assert(!!id);}body{
	if(!id.meaning) return dField(db1,id.name);
	assert(!!id.scope_);
	if(auto vd=cast(VarDecl)id.meaning){
		DExpr r=getContextFor(id.meaning,id.scope_);
		return r?dField(r,id.name):dField(db1,id.name);
	}
	if(auto fd=cast(FunctionDef)id.meaning){
		if(!fd.isNested) return dDPFun(fd);
		return dDPContextFun(fd,buildContextFor(fd,id.scope_));
	}
	assert(0,"unsupported");
}
DExpr readVariable(VarDecl var,Scope from){
	DExpr r=getContextFor(var,from);
	if(r) return dField(r,var.getName);
	auto v=dField(db1,var.getName);
	//if(v in cur.freeVars) return v; // TODO!
	return v;
	//return null;
}
