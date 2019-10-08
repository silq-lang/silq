import std.conv;

import ast.expression, ast.declaration, ast.scope_;
import dexpr;
// TODO: move this to semantic_, as a rewrite
DExpr readVariable(alias readLocal)(VarDecl var,Scope from){
	DExpr r=getContextFor!readLocal(var,from);
	if(r) return dField(r,var.getName);
	return readLocal(var.getName);
}
DExpr getContextFor(alias readLocal)(Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{
	DExpr r=null;
	auto meaningScope=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		meaningScope=fd.realScope;
	assert(sc&&sc.isNestedIn(meaningScope));
	for(auto csc=sc;csc !is meaningScope;){
		void add(string name){
			if(!r) r=readLocal(name);
			else r=dField(r,name);
			assert(!!cast(NestedScope)csc);
		}
		assert(cast(NestedScope)csc);
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto fsc=cast(FunctionScope)csc){
			auto fd=fsc.getFunction();
			if(fd.isConstructor){
				if(meaning is fd.thisVar) break;
				add(fd.thisVar.getName);
			}else add(fd.contextName);
		}else if(cast(AggregateScope)csc) add(csc.getDatDecl().contextName);
		csc=(cast(NestedScope)csc).parent;
	}
	return r;
}
DExpr buildContextFor(alias readLocal)(Declaration meaning,Scope sc)in{assert(meaning&&sc);}body{ // template, forward references 'doIt'
	if(auto ctx=getContextFor!readLocal(meaning,sc)) return ctx;
	DExpr[string] record;
	auto msc=meaning.scope_;
	if(auto fd=cast(FunctionDef)meaning)
		msc=fd.realScope;
	for(auto csc=msc;;csc=(cast(NestedScope)csc).parent){
		if(!cast(NestedScope)csc) break;
		foreach(vd;&csc.all!VarDecl)
			if(auto var=readVariable!readLocal(vd,sc))
				record[vd.getName]=var;
		if(!cast(NestedScope)(cast(NestedScope)csc).parent) break;
		if(auto dsc=cast(DataScope)csc){
			auto name=dsc.decl.contextName;
			record[name]=readLocal(name);
			break;
		}
		if(auto fsc=cast(FunctionScope)csc){
			auto cname=fsc.getFunction().contextName;
			record[cname]=readLocal(cname);
			break;
		}
	}
	return dRecord(record);
}
DExpr lookupMeaning(alias readLocal,alias readFunction)(Identifier id)in{assert(id && id.scope_,text(id," ",id.loc));}body{
	if(!id.meaning||!id.scope_||!id.meaning.scope_)
		return readLocal(id.name);
	if(auto vd=cast(VarDecl)id.meaning){
		DExpr r=getContextFor!readLocal(id.meaning,id.scope_);
		return r?dField(r,id.name):readLocal(id.name);
	}
	if(cast(FunctionDef)id.meaning) return readFunction(id);
	return null;
}
