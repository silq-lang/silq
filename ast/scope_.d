// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module ast.scope_;

import std.format, std.conv, std.algorithm, std.stdio;
import std.typecons:Q=Tuple,q=tuple;
import ast.lexer, ast.expression, ast.declaration, ast.type, ast.error;
import util;

struct Dependency{
	bool isTop;
	SetX!string dependencies;
	void joinWith(Dependency rhs){
		if(isTop) return;
		if(rhs.isTop){
			this=rhs;
			return;
		}
		foreach(x;rhs.dependencies)
			dependencies.insert(x);
	}
	void replace(string name, Dependency rhs){
		if(name !in dependencies) return;
		dependencies.remove(name);
		joinWith(rhs);
	}
	void rename(string decl,string ndecl){
		if(decl in dependencies){
			dependencies.remove(decl);
			dependencies.insert(ndecl);
		}
	}
	void remove(string decl){
		dependencies.remove(decl);
	}
	Dependency dup(){
		return Dependency(isTop, dependencies.dup);
	}
}

struct Dependencies{
	Dependency[string] dependencies;
	void joinWith(Dependencies rhs){
		foreach(k,ref v;dependencies){
			if(k in rhs.dependencies)
				v.joinWith(rhs.dependencies[k]);
		}
	}
	void pushUp(string removed)in{
		assert(removed in dependencies,removed);
	}body{
		Dependency x=dependencies[removed];
		dependencies.remove(removed);
		foreach(k,ref v;dependencies)
			v.replace(removed, x);
	}
	void rename(string decl,string ndecl)in{
		assert(decl in dependencies);
		assert(ndecl !in dependencies);
	}do{
		foreach(k,ref v;dependencies) v.rename(decl,ndecl);
		dependencies[ndecl]=dependencies[decl];
		dependencies.remove(decl);
	}
	void add(string decl)in{
		assert(decl !in dependencies);
	}do{
		dependencies[decl]=Dependency(true);
	}
	Dependencies dup(){
		Dependency[string] result;
		foreach(k,ref v;dependencies)
			result[k]=v.dup;
		return Dependencies(result);
	}
	bool canForget(string decl)in{
		assert(decl in dependencies);
	}do{
		return !dependencies[decl].isTop;
	}
	void clear(){
		dependencies.clear();
	}
}

enum Lookup{
	consuming,
	constant,
	probing,
}

abstract class Scope{
	abstract @property ErrorHandler handler();
	bool allowsLinear(){
		return true;
	}
	bool insert(Declaration decl,bool force=false)in{assert(!decl.scope_);}body{
		if(auto d=symtabLookup(decl.name,false,Lookup.probing)){
			if(decl.sstate!=SemState.error) redefinitionError(decl, d);
			decl.sstate=SemState.error;
			return false;
		}
		rename(decl);
		symtab[decl.name.ptr]=decl;
		if(decl.rename){
			assert(decl.rename.ptr !in rnsymtab);
			rnsymtab[decl.rename.ptr]=decl;
		}
		if(decl.getName in dependencies.dependencies){
			assert(toPush.canFind(decl.getName),text(decl," ",toPush));
			auto ndecl="`renamed`"~decl.getName;
			assert(ndecl !in dependencies.dependencies);
			foreach(ref x;toPush) if(x == decl.getName) x=ndecl;
			dependencies.rename(decl.getName,ndecl);
		}
		dependencies.add(decl.getName);
		decl.scope_=this;
		return true;
	}
	void redefinitionError(Declaration decl, Declaration prev) in{
		assert(decl);
	}body{
		error(format("redefinition of \"%s\"",decl.name), decl.name.loc);
		note("previous definition was here",prev.name.loc);
	}

	struct ConstBlockContext{
		private Identifier[Declaration] constBlock;
	}
	ConstBlockContext saveConst(){ return ConstBlockContext(constBlock); }
	void resetConst(ConstBlockContext previous){ constBlock=previous.constBlock; }
	void resetConst(){ constBlock.clear(); }
	Identifier isConst(Declaration decl){ return constBlock.get(decl, null); }

	/+private+/ string[] toPush;
	final void consume(Declaration decl){
		symtab.remove(decl.name.ptr);
		if(decl.rename) rnsymtab.remove(decl.rename.ptr);
		toPush~=decl.getName;
	}
	final void pushUp(ref Dependency dependency,string removed){
		dependency.replace(removed,dependencies.dependencies[removed]);
	}
	final void pushConsumed(){
		foreach(name;toPush)
			dependencies.pushUp(name);
		toPush=[];
	}

	protected final Declaration symtabLookup(Identifier ident,bool rnsym,Lookup kind){
		if(allowMerge) return null;
		auto r=symtab.get(ident.ptr, null);
		if(rnsym&&!r) r=rnsymtab.get(ident.ptr,null);
		if(kind==Lookup.consuming&&r&&r.isLinear()){
			if(auto read=isConst(r)){
				error(format("cannot consume 'const' variable '%s'",ident), ident.loc);
				note("variable was made 'const' here", read.loc);
				ident.sstate=SemState.error;
			}else consume(r);
		}
		if(kind==Lookup.constant&&r&&r.isLinear()){
			if(r !in constBlock)
				constBlock[r]=ident;
		}
		return r;
	}
	Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind){
		return lookupHere(ident,rnsym,kind);
	}
	protected final void rename(Declaration decl){
		for(;;){ // TODO: quite hacky
			auto cname=decl.rename?decl.rename:decl.name;
			auto d=lookup(cname,true,true,Lookup.probing);
			import ast.semantic_: isBuiltIn;
			if(!d&&!isBuiltIn(cname)) break;
			decl.rename=new Identifier(decl.getName~"'");
			decl.rename.loc=decl.name.loc;
		}
	}
	final Declaration lookupHere(Identifier ident,bool rnsym,Lookup kind){
		auto r = symtabLookup(ident,rnsym,kind);
		return r;
	}

	bool isNestedIn(Scope rhs){ return rhs is this; }

	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}

	final bool close(){
		bool errors=false;
		foreach(n,d;symtab.dup){
			if(d.isLinear()){
				if(!canForgetAppend(d)){
					errors=true;
					if(d.sstate!=SemState.error)
						error(format("%s '%s' is not consumed",d.kind,d.getName),d.loc);
					d.sstate=SemState.error;
				}else{
					consume(d);
					pushConsumed();
				}
			}
		}
		foreach(n,d;rnsymtab) assert(!d.isLinear()||canForget(d));
		return errors;
	}

	auto controlDependency=Dependency(false,SetX!string.init);
	void addControlDependency(Dependency dep){
		controlDependency.joinWith(dep);
	}

	void addDependency(Declaration decl, Dependency dep){
		dep.joinWith(controlDependency);
		dependencies.dependencies[decl.getName]=dep;
	}

	final bool dependencyTracked(Identifier id){
		return !!(id.name in dependencies.dependencies);
	}
	final Dependency getDependency(Identifier id)in{
		assert(id.sstate==SemState.completed);
	}do{
		return dependencies.dependencies.get(id.name,Dependency(true));
	}
	final Dependency getDependency(Declaration decl)in{
		assert(decl.sstate==SemState.completed,text(decl," ",decl.sstate));
	}do{
		return dependencies.dependencies.get(decl.getName,Dependency(true));
	}

	bool canForget(Declaration decl)in{
		assert(toPush.length==0,text(toPush));
	}do{
		if(decl.sstate==SemState.error) return true;
		assert(decl.sstate==SemState.completed);
		return dependencies.canForget(decl.getName);
	}

	Declaration[] forgottenVars;
	final bool canForgetAppend(Declaration decl){
		if(canForget(decl)){
			forgottenVars~=decl;
			return true;
		}
		return false;
	}
	Q!(Declaration,Expression)[] mergedVars;
	final void mergeVar(Declaration decl,Expression ntype){
		mergedVars~=q(decl,ntype);
	}

	bool allowMerge=false;
	SetX!NestedScope activeNestedScopes;
	void nest(NestedScope r)in{
		assert(allowsLinear());
		assert(r.parent is this);
	}do{
		r.controlDependency.joinWith(controlDependency);
		r.dependencies=dependencies.dup;
		r.symtab=symtab.dup;
		r.rnsymtab=rnsymtab.dup;
		allowMerge=true;
		activeNestedScopes.insert(r);
	}

	bool merge(bool quantumControl,NestedScope[] scopes...)in{
		assert(scopes.length);
		assert(toPush.length==0);
		assert(scopes.all!(sc=>sc.toPush.length==0));
		//debug assert(allowMerge);
	}do{
		foreach(sc;scopes)
			activeNestedScopes.remove(sc);
		allowMerge=false;
		dependencies=scopes[0].dependencies.dup;
		symtab=scopes[0].symtab.dup;
		rnsymtab=scopes[0].rnsymtab.dup;
		bool errors=false;
		foreach(sc;scopes[1..$])
			dependencies.joinWith(sc.dependencies);
		foreach(sym;symtab.dup){
			foreach(sc;scopes[1..$]){
				if(sym.name.ptr !in sc.symtab){
					symtab.remove(sym.name.ptr);
					if(sym.rename) rnsymtab.remove(sym.rename.ptr);
					if(sym.isLinear()&&!scopes[0].canForgetAppend(sym)){
						error(format("variable '%s' is not consumed", sym.getName), sym.loc);
						errors=true;
					}
				}else{
					auto osym=sc.symtab[sym.name.ptr];
					if((sym.scope_ is scopes[0]||osym.scope_ is sc)){
						import ast.semantic_: typeForDecl;
						auto ot=typeForDecl(osym),st=typeForDecl(sym);
						if(!ot) ot=st;
						if(!st) st=ot;
						if(ot&&st){
							auto nt=ot&&st?joinTypes(ot,st):null;
							if(!nt||quantumControl&&nt.hasClassicalComponent()){
								symtab.remove(sym.name.ptr);
								if(sym.rename) rnsymtab.remove(sym.rename.ptr);
								if(sym.isLinear()&&!scopes[0].canForgetAppend(sym)||
								   osym.isLinear()&&!sc.canForgetAppend(osym)){
									error(format("variable '%s' is not consumed", sym.getName), sym.loc);
									if(!nt) note(format("declared with incompatible types '%s' and '%s' in different branches",ot,st), osym.loc);
									errors=true;
								}
							}
							// TODO: automatically promote to quantum if possible
							if(st&&nt&&st!=nt){ // TODO: more efficient implementation for more than 2 scopes
								symtab.remove(sym.name.ptr);
								if(sym.rename) rnsymtab.remove(sym.rename.ptr);
								addVariable(sym,nt);
								scopes[0].mergeVar(sym,nt);
							}
							if(ot&&nt&&ot!=nt) sc.mergeVar(osym,nt);
						}
					}
				}
			}
		}
		foreach(sc;scopes[1..$]){
			foreach(sym;sc.symtab){
				if(sym.name.ptr !in symtab){
					if(sym.isLinear()&&!sc.canForgetAppend(sym)){
						error(format("variable '%s' is not consumed", sym.getName), sym.loc);
						errors=true;
					}
				}
			}
		}
		foreach(sc;scopes){
			sc.dependencies.clear();
			sc.symtab.clear();
			sc.rnsymtab.clear();
		}
		foreach(k,v;dependencies.dependencies.dup){
			if(k.ptr !in symtab && k.ptr !in rnsymtab)
				dependencies.dependencies.remove(k);
		}
		foreach(k,v;symtab) if(!this.isNestedIn(v.scope_)) v.scope_=this;
		foreach(k,v;rnsymtab) if(!this.isNestedIn(v.scope_)) v.scope_=this;
		return errors;
	}

	final bool addVariable(Declaration decl,Expression type,bool isFirstDef=false){
		auto id=new Identifier(decl.name.name);
		id.loc=decl.name.loc;
		auto var=new VarDecl(id);
		var.loc=decl.loc;
		if(decl.rename){
			var.rename=new Identifier(decl.rename.name);
			var.rename.loc=decl.rename.loc;
		}
		if(auto d=symtabLookup(var.name,false,Lookup.probing)){
			if(isFirstDef) redefinitionError(d,var);
			else redefinitionError(var,d);
			return false;
		}
		symtab[var.name.ptr]=var;
		if(var.rename) rnsymtab[var.rename.ptr]=var;
		var.vtype=type;
		if(var.getName !in dependencies.dependencies)
			dependencies.add(var.getName);
		var.scope_=this;
		import ast.semantic_:varDeclSemantic;
		varDeclSemantic(var,this);
		return var.sstate==SemState.completed;
	}

	bool addCaptureImpl(Identifier id,Scope ignore){ return true; }
	final bool addCapture(Identifier id){
		return addCaptureImpl(id,this);
	}

	Annotation restriction(){
		return Annotation.none;
	}

	abstract FunctionDef getFunction();
	abstract DatDecl getDatDecl();
	final int all(T)(int delegate(T) dg){
		foreach(k,v;symtab){
			auto t=cast(T)v;
			if(!t) continue;
			if(auto r=dg(t)) return r;
		}
		return 0;
	}
	IndexExp indexToReplace=null;
private:
	Dependencies dependencies;
	Identifier[Declaration] constBlock;
	Declaration[const(char)*] symtab;
	Declaration[const(char)*] rnsymtab;
}

class TopScope: Scope{
	private ErrorHandler handler_;
	override @property ErrorHandler handler(){ return handler_; }
	this(ErrorHandler handler){ this.handler_=handler; }
	override bool allowsLinear(){
		return false;
	}
	final void import_(Scope sc){
		imports~=sc;
		// TODO: store a location for better error messages
		// TODO: allow symbol lookup by full path
	}
	override Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind){
		if(auto d=super.lookup(ident,rnsym,lookupImports,kind)) return d;
		if(lookupImports){
			Declaration[] ds;
			foreach(sc;imports) if(auto d=sc.lookup(ident,rnsym,false,kind)) ds~=d;
			if(ds.length==1||ds.length>=1&&rnsym) return ds[0];
			if(ds.length>1){
				error(format("multiple imports of %s",ident.name),ident.loc);
				foreach(d;ds) note("declaration here",d.loc);
				// TODO: return error
			}
		}
		return null;
	}
	override FunctionDef getFunction(){ return null; }
	override DatDecl getDatDecl(){ return null; }
private:
	Scope[] imports; // TODO: local imports, import declarations
}

class NestedScope: Scope{
	Scope parent;
	override @property ErrorHandler handler(){ return parent.handler; }
	this(Scope parent){ this.parent=parent; }
	override Declaration lookup(Identifier ident,bool rnsym,bool lookupImports,Lookup kind){
		if(auto decl=lookupHere(ident,rnsym,kind)) return decl;
		return parent.lookup(ident,rnsym,lookupImports,kind);
	}

	override Annotation restriction(){ return parent.restriction(); }
	override Identifier isConst(Declaration decl){
		if(auto r=super.isConst(decl)) return r;
		return parent.isConst(decl);
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }

	private bool insertCapture(Identifier id,Scope ignore){
		if(this is ignore) return true;
		if(!id.meaning) return false;
		import ast.semantic_: typeForDecl;
		if(!id.meaning.isLinear()) return true;
		auto type=typeForDecl(id.meaning);
		if(!type) return false;
		return addVariable(id.meaning,type,true);
	}
	override bool addCaptureImpl(Identifier id,Scope ignore){
		foreach(sc;activeNestedScopes)
			if(!sc.insertCapture(id,ignore))
				return false;
		return parent.addCaptureImpl(id,ignore);
	}

	override FunctionDef getFunction(){ return parent.getFunction(); }
	override DatDecl getDatDecl(){ return parent.getDatDecl(); }
}

class RawProductScope: NestedScope{
	Annotation annotation;
	this(Scope parent,Annotation annotation){
		super(parent);
		this.annotation=annotation;
	}
	override Annotation restriction(){
		return annotation;
	}
	void forceClose(){}
}

class FunctionScope: NestedScope{
	FunctionDef fd;
	this(Scope parent,FunctionDef fd){
		super(parent);
		this.fd=fd;
	}
	override bool addCaptureImpl(Identifier id,Scope ignore){
		foreach(sc;activeNestedScopes)
			sc.insertCapture(id,ignore);
		insertCapture(id,ignore);
		fd.addCapture(id);
		return true;
	}
	override Annotation restriction(){
		return fd.annotation;
	}
	void forceClose(){}
	// ~this(){ import std.stdio; writeln(fd.loc.rep); }
	override FunctionDef getFunction(){ return fd; }
}
class DataScope: NestedScope{
	DatDecl decl;
	override bool allowsLinear(){
		return false; // TODO!
	}
	this(Scope parent,DatDecl decl){
		super(parent);
		this.decl=decl;
	}

	override DatDecl getDatDecl(){ return decl; }
}
class BlockScope: NestedScope{
	this(Scope parent,Annotation restriction_=Annotation.none){
		super(parent);
		if(parent.allowsLinear()) parent.nest(this);
		this.restriction_=restriction_;
	}
	Annotation restriction_;
	override Annotation restriction(){
		return max(restriction_,super.restriction());
	}
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
	override bool allowsLinear(){
		return false; // TODO!
	}
}
