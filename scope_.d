// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.format, std.conv, std.algorithm, std.stdio;
import lexer, expression, declaration, type, error;
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
	bool insert(Declaration decl)in{assert(!decl.scope_); debug assert(!allowsLinear||!closed,text(decl)); }body{
		if(auto d=symtabLookup(decl.name,false,Lookup.probing)){
			redefinitionError(decl, d);
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

	void resetConst(){ constBlock.clear(); }
	Identifier isConst(Identifier ident){ return constBlock.get(ident.ptr, null); }

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
			if(auto read=isConst(ident)){
				error(format("cannot consume 'const' variable '%s'",ident), ident.loc);
				note("variable was made 'const' here", read.loc);
				ident.sstate=SemState.error;
			}else consume(r);
		}
		if(kind==Lookup.constant&&r&&r.isLinear()){
			if(ident.ptr !in constBlock)
				constBlock[ident.ptr]=ident;
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
			import semantic_: isBuiltIn;
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

	debug{
		private bool closed=false;
		~this(){ debug if((!closed||allowMerge)&&allowsLinear()){ import std.stdio; writeln(typeid(this)," ",__FILE__," ",__LINE__); assert(0); } }
	}

	bool close()in{
		debug assert(!allowMerge);
	}do{
		debug closed=true;
		bool errors=false;
		foreach(n,d;symtab){
			if(!d.isLinear()||canForget(d)) continue;
			if(d.rename) rnsymtab.remove(d.rename.ptr);
			errors=true;
			error(format("%s '%s' is not consumed",d.kind,d.name),d.loc);
		}
		foreach(n,d;rnsymtab) assert(!d.isLinear()||canForget(d));
		return errors;
	}

	private auto controlDependency=Dependency(false,SetX!string.init);
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

	bool allowMerge=false;
	void nest(NestedScope r)in{
		assert(allowsLinear());
		assert(r.parent is this);
	}do{
		r.controlDependency.joinWith(controlDependency);
		r.dependencies=dependencies.dup;
		r.symtab=symtab.dup;
		r.rnsymtab=rnsymtab.dup;
		allowMerge=true;
	}

	bool merge(bool quantumControl,Scope[] scopes...)in{
		assert(scopes.length);
		assert(toPush.length==0);
		assert(scopes.all!(sc=>sc.toPush.length==0));
		debug assert(allowMerge);
	}do{
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
					if(sym.isLinear()&&!canForget(sym)){
						error(format("variable '%s' is not consumed", sym.name), sym.loc);
						errors=true;
					}
				}else{
					auto osym=sc.symtab[sym.name.ptr];
					import semantic_: typeForDecl;
					auto ot=typeForDecl(osym),st=typeForDecl(sym);
					if((sym.scope_ is scopes[0]||osym.scope_ is sc)&&ot&&st&&(ot!=st||quantumControl&&st.hasClassicalComponent())){
						symtab.remove(sym.name.ptr);
						if(sym.rename) rnsymtab.remove(sym.rename.ptr);
						if(sym.isLinear()&&!canForget(sym)){
							error(format("variable '%s' is not consumed", sym.name), sym.loc);
							errors=true;
						}
					}
				}
			}
		}
		foreach(sc;scopes[1..$]){
			foreach(sym;sc.symtab){
				if(sym.name.ptr !in symtab){
					if(sym.isLinear()&&!sc.canForget(sym)){
						error(format("variable '%s' is not consumed", sym.name), sym.loc);
						errors=true;
					}
				}
			}
		}
		foreach(sc;scopes){
			sc.dependencies.clear();
			sc.symtab.clear();
			sc.rnsymtab.clear();
			debug sc.closed=true;
		}
		foreach(k,v;dependencies.dependencies.dup){
			if(k.ptr !in symtab && k.ptr !in rnsymtab)
				dependencies.dependencies.remove(k);
		}
		foreach(k,v;symtab) if(!this.isNestedIn(v.scope_)) v.scope_=this;
		foreach(k,v;rnsymtab) if(!this.isNestedIn(v.scope_)) v.scope_=this;
		return errors;
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
	Identifier[const(char)*] constBlock;
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
	override Identifier isConst(Identifier ident){
		if(auto r=super.isConst(ident)) return r;
		return parent.isConst(ident);
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }

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
	void forceClose(){
		debug closed=true;
	}
}

class FunctionScope: NestedScope{
	FunctionDef fd;
	this(Scope parent,FunctionDef fd){
		super(parent);
		this.fd=fd;
	}
	override Annotation restriction(){
		return fd.annotation;
	}
	void forceClose(){
		debug closed=true;
	}
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
	override bool close(){
		auto errors=parent.allowsLinear()?parent.merge(false,this):false;
		debug closed=true;
		return errors;
	}
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
	override bool allowsLinear(){
		return false; // TODO!
	}
}
