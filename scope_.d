// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.format, std.conv, std.algorithm, std.stdio;
import lexer, expression, declaration, type, error;

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

	protected final Declaration symtabLookup(Identifier ident,bool rnsym,Lookup kind){
		if(allowMerge) return null;
		auto r=symtab.get(ident.ptr, null);
		if(rnsym&&!r) r=rnsymtab.get(ident.ptr,null);
		if(kind==Lookup.consuming&&r&&r.isLinear()){
			if(ident.ptr in constBlock){
				error(format("cannot consume 'const' variable '%s'",ident), ident.loc);
				note("variable was made 'const' here", constBlock[ident.ptr].loc);
				ident.sstate=SemState.error;
			}else{
				symtab.remove(r.name.ptr);
				if(r.rename) rnsymtab.remove(r.rename.ptr);
			}
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
		~this(){ if((!closed||allowMerge)&&allowsLinear()){ import std.stdio; writeln(typeid(this)," ",__FILE__," ",__LINE__); assert(0); } }
	}

	bool close()in{
		assert(!allowMerge);
	}do{
		debug closed=true;
		bool errors=false;
		foreach(n,d;symtab){
			if(!d.isLinear()) continue;
			if(d.rename) rnsymtab.remove(d.rename.ptr);
			errors=true;
			error(format("%s '%s' is not consumed",d.kind,d.name),d.loc);
		}
		foreach(n,d;rnsymtab) assert(!d.isLinear());
		return errors;
	}

	debug private bool allowMerge=false;
	void nest(NestedScope r)in{
		assert(allowsLinear());
		assert(r.parent is this);
	}do{
		r.constBlock=constBlock.dup;
		r.symtab=symtab.dup;
		r.rnsymtab=rnsymtab.dup;
		allowMerge=true;
	}

	bool merge(Scope[] scopes...)in{
		assert(scopes.length);
		debug assert(allowMerge);
	}do{
		debug allowMerge=false;
		symtab=scopes[0].symtab.dup;
		rnsymtab=scopes[0].rnsymtab.dup;
		bool errors=false;
		foreach(sym;symtab.dup){
			foreach(sc;scopes[1..$]){
				if(sym.name.ptr !in sc.symtab){
					symtab.remove(sym.name.ptr);
					if(sym.rename) rnsymtab.remove(sym.rename.ptr);
					if(sym.isLinear()){
						error(format("variable '%s' is not consumed", sym.name), sym.loc);
						errors=true;
					}
				}else{
					auto osym=sc.symtab[sym.name.ptr];
					import semantic_: typeForDecl;
					auto ot=typeForDecl(osym),st=typeForDecl(sym);
					if(ot!=st||st.hasClassicalComponent()){
						symtab.remove(sym.name.ptr);
						if(sym.rename) rnsymtab.remove(sym.rename.ptr);
						if(sym.isLinear()){
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
					if(sym.isLinear()){
						error(format("variable '%s' is not consumed", sym.name), sym.loc);
						errors=true;
					}
				}
			}
		}
		foreach(sc;scopes){
			sc.symtab.clear();
			sc.rnsymtab.clear();
			sc.closed=true;
		}
		return errors;
	}

	FunctionAnnotation restriction(){
		return FunctionAnnotation.none;
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
private:
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

	override FunctionAnnotation restriction(){
		return parent.restriction();
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }

	override FunctionDef getFunction(){ return parent.getFunction(); }
	override DatDecl getDatDecl(){ return parent.getDatDecl(); }
}

class RawProductScope: NestedScope{
	this(Scope parent){ super(parent); }
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
	override FunctionAnnotation restriction(){
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
	this(Scope parent,FunctionAnnotation restriction_=FunctionAnnotation.none){
		super(parent);
		if(parent.allowsLinear()) parent.nest(this);
		this.restriction_=restriction_;
	}
	FunctionAnnotation restriction_;
	override FunctionAnnotation restriction(){
		return max(restriction_,super.restriction());
	}
	override bool close(){
		auto errors=parent.allowsLinear()?parent.merge(this):false;
		closed=true;
		return errors;
	}
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
	override bool allowsLinear(){
		return false; // TODO!
	}
}
