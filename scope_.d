// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.format;
import lexer, expression, declaration, error;

abstract class Scope{
	abstract @property ErrorHandler handler();
	bool insert(Declaration decl)in{assert(!decl.scope_);}body{
		if(auto d=symtabLookup(decl.name,false)){
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

	protected final Declaration symtabLookup(Identifier ident,bool rnsym){
		auto r=symtab.get(ident.ptr, null);
		if(rnsym&&!r) r=rnsymtab.get(ident.ptr,null);
		return r;
	}
	Declaration lookup(Identifier ident,bool rnsym,bool lookupImports){
		return lookupHere(ident,rnsym);
	}
	protected final void rename(Declaration decl){
		for(;;){ // TODO: quite hacky
			auto cname=decl.rename?decl.rename:decl.name;
			auto d=lookup(cname,true,true);
			import semantic_: isBuiltIn;
			if(!d&&!isBuiltIn(cname)) break;
			decl.rename=new Identifier(decl.getName~"'");
			decl.rename.loc=decl.name.loc;
		}
	}
	final Declaration lookupHere(Identifier ident,bool rnsym){
		auto r = symtabLookup(ident,rnsym);
		return r;
	}
	
	bool isNestedIn(Scope rhs){ return rhs is this; }

	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}

	abstract FunctionDef getFunction();
	abstract DatDecl getDatDecl();
	abstract ForExp getForExp();
	final int all(T)(int delegate(T) dg){
		foreach(k,v;symtab){
			auto t=cast(T)v;
			if(!t) continue;
			if(auto r=dg(t)) return r;
		}
		return 0;
	}
private:
	Declaration[const(char)*] symtab;
	Declaration[const(char)*] rnsymtab;
}

class TopScope: Scope{
	private ErrorHandler handler_;
	override @property ErrorHandler handler(){ return handler_; }
	this(ErrorHandler handler){
		this.handler_=handler;
	}
	final void import_(Scope sc){
		imports~=sc;
		// TODO: store a location for better error messages
		// TODO: allow symbol lookup by full path
	}
	override Declaration lookup(Identifier ident,bool rnsym,bool lookupImports){
		if(auto d=super.lookup(ident,rnsym,lookupImports)) return d;
		if(lookupImports){
			Declaration[] ds;
			foreach(sc;imports) if(auto d=sc.lookup(ident,rnsym,false)) ds~=d;
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
	override ForExp getForExp(){ return null; }
private:
	Scope[] imports; // TODO: local imports, import declarations
}

class NestedScope: Scope{
	Scope parent;
	override @property ErrorHandler handler(){ return parent.handler; }
	this(Scope parent){ this.parent=parent; }
	override Declaration lookup(Identifier ident,bool rnsym,bool lookupImports){
		if(auto decl=lookupHere(ident,rnsym)) return decl;
		return parent.lookup(ident,rnsym,lookupImports);
	}

	override bool isNestedIn(Scope rhs){ return rhs is this || parent.isNestedIn(rhs); }
	
	override FunctionDef getFunction(){ return parent.getFunction(); }
	override DatDecl getDatDecl(){ return parent.getDatDecl(); }
	override ForExp getForExp(){ return parent.getForExp(); }
}

class FunctionScope: NestedScope{
	FunctionDef fd;
	this(Scope parent,FunctionDef fd){
		super(parent);
		this.fd=fd;
	}

	override FunctionDef getFunction(){ return fd; }
}
class DataScope: NestedScope{
	DatDecl decl;
	this(Scope parent,DatDecl decl){
		super(parent);
		this.decl=decl;
	}

	override DatDecl getDatDecl(){ return decl; }
}
class BlockScope: NestedScope{
	this(Scope parent){ super(parent); }
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
}
class ForExpScope: NestedScope{
	ForExp fe;
	this(Scope parent,ForExp fe){
		super(parent);
		this.fe=fe;
	}
	override ForExp getForExp(){ return fe; }
}
