import std.format;
import lexer, expression, declaration, error;

abstract class Scope{
	abstract @property ErrorHandler handler();
	bool insert(Declaration decl)in{assert(!decl.scope_);}body{
		auto d=symtabLookup(decl.name);
		if(d){
			redefinitionError(decl, d);
			decl.sstate=SemState.error;
			return false;
		}
		symtab[decl.name.ptr]=decl;
		decl.scope_=this;
		return true;
	}
	void redefinitionError(Declaration decl, Declaration prev) in{
		assert(decl);
		assert(decl.name.ptr is prev.name.ptr);
	}body{
		error(format("redefinition of '%s'",decl.name), decl.name.loc);
		note("previous definition was here",prev.name.loc);
	}

	protected final Declaration symtabLookup(Identifier ident){
		return symtab.get(ident.ptr, null);
	}
	Declaration lookup(Identifier ident){
		return lookupHere(ident);
	}
	final Declaration lookupHere(Identifier ident){
		auto r = symtabLookup(ident);
		if(!r){
			
		}
		return r;
	}
	
	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}

	abstract FunctionDef getFunction();

private:
	Declaration[const(char)*] symtab;
}

class TopScope: Scope{
	private ErrorHandler handler_;
	override @property ErrorHandler handler(){ return handler_; }
	this(ErrorHandler handler){
		this.handler_=handler;
	}
	override FunctionDef getFunction(){ return null; }
}

class NestedScope: Scope{
	Scope parent;
	override @property ErrorHandler handler(){ return parent.handler; }
	this(Scope parent){ this.parent=parent; }
	override Declaration lookup(Identifier ident){
		if(auto decl=lookupHere(ident)) return decl;
		return parent.lookup(ident);
	}

	override FunctionDef getFunction(){ return parent.getFunction(); }
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
}
class BlockScope: NestedScope{
	this(Scope parent){ super(parent); }
}
class AggregateScope: NestedScope{
	this(Scope parent){ super(parent); }
}
