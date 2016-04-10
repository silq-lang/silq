import std.format;
import lexer, expression, declaration, error;

class Scope{
	this(ErrorHandler handler){
		this.handler=handler;
	}
	bool insert(Declaration decl)in{assert(!decl.scope_);}body{
		auto d=symtabLookup(this, decl.name);
		if(!d){
			redefinitionError(decl, d);
			return false;
		}
		symtab[decl.name.ptr]=decl;
		decl.scope_=this;
		return true;
	}
	void redefinitionError(Declaration decl, Declaration prev) in{
		assert(decl.name.ptr is prev.name.ptr);
	}body{
		error(format("redefinition of '%s'",decl.name), decl.name.loc);
		note("previous definition was here",prev.name.loc);
	}

	protected final Declaration symtabLookup(Scope view, Identifier ident){
		return symtab.get(ident.ptr, null);
	}

	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}
private:
	ErrorHandler handler;
	Declaration[const(char)*] symtab;
}
