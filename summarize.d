import std.algorithm, std.array, std.conv;
import declaration, type, error;

string[] getSummary(FunctionDef fd,string[] entries){
	return entries.map!(e=>getValue(fd,e)).array;
}

string getValue(FunctionDef fd,string property){
	switch(property){
		case "name":
			return fd.name.toString();
		case "arg-arity":
			auto fty=cast(FunTy)fd.ftype;
			if(!fty) return "-1";
			return fty.names.length.to!string;
		case "ret-arity":
			auto fty=cast(FunTy)fd.ftype;
			if(!fty) return "-1";
			if(auto tpl=cast(TupleTy)fty.cod) return tpl.types.length.to!string;
			return "1";
		default: throw new Exception(text("summarize: unknown key '",property,"'"));
	}
}
