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
			return fd.numArgs.to!string;
		case "ret-arity":
			return fd.numReturns.to!string;
		default: throw new Exception(text("summarize: unknown key '",property,"'"));
	}
}
