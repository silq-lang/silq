import std.stdio, std.path, std.array;
import file=std.file;
import util;
import lexer, parser, error;

import distrib, dexpr;

string getActualPath(string path){
	// TODO: search path
	auto ext = path.extension;
	if(ext=="") path = path.setExtension("prb");
	return "test/"~path;
}

string readCode(File f){
	// TODO: use memory-mapped file with 4 padding zero bytes
	auto app=mallocAppender!(char[])();
	foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
	app.put("\0\0\0\0"); // insert 4 padding zero bytes
	return cast(string)app.data;	
}
string readCode(string path){ return readCode(File(path)); }

int run(string path){
	path = getActualPath(path);
	auto ext = path.extension;
	if(ext != ".prb" && ext != ".di"){
		stderr.writeln(path~": unrecognized extension: "~ext);
		return 1;
	}
	string code;
	try code=readCode(path);
	catch(Exception){
		if(!file.exists(path)) stderr.writeln(path ~ ": no such file");
		else stderr.writeln(path ~ ": error reading file");
		return 1;
	}
	auto src=new Source(path, code);
	auto expr=parseExpression(src,new FormattingErrorHandler());
	writeln(expr);
	return 0;
}


int main(string[] args){
	version(TEST) test();
	if(args.length<2){
		stderr.writeln("error: no input files");
		return 1;
	}
	args.popFront();
	foreach(x;args) if(auto r=run(x)) return r;
	return 0;
}

version=TEST;
void test(){
	auto v="x".dVar;
	writeln(dInteg(v,dE.dPow(2.dInt.dMult(3.dInt.dPlus(3.dInt).dPlus(3.dInt))).dPow(v.dPlus(v))));
}
