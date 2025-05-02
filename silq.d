// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import util.path;
import util.optparse;
import std.array, std.string, std.algorithm, std.conv;
import util, util.io;
import ast.lexer, ast.parser, ast.expression, ast.declaration, ast.error, help;
import astopt;
import options, ast.scope_, ast.modules, ast.summarize;

static this(){
	opt.importPath ~= buildPath(dirName(file.thisExePath),"library");
	static if(language==psi) opt.importPath ~= buildPath(dirName(file.thisExePath),"..","..","..","..","ras","psi","library"); // TODO: remove
}

int run(string path){
	path = getActualPath(path);
	auto ext = path.extension;
	if(ext != (language==astopt.silq?".slq":".psi")){ // TODO: support only language==silq
		stderr.writeln(path~": unrecognized extension: "~ext);
		return 1;
	}
	auto err=makeErrorHandler(opt.errorFormat);
	scope(exit) err.finalize();
	auto sc=new TopScope(err);
	Expression[] exprs;
	if(auto r=importModule(path,err,exprs,sc,Location.init))
		return r;
	if(err.nerrors) return 1;
	FunctionDef[string] functions;
	foreach(expr;exprs){
		if(cast(ErrorExp)expr) continue;
		if(auto fd=cast(FunctionDef)expr){
			functions[fd.name.name]=fd;
		}else if(!cast(Declaration)expr&&!cast(DefineExp)expr&&!cast(CommaExp)expr) err.error("top level expression must be declaration",expr.loc);
	}
	if(opt.summarize.length){
		try{
			foreach(expr;exprs)
				if(auto fd=cast(FunctionDef)expr)
					writefln(getSummary(fd,opt.summarize).join(","));
		}catch(Exception e){
			stderr.writeln("error: ",e.msg);
			return 1;
		}
		return 0;
	}
	version(CHECK_AST){
		foreach(expr;exprs){
			if(auto fd=cast(FunctionDef)expr){
				import ast.checker:checkFunction;
				checkFunction(fd);
			}
		}
	}
	// TODO: add some backends
	if(err.nerrors) return 1;
	if(opt.backend==BackendType.run){
		import qsim;
		auto be=new QSim(path);
		if("main" in functions){
			auto fun=functions["main"];
			foreach(i;0..opt.numRuns){
				auto qstate=be.run(fun,err);
				if("`value" in qstate.vars)
					writeln(qstate.formatQValue(qstate.vars["`value"]));
				if(astopt.projectForget){
					auto total=qstate.totalProb();
					if(total>zeroThreshold)
						writefln("Pr[error] = %f",1.0L-total);
				}
			}
		}
	}
	return !!err.nerrors;
}

int main(string[] args){
	//import core.memory; GC.disable();
	version(TEST) test();

	int r = OptParser()
		.add!("help")(() {
			stderr.writeln(help.help);
			return 1;
		})
		.add!("noboundscheck")(() {
			opt.noBoundsCheck = true;
			return 0;
		})
		.add!("trace")((bool v) {
			opt.trace = v;
			return 0;
		})
		.add!("dump-reverse")((bool v) {
			opt.dumpReverse = v;
			return 0;
		})
		.add!("error-json", 'j')(() {
			opt.errorFormat=ErrorFormat.json;
			return 0;
		})
		.addOptional!("run")((string arg) {
			opt.backend=BackendType.run;
			if(arg) {
				opt.numRuns = to!ulong(arg);
			}
			return 0;
		})
		.add!("unsafe-capture-const")((bool v) {
			astopt.allowUnsafeCaptureConst = v;
			return 0;
		})
		.add!("remove-loops")((bool v) {
			astopt.removeLoops = v;
			return 0;
		})
		.add!("project-forget")((bool v) {
			astopt.projectForget = v;
			return 0;
		})
		.add!("summarize")((string arg) {
			import std.regex: regex, match;
			auto r=regex(r"^\[(([-a-z])*,)*([-a-z])*,?\]$");
			if(match(arg,r)){
				arg=arg[1..$-1];
				if(arg.endsWith(",")) arg=arg[0..$-1];
				opt.summarize=arg.split(',');
			}else{
				stderr.writeln("error: summary specification needs to be of format [key1,key2,...]");
				return 1;
			}
			return 0;
		})
		.add!("seed")((string arg) {
			import std.random;
			try{
				rndGen.seed(to!uint(arg));
			}catch(Exception){
				stderr.writeln("error: random seed must be 32-bit unsigned integer");
				return 1;
			}
			return 0;
		})
		.parse(args);
	if(r) return r;

	args.popFront();
	if(args.empty) {
		stderr.writeln("error: no input files");
		return 1;
	}
	foreach(x; args) {
		r = run(x);
		if(r) return r;
	}
	return 0;
}
