// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import util.path;
import util.optparse;
import util.terminal;
import std.array, std.string, std.algorithm, std.conv;
import util, util.io;
import ast.lexer, ast.parser, ast.expression, ast.declaration, ast.error, help;
import astopt;
import options, ast.scope_, ast.modules, ast.summarize;

static this(){
	astopt.importPath ~= buildPath(dirName(file.thisExePath),"library");
	static if(language==psi) astopt.importPath ~= buildPath(dirName(file.thisExePath),"..","..","..","..","ras","psi","library"); // TODO: remove
}

class Backend {
	abstract int run(FunctionDef[string] functions, ErrorHandler err);
}

scope class SummarizeBackend: Backend {
	string[] entries;

	override int run(FunctionDef[string] functions, ErrorHandler err) {
		try{
			foreach(fd;functions)
				writefln(getSummary(fd,entries).join(","));
		}catch(Exception e){
			stderr.writeln("error: ",e.msg);
			return 1;
		}
		return 0;
	}
}

scope class QSimBackend: Backend {
	ulong numRuns = 1;

	override int run(FunctionDef[string] functions, ErrorHandler err) {
		import qsim;
		auto pfun = "main" in functions;
		if(!pfun) return 0;
		auto fun=*pfun;
		auto be=new QSim(fun.loc.source.name);
		foreach(i;0..numRuns){
			auto qstate=be.run(fun,err);
			if("`value" in qstate.vars)
				writeln(qstate.formatQValue(qstate.vars["`value"]));
			if(opt.projectForget){
				auto total=qstate.totalProb();
				if(total>zeroThreshold)
					writefln("Pr[error] = %f",1.0L-total);
			}
		}
		return !!err.nerrors;
	}
}

int run(Backend backend, string path, ErrorHandler err){
	path = getActualPath(path);
	auto ext = path.extension;
	if(ext != (language==astopt.silq?".slq":".psi")){ // TODO: support only language==silq
		stderr.writeln(path~": unrecognized extension: "~ext);
		return 1;
	}
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
	if(opt.check){
		foreach(expr;exprs){
			if(auto fd=cast(FunctionDef)expr){
				import ast.checker:checkFunction;
				checkFunction(fd);
			}
		}
	}
	// TODO: add some backends
	if(err.nerrors) return 1;
	if(!backend) return 0;
	return backend.run(functions, err);
}

int main(string[] args){
	//import core.memory; GC.disable();
	version(TEST) test();

	Backend backend = null;
	scope auto qsimBackend = new QSimBackend();
	scope auto summarizeBackend = new SummarizeBackend();

	string jsonOut = null;

	int r = OptParser()
		.add!("help")(() {
			stderr.writeln(help.help);
			return 1;
		})
		.add!("noboundscheck")(() {
			stderr.writeln("warning: --noboundscheck is deprecated and has no effect");
			return 0;
		})
		.add!("trace")((bool v) {
			opt.trace = v;
			return 0;
		})
		.add!("dump-reverse")((bool v) {
			astopt.dumpReverse = v;
			return 0;
		})
		.add!("dump-loops")((bool v) {
			astopt.dumpLoops = v;
			return 0;
		})
		.addOptional!("error-json", 'j')((string path) {
			if(path is null) {
				jsonOut = "-";
			} else {
				jsonOut = path;
			}
			return 0;
		})
		.addOptional!("run")((string arg) {
			backend = qsimBackend;
			if(arg) {
				qsimBackend.numRuns = to!ulong(arg);
			}
			return 0;
		})
		.add!("inference-limit")((string v) {
			astopt.inferenceLimit = to!int(v);
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
		.add!("split-components")((bool v) {
			astopt.splitComponents = v;
			return 0;
		})
		.add!("check")((bool v) {
			opt.check = v;
			return 0;
		})
		.add!("project-forget")((bool v) {
			opt.projectForget = v;
			return 0;
		})
		.add!("summarize")((string arg) {
			import std.regex: regex, match;
			auto r=regex(r"^\[(([-a-z])*,)*([-a-z])*,?\]$");
			if(match(arg,r)){
				arg=arg[1..$-1];
				if(arg.endsWith(",")) arg=arg[0..$-1];
				summarizeBackend.entries=arg.split(',');
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

	// --summarize, if not empty, overrides any other backend choice.
	if(summarizeBackend.entries) {
		backend = summarizeBackend;
	}

	try{
		args.popFront();
		if(args.empty) {
			stderr.writeln("error: no input files");
			return 1;
		}
		ErrorHandler err;
		File errFile;
		if(!jsonOut) {
			if(isATTy(stderr)){
				err = new FormattingErrorHandler();
			} else {
				err = new VerboseErrorHandler();
			}
		} else if(jsonOut == "-") {
			err = new JSONErrorHandler(stdout, false);
		} else {
			err = new JSONErrorHandler(File(jsonOut, "w"), true);
		}
		scope(exit) err.finalize();

		foreach(x; args) {
			r = run(backend, x, err);
			if(r) return r;
		}
		return 0;
	}catch(Throwable e){
		stderr.writeln(e.toString());
		import core.stdc.signal:SIGABRT;
		return 128+SIGABRT;
	}
}
