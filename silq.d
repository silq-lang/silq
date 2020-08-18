// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.stdio, std.path, std.array, std.string, std.algorithm, std.conv;
import file=std.file;
import util;
import ast.lexer, ast.parser, ast.expression, ast.declaration, ast.error, help;
import astopt;
import options, ast.scope_, ast.semantic_, ast.summarize;

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
	if(auto r=importModule(path,err,exprs,sc))
		return r;
	if(err.nerrors) return 1;
	FunctionDef[string] functions;
	foreach(expr;exprs){
		if(cast(ErrorExp)expr) continue;
		if(auto fd=cast(FunctionDef)expr){
			functions[fd.name.name]=fd;
		}else if(!cast(Declaration)expr&&!cast(DefExp)expr&&!cast(CommaExp)expr) err.error("top level expression must be declaration",expr.loc);
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
			}
		}
	}
	return !!err.nerrors;
}

int main(string[] args){
	//import core.memory; GC.disable();
	version(TEST) test();
	if(args.length) args.popFront();
	auto idx=args.countUntil("--read-args");
	if(idx<args.length){
		args=args[0..idx]~args[idx+1..$];
		foreach(filename;args){
			if(filename.startsWith("--")) continue;
			auto firstLine=File(filename).readln().strip();
			if(firstLine.startsWith("// args: ")) args=firstLine["// args: ".length..$].split~args;
			else if(firstLine.startsWith("//args: ")) args=firstLine["//args: ".length..$].split~args;
			break;
		}
	}
	bool isFormatting(string flag){
		import std.traits: EnumMembers;
		import std.conv: to;
		foreach(m;EnumMembers!Format){
			if(m==Format.default_) continue;
			if(flag=="--"~to!string(m)) return true;
		}
		return false;
	}
	args.sort!((a,b)=>a.startsWith("--")>b.startsWith("--")||a.startsWith("--")&&b.startsWith("--")&&isFormatting(a)&&!isFormatting(b)); // TODO: make better
	bool hasInputFile=false;
	foreach(x;args){
		switch(x){
			case "--help": writeln(help.help); return 0;
			//case "--syntax": writeln(syntax); return 0;
			/+case "--distributions":
				writeln(computeDistributionDocString());
				return 0;+/
			//case "--cdf": opt.cdf=true; break;
			//case "--plot": opt.plot=true; break;
			//case "--kill": opt.kill=true; break;
			//case "--nointegrate": opt.integrationLevel=IntegrationLevel.none; break;
			//case "--integratedeltas": opt.integrationLevel=IntegrationLevel.deltas; break;
			case "--noboundscheck": opt.noBoundsCheck=true; break;
			case "--nocheck": opt.noCheck=true; break;
			//case "--nonormalize": opt.noNormalize=true; break;
			case "--trace": opt.trace=true; break;
			case "--dump-reverse": opt.dumpReverse=true; break;
			//case "--expectation": opt.expectation=true; break;
			//case "--gnuplot": opt.formatting=Format.gnuplot; break;
			//case "--matlab": opt.formatting=Format.matlab; break;
			//case "--maple": opt.formatting=Format.maple; break;
			//case "--mathematica": opt.formatting=Format.mathematica; break;
			//case "--python": opt.formatting=Format.python; break;
			//case "--sympy": opt.formatting=Format.sympy; break;
			//case "--lisp": opt.formatting=Format.lisp; break;
			case "--error-json": opt.errorFormat=ErrorFormat.json; break;
			//case "--raw": opt.outputForm=OutputForm.raw; break;
			//case "--raw-error": opt.outputForm=OutputForm.rawError; break;
			case "--run": opt.backend=BackendType.run; break;
			case "--unsafe-capture-const": astopt.allowUnsafeCaptureConst=true; break;
			default:
				/+if(x.startsWith("--plot=")){
					auto rest=x["--plot=".length..$];
					import std.regex;
					auto r=regex(r"^\[-?[0-9]+(\.[0-9]+)?:-?[0-9]+(\.[0-9]+)?\]$");
					if(match(rest,r)){
						opt.plot=true;
						opt.plotRange=rest;
						continue;
					}else{
						stderr.writeln("error: plot range needs to be of format [l:r], where l and r are decimal numbers");
						return 1;
					}
				}+/
				/+if(x.startsWith("--plot-file=")){
					opt.plot=true;
					opt.plotFile=x["--plot-file=".length..$];
					continue;
				}+/
				if(x.startsWith("--summarize=")){
					auto rest=x["--summarize=".length..$];
					import std.regex: regex, match;
					auto r=regex(r"^\[(([-a-z])*,)*([-a-z])*,?\]$");
					if(match(rest,r)){
						rest=rest[1..$-1];
						if(rest.endsWith(",")) rest=rest[0..$-1];
						opt.summarize=rest.split(',');
					}else{
						stderr.writeln("error: summary specification needs to be of format [key1,key2,...]");
						return 1;
					}
					continue;
				}
				if(x.startsWith("--run=")){
					auto rest=x["--run=".length..$];
					try{
						opt.backend=BackendType.run;
						opt.numRuns=to!ulong(rest);
					}catch(Exception){
						stderr.writeln("error: number of samples needs to be 64-bit unsigned integer");
						return 1;
					}
					continue;
				}
				if(x.startsWith("--seed=")){
					import std.random;
					try{
						rndGen.seed(to!uint(x["--seed=".length..$]));
					}catch(Exception){
						stderr.writeln("error: random seed must be 32-bit unsigned integer");
						return 1;
					}
					continue;
				}
				hasInputFile=true;
				if(auto r=run(x)) return r;
		}
	}
	if(!hasInputFile){
		stderr.writeln("error: no input files");
		return 1;
	}
	return 0;
}
