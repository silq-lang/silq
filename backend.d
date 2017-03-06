// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import options,declaration,distrib,error,dexpr,util;
import symbolic,bruteforce;
import std.stdio, std.path, std.algorithm;

Distribution getCDF(Distribution dist){
	dist=dist.dup;
	auto freeVars=dist.freeVars.dup;
	foreach(freeVar;freeVars){
		auto nvar=dist.getVar("c"~freeVar.name);
		dist.distribute(dIvr(DIvr.Type.leZ,-freeVar-20)*dIvr(DIvr.Type.leZ,freeVar-nvar));
		dist.marginalize(freeVar);
		dist.distribution=dist.distribution.substitute(nvar,freeVar);
		dist.freeVars.remove(nvar);
		dist.freeVars.insert(freeVar);
	}
	dist.simplify();
	return dist;
}

abstract class Backend{
	static Backend create(string source){
		final switch(opt.backend){
			case InferenceMethod.symbolic:
				return new Symbolic(source);
			case InferenceMethod.bruteforce:
				return new Bruteforce(source);
			case InferenceMethod.simulate:
				return new Bruteforce(source);
		}
	}
	abstract Distribution analyze(FunctionDef fd,ErrorHandler err);
}

void printResult(Backend be,string path,FunctionDef fd,ErrorHandler err,bool isMain){
	auto dist=be.analyze(fd,err).dup;
	if(isMain){
		dist.renormalize();
		if(fd.params.length){
			dist.assumeInputNormalized(fd.params.length,fd.isTuple);
		}
		//dist.distribution=dist.distribution.substituteFun("q".dFunVar,one,DVar[].init,SetX!DVar.init).simplify(one);
	}
	import dparse;
	import approximate;
	//import hashtable; dist.distribution=approxLog(dist.freeVars.element);
	//import hashtable; dist.distribution=approxGaussInt(dist.freeVars.element);
	if(opt.kill) dist.distribution=dist.distribution.killIntegrals();
	if(opt.expectation||opt.backend==InferenceMethod.simulate){ // TODO: deal with non-convergent expectations
		import type, std.conv : text;
		if(fd.ret != ℝ && opt.backend!=InferenceMethod.simulate){
			err.error(text("with --expectation switch, functions should return a single number (not '",fd.ret,"')"),fd.loc);
			return;
		}
		assert(dist.orderedFreeVars.length==1);
		auto var=dist.orderedFreeVars[0];
		auto expectation = dIntSmp(var,var*dist.distribution/(one-dist.error),one);
		final switch(opt.backend==InferenceMethod.simulate?OutputForm.raw:opt.outputForm){
			case OutputForm.default_:
				writeln(opt.formatting==Format.mathematica?"E[":"𝔼[",var.toString(opt.formatting),dist.error!=zero?(opt.formatting==Format.mathematica?"|!error":"|¬error"):"","] = ",expectation.toString(opt.formatting));
				if(dist.error != zero) writeln("Pr[error] = ",dist.error.toString(opt.formatting));
				break;
			case OutputForm.raw:
				if(opt.backend==InferenceMethod.simulate && dist.error==one){
					writeln("⊥");
					break;
				}
				writeln(expectation.toString(opt.formatting));
				break;
			case OutputForm.rawError:
				writeln(dist.error.toString(opt.formatting));
				break;
		}
		return;
	}
	if(opt.cdf) dist=getCDF(dist);
	if(expected.exists) with(expected){
		writeln(ex==dist.distribution.toString()?todo?"FIXED":"PASS":todo?"TODO":"FAIL");
	}
	auto str=dist.toString(opt.formatting);
	final switch(opt.outputForm){
		case OutputForm.default_:
			writeln(str);
			break;
		case OutputForm.raw:
			writeln(dist.distribution.toString(opt.formatting));
			break;
		case OutputForm.rawError:
			writeln(dist.error.toString(opt.formatting));
			break;
	}
	if(opt.casBench){
		import std.file, std.conv;
		auto bpath=buildPath(dirName(thisExePath()),"test/benchmarks/casBench/",to!string(opt.formatting),setExtension(baseName(path,".psi"),casExt()));
		auto epath=buildPath(dirName(thisExePath()),"test/benchmarks/casBench/",to!string(opt.formatting),setExtension(baseName(path,".psi")~"Error",casExt()));
		auto bfile=File(bpath,"w");
		bfile.writeln(dist.distribution.toString(opt.formatting));
		if(dist.error.hasIntegrals()){
			auto efile=File(epath,"w");
			efile.writeln(dist.error.toString(opt.formatting));
		}
	}
	bool plotCDF=opt.cdf;
	if(str.canFind("δ")) plotCDF=true;
	import hashtable;
	if(opt.plot && (dist.freeVars.length==1||dist.freeVars.length==2)){
		if(plotCDF&&!opt.cdf){
			dist=dist.dup();
			foreach(freeVar;dist.freeVars.dup){
				auto nvar=dist.declareVar("foo"~freeVar.name);
				dist.distribute(dIvr(DIvr.Type.leZ,-freeVar-20)*dIvr(DIvr.Type.leZ,freeVar-nvar));
				dist.marginalize(freeVar);
			}
		}
		writeln("plotting... ",(plotCDF?"(CDF)":"(PDF)"));
		//matlabPlot(dist.distribution.toString(Format.matlab).replace("q(γ⃗)","1"),dist.freeVars.element.toString(Format.matlab));
		gnuplot(dist.distribution,dist.freeVars,opt.plotRange,opt.plotFile);
	}
}


void matlabPlot(string expression,string variable){
	import std.process,std.file;
	auto input=pipe();
	auto output=File("/dev/null","w");
	auto error=File("/dev/null","w");
	// TODO: make plot configurable from the outside
	auto id=spawnProcess(["octave"],input.readEnd,output,stderr);
	scope(exit) wait(id);
	string command=
		"fixNaN=@(x) [0,x]((x==x)+1);\n"~
		variable~"=-20:0.001:20;\n"~
		variable~"Dist="~expression~";\n"~
		"plot("~variable~","~variable~"Dist);\n";
	if(command.length<1000){
		writeln("command: ");
		writeln(command);
	}
	input.writeEnd.writeln(command);
	input.writeEnd.writeln("sleep(5);exit");
	input.writeEnd.flush();
	//writeln(input.readEnd.readln());
	//foreach(i;0..100) writeln(error.readEnd.readln());
}
void gnuplot(DExpr expr,SetX!DNVar varset,string range="[-1:3]",string outfile=""){
	DVar[] vars;
	foreach(var;varset) vars~=var;
	assert(vars.length==1||vars.length==2);
	import std.process,std.file;
	auto input=pipe();
	auto output=File("/dev/null","w");
	auto error=File("/dev/null","w");
	// TODO: make plot configurable from the outside
	auto id=spawnProcess(["gnuplot","-"],input.readEnd,output,stderr);
	scope(success) wait(id);
	if(vars[0]!is "x".dVar){ // TODO: fix
		assert(!expr.hasFreeVar("x".dVar));
		expr=expr.substitute(vars[0],"x".dVar);
	}
	if(vars.length==2){
		assert(!expr.hasFreeVar("y".dVar));
		expr=expr.substitute(vars[1],"y".dVar);
	}
	import std.string;
	if(outfile.length){
		input.writeEnd.writeln("set terminal postscript eps\nset output \"",outfile,"\"");
	}
	auto str=expr.toString(Format.gnuplot).replace("`q()","1");
	string command=
		//"set enhanced color lw 2 \"Times\" 30\n"~
		"set pointsize 20\n"
		~"set xlabel \""~vars[0].toString(Format.gnuplot)~"\"\n"
		~(vars.length==2?"set ylabel \""~vars[1].toString(Format.gnuplot)~"\"\n":"")
		~"set "~(vars.length==1?"y":"z")~"label \"density\"\n"
		~"set samples 500, 500\n"
		~"set isosample 200\n"
		~"unset key\n";
	if(vars.length==1) command~="plot "~range~" "~str~"\n";
	else command~="splot "~range~" "~range~" "~str~"\n";
	if(command.length<10000){
		writeln("command: ");
		writeln(command);
	}
	input.writeEnd.writeln(command);
	if(outfile.length) input.writeEnd.writeln("exit");
	else input.writeEnd.writeln("bind \"x\" \"exit\"\n");
	input.writeEnd.flush();	
}
