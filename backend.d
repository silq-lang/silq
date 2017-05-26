// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import options,declaration,distrib,error,dexpr,util;
import symbolic,dp;
import std.stdio, std.path, std.algorithm;

Distribution getCDF(Distribution dist){
	dist=dist.dup;
	auto vars=dist.freeVars.dup;
	foreach(var;vars){
		auto nvar=dist.getVar("c"~var.name);
		dist.distribute(dIvr(DIvr.Type.leZ,var-nvar));
		dist.marginalize(var);
		dist.distribution=dist.distribution.substitute(nvar,var);
		dist.freeVars.remove(nvar);
		dist.freeVars.insert(var);
	}
	dist.simplify();
	return dist;
}

abstract class Backend{
	static Backend create(string source){
		final switch(opt.backend){
			case InferenceMethod.symbolic:
				return new Symbolic(source);
			case InferenceMethod.dp:
				return new Bruteforce(source);
			case InferenceMethod.simulate:
				return new Bruteforce(source);
		}
	}
	abstract Distribution analyze(FunctionDef fd,ErrorHandler err);
}

void printResult(Backend be,string path,FunctionDef fd,ErrorHandler err,bool isMain){
	import type, std.conv : text;
	if(opt.expectation){
		bool check(Expression ty){
			if(ty==ℝ) return true;
			if(auto tpl=cast(TupleTy)ty)
				return tpl.types.all!check;
			return false;
		}
		if(!check(fd.ret)){
			err.error(text("with --expectation switch, '",fd.name,"' should return numbers (not '",fd.ret,"')"),fd.loc);
			return;
		}
	}
	auto dist=be.analyze(fd,err).dup;
	if(isMain) dist.renormalize();
	import dparse;
	import approximate;
	//import hashtable; dist.distribution=approxLog(dist.freeVars.element);
	//import hashtable; dist.distribution=approxGaussInt(dist.freeVars.element);
	if(opt.kill) dist.distribution=dist.distribution.killIntegrals();
	if(opt.expectation||opt.backend==InferenceMethod.simulate){ // TODO: deal with non-convergent expectations
		auto exp=!dist.isTuple?dist.orderedFreeVars[0]:dTuple(cast(DExpr[])dist.orderedFreeVars);
		// TODO: do not compute full distribution with --expectation switch
		DExpr compute(DExpr e,Expression ty){
			if(ty==ℝ){
				auto r=e*dist.distribution/(one-dist.error);
				foreach_reverse(v;dist.orderedFreeVars) r=dIntSmp(v,r,one);
				return r;
			}
			if(auto tpl=cast(TupleTy)ty){
				DExpr[] r;
				foreach(i,nty;tpl.types) r~=compute(e[i.dℚ],nty);
				return dTuple(r);
			}
			assert(0);
		}
		auto expectation = compute(exp,fd.ret);
		final switch(opt.backend==InferenceMethod.simulate?OutputForm.raw:opt.outputForm){
			case OutputForm.default_:
				auto astr=dist.argsToString(opt.formatting);
				if(dist.error!=zero && opt.formatting!=Format.mathematica)
					astr=astr.length?"¬error,"~astr:"¬error";
				writeln(opt.formatting==Format.mathematica?"E[":"𝔼[",dist.varsToString(opt.formatting),astr.length?"|"~astr:"","] = ",expectation.toString(opt.formatting));
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
		auto varset=expectation.freeVars.setx;
		if(opt.plot && (varset.length==1||varset.length==2)){
			writeln("plotting... ");
			gnuplot(expectation,cast(SetX!DNVar)varset,"expectation",opt.plotRange,opt.plotFile);
		}
		return;
	}
	if(opt.cdf) dist=getCDF(dist);
	if(expected.exists) with(expected){
		writeln(ex==dist.distribution.toString()?todo?"FIXED":"PASS":todo?"TODO":"FAIL");
	}
	final switch(opt.outputForm){
		case OutputForm.default_:
			writeln(dist.toString(opt.formatting));
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
	if(!dist.distribution.isContinuousMeasure()) plotCDF=true;
	import hashtable;
	SetX!DNVar varset=dist.freeVars.dup;
	foreach(a;dist.args) varset.insert(a);
	if(opt.plot && (varset.length==1||varset.length==2)){
		if(plotCDF&&!opt.cdf) dist=getCDF(dist);
		writeln("plotting... ",(plotCDF?"(CDF)":"(PDF)"));
		//matlabPlot(dist.distribution.toString(Format.matlab).replace("q(γ⃗)","1"),dist.freeVars.element.toString(Format.matlab));
		gnuplot(dist.distribution,varset,plotCDF?"probability":"density",opt.plotRange,opt.plotFile);
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
void gnuplot(DExpr expr,SetX!DNVar varset,string label,string range="[-1:3]",string outfile=""){
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
	expr=expr.substituteAll(vars,[cast(DExpr)"x".dVar,"y".dVar][0..vars.length]);
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
		~"set "~(vars.length==1?"y":"z")~"label \""~label~"\"\n"
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
