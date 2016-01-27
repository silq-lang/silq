import std.stdio, std.path, std.array, std.string, std.algorithm;
import file=std.file;
import util;
import lexer, parser, expression, error;

import analysis, distrib, dexpr;

bool plot=false;// TODO: get rid of globals?
bool kill=false;
auto formatting=Format.default_;
bool casBench=false;

string casExt(Format formatting=.formatting){
	final switch(formatting) with(Format){
		case default_: return "dexpr";
		case matlab: return "m";
		case mathematica: return "m";
		case maple: return "mpl";
		case sympy: return "py";
	}
}

string getActualPath(string path){
	// TODO: search path
	auto ext = path.extension;
	if(ext=="") path = path.setExtension("prb");
	return file.getcwd().canFind("/test")?path:"test/"~path;
}

string readCode(File f){
	// TODO: use memory-mapped file with 4 padding zero bytes
	auto app=mallocAppender!(char[])();
	foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
	app.put("\0\0\0\0"); // insert 4 padding zero bytes
	return cast(string)app.data;	
}
string readCode(string path){ return readCode(File(path)); }

void performAnalysis(string path,FunctionDef fd,ErrorHandler err,bool renormalize){
	auto dist=analyze(fd,err).dup;
	if(renormalize) dist.renormalize();
	import approximate;
	//import hashtable; dist.distribution=approxLog(dist.freeVars.element);
	//import hashtable; dist.distribution=approxGaussInt(dist.freeVars.element);
	if(kill) dist.distribution=dist.distribution.killIntegrals();
	auto str=dist.toString(formatting);
	if(expected.exists) with(expected){
			if(formatting==Format.default_)
				writeln(ex==dist.distribution.toString()?todo?"FIXED":"PASS":todo?"TODO":"FAIL");
			else writeln("SKIPPED: NON-DEFAULT FORMATTING");
	}
	//writeln((cast(DPlus)dist.distribution).summands.length);
	if(str.length<10000) writeln(str);
	else{
		writeln("writing output to temporary file...");
		auto f=File("tmp.deleteme","w");
		f.writeln(str);
	}
	if(casBench){
		import std.file, std.conv;
		auto bpath=buildPath(dirName(thisExePath()),"test/benchmarks/casBench/",to!string(formatting),setExtension(baseName(path,".prb"),casExt()));
		auto epath=buildPath(dirName(thisExePath()),"test/benchmarks/casBench/",to!string(formatting),setExtension(baseName(path,".prb")~"Error",casExt()));
		auto bfile=File(bpath,"w");
		bfile.writeln(dist.distribution.toString(formatting));
		if(dist.error.hasIntegrals()){
			auto efile=File(epath,"w");
			efile.writeln(dist.error.toString(formatting));
		}
	}
	bool plotCDF=false;
	if(str.canFind("δ")) plotCDF=true;
	import hashtable;
	if(plot && dist.freeVars.length==1){
		if(plotCDF){
			dist=dist.dup();
			auto freeVar=dist.freeVars.element;
			auto nvar=dist.declareVar("foo");
			dist.distribute(dIvr(DIvr.Type.leZ,-freeVar-20)*dIvr(DIvr.Type.leZ,freeVar-nvar));
			dist.marginalize(freeVar);
		}
		writeln("plotting... ",(plotCDF?"(CDF)":"(PDF)"));
		matlabPlot(dist.distribution.toString(Format.matlab),dist.freeVars.element.toString(Format.matlab));
	}
}

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
	auto err=new FormattingErrorHandler();
	auto exprs=parseFile(src,err);
	foreach(expr;exprs){
		if(auto fd=cast(FunctionDef)expr){
			analysis.functions[fd.name.name]=fd;
		}else{
			err.error("top level declaration must be function",expr.loc);
		}
	}
	sourceFile=path;
	scope(exit){ // TODO: get rid of globals
		analysis.functions=(FunctionDef[string]).init;
		analysis.summaries=(Distribution[string]).init;
		sourceFile=null;
	}
	if(err.nerrors) return 1;
	if("main" !in functions){
		if(casBench && functions.length>1){
			stderr.writeln("cannot extract benchmark: no entry point");
			return 1;
		}
		foreach(name,fd;functions){
			writeln(name,":");
			performAnalysis(path,fd,err,false);
		}
	}else performAnalysis(path,functions["main"],err,true);
	return !!err.nerrors;
}


int main(string[] args){
	//import core.memory; GC.disable();
	version(TEST) test();
	if(args.length<2){
		stderr.writeln("error: no input files");
		return 1;
	}
	args.popFront();
	args.sort!((a,b)=>a.startsWith("--")>b.startsWith("--"));
	foreach(x;args){
		switch(x){
			case "--plot": plot=true; break;
			case "--kill": kill=true; break;
			case "--raw": simplification=Simpl.raw;  break;
			case "--deltas": simplification=Simpl.deltas; break;
			case "--casbench": casBench=true; break;
			case "--matlab": formatting=Format.matlab; break;
			case "--maple": formatting=Format.maple; break;
			case "--mathematica": formatting=Format.mathematica; break;
			case "--sympy": formatting=Format.sympy; break;
			default: if(auto r=run(x)) return r;
		}
	}
	return 0;
}

version=TEST;
void test(){
	/+//auto v="x".dVar;
	//writeln(dInt(v,dE.dPow(2.dℕ.dMult(3.dℕ.dPlus(3.dℕ).dPlus(3.dℕ))).dPow(v.dPlus(v))));
	auto d=new Distribution();
	auto v=d.declareVar("x₁");
	//d.distribute(v,uniformPDF(v,-one,one+one));
	d.distribute(v,gaussianPDF(v,zero,one));
	writeln(d);
	auto w=d.declareVar("x₂");
	d.distribute(w,gaussianPDF(w,one,one));
	writeln(d);
	/*d.marginalize(v);
	writeln(d);
	d.marginalize(w);
	writeln(d);*/
	//d.distribute(w,gaussianPDF(w,zero,one));
	auto u=d.declareVar("x₃");
	d.assign(u,v+w);
	//d.distribute(v,gaussianPDF(v,0.dℕ,1.dℕ));
	//d.distribute(v,gaussianPDF(v,0.dℕ,1.dℕ));
	//d.distribute(v,gaussianPDF(v,0.dℕ,1.dℕ));
	writeln(d);
	d.marginalize(v);
	writeln(d);
	d.marginalize(w);
	writeln(d);
	writeln(one/10*(one/2));
	writeln((one+one)^^-2+2);
	writeln(-one-2^^(-one)*3);
	writeln((-one)+2^^(-one)*(-1)+2^^(-one)*(-1));
	writeln((v^^2+w^^2)^^(one/2));
	writeln(underline(overline(overline("HELLO"))));
	writeln(dInt(v,2*v));
	writeln(dInt(v,v+w));
	writeln(dInt(v,v.dDelta)+dInt(w,w.dDelta));
	writeln(dInt(v,one)+dInt(w,one));
	writeln((3*v-2*w).solveFor(v,zero));
	writeln(-1*(-one/2));
	writeln((v^^2/2)/(v^^2/2));+/
	/*auto d=new Distribution();
	auto x=d.declareVar("x");
	d.initialize(x,one);
	d.assign(x,x+1);
	auto y=d.declareVar("y");
	d.initialize(y,3.dℕ);
	auto tmpx=d.getVar("x");
	d.initialize(tmpx,x);
	auto dthen=d.dup(),dothw=d.dup();
	dthen.assign(y,y-x);
	writeln(dthen," ",dothw);
	d=dthen.join(d.vbl,d.symtab,d.freeVars,dothw,dIvr(DIvr.Type.lZ,(x-y)));
	writeln(d);
	d.marginalize(tmpx);
	d.marginalize(x);
	//writeln((x*dIvr(DIvr.Type.lZ,x)).substitute(x,one+one));
	writeln(d);*/
	/*auto x="x".dVar,y="y".dVar;
	writeln(dDiff(x,x^^(x^^2)*y));
	writeln(dDiff(y,dDiff(x,x^^(x^^2)*y)));
	writeln(dDiff(x,dLog(x)));
	writeln(dDiff(x,dDiff(x,dE^^(2*x))));
	writeln(dDiff(x,2^^(dLog(x))));
	writeln(dLog(dE^^x));
	writeln(dDiff(y,dInt(x,x*dIvr(DIvr.Type.lZ,-x)*dIvr(DIvr.Type.lZ,x-y))));*/
	/*auto f="f".dVar,x="x".dVar;
	auto g="g".dVar,y="y".dVar;
	auto z="z".dVar;
	auto dist=dFun(f,[x,y])*dDelta(x*y-z);
	//auto dist=uniformPDF(x,zero,one)*uniformPDF(y,zero,one)*dDelta(x*y-z);
	writeln(dist);
	//writeln(dInt(x,dist));
	//writeln(dInt(y,dInt(x,dist)));*/
	/*auto x="x".dVar, y="y".dVar;
	writeln(splitMultAtVar(dE^^((x+y)^^2),x));*/
	//-(-2+__g₂)²·⅙+-x₁²·¼+-¼+x₁·½
	/*auto x="x".dVar,y="y".dVar;
	auto e=-(-2+x)^^2/6-y^^2/4-one/4+y/3;
	writeln(splitPlusAtVar(e,x));*/
	/*auto x="x".dVar;
	writeln((x^^10+2*x^^2+3*x+4).asPolynomialIn(x).toDExpr());*/
	/*auto x="x".dVar,y="y".dVar;
	auto pdf=gaussianPDF(x,1.dℕ,2.dℕ)*gaussianPDF(y,3.dℕ,4.dℕ);
	writeln(dInt(x,pdf));
	writeln(dInt(y,pdf));
	writeln(dInt(y,dInt(x,pdf)));
	writeln(dInt(x,dInt(y,pdf)));*/
	//(∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·δ[-z+y·ξ₁])·[-1+y≤0]·[-y≤0]
	/+auto xi1="ξ₁".dVar,y="y".dVar,z="z".dVar;
	auto res=dInt(xi1,dDelta(y*xi1)*dIvr(DIvr.Type.leZ,xi1));
	writeln(res);
	writeln(dInt(y,res));+/
	/*auto a="a".dVar,b="b".dVar,r="r".dVar;
	auto exp=dE^^(-a^^2/2-b^^2/2)*dDelta(r-1)/(2*dΠ);
	writeln(dInt(b,dInt(a,exp)));*/
	/+import dparse;
	auto x="x".dVar,y="y".dVar,a="a".dVar,b="b".dVar;
	auto e="(δ[-x+1+[-b+a<0]]·δ[-y+1+[-b+a<0]]·⅟4+δ[-x+[-b+a<0]]·δ[-y+[-b+a<0]]·⅟4)·e^(-a²·⅟2+-b²·⅟2)·δ[-r+[-x+y=0]]·⅟π".dParse;
	//auto e2=dInt(y,dInt(x,e));
	//writeln(dInt(a,dInt(b,e2)));
	//auto e2=dInt(a,e);
	auto e2="((∫dξ₁δ[-x+1+[-b+ξ₁<0]]·δ[-y+1+[-b+ξ₁<0]]·⅟e^(ξ₁²·⅟2))·⅟4+(∫dξ₁δ[-x+[-b+ξ₁<0]]·δ[-y+[-b+ξ₁<0]]·⅟e^(ξ₁²·⅟2))·⅟4)·δ[-r+[-x+y=0]]·⅟e^(b²·⅟2)·⅟π".dParse;
	writeln(dInt(b,dInt(y,dInt(x,e2))));
	//writeln(dInt(x,e2));
	//auto e3="(∫dξ₁((∫dξ₂δ[-x+1+[-ξ₁+ξ₂<0]]·δ[-y+1+[-ξ₁+ξ₂<0]]·⅟e^(ξ₂²·⅟2))·⅟4+(∫dξ₂δ[-x+[-ξ₁+ξ₂<0]]·δ[-y+[-ξ₁+ξ₂<0]]·⅟e^(ξ₂²·⅟2))·⅟4)·⅟e^(ξ₁²·⅟2))·δ[-r+[-x+y=0]]·⅟π".dParse;
	//auto e3="(∫dξ₁δ[-x+1+[-b+ξ₁<0]]·δ[-y+1+[-b+ξ₁<0]]·⅟e^(ξ₁²·⅟2))·⅟4+(∫dξ₁δ[-x+[-b+ξ₁<0]]·δ[-y+[-b+ξ₁<0]]·⅟e^(ξ₁²·⅟2))·⅟4)·δ[-r+[-x+y=0]]·⅟e^(b²·⅟2)·⅟π".dParse;
	//auto e3="∫dξ₁((∫dξ₂δ[-y+1+[-b+ξ₂<0]]·δ[-ξ₁+1+[-b+ξ₂<0]]·⅟e^(ξ₂²·⅟2)))·⅟4·⅟e^(b²·⅟2)·⅟π".dParse;
	//writeln(dInt(b,dInt(a,e))is e3);
	//writeln(e3);
	//writeln(dInt(y,dInt(x,e3)));

	/*auto e3="(∫dξ₁((∫dξ₂δ[-x+1+[-ξ₁+ξ₂<0]]·δ[-y+1+[-ξ₁+ξ₂<0]]·⅟e^(ξ₂²·⅟2))·⅟4)·⅟e^(ξ₁²·⅟2))·δ[-r+[-x+y=0]]·⅟π".dParse;
	writeln(e3);
	writeln(dInt(y,dInt(x,e3)));*/ +/
	/*import dparse;
	  writeln("((x₃)²)".dParse);*/
	import dparse;
	//writeln("⅟√1̅0̅".dParse);
	//writeln("e^((x₃·⅟2+⅟6)²·3·⅟5+-11·⅟12+-x₃²·⅟4+x₃·⅟2)·⅟√1̅0̅·⅟√π̅".dParse);
	//writeln("∫dξ₁δ[-ξ₁·⅟2+1]".dParse);
	//writeln("[x<0]^2".dParse);
	//writeln("[(-[-1+z≤0]+1)·z+-1≤0]".dParse);
	//writeln("[(-1+z)·[-z+1≠0]·[-z+1≤0]+-[-1+z≤0]≤0]".dParse);
	// [([-z+1<0]·z+-1≤0]
	//writeln("(((-1+w)·[-w+2≤0]+-1)·[-2+w≤0]+(-1+w)·[-w+2≤0])".dParse.factorDIvr!(a=>dIvr(DIvr.Type.leZ,a)));
	//writeln("x".dVar^^2);
	//writeln("(∫dξ₁((-1+-ξ₁+x)·[-2+-ξ₁+x≤0]+[-x+2+ξ₁≠0]·[-x+2+ξ₁≤0])²·[-1+ξ₁≤0]·[-2+-ξ₁+x≤0]·[-x+1+ξ₁≤0]·[-x+2+ξ₁≠0]·[-ξ₁≤0])".dParse);
	//writeln("∫dξ₁(-x+1+ξ₁)·(-ξ₁+x)·[-1+ξ₁≤0]·[-2+-ξ₁+x≤0]·[-x+1+ξ₁≠0]·[-x+1+ξ₁≤0]·[-ξ₁≤0]".dParse);
	//writeln("(∫dξ₁((-1+ξ₁)²·ξ₁+-(-1+ξ₁)²)·[-1+-ξ₁+x≤0]·[-4+ξ₁≤0]·[-x+ξ₁≤0]·[-ξ₁+3≠0]·[-ξ₁+3≤0])".dParse);
	//writeln("∫dcur[-1+-2·cur+2·x≠0]·[-1+-2·cur+2·x≤0]·[-1+-cur+x≤0]·[-1+2·cur≠0]·[-1+2·cur≤0]·[-1+cur≤0]·[-cur≤0]·[-x+cur≤0]".dParse);
	//writeln("[([x=0]+x)·(1+[x=0])≤0]".dParse.simplify(one)); // non-termination in factorDIvr
	//writeln("x·[x=0]".dParse.simplify(one));
	//writeln("[([x≠0]+1)·(1+[x≠0])≤0]".dParse);
	//writeln("[x<0]".dParse.simplify("[x≤0]".dParse));
	//writeln("[x≤0]".dParse.simplify("[-x<0]".dParse));
	//writeln("[[z≠0]·[z≤0]≤0]".dParse); // TODO: this is convoluted!
	//writeln("[z+-3≤0]·[z+-2≤0]".dParse);
	//writeln("[-3+x≤0]·[-x+2≤0]".dParse);
	//writeln("[z≤0]".dParse.simplify("[-z≤0]·[z≠0]".dParse));
	//writeln("[[x≤0]≤0]".dParse);
	//writeln("(∫dξ₁[-b+ξ₁≠0]·[-b+ξ₁≤0]·⅟e^(ξ₁²·⅟2))·δ[-x+2]·δ[-y+2]·⅟4+(∫dξ₁[-b+ξ₁≠0]·[-ξ₁+b≤0]·⅟e^(ξ₁²·⅟2))·δ[-x+1]·δ[-y+1]·⅟4");
	//writeln("([-b+a≠0]·[-b+a≤0]·⅟e^(a²·⅟2))·⅟4+([-b+a≠0]·[-a+b≤0]·⅟e^(a²·⅟2))·⅟4".dParse.simplify(one));
	//writeln("(([-b+a=0]+[-b+a≠0]·⅟2)·[-b+a≠0]·δ[-r+1]+[-b+a=0]·δ[-r+1]·⅟2)·e^(-a²·⅟2+-b²·⅟2)·⅟π".dParse.simplify(one).simplify(one));
	//writeln("([-a+b≤0]·[-b+a≠0]·δ[-r+1]·⅟2+[-b+a≤0]·δ[-r+1]·⅟2)·e^(-a²·⅟2+-b²·⅟2)·⅟π".dParse.simplify(one));
	//writeln("((∫dξ₁(∫dξ₂[-ξ₁+ξ₂≠0]·[-ξ₁+ξ₂≤0]·⅟e^(ξ₂²·⅟2))·⅟e^(ξ₁²·⅟2))·δ[-r+1]·⅟2+(∫dξ₁(∫dξ₂[-ξ₁+ξ₂≠0]·[-ξ₂+ξ₁≤0]·⅟e^(ξ₂²·⅟2))·⅟e^(ξ₁²·⅟2))·δ[-r+1]·⅟2)·⅟π".dParse.simplify(one));
	//writeln("∫dage2₁∫dage2₂∫dage1₁∫dage1₂(-[-age1₁+age2₁≠0]·[-age1₁+age2₁≤0]+1)·(δ[-isGirl1+1]·⅟1682+δ[isGirl1]·⅟1682)·(δ[-isGirl2+1]+δ[isGirl2])·[-30+age1≤0]·[-30+age2≤0]·[-age1+1≤0]·[-age2+1≤0]·isGirl2·δ[-age1₁+age1]·δ[-age1₂+age1]·δ[-age2₁+age2]·δ[-age2₂+age2]+(δ[-isGirl1+1]·⅟1682+δ[isGirl1]·⅟1682)·(δ[-isGirl2+1]+δ[isGirl2])·[-30+age1≤0]·[-30+age2≤0]·[-age1+1≤0]·[-age1₁+age2₁≠0]·[-age1₁+age2₁≤0]·[-age2+1≤0]·isGirl1·δ[-age1₁+age1]·δ[-age1₂+age1]·δ[-age2₁+age2]·δ[-age2₂+age2]".dParse);
	/+auto eu4="-125·[-4+x≠0]·[-5+x≤0]·[-x+4≤0]·x·⅟6+-22·[-3+x≤0]·[-x+2≤0]·[-x+3≠0]·x·⅟3+-31·[-3+x≤0]·[-x+2≠0]·[-x+2≤0]·x·⅟6+-39·[-4+x≤0]·[-x+3≠0]·[-x+3≤0]·x²·⅟4+-4·[-3+x≤0]·[-x+2≤0]·[-x+3≠0]·x³·⅟3+-4·[-4+x≠0]·[-4+x≤0]·[-x+3≤0]·x²+-50·[-4+x≤0]·[-x+3≠0]·[-x+3≤0]·⅟3+-5·[-2+x≤0]·[-x+1≤0]·[-x+2≠0]·⅟24+-5·[-4+x≠0]·[-5+x≤0]·[-x+4≤0]·x³·⅟6+-7·[-3+x≤0]·[-x+2≠0]·[-x+2≤0]·x³·⅟6+-85·[-4+x≠0]·[-4+x≤0]·[-x+3≤0]·⅟8+-[-2+x≤0]·[-x+1≠0]·[-x+1≤0]·x²·⅟4+-[-2+x≤0]·[-x+1≠0]·[-x+1≤0]·x⁴·⅟24+-[-2+x≤0]·[-x+1≤0]·[-x+2≠0]·x²+-[-2+x≤0]·[-x+1≤0]·[-x+2≠0]·x⁴·⅟8+-[-4+x≠0]·[-4+x≤0]·[-x+3≤0]·x⁴·⅟24+-[-4+x≤0]·[-x+3≠0]·[-x+3≤0]·x⁴·⅟8+10·[-3+x≤0]·[-x+2≤0]·[-x+3≠0]·⅟3+11·[-4+x≤0]·[-x+3≠0]·[-x+3≤0]·x³·⅟6+11·[-x+2=0]·⅟24+11·[-x+3=0]·⅟24+131·[-4+x≤0]·[-x+3≠0]·[-x+3≤0]·x·⅟6+15·[-3+x≤0]·[-x+2≠0]·[-x+2≤0]·x²·⅟4+25·[-3+x≤0]·[-x+2≠0]·[-x+2≤0]·⅟8+25·[-4+x≠0]·[-5+x≤0]·[-x+4≤0]·x²·⅟4+2·[-2+x≤0]·[-x+1≤0]·[-x+2≠0]·x³·⅟3+2·[-2+x≤0]·[-x+1≤0]·[-x+2≠0]·x·⅟3+2·[-4+x≠0]·[-4+x≤0]·[-x+3≤0]·x³·⅟3+32·[-4+x≠0]·[-4+x≤0]·[-x+3≤0]·x·⅟3+5·[-3+x≤0]·[-x+2≤0]·[-x+3≠0]·x²+625·[-4+x≠0]·[-5+x≤0]·[-x+4≤0]·⅟24+[-1+x≤0]·[-x+1≠0]·[-x≤0]·x⁴·⅟24+[-2+x≤0]·[-x+1≠0]·[-x+1≤0]·x³·⅟6+[-2+x≤0]·[-x+1≠0]·[-x+1≤0]·x·⅟6+[-3+x≤0]·[-x+2≠0]·[-x+2≤0]·x⁴·⅟8+[-3+x≤0]·[-x+2≤0]·[-x+3≠0]·x⁴·⅟8+[-4+x≠0]·[-5+x≤0]·[-x+4≤0]·x⁴·⅟24+[-x+1=0]·⅟24+[-x+4=0]·⅟24".dParse;
	auto ey=uniformPDF("y".dVar,zero,one);
	auto eu=eu4*ey*dDelta("z".dVar-"x".dVar-"y".dVar);
	auto wy=dInt("y".dVar,eu);
	auto wx=dInt("x".dVar,wy);
	wx=wx.simplify(one);+/
	//writeln();
	//writeln(
	//auto k=(eu4*ey);//.substitute("y".dVar,-"x".dVar+"z".dVar);
	//writeln(k);
	/+DExpr x="x".dVar;
	DExpr d=zero;	
	foreach(i;0..13){
		foreach(j;0..13){
			d=d+j*x^^j/(i+1)*dIvr(DIvr.Type.leZ,i-x)*dIvr(DIvr.Type.lZ,x-1-i);
		}
	}
	//writeln(d);
	writeln(dInt("x".dVar,d*dIvr(DIvr.Type.leZ,x-"y".dVar)));+/
	//writeln("([-1+y≤0]·y+[-y+1≠0]·[-y+1≤0])^1000".dParse);
	//writeln("-[-x+3≤0]+2·[-3+x≤0]·[-x+3≠0]+[-x+3≤0]·x".dParse^^31);
	//writeln(d);
	//DExpr x="x".dVar,y="y".dVar;
	//writeln((x+x^^2)^^10);
	//writeln("-4·[-i+2≤0]·⅟(-2·i+2·i²)+[-i+2≤0]·i·⅟(-i+i²)".dParse.simplify(one));
	//writeln("∫da[-a+b≤0]·e^(-a²·⅟2+-b²·⅟2)".dParse);
	//writeln("∫dx(((-113·⅟8+-39·x²·⅟4+-x⁴·⅟8+11·x³·⅟6+133·x·⅟6)·[-x+3≠0]·[-x+3≤0]+-23·[-3+x≤0]·[-x+3≠0]·x·⅟3+-31·[-x+3≤0]·⅟8+-4·[-3+x≤0]·[-x+3≠0]·x³·⅟3+4·[-3+x≤0]+5·[-3+x≤0]·[-x+3≠0]·x²+[-3+x≤0]·[-x+3≠0]·x⁴·⅟8)·(([-3+x≤0]+[-4+x≤0]·[-x+3≠0])·[-x+3≤0]+[-3+x≤0]·[-x+2≤0]·[-x+3≠0])+((-125·x·⅟6+-5·x³·⅟6+123·⅟8+25·x²·⅟4+x⁴·⅟24)·[-x+4≠0]·[-x+4≤0]+-4·[-4+x≤0]·[-x+4≠0]·x²+-85·[-4+x≤0]·⅟8+-[-4+x≤0]·[-x+4≠0]·x⁴·⅟24+2·[-4+x≤0]·[-x+4≠0]·x³·⅟3+32·[-4+x≤0]·[-x+4≠0]·x·⅟3+32·[-x+4≤0]·⅟3)·(([-4+x≤0]+[-5+x≤0]·[-x+4≠0])·[-x+4≤0]+[-4+x≤0]·[-x+3≤0]·[-x+4≠0])+((-3·[-2+x≠0]·[-3+x≤0]·⅟2+-3·[-2+x≤0]·⅟2)·[-x+2≤0]+-3·[-2+x≠0]·[-2+x≤0]·[-x+1≤0]·⅟2)·((-x²·⅟2+-⅟2+x)·[-2+x≠0]·[-x+2≤0]+-[-2+x≤0]·⅟2+2·[-x+2≤0]+[-2+x≠0]·[-2+x≤0]·x²·⅟2)+((-3·x²·⅟2+-x⁴·⅟4+-⅟4+x+x³)·[-2+x≠0]·[-x+2≤0]+-[-2+x≤0]·⅟4+4·[-x+2≤0]+[-2+x≠0]·[-2+x≤0]·x⁴·⅟4)·((-[-2+x≠0]·[-3+x≤0]·⅟3+-[-2+x≤0]·⅟3)·[-x+2≤0]+-[-2+x≠0]·[-2+x≤0]·[-x+1≤0]·⅟3)+((-3·x²·⅟2+-x⁴·⅟4+-⅟4+x+x³)·[-x+1≠0]·[-x+1≤0]+[-1+x≤0]·[-x+1≠0]·x⁴·⅟4+[-x+1≤0]·⅟4)·(([-2+x≤0]·[-x+1≠0]·⅟6+[-x+1=0]·⅟6)·[-x+1≤0]+[-1+x≤0]·[-x+1≠0]·[-x≤0]·⅟6)+((-3·x·⅟2+-x³·⅟3+19·⅟24+x²+x⁴·⅟24)·[-2+x≠0]·[-x+2≤0]+-5·[-2+x≤0]·⅟24+-[-2+x≠0]·[-2+x≤0]·x²·⅟4+-[-2+x≠0]·[-2+x≤0]·x⁴·⅟24+[-2+x≠0]·[-2+x≤0]·x³·⅟6+[-2+x≠0]·[-2+x≤0]·x·⅟3+[-x+2≤0]·⅟3)·(([-2+x≠0]·[-3+x≤0]+[-2+x≤0])·[-x+2≤0]+[-2+x≠0]·[-2+x≤0]·[-x+1≤0])+((-x+-x³·⅟3+x²+⅟3)·[-2+x≠0]·[-x+2≤0]+-[-2+x≤0]·⅟3+8·[-x+2≤0]·⅟3+[-2+x≠0]·[-2+x≤0]·x³·⅟3)·((3·[-2+x≠0]·[-3+x≤0]·⅟2+3·[-2+x≤0]·⅟2)·[-x+2≤0]+3·[-2+x≠0]·[-2+x≤0]·[-x+1≤0]·⅟2)+((-x+1)·[-2+x≠0]·[-x+2≤0]+-[-2+x≤0]+2·[-x+2≤0]+[-2+x≠0]·[-2+x≤0]·x)·(([-2+x≠0]·[-3+x≤0]·⅟3+[-2+x≤0]·⅟3)·[-x+2≤0]+[-2+x≠0]·[-2+x≤0]·[-x+1≤0]·⅟3)+((-x+1)·[-x+3≠0]·[-x+3≤0]+-2·[-3+x≤0]+3·[-x+3≤0]+[-3+x≤0]·[-x+3≠0]·x)·(([-3+x≤0]·⅟3+[-4+x≤0]·[-x+3≠0]·⅟3)·[-x+3≤0]+[-3+x≤0]·[-x+2≤0]·[-x+3≠0]·⅟3))·[-x≤0]·[x+-y≤0]".dParse);
	//writeln(dDiff("x".dVar,"y".dVar));
	//writeln("(∫dξ₁[-1+-ξ₁+x₃≤0]·[-1+ξ₁≤0]·[-x₃+ξ₁≤0]·[-ξ₁≤0])".dParse);
	/+DExpr bound;
	auto r=(cast(DIvr)"[-1+-ξ₁+x₃≤0]".dParse).getBoundForVar("x₃".dVar,bound);
	writeln(r," ",bound);+/
	//writeln("∫dxδ[-x]·δ[z+-x+-y]".dParse);
	//writeln("∫dyδ[-x+0+-y]·[-y≤0]·[y+-1≤0]".dParse);
	//writeln("∫dxδ[-x+z+-y]·δ[-x]".dParse.simplify(one));
	//writeln(d
	//writeln("!@# ", dDiff(dVar("x"),-dVar("x"),zero));
	//writeln("∫dξ₁((-1+-ξ₁+x)·(-x+2+ξ₁)+(-x+1)·ξ₁+-x+x²·⅟2+ξ₁²·⅟2+⅟2)·[-1+ξ₁≤0]·[-2+-ξ₁+x≠0]·[-2+-ξ₁+x≤0]·[-x+1+ξ₁≤0]·[-ξ₁≤0]".dParse);
	//writeln("∫dξ₁((-1+-ξ₁+x)·(-x+2+ξ₁))·[-1+ξ₁≤0]·[-2+-ξ₁+x≠0]·[-2+-ξ₁+x≤0]·[-x+1+ξ₁≤0]·[-ξ₁≤0]".dParse);
	//writeln("(-1+-ξ₁+x)·(-x+2+ξ₁)".dParse.polyNormalize(dVar("ξ₁")).simplify(one));
	//writeln("(∫dy[-1+y≤0]·[-w+x·y≤0]·[-y≤0]·[x·y≠0]·[x·y≤0]·⅟y)".dParse);
	//writeln("∫dy[-1+z·⅟y≤0]·[-1+y≤0]·[-z·⅟y≤0]·[-y≤0]·[y≠0]·⅟y".dParse);
	//writeln("(∫dξ₁[-1+ξ₁≤0]·[-z+ξ₁≤0]·[-z·⅟ξ₁≤0]·[-ξ₁≤0]·[ξ₁≠0]·⅟ξ₁)".dParse)
	//writeln("(∫dξ₁[-1+ξ₁≤0]·[-z+ξ₁≤0]·[-z·⅟ξ₁≤0]·[-ξ₁≤0]·⅟ξ₁)".dParse);
	//writeln("[((([-1+z≤0]·[-⅟0≤0]+[z≤0]·[⅟0≠0]·[⅟0≤0])·[-⅟0=0]+([-⅟0+z≤0]·[-⅟0≤0]+[-⅟0+z≤0]·[⅟0≠0]·[⅟0≤0])·[⅟0≠0])·[⅟0≤0]+[-1+z≤0]·[-⅟0≤0]·[⅟0≠0])·z+((([-z+1≠0]·[-⅟0≤0]+[-z≠0]·[⅟0≠0]·[⅟0≤0])·[-⅟0=0]+([-z+⅟0≠0]·[-⅟0≤0]+[-z+⅟0≠0]·[⅟0≠0]·[⅟0≤0])·[⅟0≠0])·[⅟0≤0]+[-z+1≠0]·[-⅟0≤0]·[⅟0≠0])·((([-z+1≤0]·[-⅟0≤0]+[-z≤0]·[⅟0≠0]·[⅟0≤0])·[-⅟0=0]+([-z+⅟0≤0]·[-⅟0≤0]+[-z+⅟0≤0]·[⅟0≠0]·[⅟0≤0])·[⅟0≠0])·[⅟0≤0]+[-z+1≤0]·[-⅟0≤0]·[⅟0≠0])·([-⅟0≤0]+[⅟0≠0]·[⅟0≤0]·⅟0)≠0]".dParse);
	//writeln("∫dξ₁([-1+ξ₁≤0]·[-z+ξ₁≤0]·[-z≤0]·[-ξ₁≤0]·[-⅟0+ξ₁≤0]·⅟ξ₁)+∫dξ₁([-1+ξ₁≤0]·[-z+ξ₁≤0]·[-ξ₁+⅟0≠0]·[-ξ₁+⅟0≤0]·[-ξ₁≤0]·[z≤0]·⅟ξ₁)".dParse);

	//writeln("[[-w·⅟z+1≤0]≠0]".dParse);
	//writeln("[-w=0]·[-w·y≠0]".dParse);
	/+SolutionInfo info;
	SolUse usage={caseSplit:true,bound:true};
	writeln(solveFor("-z·⅟ξ₁".dParse,dVar("ξ₁"),zero,usage,info)," ",info.caseSplits);+/
	//writeln("∫dz[-1+-⅟z≤0]·[-1+⅟z≤0]·[z≠0]·⅟(-2·[z²≠0]·[z²≤0]·z²+2·[-z²≤0]·z²)".dParse);
	//writeln("∫dy([-y+2≤0]·⅟2)·e^(-1+-y²·⅟4+y)·⅟√π̅".dParse.simplify(one));
	//writeln("(∫dξ₁(((((((-2557.4741704993198255+629.1897385856640312·ξ₁)·ξ₁+4210.1081976674804537)·ξ₁+-3594.7906656730001487)·ξ₁+1694.9871901131500636)·ξ₁+-436.9879652054199823)·ξ₁+60.1321271299536022)·ξ₁+-5.1644521185101802)·[-1+ξ₁≤0]·[-10·ξ₁+1≤0]·[-w+ξ₁≠0]·[-w·⅟ξ₁≠0]·[-ξ₁+w≤0]·[-ξ₁≤0]·[ξ₁·⅟w≠0]·⅟ξ₁)".dParse);
	//writeln("∫dtmp((∫dξ₁([-1+tmp≤0]·[-10·tmp+1≤0]+[-10+tmp≤0]·[-tmp+1≤0]+-log(ξ₁))·[-tmp+ξ₁≤0]·[-ξ₁+r≠0]·[-ξ₁+r≤0]·[-ξ₁≠0]·[-ξ₁≤0]·⅟ξ₁)·[-1+tmp≤0]·[-tmp≠0]·[-tmp≤0]·log(tmp))".dParse);
	//writeln("∫dtmpfubi1((-(∫dξ₁[-1+ξ₁≤0]·[-ξ₁+tmpfubi1≤0]·[-ξ₁≠0]·[-ξ₁≤0]·log(ξ₁))·log(tmpfubi1)+∫dξ₁[-1+ξ₁≤0]·[-10·ξ₁+1≤0]·[-ξ₁+tmpfubi1≤0]·[-ξ₁≠0]·[-ξ₁≤0]·log(ξ₁))·[-tmpfubi1+r≠0]·[-tmpfubi1+r≤0]·[-tmpfubi1≠0]·[-tmpfubi1≤0]·⅟tmpfubi1)".dParse);
	//import approximate;
	//writeln(dInt("x".dVar,dBounded!"[]"("x".dVar,zero,one)*-approxLog("x".dVar)).simplify(one));
	//writeln("∫dξ₁([-10·r+1≠0]·⅟ξ₁+[-10·r+1≤0]·⅟ξ₁)·[-1+ξ₁≤0]·[-10·ξ₁+1≤0]·[-ξ₁+1≠0]·[-ξ₁≠0]·[-ξ₁≤0]".dParse);
	//writeln("∫dx(log(x)·[-x<0]·[x+-1≤0])".dParse);
	//writeln("∫dx(-log(r)+log(x))·[-1+x≤0]·[-x+r≤0]".dParse);
	//writeln("∫dx([x+-y=0]·[3·y+z=0]·δ[x+-z])".dParse);
	//writeln("(((((((1+ξ₁)·ξ₁+1)·ξ₁+1)·ξ₁+1)·ξ₁+1)·ξ₁+1)·ξ₁+1)·⅟ξ₁".dParse.polyNormalize("ξ₁".dVar));
	//writeln("(∫dξ₁(((((((1+ξ₁)·ξ₁+1)·ξ₁+1)·ξ₁+1)·ξ₁+1)·ξ₁+1)·ξ₁+1)·[-1+ξ₁≤0]·[-10·ξ₁+1≤0]·[-ξ₁+r≤0]·[-ξ₁≠0]·[-ξ₁≤0]·⅟ξ₁)".dParse);
	//writeln("∫dx(∫dy q(x,y))·[x=0]".dParse);
	//writeln("[0.0=0]".dParse);
	//writeln("(∫dξ₁[-ξ₁+3≠0]·[-ξ₁+3≤0]·⅟e^(3·ξ₁))".dParse.simplify(one));
	//writeln("[x=0]·δ[x]".dParse.simplify(one));
	//import approximate;
	//writeln("∫dx log(x)·1/x·[-x<0]·[x+-y≤0]".dParse.simplify(one).killIntegrals().simplify(one));
	//writeln("2^(3/2)+2".dParse.simplify(one));
	//writeln("⅟(2+√2̅)·√2̅".dParse.simplify(one));
	//writeln("⅟2^(3·⅟2)".dParse.simplify(one));
	//writeln("⅟(2·√2̅)·2".dParse.simplify(one));
	import integration,asymptotics;
	//writeln(tryGetAntiderivative(dVar("x"),"(e^(-1000·⅟3+-x²·⅟15+40·x·⅟3)·⅟√3̅0̅)".dParse,one));
	//writeln(tryGetAntiderivative(dVar("x"),"((d/dx)⁻¹[e^(-x²)](-10·⅟3·√3̅0̅+x·⅟√3̅0̅))·e^(-x²·⅟30+20·x·⅟3))".dParse,one));
	//writeln("lim[x→ ∞] (x+x)".dParse.simplify(one));
	//writeln("∫dx((d/dx)⁻¹[e^(-x²)](-10·⅟3·√3̅0̅+x·⅟√3̅0̅))·e^(-x²·⅟30+20·x·⅟3)".dParse);
	//writeln("lim[x→ ∞](((d/dx)⁻¹[e^(-x²)](-10·⅟3·√3̅0̅+x·⅟√3̅0̅))²·e^(1000·⅟3)·√3̅0̅+-(d/dx)⁻¹[e^(-x²)](-20·⅟3·√1̅5̅+x·⅟√1̅5̅)·e^(-x²·⅟30+1000·⅟3+20·x·⅟3)·⅟√2̅)".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞]-(d/dx)⁻¹[e^(-x²)](-20·⅟3·√1̅5̅+ξ₁·⅟√1̅5̅)·e^(-ξ₁²·⅟30+1000·⅟3+20·ξ₁·⅟3)·⅟√2̅".dParse.simplify(one));
	//writeln("lim[x→ ∞](-x²·⅟30+1000·⅟3+20·x·⅟3)".dParse.simplify(one));
	//writeln(growsFasterThan(dVar("x"),-dVar("x")^^(5/2.dℕ),dParse("x·x")));
	//auto anti=tryGetAntiderivative(dVar("z"),"((d/dx)⁻¹[e^(-x²)](-z·⅟√2̅+⅟√2̅)·e^(z²·⅟2)·√2̅+-(d/dx)⁻¹[e^(-x²)](-z·⅟√2̅)·e^(z²·⅟2)·√2̅)·⅟e^(z²·⅟2)·⅟√2̅·⅟√π̅)".dParse,one).antiderivative;
	//writeln("∫dz((d/dx)⁻¹[e^(-x²)](-z·⅟√2̅+⅟√2̅)+-(d/dx)⁻¹[e^(-x²)](-z·⅟√2̅))".dParse.simplify(one));
	//writeln(dLim(dVar("z"),dInf,anti));
	//writeln(dLimSmp(dVar("x"),dInf,anti));
	//writeln(dLimSmp(dVar("ξ₁"),dInf,"-(d/dx)⁻¹[e^(-x²)](-z·⅟√2̅)·ξ₁·⅟√π̅".dParse));
	//writeln((-2)^^(one/2));
	//writeln("lim[ξ₁ → -∞](d/dx)⁻¹[e^(-x²)](-20+ξ₁·⅟5)·e^(-ξ₁²·⅟50+200+4·ξ₁)·⅟√5̅0̅".dParse.simplify(one));
	//writeln("lim[x → -∞]e^(-x²·⅟50+200+4·x)".dParse.simplify(one));
	//writeln("lim[x→ -∞]-(x²·⅟50)".dParse.simplify(one));
	//writeln("lim[x→ -∞] x²".dParse.simplify(one));
	//writeln("(lim[ξ₁ → -∞]((d/dx)⁻¹[e^(-x²)](-20+ξ₁·⅟5)·5·e^(-ξ₁²·⅟50+200+4·ξ₁)·⅟√5̅0̅))".dParse.simplify(one));
	//writeln("(lim[x → ∞]e^((1160·⅟161+2·x·⅟105)·y+-x²·⅟42+11000·⅟161+20·x·⅟7+y²·⅟483))".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞](-ξ₁²·⅟42+20·ξ₁·⅟7+2·y·ξ₁·⅟105+y²·⅟483)".dParse.simplify(one));
	//writeln(asymptoticNormalize(dVar("tmp"),"20·tmp·⅟7+2·tmp·y·⅟105".dParse));

	//writeln("∫dξ₁(((-2+-2·[-1+ξ₁≤0])·ξ₁+1+[-1+ξ₁≤0])·(1+[-1+ξ₁≤0])·[-1+2·ξ₁≤0]·[-ξ₁+1≤0]+((-1+-[-1+ξ₁≤0])·ξ₁+⅟2+[-1+ξ₁≤0]·⅟2)·(2+2·[-1+ξ₁≤0])·[-1+2·ξ₁≤0]·[-ξ₁+1≤0]+((-[-3+2·ξ₁=0]·⅟2+-⅟2+ξ₁)·(1+[-3+2·ξ₁≤0])+-⅟2+-[-3+2·ξ₁≤0]·⅟2)·[-1+ξ₁≤0]·[-2·ξ₁+3≤0]+((1+[-1+ξ₁≤0])·ξ₁+-⅟2+-[-1+ξ₁≤0]·⅟2)·(4+4·[-1+ξ₁≤0])·[-1+2·ξ₁≤0]·[-ξ₁+1≤0]+(-3·[-ξ₁+2=0]+-3+3)·([-2+ξ₁≤0]+1)·[-1+2·ξ₁≤0]·[-ξ₁+2≤0])".dParse.simplify(one)); // TODO!

	//writeln("∫dx⅟2·[-x≤0]·[x+-1≤0]·[x+-z≤0]·[z+-x+-2≤0]".dParse.simplify(one));
	//writeln("[x+y+z+-5≤0]·[5+-(x+y)≤0]·[z≠0]·[-z≤0]".dParse.simplify(one)); // TODO

	//writeln("∫dξ₁[-1+ξ₁=0]·q(ξ₁)".dParse.substituteFun("q".dFunVar,"δ[1+-x]".dParse,["x".dVar]).simplify(one));
	//auto e="∫dx[-1+-y≤0]·[-1+x≤0]·[-1+y≤0]·[-x≤0]·[y≠0]·δ[-z+x·⅟y]·⅟2".dParse;
	//writeln(dInt("y".dVar,e).simplify(one));
	/+auto e1="(((∫dξ₁[-1+-ξ₁≤0]·[-ξ₁+⅟z≠0]·[-ξ₁+⅟z≤0]·[ξ₁≠0]·[ξ₁≤0]·⅟(-2·[⅟ξ₁≤0]·⅟ξ₁+2·[-⅟ξ₁≤0]·⅟ξ₁))·[z≤0]+(∫dξ₁[-1+-ξ₁≤0]·[-⅟z+ξ₁≤0]·[ξ₁≠0]·[ξ₁≤0]·⅟(-2·[⅟ξ₁≤0]·⅟ξ₁+2·[-⅟ξ₁≤0]·⅟ξ₁))·[-z≤0])·[-z≠0]+(∫dξ₁[-1+-ξ₁≤0]·[ξ₁≠0]·[ξ₁≤0]·⅟(-2·[⅟ξ₁≤0]·⅟ξ₁+2·[-⅟ξ₁≤0]·⅟ξ₁))·[-z=0])·[z≤0]".dParse;
	auto e2="(((∫dξ₁[-1+ξ₁≤0]·[-ξ₁+⅟z≠0]·[-ξ₁+⅟z≤0]·[-ξ₁≤0]·[ξ₁≠0]·⅟(-2·[⅟ξ₁≤0]·⅟ξ₁+2·[-⅟ξ₁≤0]·⅟ξ₁))·[z≤0]+(∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·[-⅟z+ξ₁≤0]·[ξ₁≠0]·⅟(-2·[⅟ξ₁≤0]·⅟ξ₁+2·[-⅟ξ₁≤0]·⅟ξ₁))·[-z≤0])·[-z≠0]+(∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·[ξ₁≠0]·⅟(-2·[⅟ξ₁≤0]·⅟ξ₁+2·[-⅟ξ₁≤0]·⅟ξ₁))·[-z=0])·[-z≤0]".dParse;
	writeln(dIntSmp("z".dVar,e2));+/
	//writeln("lim[ξ₁ → ∞](d/dx)⁻¹[e^(-x²)](-skill1·⅟√3̅0̅+ξ₁·⅟√3̅0̅)·(d/dx)⁻¹[e^(-x²)](-skill2·⅟√3̅0̅+ξ₁·⅟√3̅0̅)·e^(skill2²·⅟30)·√3̅0̅".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞](d/dx)⁻¹[e^(-x²)](-skill1·⅟√3̅0̅+ξ₁·⅟√3̅0̅)".dParse.simplify(one));
	//writeln("lim[tmp → ∞](tmp·⅟√3̅0̅)".dParse.simplify(one));
	//writeln("∫dx (d/dx)⁻¹[e^(-x²)](a·x+b)·[x≤y]".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞]((d/dx)⁻¹[e^(-x²)](ξ₁·⅟a)·ξ₁·⅟a+-⅟e^(ξ₁²·⅟a²))·⅟a".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞](-⅟e^(ξ₁²·⅟a²))·⅟a".dParse.simplify(one));
	//writeln("lim[ξ₁ → -∞]((d/dx)⁻¹[e^(-x²)](-10·⅟3·√3̅0̅+ξ₁·⅟√3̅0̅))²·e^(1000·⅟3)·√3̅0̅+-(d/dx)⁻¹[e^(-x²)](-20·⅟3·√1̅5̅+ξ₁·⅟√1̅5̅)·e^(-ξ₁²·⅟30+1000·⅟3+20·ξ₁·⅟3)·⅟√2̅".dParse.simplify(one));
	//writeln("lim[ξ₁ → -∞](f(ξ₁)+g(ξ₁))".dParse.simplify(one));
	//writeln("lim[ξ₁ → -∞](((d/dx)⁻¹[e^(-x²)](-10·⅟3·√3̅0̅+ξ₁·⅟√3̅0̅))²·e^(1000·⅟3)·√3̅0̅+-(d/dx)⁻¹[e^(-x²)](-20·⅟3·√1̅5̅+ξ₁·⅟√1̅5̅)·e^(-ξ₁²·⅟30+1000·⅟3+20·ξ₁·⅟3)·⅟√2̅)".dParse.simplify(one));
	//writeln("∫da(-(d/dx)⁻¹[e^(-x²)](-10·⅟3·√3̅0̅+a·⅟√3̅0̅)·e^(1000·⅟3)·⅟√3̅0̅+e^(1000·⅟3)·⅟√3̅0̅·√π̅)".dParse.simplify(one));
	//writeln("∫da [a≤b]·e^(-a²·⅟2+-b²·⅟2)".dParse.simplify(one));
	//writeln("∫db(d/dx)⁻¹[e^(-x²)](b·⅟√2̅)·⅟e^(b²·⅟2)·√2̅".dParse.simplify(one));
	//writeln("∫dx e^(-(x/√2̅)²)·[x≤b]".dParse.simplify(one));
	//writeln(dDiff("b".dVar,"(d/dx)⁻¹[e^(-x²)](b·⅟√2̅)".dParse));
	//writeln("∫dx e^(-x²)·x²·[x≤y]·[-y≤x]".dParse.simplify(one)); // TODO
	//writeln("∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·ξ₁⁸·⅟e^(ξ₁·⅟2)".dParse.simplify(one));
	//writeln("(x-y)·[x=y]".dParse.simplify(one));
	//writeln("(1+⅟(-x+1))".dParse.simplify(one));
	//writeln("[2·√2̅+√3̅=0]".dParse.simplify(one));
	import approximate;
	//writeln("(∫dξ₁(∫dξ₂(∫dξ₃(-(∫dξ₄(∫dξ₅(d/dx)⁻¹[e^(-x²)](-ξ₄·⅟√3̅0̅+ξ₅·⅟√3̅0̅)·e^(-ξ₅²·⅟30+ξ₂·ξ₅·⅟15))·e^(-ξ₄²·⅟12+10·ξ₄+ξ₃·ξ₄·⅟15))·⅟20·√3̅0̅+3·e^(300+4·ξ₃+ξ₂²·⅟30+ξ₃²·⅟75)·π^(3·⅟2)·⅟2·√1̅2̅)·(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₃·⅟√3̅0̅)·⅟e^(ξ₃²·⅟30))·(∫dξ₃(d/dx)⁻¹[e^(-x²)](-ξ₂·⅟√3̅0̅+ξ₃·⅟√3̅0̅)·e^(-ξ₃²·⅟30+ξ₁·ξ₃·⅟15))·e^(-ξ₂²·⅟12+10·ξ₂))·e^(-ξ₁²·⅟12+10·ξ₁))".dParse.simplify(one).killIntegrals());
	//writeln("(∫dξ₃(d/dx)⁻¹[e^(-x²)](-ξ₂·⅟√3̅0̅+ξ₃·⅟√3̅0̅)·[0≤ξ₃]·[ξ₃≤1])".dParse.killIntegrals());
	//e^(-ξ₃²·⅟30+ξ₁·ξ₃·⅟15)
	//writeln("(∫dξ₃(d/dx)⁻¹[e^(-x²)](-ξ₂·⅟√3̅0̅+ξ₃·⅟√3̅0̅)·e^(-ξ₃²·⅟30+ξ₁·ξ₃·⅟15))".dParse.killIntegrals());
	//writeln("∫dx((d/dx)⁻¹[e^(-x²)](x)·x·[0≤x]·[x≤y])".dParse.killIntegrals());
	//writeln("(∫dξ₁(∫dξ₂(∫dξ₃(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₃·⅟√3̅0̅)·(∫dξ₄(d/dx)⁻¹[e^(-x²)](-ξ₂·⅟√3̅0̅+ξ₄·⅟√3̅0̅)·e^((20·⅟7+2·ξ₃·⅟105)·ξ₄+-ξ₄²·⅟42))·e^(-ξ₃²·⅟42+20·ξ₃·⅟7))·(∫dξ₃(d/dx)⁻¹[e^(-x²)](-ξ₂·⅟√3̅0̅+ξ₃·⅟√3̅0̅)·e^(-ξ₃²·⅟30+ξ₁·ξ₃·⅟15))·e^(-ξ₂²·⅟20+10·ξ₂))·e^(-ξ₁²·⅟12+10·ξ₁))".dParse);
	//writeln("(∫dξ₄(d/dx)⁻¹[e^(-x²)](-ξ₂·⅟√3̅0̅+ξ₄·⅟√3̅0̅)·e^((20·⅟7+2·ξ₃·⅟105)·ξ₄+-ξ₄²·⅟42))".dParse.killIntegrals());
	//writeln("(∫dξ₁[-ξ₁+ξ₂≠0]·[-ξ₁+ξ₂≤0]·[ξ₁≤0]·e^((20·⅟7+2·ξ₃·⅟105)·ξ₁+-ξ₁²·⅟42)·ξ₁²)".dParse.simplify(one));
	//writeln("∫dξ₁(-e^((20·⅟7+2·ξ₃·⅟105)·ξ₁+-ξ₁²·⅟42)·ξ₁²·⅟30+e^((20·⅟7+2·ξ₃·⅟105)·ξ₁+-ξ₁²·⅟42)·ξ₁·ξ₂·⅟15)".dParse.killIntegrals());
	//writeln("(∫dξ₂(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₂·⅟√3̅0̅)·e^(-ξ₂²·⅟50+4·ξ₂))".dParse.killIntegrals());
	//writeln("1/(∫dξ₁(∫dξ₂(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₂·⅟√3̅0̅)·e^(-ξ₂²·⅟50+4·ξ₂))·e^(-ξ₁²·⅟20+10·ξ₁))".dParse.killIntegrals());
	//writeln("(∫dξ₁(-(d/dx)⁻¹[e^(-x²)](-skill1·⅟√3̅0̅+ξ₁·⅟√3̅0̅)·e^(skill1²·⅟30)·⅟600·√3̅0̅+e^(skill1²·⅟30)·⅟600·√3̅0̅·√π̅)·(d/dx)⁻¹[e^(-x²)](-skill1·⅟√3̅0̅+ξ₁·⅟√3̅0̅)·e^(-ξ₁²·⅟30+skill2·ξ₁·⅟15))".dParse.killIntegrals());
	//writeln("(∫dξ₁(∫dξ₂(-(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₂·⅟√3̅0̅)·e^(ξ₁²·⅟30)·⅟600·√3̅0̅+e^(ξ₁²·⅟30)·⅟600·√3̅0̅·√π̅)·(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₂·⅟√3̅0̅)·e^(-ξ₂²·⅟50+4·ξ₂))·e^(-ξ₁²·⅟12+10·ξ₁))".dParse.killIntegrals());
	//writeln("(∫dξ₁(-(d/dx)⁻¹[e^(-x²)](-skill1·⅟√3̅0̅+ξ₁·⅟√3̅0̅)·e^(skill1²·⅟30)·⅟600·√3̅0̅+e^(skill1²·⅟30)·⅟600·√3̅0̅·√π̅)·(d/dx)⁻¹[e^(-x²)](-skill1·⅟√3̅0̅+ξ₁·⅟√3̅0̅)·e^(-ξ₁²·⅟30+skill2·ξ₁·⅟15))·e^(-300+-skill1²·⅟12+-skill2²·⅟12+10·skill1+10·skill2)·⅟(∫dξ₁(∫dξ₂(-(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₂·⅟√3̅0̅)·e^(ξ₁²·⅟30)·⅟600·√3̅0̅+e^(ξ₁²·⅟30)·⅟600·√3̅0̅·√π̅)·(d/dx)⁻¹[e^(-x²)](-ξ₁·⅟√3̅0̅+ξ₂·⅟√3̅0̅)·e^(-ξ₂²·⅟50+4·ξ₂))·e^(-ξ₁²·⅟12+10·ξ₁))·⅟√1̅2̅·⅟√π̅".dParse.killIntegrals());
	//writeln("(∫dξ₁(-4·⅟3+4·e^(-20·ξ₁²+-600)·⅟3)·[ξ₁≤0]·e^(-ξ₁²·⅟50+4·ξ₁)·ξ₁)".dParse.killIntegrals());
	//writeln("∫dξ₁(-4·[ξ₁≤0]·e^(-ξ₁²·⅟50+4·ξ₁)·ξ₁)".dParse.killIntegrals());
	//writeln("∫dξ₁(e^(-ξ₁²·⅟50+4·ξ₁)·ξ₁)".dParse.simplify(one));
	//writeln("lim[tmp→ -∞](-100·√5̅0̅+-50·tmp·√5̅0̅)·(d/dx)⁻¹[e^(-x²)](2·√5̅0̅+tmp·√5̅0̅)".dParse.simplify(one));
	//writeln("(∫dξ₁(d/dx)⁻¹[e^(-x²)](-skillB·⅟√3̅0̅+ξ₁·⅟√3̅0̅)·e^(-ξ₁²·⅟30+skillC·ξ₁·⅟15))".dParse.simplify(one));
	//writeln("(∫dξ₁[ξ₁≤0]·e^(-ξ₁²·⅟50+4·ξ₁)·ξ₁²)".dParse.simplify(one));
	//auto r=dDiff("x".dVar,dIntSmp("tmp".dVar,"[tmp≤x]".dParse*"(d/dx)⁻¹[e^(-x²)](-2·√5̅0̅+tmp·⅟√5̅0̅)".dParse)).simplify(one); // TODO: simplify better!
	//writeln(r);
	//auto r=dIntSmp("tmp".dVar,"[tmp≤x]".dParse*"(d/dx)⁻¹[e^(-x²)](-2·√5̅0̅+tmp·⅟√5̅0̅)".dParse);
	//matlabPlot(r.toString(),"x");
	//writeln(dDiff("x".dVar,"1/2·(x·(2·(d/dx)⁻¹[e^(-x²)](x)-1)+e^(-x²)+x)".dParse).simplify(one));
	//writeln(dDiff("x".dVar,dIntSmp("y".dVar,"(d/dx)⁻¹[e^(-x²)](a·y+b)·[y≤x]".dParse)).simplify(one));
	//writeln(dDiff("x".dVar,"⅟a·((a·x+b)·(d/dx)⁻¹[e^(-x²)](a·x+b)+e^(-(a·x+b)²)/2)".dParse).simplify(one));
	//writeln(dDiff("x".dVar,"(d/dx)⁻¹[e^(-x²)](x)·x-e^(-x²))".dParse));
	//auto r="∫dy[0≤y]·[y≤x]·y³·e^(-y²)".dParse.simplify(one);
	//auto r="x²·e^(-x²)".dParse;
	//r=r.polyNormalize("x".dVar).simplify(one);
	//writeln(r);
	//writeln(dDiff("x".dVar,"-(d/dx)⁻¹[e^(-x²)](x)·24·x⁵·⅟11+-(d/dx)⁻¹[e^(-x²)](x)·50·x³·⅟11+-35·x⁴·⅟22·⅟e^(x²)+-60·x²·⅟11·⅟e^(x²)+-60·⅟11·⅟e^(x²)+60·⅟11".dParse).simplify(one));
	//writeln(dDiff("x".dVar,tryGetAntiderivative("x".dVar,"x²·e^(-x²)".dParse,one).antiderivative).simplify(one));
	//matlabPlot(r.toString(Format.matlab),"x");
	//writeln("∫dx(d/dx)⁻¹[e^(-x²)](x)·x".dParse.simplify(one));
	//writeln("(∫dξ₁ ξ₁²·⅟e^(ξ₁²·⅟200))".dParse.simplify(one));// TODO: improve limit evaluation
	//writeln("1/(-2·a⁴·⅟3+2·a)·∫dx (1-a·x²)·[-a≤x]·[x≤a]".dParse.simplify("[0≤a]".dParse));
	//writeln("∫dx (1-a²·(x-b/a)²)·[-a²≤x-b/a]·[x-b/a≤a²]".dParse.simplify("[0≤a]".dParse));
	//writeln("3/(4·5^(1/2))·∫dx (1-x²/5)·x²·[-5^(1/2)≤x]·[x≤5^(1/2)]".dParse.simplify(one)); // TODO: simplify this better
	//writeln((-dVar("x"))^^(one/2));
	//writeln("(∫dξ₁[-1+√ξ̅₁̅≤0]·[-ξ₁≤0]·[ξ₁≠0]·⅟(-2·[√ξ̅₁̅≠0]·[√ξ̅₁̅≤0]·√ξ̅₁̅+2·√ξ̅₁̅)+∫dξ₁[-1+√ξ̅₁̅≤0]·[-ξ₁≤0]·⅟(-2·[√ξ̅₁̅≠0]·[√ξ̅₁̅≤0]·√ξ̅₁̅+2·√ξ̅₁̅))".dParse);
	//writeln("-2·[√ξ̅₁̅≠0]·[√ξ̅₁̅≤0]·√ξ̅₁̅+2·√ξ̅₁̅".dParse.simplify("[√ξ̅₁̅≤0]".dParse));
	//writeln("[√ξ̅₁̅≤0]".dParse.simplify(one));
	//writeln(DExpr.simplifyMemo);
	//writeln("(2·x·π)^(⅟2)".dParse);
	/*writeln(linearizeConstraints("[1/x+1≤0]".dParse,"x".dVar));
	writeln(linearizeConstraints("[x²≤1]".dParse,"x".dVar));
	writeln(linearizeConstraints("[-x²=1]".dParse,"x".dVar));
	writeln(linearizeConstraints("[x²=1]·[x≤0]".dParse,"x".dVar).polyNormalize("x".dVar));
	writeln(linearizeConstraints("[x³=-1]".dParse,"x".dVar)); 
	writeln(linearizeConstraints("[x³≤1]".dParse,"x".dVar)); 
	writeln(linearizeConstraints("[x³≤-1]".dParse,"x".dVar));
	writeln(linearizeConstraints("[x²+x+1≤10]".dParse,"x".dVar));
	writeln(linearizeConstraints("[-1-x²≤0]".dParse,"x".dVar));
	writeln(linearizeConstraints("[-1-x-x²≤0]".dParse,"x".dVar));
	writeln(linearizeConstraints("[x²=0]".dParse,"x".dVar));
	writeln("(-3)^(1/2)".dParse);*/
	//writeln(linearizeConstraints("[1/10-1/(x²+x+1)≤0]".dParse,"x".dVar));
	//writeln("[1/10-1/(x²+x+1)≤0]".dParse);
	//writeln("[-1/10+1/(x²+x+1)≤0]".dParse);
	//writeln(linearizeConstraints("[-1/10+1/(x²+x+1)≤0]".dParse,"x".dVar));
	//writeln(splitPlusAtVar("-1+10·⅟(1+x+x²)".dParse,"x".dVar));
	//writeln(linearizeConstraints("[(x-1)^2<=0]".dParse,"x".dVar));
	//writeln(linearizeConstraints("[(x-1)^2!=0]".dParse,"x".dVar));
	//writeln(linearizeConstraints("[y*x^2+x<=0]".dParse,"x".dVar).polyNormalize("x".dVar).simplify(one)); // TODO: check correctness
	//writeln(linearizeConstraints("[y*x^2+x=0]".dParse,"x".dVar).polyNormalize("x".dVar).simplify(one));
	//writeln(linearizeConstraints("[y*x^2+x!=0]".dParse,"x".dVar).polyNormalize("x".dVar).simplify(one));
	//writeln(linearizeConstraints("[a*x^2+b*x+c=0]".dParse,"x".dVar));
	//writeln(linearizeConstraints("[a*x^2+b*x+c<=0]".dParse,"x".dVar));
	//writeln("[x^2+y^2=1]*[x^2+y^2=2]".dParse.simplify(one)); // TODO: this should be simplified!
	//writeln(linearizeConstraints("[x^2+y^2=1]".dParse,"x".dVar));
	//writeln(linearizeConstraints("δ[(x-1)*(2*x-4)]".dParse,"x".dVar));
	//writeln(linearizeConstraints("[1/(x^2+x+1)<=10]".dParse,"x".dVar));
	//writeln(linearizeConstraints("[x^2+x+1<=1]".dParse,"x".dVar));
	//writeln(linearizeConstraints("[x^2+x+1<=0]".dParse,"x".dVar));
	//writeln(linearizeConstraints("δ[x/(1+x)]".dParse,"x".dVar)); // TODO: this can actually work. generalize!
	//writeln(linearizeConstraints("δ[x^2-25]".dParse,"x".dVar));
	//writeln(linearizeConstraints("δ[-c+100000032000004800000448000029120001397760051251201464320032947200585728008200192089456640745472004587520019660800052428800065536·c₁¹⁰⁰⁰⁰⁰⁰⁰⁰⁰⁰⁰⁰⁰⁰⁰⁰]·⅟π".dParse,"c₁".dVar));
	//writeln("∫dx [0≤x]·[x≤y]·x^100000000000000".dParse.simplify(one));
	//writeln("∫dx e^(-a·x^2+b·x+c)·[0≤x]·[x≤k]".dParse.simplify(one));
	//writeln("∫dy(∫dξ₁[-ξ₁≤0]·[ξ₁≠0]·e^(-y²·⅟2·⅟ξ₁+-ξ₁²·⅟2)·⅟√ξ̅₁̅)".dParse.simplify(one));
	//writeln(linearizeConstraints("δ[-x+u·y]".dParse,"y".dVar).simplify(one));
	//writeln(linearizeConstraints("[y≠0]·δ[x·⅟y]".dParse,"y".dVar).simplify(one));
	//writeln("∫dy[y≠0]·δ[x·⅟y]".dParse); // TODO: meaning?
	//writeln("∫dx ((([-x+√-̅y̅²̅+̅1̅≤0]·⅟4+[x+√-̅y̅²̅+̅1̅≤0]·⅟4)·[-1+y²≤0]·[-y²+1≠0]+[-y²+1≤0]·⅟4)·([-1+y²≤0]·[-√-̅y̅²̅+̅1̅+x≠0]·[x+√-̅y̅²̅+̅1̅≠0]+[-y²+1≠0]·[-y²+1≤0])·δ[z]+[-1+y²≤0]·[-x+-√-̅y̅²̅+̅1̅≤0]·[-√-̅y̅²̅+̅1̅+x≤0]·δ[-z+1]·⅟4)·[-1+-x≤0]·[-1+-y≤0]·[-1+x≤0]·[-1+y≤0]".dParse.simplify(one).polyNormalize("y".dVar));
	//writeln("∫dy [-1+-y≤0]·[-1+y²≤0]·[-1+y≤0]·[-1+√-̅y̅²̅+̅1̅≤0]·δ[-z+1]·⅟2·√-̅y̅²̅+̅1̅".dParse.simplify(one));
	//writeln("∫dy [-1+-y≤0]·[-1+y≤0]·[-y²+1≤0]·δ[z]·⅟2".dParse.simplify(one));
	/+auto larger="δ[z]·[[x²+y²<=1]=0]·[0≤x]·[0≤y]·[x≤1]·[y≤1]".dParse.simplify(one);
	auto lin=linearizeConstraints(larger,"x".dVar).simplify(one);
	writeln(lin.polyNormalize("x".dVar));
	auto ii=dInt("x".dVar,lin).simplify(one);
	writeln(ii);
	auto jj=dInt("y".dVar,ii).simplify(one);
	writeln(jj);+/
	//auto x0="∫dx ((([-x+√-̅y̅²̅+̅1̅≤0]·⅟4+[x+√-̅y̅²̅+̅1̅≤0]·⅟4)·[-1+y²≤0]·[-y²+1≠0]+[-y²+1≤0]·⅟4)·([-1+y²≤0]·[-√-̅y̅²̅+̅1̅+x≠0]·[x+√-̅y̅²̅+̅1̅≠0]+[-y²+1≠0]·[-y²+1≤0])·δ[z]+[-1+y²≤0]·[-x+-√-̅y̅²̅+̅1̅≤0]·[-√-̅y̅²̅+̅1̅+x≤0]·δ[-z+1]·⅟4)·[-1+-x≤0]·[-1+-y≤0]·[-1+x≤0]·[-1+y≤0]".dParse.simplify(one).polyNormalize("y".dVar);
	//auto dz="-[-1+-y≤0]·[-1+-√-̅y̅²̅+̅1̅=0]·[-1+y²≤0]·[-1+y≤0]·[-y²+1≠0]·δ[z]·⅟2·√-̅y̅²̅+̅1̅+-[-1+-y≤0]·[-1+y²≤0]·[-1+y≤0]·[-1+√-̅y̅²̅+̅1̅≤0]·[-y²+1≠0]·[1+√-̅y̅²̅+̅1̅≠0]·δ[z]·⅟2·√-̅y̅²̅+̅1̅+3·[-1+-y≤0]·[-1+y²≤0]·[-1+y≤0]·[-y²+1≠0]·[1+√-̅y̅²̅+̅1̅≠0]·[1+√-̅y̅²̅+̅1̅≤0]·δ[z]·⅟2+[-1+-y≤0]·[-1+-√-̅y̅²̅+̅1̅=0]·[-1+y²≤0]·[-1+y≤0]·[-y²+1≠0]·δ[z]·⅟2+[-1+-y≤0]·[-1+y²≤0]·[-1+y≤0]·[-1+√-̅y̅²̅+̅1̅≤0]·[-y²+1≠0]·[1+√-̅y̅²̅+̅1̅≠0]·δ[z]·⅟2+[-1+-y≤0]·[-1+y≤0]·[-y²+1≤0]·δ[z]·⅟2".dParse.simplify(one);
	//auto x1=linearizeConstraints(dz,"y".dVar);
	//writeln(dInt("y".dVar,x1).simplify(one));
	//writeln(linearizeConstraints("[-1+-y≤0]·[-1+y²≤0]·[-1+y≤0]·[-1+√-̅y̅²̅+̅1̅≤0]·[-y²+1≠0]·[1+√-̅y̅²̅+̅1̅≠0]".dParse,"y".dVar));
	//auto xyz="([-1+x²+y²≤0]·δ[-z+1]·⅟4+[-x²+-y²+1≠0]·[-x²+-y²+1≤0]·δ[z]·⅟4)·[-1+-x≤0]·[-1+-y≤0]·[-1+x≤0]·[-1+y≤0]".dParse;
	//auto xyz="([-x²+-y²+1≠0]·[-x²+-y²+1≤0]·δ[z]·⅟4)·[-1+-x≤0]·[-1+-y≤0]·[-1+x≤0]·[-1+y≤0]".dParse;
	//auto xyz="[-1<=x]*[x<=1]*[-1<=y]*[y<=1]*[-x²+-y²+1≤0]".dParse;
	//writeln(xyz.linearizeConstraints("x".dVar).simplify(one));
	//auto yz=dIntSmp("x".dVar,xyz);
	//auto yz="(([-1+-√-̅y̅²̅+̅1̅≠0]·[1+√-̅y̅²̅+̅1̅≤0]·⅟2)·(-[-1+-√-̅y̅²̅+̅1̅≠0]·[-1+-√-̅y̅²̅+̅1̅≤0]·√-̅y̅²̅+̅1̅+1+[1+√-̅y̅²̅+̅1̅≤0])·[-1+y²≤0]·[-y²+1≠0]+([-1+y²≤0]·⅟2+[-y²+1≠0]·⅟2)·[-y²+1≤0])·[-1+-y≤0]·[-1+y≤0]·δ[z]".dParse;
	//auto yz="(((2·[-1+-√-̅y̅²̅+̅1̅≠0]·[-1+√-̅y̅²̅+̅1̅≤0]+2·[1+√-̅y̅²̅+̅1̅=0])·[-1+-√-̅y̅²̅+̅1̅≤0]+2·[-1+-√-̅y̅²̅+̅1̅≠0]·[1+√-̅y̅²̅+̅1̅≤0])·(-[-1+-√-̅y̅²̅+̅1̅≠0]·[-1+-√-̅y̅²̅+̅1̅≤0]·√-̅y̅²̅+̅1̅+1+[1+√-̅y̅²̅+̅1̅≤0])·[-1+y²≤0]·[-y²+1≠0]+2·[-y²+1≤0])·[-1+-y≤0]·[-1+y≤0]".dParse;
	//auto yz="[-1≤√-̅y̅²̅+̅1̅]".dParse;
	//writeln(yz.linearizeConstraints("y".dVar));
	//writeln(dIntSmp("y".dVar,yz));
	//auto e="δ[-a₁+⅟k]".dParse;
	//auto lin=e.linearizeConstraints("k".dVar);
	//writeln(dIntSmp("k".dVar,e*"[0<=k]*[k<=x]".dParse));
	//writeln("[a+⅟k≠0]".dParse.linearizeConstraints("k".dVar));
	//writeln("[a+⅟b<=0]".dParse.linearizeConstraints("b".dVar).polyNormalize("a".dVar).simplify(one));
	//writeln("[-a-⅟b<=0]".dParse.linearizeConstraints("b".dVar).polyNormalize("a".dVar).simplify(one));
	/*import dparse;
	auto good="(2·δ[-a₂+⅟k]·⅟3+δ[a₂]·⅟3)·(2·δ[a₁]·⅟3+δ[-a₁+⅟k]·⅟3)·(δ[-1+k]·⅟3+δ[-2+k]·⅟3+δ[-3+k]·⅟3)·[-1+a₁+a₂+⅟k≠0]·[k≠0]·δ[-a₃+⅟k]"
	auto middle="(2·[a₂≠0]·δ[-⅟a₂+k]·⅟3·⅟a₂²+δ[a₂]·⅟3)·(2·δ[a₁]·⅟3+[a₁≠0]·δ[-⅟a₁+k]·⅟3·⅟a₁²)·(δ[-1+k]·⅟3+δ[-2+k]·⅟3+δ[-3+k]·⅟3)·[-1+a₁+a₂+⅟k≠0]·[a₃≠0]·[k≠0]·δ[-⅟a₃+k]·⅟a₃²";
	auto bad="(2·[a₂≠0]·δ[-⅟a₂+k]·⅟3·⅟a₂²+δ[a₂]·⅟3)·(2·δ[a₁]·⅟3+[a₁≠0]·δ[-⅟a₁+k]·⅟3·⅟a₁²)·(δ[-1+k]·⅟3+δ[-2+k]·⅟3+δ[-3+k]·⅟3)·[-a₁+-a₂+1≠0]·[-⅟(-a₁+-a₂+1)+k≠0]·[a₃≠0]·[k≠0]·δ[-⅟a₃+k]·⅟a₃²";
	if(nexpr.toString() == good){
		writeln("!!!");
		nexpr=middle.dParse;
	}*/
	//auto d="(δ[-x+1]·⅟2+δ[x]·⅟2)·δ[-y+x²]".dParse;
	//writeln(d.linearizeConstraints("x".dVar));
	//auto d="δ[x^(1/2)-y]".dParse;
	/*auto x="δ[x-y²]".dParse;
	writeln("orig: ",x);
	auto d=x.linearizeConstraints("y".dVar).simplify(one);
	writeln("liny: ",d);
	auto k=d.linearizeConstraints("x".dVar).simplify(one);
	writeln("linx: ",k);
	auto j=k.linearizeConstraints("y".dVar).simplify(one);
	writeln("liny: ",j);
	writeln("linx: ",j.linearizeConstraints("x".dVar).simplify(one)); // TODO: implement suitable simplification rules such that this is δ[x-y²] and d=j*/
	/*auto x="δ[z-x*y]".dParse;
	writeln(x.linearizeConstraints("x".dVar));
	writeln(dIntSmp("x".dVar,x*"f(x,y,z)".dParse));*/
	/*auto x="δ[x/y]".dParse;
	writeln(x.linearizeConstraints("x".dVar));
	writeln(x.linearizeConstraints("y".dVar));
	writeln(dIntSmp("x".dVar,x*"f(x,y)*[y!=0]".dParse).simplify(one));*/
	//writeln("([6+√1̅2̅≤0]·[2+√1̅2̅≤0])^-1)".dParse);
	//writeln("δ[y-x·(x+1)]".dParse.linearizeConstraints("x".dVar).simplify(one));
	//writeln("Msum(Weight(x,Msum(Weight(1/216*x^3,Msum(Weight(1/3*x,Ret(x)),Weight(5/12-5/12*x,Ret(x)))),Weight(-1/27*x^2*(-1+x),Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))),Weight(-1/144*x^2*(-1+x),Msum(Weight(1/3*x,Ret(x)),Weight(5/12-5/12*x,Ret(x)))),Weight(1/18*x*(-1+x)^2,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))),Weight(1/384*x*(-1+x)^2,Msum(Weight(1/3*x,Ret(x)),Weight(5/12-5/12*x,Ret(x)))),Weight(-1/48*(-1+x)^3,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))),Weight(1-x,Msum(Weight(1/216*x^3,Msum(Weight(1/3*x,Ret(x)),Weight(5/12-5/12*x,Ret(x)))),Weight(-1/36*x^2*(-1+x),Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))),Weight(-1/144*x^2*(-1+x),Msum(Weight(1/3*x,Ret(x)),Weight(5/12-5/12*x,Ret(x)))),Weight(1/24*x*(-1+x)^2,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))),Weight(1/384*x*(-1+x)^2,Msum(Weight(1/3*x,Ret(x)),Weight(5/12-5/12*x,Ret(x)))),Weight(-1/64*(-1+x)^3,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))))".dParse.substituteFun("Msum".dFunVar,"a+b".dParse,["a".dVar,"b".dVar]).substituteFun("Msum".dFunVar,"a".dVar,["a".dVar]).substituteFun("Msum".dFunVar,"a+b+c".dParse,["a".dVar,"b".dVar,"c".dVar]).substituteFun("Weight".dFunVar,"a*b".dParse,["a".dVar,"b".dVar]).substituteFun("Msum".dFunVar,"a+b+c+d".dParse,["a".dVar,"b".dVar,"c".dVar,"d".dVar]).substituteFun("Msum".dFunVar,"a+b+c+d+e".dParse,["a".dVar,"b".dVar,"c".dVar,"d".dVar,"e".dVar]).substituteFun("Msum".dFunVar,"a+b+c+d+k+f".dParse,["a".dVar,"b".dVar,"c".dVar,"d".dVar,"k".dVar,"f".dVar]).polyNormalize("x".dVar).substituteFun("Ret".dFunVar,one,["a".dVar]));
	//writeln("Msum(a,Msum(b,c))".dParse.substituteFun("Msum".dFunVar,"a+b".dParse,["a".dVar,"b".dVar])); // TODO: this should work!
	//writeln("Msum(W(a,Msum(b,c),Msum(a,b,c)),d)".dParse.substituteFun("Msum".dFunVar,"x+y".dParse,["x".dVar,"y".dVar]));
	/*auto e="-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_0₂+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_0₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₂+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₁]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36+-[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_1₂+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₁]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟12+[-1+similarityAll≤0]·[-similarityAll≤0]·similarityAll²·δ[-clicks_0₁+1]·δ[-clicks_0₂+1]·δ[-clicks_0₃+1]·δ[-clicks_1₁+1]·δ[-clicks_1₂+1]·δ[-clicks_1₃+1]·δ[-i+1]·δ[-sim_0₁+1]·δ[-sim_1₁+1]·δ[clicks_0₄]·δ[clicks_0₅]·δ[clicks_1₄]·δ[clicks_1₅]·δ[sim_0₂]·δ[sim_0₃]·δ[sim_0₄]·δ[sim_0₅]·δ[sim_1₂]·δ[sim_1₃]·δ[sim_1₄]·δ[sim_1₅]·⅟36".dParse;
	import std.datetime;
	StopWatch sw;
	sw.start();
	e=e.simplify(one);
	sw.stop();
	writeln(sw.peek().to!("seconds",double));
	dw(e);*/
	/*auto expr="((-mean₁·⅟3141+1)·δ[answer₁]+mean₁·δ[-answer₁+1]·⅟3141)·((-mean₁·⅟3141+1)·δ[answer₃]+mean₁·δ[-answer₃+1]·⅟3141)·((-mean₁·⅟3141+1)·δ[answer₄]+mean₁·δ[-answer₄+1]·⅟3141)·((-mean₂·⅟2718+1)·δ[answer₅]+mean₂·δ[-answer₅+1]·⅟2718)·(-mean₂·⅟2718+1)·([variance₁=0]·δ[-mean₁+votes₁]+[variance₁≠0]·e^((-mean₁²·⅟2+-votes₁²·⅟2+mean₁·votes₁)·⅟variance₁)·⅟√2̅·⅟√v̅a̅r̅i̅a̅n̅c̅e̅₁̅·⅟√π̅)·([variance₂=0]·δ[-mean₂+votes₂]+[variance₂≠0]·e^((-mean₂²·⅟2+-votes₂²·⅟2+mean₂·votes₂)·⅟variance₂)·⅟√2̅·⅟√v̅a̅r̅i̅a̅n̅c̅e̅₂̅·⅟√π̅)·[-2718+mean₂≤0]·[-3141+mean₁≤0]·[-answer₁+1=0]·[-answer₃+1=0]·[-answer₄+1=0]·[-answer₅+1=0]·[-mean₁≤0]·[-mean₂≤0]·[-variance₁≤0]·[-variance₂≤0]·δ[-ansBias₁+bias₁]·δ[-ansBias₂+bias₂]·δ[-ansBias₃+bias₁]·δ[-ansBias₄+bias₁]·δ[-ansBias₅+bias₂]·δ[-bias₁·mean₁+-variance₁+mean₁]·δ[-bias₂·mean₂+-variance₂+mean₂]·δ[-mean₁+3141·bias₁]·δ[-mean₂+2718·bias₂]·δ[answer₂]".dParse;
	auto expr1=dIntSmp("mean₁".dVar,expr);
	auto expr2=dIntSmp("bias₁".dVar,expr1);
	auto expr3=dIntSmp("ansBias₃".dVar,expr2);
	auto expr4=dIntSmp("ansBias₁".dVar,expr3);
	auto expr5=dIntSmp("ansBias₄".dVar,expr4);
	auto expr6=dIntSmp("variance₁".dVar,expr5);
	auto expr7=dIntSmp("votes₁".dVar,expr6);
	auto expr8=dIntSmp("mean₂".dVar,expr7);
	auto expr9=dIntSmp("variance₂".dVar,expr8);
	auto expr10=dIntSmp("votes₂".dVar,expr9);
	auto expr11=dIntSmp("answer₁".dVar,expr10);
	auto expr12=dIntSmp("answer₂".dVar,expr11);
	auto expr13=dIntSmp("answer₃".dVar,expr12);
	auto expr14=dIntSmp("answer₅".dVar,expr13);
	auto expr15=dIntSmp("ansBias₂".dVar,expr14);
	auto expr16=dIntSmp("ansBias₅".dVar,expr15);
	auto expr17=dIntSmp("answer₄".dVar,expr16);
	//dw(expr16);
	//dw(expr17);
	auto foo="(∫dξ₁(∫dξ₂((-⅟17074476·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅+⅟5436)·δ[answer₄])·(-ξ₂·⅟3141+⅟2+⅟6282·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅)·[-3141+4·ξ₂≤0]·[-3141+√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅≤0]·[-4·ξ₂+3141≠0]·[-ξ₂≤0]·[ξ₂≠0]·e^(((3141·⅟2+⅟2·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅)·ξ₁+-3141·⅟4·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅+-9865881·⅟4+-ξ₁²·⅟2+3141·ξ₂·⅟2)·⅟ξ₂)·⅟√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅·⅟√ξ̅₂̅+∫dξ₂((349·⅟302+⅟2718·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅)·δ[answer₄])·(-ξ₂·⅟19731762+-⅟39463524·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅+⅟12564)·[-3141+4·ξ₂≤0]·[-3141+√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅≤0]·[-4·ξ₂+3141≠0]·[-ξ₂≤0]·[ξ₂≠0]·e^(((-⅟2·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅+3141·⅟2)·ξ₁+-9865881·⅟4+-ξ₁²·⅟2+3141·ξ₂·⅟2+3141·⅟4·√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅)·⅟ξ₂)·⅟√-̅1̅2̅5̅6̅4̅·̅ξ̅₂̅+̅9̅8̅6̅5̅8̅8̅1̅₂̅))·[-answer₄+1=0]".dParse;
	dw(dIntSmp("answer₄".dVar,foo));*/
	//auto bar="∫dx(∫dξ₁∫dξ₂ (δ[x]/(ξ₁^2+ξ₂^2)+δ[x]/(ξ₁^3+ξ₂^3))+∫dξ₁∫dξ₂ (δ[x]/(ξ₁^2+ξ₂^3)+δ[x]/(ξ₁^3+ξ₂^2)))*[x=0]".dParse.simplify(one);
	//writeln(bar);// ∫dξ₁∫dξ₂ 1/(ξ₁^2+ξ₂^2)
	//writeln("∫dx∫dy [1/x+y≤0]".dParse.simplify(one));
	//writeln("∫dx (1/x^(1/2)+-x/x^(1/2))·[0≤x]·[x≤1]".dParse.simplify(one)); // TODO
	//writeln("[-2+⅟y≤0]·[-⅟y+1≤0]·[y≠0]·⅟y²".dParse.linearizeConstraints("y".dVar).simplify(one));
	/+writeln("∫dy log(y)^(-2)·[0<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)^(-1)·[0<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)·[0<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)²·[0<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)³·[0<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)³·[0<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)⁴·[0<y]·[y≤x]".dParse.simplify(one));+/

	/+writeln("∫dy log(y)^(-2)/y·[1/100<y]·[y≤x]".dParse.simplify(one)); // TODO: 1/log(x)
	writeln("∫dy log(y)^(-1)/y·[1/100<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)/y·[1/100<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)²/y·[1/100<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)³/y·[1/100<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)³/y·[1/100<y]·[y≤x]".dParse.simplify(one));
	writeln("∫dy log(y)⁴/y·[1/100<y]·[y≤x]".dParse.simplify(one));+/
}
/*
[([x=0]+x)·(1+[x=0])≤0]

[x≠0][x≤0]


[x=0]·[(1+x)·(1+[x=0]≤0]

// [([x=0]+x)·(1+[x=0])≤0]

/// [x=0] */
