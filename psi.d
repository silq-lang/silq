import std.stdio, std.path, std.array, std.string, std.algorithm;
import file=std.file;
import util;
import lexer, parser, expression, declaration, error;

import scope_, semantic_, analysis, distrib, dexpr;

bool plot=false;// TODO: get rid of globals?
bool cdf=false;
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
	//return file.getcwd().canFind("/test")?path:"test/"~path;
	return path;
}

string readCode(File f){
	// TODO: use memory-mapped file with 4 padding zero bytes
	auto app=mallocAppender!(char[])();
	foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
	app.put("\0\0\0\0"); // insert 4 padding zero bytes
	return cast(string)app.data;	
}
string readCode(string path){ return readCode(File(path)); }

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

void performAnalysis(string path,FunctionDef fd,ErrorHandler err,bool isMain){
	auto dist=analyze(fd,err).dup;
	if(isMain){
		dist.renormalize();
		if(fd.params.length){
			dist.deleteContext(fd.params.length);
			dist.assumeInputNormalized(fd.params.length);
		}
		//dist.distribution=dist.distribution.substituteFun("q".dFunVar,one,DVar[].init,SetX!DVar.init).simplify(one);
	}
	import dparse;
	import approximate;
	//import hashtable; dist.distribution=approxLog(dist.freeVars.element);
	//import hashtable; dist.distribution=approxGaussInt(dist.freeVars.element);
	if(kill) dist.distribution=dist.distribution.killIntegrals();
	if(cdf) dist=getCDF(dist);
	auto str=dist.toString(formatting);
	if(expected.exists) with(expected){
		writeln(ex==dist.distribution.toString()?todo?"FIXED":"PASS":todo?"TODO":"FAIL");
	}
	//writeln((cast(DPlus)dist.distribution).summands.length);
	writeln(str);
	/+if(str.length<10000) writeln(str);
	else{
		writeln("writing output to temporary file...");
		auto f=File("tmp.deleteme","w");
		f.writeln(str);
	}+/
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
	bool plotCDF=cdf;
	if(str.canFind("δ")) plotCDF=true;
	import hashtable;
	if(plot && dist.freeVars.length==1){
		if(plotCDF&&!cdf){
			dist=dist.dup();
			auto freeVar=dist.freeVars.element;
			auto nvar=dist.declareVar("foo");
			dist.distribute(dIvr(DIvr.Type.leZ,-freeVar-20)*dIvr(DIvr.Type.leZ,freeVar-nvar));
			dist.marginalize(freeVar);
		}
		writeln("plotting... ",(plotCDF?"(CDF)":"(PDF)"));
		matlabPlot(dist.distribution.toString(Format.matlab).replace("q(γ⃗)","1"),dist.freeVars.element.toString(Format.matlab));
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
	exprs=semantic(exprs,new TopScope(err));
	foreach(expr;exprs){
		if(cast(ErrorExp)expr) continue;
		if(auto fd=cast(FunctionDef)expr){
			analysis.functions[fd.name.name]=fd;
		}else if(!cast(Declaration)expr) err.error("top level expression must be declaration",expr.loc);
	}
	sourceFile=path;
	scope(exit){ // TODO: get rid of globals
		analysis.functions=(FunctionDef[string]).init;
		analysis.summaries=(Distribution[FunctionDef]).init;
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
			case "--cdf": cdf=true; break;
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
	import dparse,type;
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
	//auto e="[-1+-x≤0]·[-1+-y≤0]·[-1+x≤0]·[-1+y≤0]·[y≠0]·δ[-z+x·⅟y]·⅟4".dParse;
	/+auto e1=dIntSmp("y".dVar,e).simplify(one);
	auto e2=dIntSmp("x".dVar,e1).simplify(one);
	writeln(e2);+/
	//writeln("∫dξ₁[-ξ₁≤0]·ξ₁⁶·⅟e^ξ₁".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞](-120·ξ₁³·⅟e^ξ₁+-360·ξ₁²·⅟e^ξ₁+-720·ξ₁·⅟e^ξ₁+-720·⅟e^ξ₁+-30·ξ₁⁴·⅟e^ξ₁+-6·ξ₁⁵·⅟e^ξ₁+-ξ₁⁶·⅟e^ξ₁)".dParse.simplify(one));
	//writeln("∫dy(((((((([-1+a=0]+[-1+a≠0]·[-a≤0])·[-1+a≤0]+[-1+a≠0]·[-a+1≤0])·[(-a·⅟y+1)·y=0]+([(-1+a·⅟y)·y+-1≤0]·[-1+a≠0]·[-a+1≤0]+[-1+a≤0])·[(-a·⅟y+1)·y≠0])·[(-a·⅟y+1)·y≤0]+(([-1+a=0]+[-1+a≠0]·[-a≤0])·[-1+a≤0]+[-1+a≠0]·[-a+1≤0])·[(-1+a·⅟y)·y≤0]·[(-a·⅟y+1)·y≠0])·((-a·⅟y+1)·[(-a·⅟y+1)·y≠0]·[(-a·⅟y+1)·y≤0]·y+[-1+a≠0]·[-1+a≤0]·a+[-a+1≤0])·[-⅟y≤0]+((-[(-1+a·⅟y)·y≤0]·[(-a·⅟y+1)·y≠0]·[-a≤0]+-[(-a·⅟y+1)·y≤0])·a+1)·(([-1+a≤0]·[-a≤0]+[a≠0]·[a≤0])·[(-1+a·⅟y)·y≤0]·[(-a·⅟y+1)·y≠0]+[(-a·⅟y+1)·y≤0]·[-1+a≤0])·[[-⅟y≤0]=0])·[[⅟y≤0]=0]+(((([(-1+a·⅟y)·y+-1=0]·[-1+a≤0]+[(-1+a·⅟y)·y+-1≠0]·[(-a·⅟y+1)·y+a≤0])·[(-1+a·⅟y)·y+-1≤0]+[(-1+a·⅟y)·y+-1≠0]·[(-a·⅟y+1)·y+1≤0]·[-1+a≤0])·[a≠0]+[1+y=0]·[a=0])·[-a≤0]+(([(-1+a·⅟y)·y+-1=0]+[(-1+a·⅟y)·y+-1≠0]·[(-a·⅟y+1)·y≤0])·[(-1+a·⅟y)·y+-1≤0]+[(-1+a·⅟y)·y+-1≠0]·[(-a·⅟y+1)·y+1≤0])·[a≠0]·[a≤0])·((-1+a·⅟y)·[(-1+a·⅟y)·y+-1≠0]·[(-1+a·⅟y)·y+-1≤0]·y+-[-a≤0]·[a≠0]·a+[(-a·⅟y+1)·y+1≤0])·[[-⅟y≤0]=0]·[⅟y≤0])·[y≠0]·⅟y))".dParse.simplify(one));
	//writeln("(∫dx[(-1+a·⅟x)·x+-1≤0]·[(-a·⅟x+1)·x≠0]·[(-a·⅟x+1)·x≤0]·[[⅟x≤0]=0]·[x≠0])·[-1+a≠0]·[-a+1≤0]+(∫dx[(-1+a·⅟x)·x+-1≤0]·[(-a·⅟x+1)·x≠0]·[(-a·⅟x+1)·x≤0]·[[⅟x≤0]=0]·[x≠0]·⅟x)·[-1+a≠0]·[-a+1≤0]+-(∫dx[(-1+a·⅟x)·x+-1≤0]·[(-a·⅟x+1)·x≠0]·[(-a·⅟x+1)·x≤0]·[[⅟x≤0]=0]·[x≠0]·⅟x)·[-1+a≠0]·[-a+1≤0]·a".dParse.simplify(one));
	//writeln(dIntSmp("x".dVar,"[(-1+a·⅟x)·x+-1≤0]·[(-a·⅟x+1)·x≠0]·[(-a·⅟x+1)·x≤0]·[[⅟x≤0]=0]·[x≠0]·[-1+a≠0]·[-a+1≤0]".dParse.linearizeConstraints("x".dVar)));
	//writeln(dIntSmp("x".dVar,"[(-1+a·⅟x)·x+-1≤0]·[(-a·⅟x+1)·x≠0]·[(-a·⅟x+1)·x≤0]·[[⅟x≤0]=0]·[x≠0]·[-1+a≠0]·[-a+1≤0]".dParse.linearizeConstraints("x".dVar)));
	//writeln(dGamma(dℕ(5+1)).simplify(one));
	//writeln(dBeta(dℕ(5+1),dℕ(6+1)).simplify(one));
	//writeln((dGamma(dℕ(5+1))*dGamma(dℕ(6+1))/dGamma(dℕ(5+1+6+1))).simplify(one));
	//writeln(studentTPDF("x".dVar,7.dℕ));
	//writeln(dIntSmp("x".dVar,weibullPDF("x".dVar,1.dℕ,3.dℕ)).toString(Format.mathematica)); // TODO: this should be 1
	//writeln("!! ","[0<1/x]".dParse.simplify(one));
	//writeln("[⅟x≤0]".dParse.factorDIvr!(e=>dFun("f".dFunVar,[e])));
	//writeln("[1/x!=0]".dParse.simplify(one));
	//writeln("[x=0]".dParse.factorDIvr!(e=>dFun("f".dFunVar,[e])));
	//writeln("lim[x→ -∞] 1/x".dParse.simplify(one));
	/+DExpr parseHakaru(string s){
		return s.dParse.substituteFun("Msum".dFunVar,"a+b".dParse,["a".dVar,"b".dVar]).substituteFun("Msum".dFunVar,"a".dVar,["a".dVar]).substituteFun("Msum".dFunVar,"a+b+c".dParse,["a".dVar,"b".dVar,"c".dVar]).substituteFun("Weight".dFunVar,"a*b".dParse,["a".dVar,"b".dVar]).substituteFun("Msum".dFunVar,"a+b+c+d".dParse,["a".dVar,"b".dVar,"c".dVar,"d".dVar]).substituteFun("Msum".dFunVar,"a+b+c+d+e".dParse,["a".dVar,"b".dVar,"c".dVar,"d".dVar,"e".dVar]).substituteFun("Msum".dFunVar,"a+b+c+d+k+f".dParse,["a".dVar,"b".dVar,"c".dVar,"d".dVar,"k".dVar,"f".dVar]).polyNormalize("x".dVar).substituteFun("Ret".dFunVar,one,["a".dVar]);
	}+/
	//writeln(parseHakaru("Msum(Weight(x,Msum(Weight(1/3*x,Msum(Weight(1/3*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))),Weight(1/3-1/3*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))))),Weight(1/3-1/3*x,Msum(Weight(1/4*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))),Weight(1/4-1/4*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))))))),Weight(1-x,Msum(Weight(1/4*x,Msum(Weight(1/3*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))),Weight(1/3-1/3*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))))),Weight(1/4-1/4*x,Msum(Weight(1/4*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))),Weight(1/4-1/4*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(5/36-5/36*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(5/48-5/48*x,Ret(x)))))))))))"));
	//writeln(parseHakaru("Weight(1/12*x+1/4,Msum(Weight(1/3/(1/12*x+1/4)*x,Ret(x)),Weight(1/(1/12*x+1/4)*(1/4-1/4*x),Ret(x))))"));
	//writeln(parseHakaru("Msum(Weight(x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1-x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))"));
	//writeln(parseHakaru("Msum(Weight(x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))),Weight(1-x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))))")); // 3
	//writeln(parseHakaru("Msum(Weight(x,Msum(Weight(1/3*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))),Weight(1/3-1/3*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))))),Weight(1-x,Msum(Weight(1/4*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))),Weight(1/4-1/4*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))))))")); // 4
	//writeln(parseHakaru("Msum(Weight(x,Msum(Weight(1/3*x,Msum(Weight(1/3*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))),Weight(1/3-1/3*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))))),Weight(1/3-1/3*x,Msum(Weight(1/4*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))),Weight(1/4-1/4*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))))))),Weight(1-x,Msum(Weight(1/4*x,Msum(Weight(1/3*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))),Weight(1/3-1/3*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))))),Weight(1/4-1/4*x,Msum(Weight(1/4*x,Msum(Weight(1/3*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/3-1/3*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))),Weight(1/4-1/4*x,Msum(Weight(1/4*x,Msum(Weight(1/9*x,Ret(x)),Weight(1/12-1/12*x,Ret(x)))),Weight(1/4-1/4*x,Msum(Weight(1/12*x,Ret(x)),Weight(1/16-1/16*x,Ret(x)))))))))))"));
	//writeln(dIvr(DIvr.Type.eqZ,dFloat(0.00000001)));
	//writeln(dIntSmp("x".dVar,dSumSmp("n".dVar,dDelta("x".dVar-"n".dVar))));
	//writeln("∫dξ₁∑_ξ₂[-10+ξ₂≤0]·[-ξ₂≤0]·δ[-ξ₁+ξ₂]".dParse.simplify(one));
	//writeln("∫da(∑_ξ₁δ[-a+ξ₁])·[-10+a≤0]·[-a≤0]".dParse.simplify(one));
	//writeln("-tmp7F10320E0680·tmp7F1032681400+-tmp7F1032681400·tmp7F10326B17C0+-tmp7F1032681400·tmp7F1032A7FDC0+-tmp7F103277B640+tmp7F1032681400·tmp7F103306F980+-tmp7F1032681400·tmp7F103306F980+tmp7F10320E0680·tmp7F1032681400+tmp7F1032323440·tmp7F1032681400+tmp7F10323BAD80·tmp7F1032681400+tmp7F1032681400+tmp7F1032681400·tmp7F103290E4C0+tmp7F1032681400·tmp7F1032D9B640".dParse.simplify("[(-tmp7F1032681400·tmp7F103306F980+tmp7F10320E0680·tmp7F1032681400+tmp7F1032681400·tmp7F10326B17C0+tmp7F1032681400·tmp7F1032A7FDC0+tmp7F103277B640)·⅟tmp7F1032681400+tmp7F10330892C0=0]·[-1+tmp7F10330892C0≤0]·[-tmp7F103306F980+1+tmp7F10320E0680+tmp7F1032323440+tmp7F10323BAD80+tmp7F10326B17C0+tmp7F103290E4C0+tmp7F1032A7FDC0+tmp7F1032D9B640+tmp7F10330892C0=0]·[-tmp7F10330892C0≤0]·[tmp7F1032681400≠0]".dParse));
	//writeln(DPlus.recursiveCombine("-tmp7F9FE5070800·tmp7F9FE54CB240".dParse,"(-tmp7F9FE5A65D80+1+tmp7F9FE4AD6A80+tmp7F9FE4D19900+tmp7F9FE4E14200+tmp7F9FE53028C0+tmp7F9FE54CB240+tmp7F9FE5791C80+tmp7F9FE5A7F6C0)·tmp7F9FE5070800".dParse,one));
	//writeln("-tmp7FFFF6143580·tmp7FFFF6537C00+-tmp7FFFF6537C00·tmp7FFFF6550FC0+-tmp7FFFF6537C00·tmp7FFFF6B9BE80+-tmp7FFFF68AB0C0+tmp7FFFF6537C00·tmp7FFFF6EBB300".dParse.simplify("[(-tmp7FFFF6537C00·tmp7FFFF6EBB300+tmp7FFFF6143580·tmp7FFFF6537C00+tmp7FFFF6537C00·tmp7FFFF6550FC0+tmp7FFFF6537C00·tmp7FFFF6B9BE80+tmp7FFFF68AB0C0)·⅟tmp7FFFF6537C00+tmp7FFFF6F9F040=0]·[-1+tmp7FFFF6F9F040≤0]·[-tmp7FFFF6EBB300+1+tmp7FFFF6143580+tmp7FFFF61A4180+tmp7FFFF637CCC0+tmp7FFFF6550FC0+tmp7FFFF68ABE40+tmp7FFFF6B9BE80+tmp7FFFF6E8EA40+tmp7FFFF6F9F040=0]·[-tmp7FFFF6F9F040≤0]·[tmp7FFFF6537C00≠0]".dParse));
	//SetX!DVar s;
	//s.insert("x".dVar); //s.insert("__r₁".dVar);
	//writeln("(∫dγ⃗∫dξ₁ q(ξ₁,γ⃗)·ξ₁)".dParse.substituteFun("q".dFunVar,"δ[-x+3]·δ[-x+__arg₁]".dParse,["__arg₁".dVar],s).simplify(one));
	//writeln("∫dx [x·y²=z]·[0≤x]·[x≤1]".dParse.simplify(one));
	//writeln("∫dx [f(x,y)=z]·[0≤x]·[x≤1]".dParse.simplify(one));
	//writeln(DInt.staticSimplify("controlGroup₁".dVar,"(∫dξ₁([-1+ξ₁≤0]·[-ξ₁≤0]·probIfControl·δ[-isEffective+1]·δ[-treatedGroup₁+1]·δ[-treatedGroup₄+1]·δ[-treatedGroup₅+1]·δ[controlGroup₁]·δ[controlGroup₂]·δ[controlGroup₄]·δ[controlGroup₅]·δ[treatedGroup₂]·⅟2+[-1+ξ₁≤0]·[-ξ₁≤0]·δ[-probIfControl+ξ₁]·δ[-treatedGroup₁+1]·δ[-treatedGroup₄+1]·δ[-treatedGroup₅+1]·δ[controlGroup₁]·δ[controlGroup₂]·δ[controlGroup₄]·δ[controlGroup₅]·δ[isEffective]·δ[treatedGroup₂]·ξ₁·⅟2)·([-ξ₁+1≠0]·[-ξ₁+1≤0]+[ξ₁≠0]·[ξ₁≤0]))·[-controlGroup₁+1=0]·probIfControl".dParse));
	//writeln("∫dξ₁[-2+-ξ₁≤0]·[-2+ξ₁≤0]·[-ξ₁²+1=0]".dParse.simplify(one));
	//writeln("∫dx ((d/dx)⁻¹[e^(-x²)](x)*x·[0≤x]-x·[0≤x])".dParse.simplify(one));
	//writeln("∫dξ₁∫dξ₂(∫dξ₃[-ξ₁+ξ₃≤0]·q(ξ₃,ξ₂,γ⃗))·[-ξ₁+ξ₂≤0]·[-ξ₂+ξ₁≠0]".dParse.simplify(one));
	//writeln("∫dξ₂((0+[-ξ₂+ξ₁=0])·q(ξ₂,ξ₁,γ⃗))".dParse.simplify(one));
	//writeln("∫dξ₁[-ξ₁≤0]·ξ₁·⅟e^(13·ξ₁²·⅟120)".dParse.simplify(one)); // TODO
	//writeln(dIntSmp("x".dVar,"∫dξ₁∫dξ₂ δ[x+ξ₁+ξ₂]".dParse));
	//writeln("0+∫dξ₁(0+[ξ₁=0])·q(ξ₁,γ⃗)".dParse.simplify(one));
	//writeln(" ∫dξ₁((-[ξ₁≤0]·⅟ξ₁+[-ξ₁≤0]·⅟ξ₁)·[ξ₁≠0]·q(r·⅟ξ₁,ξ₁,γ⃗)+(∫dξ₂ q(ξ₂,ξ₁,γ⃗))·[ξ₁=0]·δ[r])".dParse.simplify(one));
	//writeln("∫dξ₂[ξ₁=0]·q(ξ₂,ξ₁,γ⃗)·δ[r]".dParse.simplify(one));
	//writeln("∫dξ₁([-1+ξ₁≤0]·[-ξ₁≤0]·δ[-tmp+1]·δ[-x₂+1]·δ[-x₆+1]·δ[ξ₁]+[-1+ξ₁≤0]·[-ξ₁≤0]·δ[-x₂+1]·δ[-x₇+ξ₁]·δ[tmp])·([-ξ₁+1≠0]·[-ξ₁+1≤0]+[ξ₁≠0]·[ξ₁≤0])".dParse.simplify(one));
	//writeln("∫dξ₁(∫dξ₂(∫dξ₃∫dξ₄([-ξ₁·ξ₂+ξ₃≤0]·[-ξ₁·ξ₂+ξ₄≤0]·[-ξ₃+ξ₁·ξ₂≠0]+[-ξ₄+ξ₁·ξ₂≠0]·[-ξ₄+ξ₁·ξ₂≤0])·q(ξ₄,ξ₃,γ⃗))·[-1+ξ₂≤0]·[-ξ₂≤0])·[-1+ξ₁≤0]·[-ξ₁≤0]".dParse.simplify(one));
	//writeln("∫dξ₁([-1/ξ₁≤0]·[ξ₁≠0]·⅟e^(ξ₁²·⅟2)·√2̅·√π̅)".dParse.simplify(one)); // TODO: this should be π not 2·π
	//writeln("[-1/ξ₁≤0]·[ξ₁≠0]".dParse.linearizeConstraints("ξ₁".dVar));
	//writeln("((-[⅟x≤0]·x·⅟2+[-⅟x≤0]·x·⅟2)·[ξ₁≠0]·∫dr₁ e^(-r₁²·x²·⅟2+-x²·⅟2))·⅟π".dParse.toString(Format.mathematica));
	//writeln("(x²)^(1/2)".dParse.simplify(one)); // oops
	//writeln("∫dξ₁(-[ξ₁≤0]·ξ₁·⅟2)·[ξ₁≠0]·⅟e^(ξ₁²·⅟2)·⅟ξ₁·⅟√π̅·√2̅".dParse.simplify(one));
	//writeln("∫dξ₁[ξ₁≠0]·[ξ₁≤0]·⅟e^(ξ₁²·⅟2)".dParse.simplify(one));
	//writeln("∫dx x·e^(-r₁²·x²·⅟2+-x²·⅟2)".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞]((-(d/dx)⁻¹[e^(-x²)](ξ₁·√r̅₁̅²̅·̅⅟̅2̅+̅⅟̅2̅)·ξ₁·√r̅₁̅²̅·̅⅟̅2̅+̅⅟̅2̅+-e^((-r₁²·⅟2+-⅟2)·ξ₁²)·⅟2)·⅟(r₁²·⅟2+⅟2)+(d/dx)⁻¹[e^(-x²)](ξ₁·√r̅₁̅²̅·̅⅟̅2̅+̅⅟̅2̅)·ξ₁·⅟√r̅₁̅²̅·̅⅟̅2̅+̅⅟̅2̅)".dParse.simplify(one));
	//writeln("lim[x → ∞] e^((-r₁²·⅟2+-⅟2)·x²)".dParse.simplify(one));
	//writeln(dInt("x".dVar,dDelta("x".dVar,dTuple([one,one,one]),tupleTy([ℝ,ℝ,ℝ]))/2+dDelta("x".dVar,dTuple([one,one,one+one]),tupleTy([ℝ,ℝ,ℝ]))/2).simplify(one));
	//writeln(dInt("x".dVar,dInt("y".dVar,dInt("z".dVar,"[0<=y]·[y<=1]·[0<=z]·[z<=1]".dParse*dDelta("x".dVar,dTuple(["y".dVar,"z".dVar]),tupleTy([ℝ,ℝ,ℝ]))))).simplify(one));
	//writeln("∫dξ₁∫dξ₂(∫dξ₃[-1+ξ₃≤0]·[-ξ₃≤0]·δ_ξ₁[(ξ₃,ξ₂)])·[-1+ξ₂≤0]·[-ξ₂≤0]".dParse.simplify(one));
	//(∫dk[-1+k≤0]·[-k≤0]·δ_x[x₁[0 ↦ k]])·[-x₁.length≤0]·[x₁.length≠0]·δ[-n+2]·δ_x₁[[k ↦ 0] (1)]
	//auto exp=dIntSmp("k".dVar,"[-1+k≤0]·[-k≤0]".dParse*dDelta("x".dVar,dIUpdate("arr".dVar,zero,"k".dVar),arrayTy(ℝ)))*dDelta("arr".dVar,dArray([zero]),arrayTy(ℝ));
	//writeln(exp);
	//DEB=true;
	//writeln(dIntSmp("arr".dVar,exp));
	//writeln(dIntSmp("k".dVar,"[-1+k≤0]·[-k≤0]".dParse*dDelta("x".dVar,dIUpdate("arr".dVar,zero,"k".dVar),arrayTy(ℝ))).substitute("arr".dVar,dArray([zero])));
	//writeln(dIntSmp("k".dVar,"[-1+k≤0]·[-k≤0]".dParse*dDelta("x".dVar,dIUpdate(dArray([zero]),zero,"k".dVar),arrayTy(ℝ))));
	//auto e="((∫dξ₁(∫dξ₂[-1+ξ₂≤0]·[-ξ₂≤0]·δ_t[(-ξ₁+ξ₂,-ξ₂+ξ₁)])·[-1+ξ₁≤0]·[-ξ₁≤0])·⅟2+δ_t[(0,0)]·⅟2)·[-t[0]+-t[1]=0]".dParse;
	//writeln(dIntSmp("t".dVar,e));
	//auto e="((∫dξ₁(∫dξ₂[-1+ξ₂≤0]·[-ξ₂≤0]·δ_x[(ξ₂,ξ₁)])·[-1+ξ₁≤0]·[-ξ₁≤0])·δ_y[(x[0],x[1])]·⅟2+(∫dξ₁(∫dξ₂[-1+ξ₂≤0]·[-ξ₂≤0]·δ_x[(ξ₂,ξ₁)])·[-1+ξ₁≤0]·[-ξ₁≤0])·δ_y[(x[1],x[0])]·⅟2)·[-t[0]+-t[1]=0]·δ_t[(-y[0]+x[0],-y[1]+x[1])]".dParse;
	//writeln(e);
	//writeln(dIntSmp("y".dVar,dIntSmp("t".dVar,dIntSmp("x".dVar,e))));
	//auto e="((∫dξ₁(∫dξ₂[-1+ξ₂≤0]·[-ξ₂≤0]·δ_t[(-y[0]+ξ₂,-y[1]+ξ₁)]·δ_y[(ξ₁,ξ₂)])·[-1+ξ₁≤0]·[-ξ₁≤0])·⅟2+(∫dξ₁(∫dξ₂[-1+ξ₂≤0]·[-ξ₂≤0]·δ_t[(-y[0]+ξ₂,-y[1]+ξ₁)]·δ_y[(ξ₂,ξ₁)])·[-1+ξ₁≤0]·[-ξ₁≤0])·⅟2)·[-t[0]+-t[1]=0]".dParse;
	//auto e="(∫dξ₁(∫dξ₂[-1+ξ₂≤0]·[-ξ₂≤0]·δ_t[(-y[0]+ξ₂,-y[1]+ξ₁)]·δ_y[(ξ₂,ξ₁)])·[-1+ξ₁≤0]·[-ξ₁≤0])·[-t[0]+-t[1]=0]".dParse;
	//writeln(dIntSmp("t".dVar,e));
	//auto e="[-1+-k+y[0]+y[1]≤0]·[-1+k≤0]·[-k+-l+y[0]+y[1]=0]·[-k≤0]·[-l≤0]·δ_y[(-k+y[0]+y[1],k)]".dParse; // this expression should not happen.
	//dw(e);
	//dw(dIntSmp("k".dVar,e));
	/+auto e="(∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·δ_x[x₁[0 ↦ ξ₁]])".dParse;
	auto f="[k ↦ 0] (1)".dParse;
	dw(e," ",f);
	dw("!!!");
	auto r=e.substitute("x₁".dVar,f);
	dw(r);+/
	//auto e="∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·δ_x[[ξ₁ ↦ [ξ₁=0]·ξ₂] (1)]".dParse;
	//auto e="∫dy∫dz δ[-x+1]·δ[-y+1]·δ[-z+1]".dParse;
	//dw(e," ",e.simplify(one));
	//writeln("e: ",e);
	//writeln("!!");
	//writeln("int: e",dInt("x".dVar,e));
	//auto e="(∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·δ_a[a₁[0 ↦ a₁[0][0 ↦ ξ₁]]])·δ_a₁[[ξ₁ ↦ ([ξ₂ ↦ 0] (1))·[-1+ξ₁=0]+([ξ₂ ↦ 0] (1))·[ξ₁=0]] (2)]".dParse;
	//writeln(dIntSmp("a₁".dVar,e));
	/+auto e="(∫dξ₁δ[ξ₁]·δ_a[a₁[0 ↦ a₁[0][0 ↦ ξ₁]]])".dParse;
	auto f="[ξ₁ ↦ ([ξ₂ ↦ 0] (1))·[-1+ξ₁=0]+([ξ₂ ↦ 0] (1))·[ξ₁=0]] (2)".dParse;
	dw(e," ",f);
	dw("!!");
	writeln(e.substitute("a₁".dVar,f));+/
	/+auto e="([ξ₂ ↦ 0] (1))·[-1+ξ₁=0]·[ξ₁≠0]+([ξ₂ ↦ [ξ₂=0]·ξ₀] (1))".dParse;
	dw("!!");
	writeln(dLambda(dBoundVar(1),e));+/
	//writeln("([ξ₂ ↦ 0] (1))·[-1+ξ₁=0]·[ξ₁≠0]+([ξ₂ ↦ [ξ₂=0]·ξ₀] (1))·[ξ₁=0]".dParse);
	//auto e="([ξ₂ ↦ 0] (1))·[-1+ξ₁=0]·[ξ₁≠0]+([ξ₂ ↦ [ξ₂=0]·ξ₀] (1))·[ξ₁=0]".dParse;
	//writeln(e.incBoundVar(1,false));
	//auto e="([i ↦ ([j ↦ 0] (1))·[-1+i=0]+([j ↦ 0] (1))·[i=0]] (2))[0 ↦ [i ↦ [j=0]·v] (1)]".dParse;
	//dw(e);
	//writeln(e.simplify(one));
	/+auto e="∫dξ₁∫dξ₂∫dξ₃(δ[-ξ₁+1]·⅟2+δ[ξ₁]·⅟2)·δ[-ξ₂+1]·δ_ξ₃[[ξ₄ ↦ 2·[-1+ξ₄=0]+[ξ₄=0]] (2)]".dParse;
	writeln(e);
	dw("!!!");
	writeln(e.simplify(one));+/
	//auto e="∫dξ₂∫dξ₃(δ[-ξ₁+1]·⅟2+δ[ξ₁]·⅟2)·δ[-ξ₂+1]·δ_ξ₃[[ξ₄ ↦ 2·[-1+ξ₄=0]+[ξ₄=0]] (2)]".dParse;
	//dw(e);
	//writeln(e.incBoundVar(-1,true));
	//writeln("∑_ξ₁(3·[-1+ξ₁=0]·⅟10+[-2+ξ₁=0]·⅟2+[ξ₁=0]·⅟5)·[-3+ξ₁≠0]·[-3+ξ₁≤0]·[-ξ₁≤0]·δ[-ξ₁+r₁]".dParse.simplify(one));
	//writeln("∑_ξ₁(([-1+ξ₁=0]+[-1+ξ₁≠0]·[-2+ξ₁=0]+[-1+ξ₁≠0]·[-2+ξ₁≠0]·[ξ₁≠0]+[ξ₁=0])·[ξ₁≠0]+([-1+ξ₁=0]+[-1+ξ₁≠0]·[-2+ξ₁=0]+[ξ₁=0])·[-1+ξ₁≠0]·[-2+ξ₁≠0]·[-3+ξ₁≠0]·[ξ₁≠0])·([-1+ξ₁=0]+[-1+ξ₁≠0]·[-2+ξ₁=0]+[ξ₁=0])·[-1+ξ₁≠0]·[-2+ξ₁≠0]·[-3+ξ₁≤0]·[-ξ₁≤0]·[ξ₁≠0]".dParse.simplify(one));
	//writeln("∑_x[0≤x]·[x≤3]·[x≠1]".dParse.simplify(one));
	//writeln("∑_ξ₁(3·[-1+x=0]·⅟10+[-2+x=0]·⅟5+[x=0]·⅟2)·[-3+x≠0]·[-3+x≤0]·[-x≤0]·δ[-x+ξ₁]".dParse.simplify(one));
	/+auto v="c₁".dVar;
	auto e="(∫dξ₁(∫dξ₂δ___r₂[ξ₁{.x ↦ ξ₁.x+ξ₂}]·⅟e^(ξ₂²·⅟2))·δ[-c₁+ξ₁]·δ[i])·δ_c[__r₂]·⅟√2̅·⅟√π̅".dParse;
	writeln(e.simplify(one));+/
	/+auto x="∑_x (([y ↦ 2·[-2+y=0]·⅟5+2·[y=0]·⅟5+[-1+y=0]·⅟5] (3))·[-1+x=0]+([y ↦ 3·[-1+y=0]·⅟10+[-2+y=0]·⅟5+[y=0]·⅟2] (3))·[x=0])".dParse;
	writeln(x.simplify(one));+/
	//auto e="(∑_y((4·[-1+y=0]·⅟5+[y=0]·⅟5)·[-1+z=0]+(9·[-1+y=0]·⅟10+[y=0]·⅟10)·[-2+z=0]+([-1+y=0]·⅟2+[y=0]·⅟2)·[z=0])·(43·[-3+z≠0]·[-3+z≤0]·[z=0]·⅟100+8·[-2+z=0]·[-3+z≠0]·[-3+z≤0]·⅟25+[-1+z=0]·[-3+z≠0]·[-3+z≤0]·⅟4)·([-1+z=0]·[-2+z=0]·[-4+y≠0]·[z≠0]+[-1+z=0]·[-2+z=0]·[-6+y≠0]·[z=0]+[-1+z=0]·[-2+z≠0]·[-2+y≠0]·[z≠0]+[-1+z=0]·[-2+z≠0]·[-4+y≠0]·[z=0]+[-1+z≠0]·[-2+z=0]·[-2+y≠0]·[z≠0]+[-1+z≠0]·[-2+z=0]·[-4+y≠0]·[z=0]+[-1+z≠0]·[-2+z≠0]·[-2+y≠0]·[z=0]+[-1+z≠0]·[-2+z≠0]·[z≠0]·[y≠0])·([-1+z=0]·[-2+z=0]·[-4+y≤0]·[z≠0]+[-1+z=0]·[-2+z=0]·[-6+y≤0]·[z=0]+[-1+z=0]·[-2+z≠0]·[-2+y≤0]·[z≠0]+[-1+z=0]·[-2+z≠0]·[-4+y≤0]·[z=0]+[-1+z≠0]·[-2+z=0]·[-2+y≤0]·[z≠0]+[-1+z≠0]·[-2+z=0]·[-4+y≤0]·[z=0]+[-1+z≠0]·[-2+z≠0]·[-2+y≤0]·[z=0]+[-1+z≠0]·[-2+z≠0]·[z≠0]·[y≤0])·([-1+z=0]·[-2+z≠0]·[z≠0]+[-1+z≠0]·[-2+z=0]·[z≠0]+[-1+z≠0]·[-2+z≠0]·[z=0])·[-(y,{.x ↦ z,.b ↦ [ξ₃ ↦ ([ξ₄ ↦ 4·[-1+ξ₄=0]·⅟5+[ξ₄=0]·⅟5] (2))·[-1+ξ₃=0]+([ξ₄ ↦ 9·[-1+ξ₄=0]·⅟10+[ξ₄=0]·⅟10] (2))·[-2+ξ₃=0]+([ξ₄ ↦ [-1+ξ₄=0]·⅟2+[ξ₄=0]·⅟2] (2))·[ξ₃=0]] (3),.a ↦ [ξ₃ ↦ ([ξ₄ ↦ 2·[-2+ξ₄=0]·⅟5+2·[ξ₄=0]·⅟5+[-1+ξ₄=0]·⅟5] (3))·[-1+ξ₃=0]+([ξ₄ ↦ 3·[-1+ξ₄=0]·⅟10+[-2+ξ₄=0]·⅟5+[ξ₄=0]·⅟2] (3))·[ξ₃=0]+([ξ₄ ↦ 3·[ξ₄=0]·⅟10+[-1+ξ₄=0]·⅟5+[-2+ξ₄=0]·⅟2] (3))·[-2+ξ₃=0]] (3)})=0]·[-3+z≠0]·[-3+z≤0]·[-y≤0])".dParse;
	//writeln(e.simplify(one));
	//auto e="[-a.length+__u₂≠0]·[-a.length+__u₂≤0]·[a[__u₂].length≤0]·δ_a[[ξ₁ ↦ (([ξ₂ ↦ 2·[-1+ξ₂=0]+3·[-2+ξ₂=0]+[ξ₂=0]] (3))·[ξ₁=0]+([ξ₂ ↦ 2·[ξ₂=0]+3·[-1+ξ₂=0]+4·[-2+ξ₂=0]] (3))+([ξ₂ ↦ 5·[ξ₂=0]+6·[-1+ξ₂=0]+7·[-2+ξ₂=0]] (3))·[-2+ξ₁=0])[0 ↦ 2+5·[-2+ξ₁=0]+[ξ₁=0]]·[-1+ξ₁=0]+(([ξ₂ ↦ 2·[-1+ξ₂=0]+3·[-2+ξ₂=0]+[ξ₂=0]] (3))·[ξ₁=0]+([ξ₂ ↦ 5·[ξ₂=0]+6·[-1+ξ₂=0]+7·[-2+ξ₂=0]] (3))·[-2+ξ₁=0])·[-1+ξ₁≠0]] (3)]".dParse;
	//writeln(dIntSmp("a".dVar,e));
	//auto e="([ξ₁ ↦ (([ξ₂ ↦ 2·[-1+ξ₂=0]+3·[-2+ξ₂=0]+[ξ₂=0]] (3))·[ξ₁=0]+([ξ₂ ↦ 2·[ξ₂=0]+3·[-1+ξ₂=0]+4·[-2+ξ₂=0]] (3))+([ξ₂ ↦ 5·[ξ₂=0]+6·[-1+ξ₂=0]+7·[-2+ξ₂=0]] (3))·[-2+ξ₁=0])[0 ↦ 2+5·[-2+ξ₁=0]+[ξ₁=0]]·[-1+ξ₁=0]+(([ξ₂ ↦ 2·[-1+ξ₂=0]+3·[-2+ξ₂=0]+[ξ₂=0]] (3))·[ξ₁=0]+([ξ₂ ↦ 5·[ξ₂=0]+6·[-1+ξ₂=0]+7·[-2+ξ₂=0]] (3))·[-2+ξ₁=0])·[-1+ξ₁≠0]] (3))[__u₂].length".dParse;
	//writeln(e.simplify(one));
	//auto e="[-a.length+__u₂≠0]·[-a.length+__u₂≤0]·[a[__u₂].length≤0]".dParse;
	//writeln(e.substitute("a".dVar,"[ξ₁ ↦ (([ξ₂ ↦ 2·[-1+ξ₂=0]+3·[-2+ξ₂=0]+[ξ₂=0]] (3))·[ξ₁=0]+([ξ₂ ↦ 2·[ξ₂=0]+3·[-1+ξ₂=0]+4·[-2+ξ₂=0]] (3))+([ξ₂ ↦ 5·[ξ₂=0]+6·[-1+ξ₂=0]+7·[-2+ξ₂=0]] (3))·[-2+ξ₁=0])[0 ↦ 2+5·[-2+ξ₁=0]+[ξ₁=0]]·[-1+ξ₁=0]+(([ξ₂ ↦ 2·[-1+ξ₂=0]+3·[-2+ξ₂=0]+[ξ₂=0]] (3))·[ξ₁=0]+([ξ₂ ↦ 5·[ξ₂=0]+6·[-1+ξ₂=0]+7·[-2+ξ₂=0]] (3))·[-2+ξ₁=0])·[-1+ξ₁≠0]] (3)".dParse.simplify(one)));
	//writeln(dIvr(DIvr.Type.neqZ,dVar("x")*dVar("y")).linearizeConstraints(dVar("x")).simplify(one));
	//writeln("[x^2<=1]".dParse.linearizeConstraints("x".dVar));
	//writeln("[-1+-y+z≤0]·[-1+y≤0]·[-y≤0]·[-z+y≤0]·δ[-w+x·z]·δ[-z+x+y]".dParse);
	//writeln("[2=0]·2".dParse.simplify(one)," ",0^^2);
	//writeln("∫dx₂ [-1+x₂≤0]·[-2+-x₂+x≤0]·[-x+x₂≤0]·[-x₂≠0]·[-x₂≤0]".dParse.simplify(one));
	//writeln("lim[r → ∞](((-12·⅟√2̅+6·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+-3·e^(-2+-r²·⅟2+2·r))·r·√2̅+(-12·√2̅+12·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·6+-12·e^(-2+-r²·⅟2+2·r)·⅟√2̅)·⅟√2̅+(((-2·r·⅟3·√2̅+8·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+2·e^(-2+-r²·⅟2+2·r)·⅟3)·r·√2̅+((-r·⅟3·√2̅+2·⅟3·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+e^(-2+-r²·⅟2+2·r)·⅟3)·r²·√2̅+(-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·4·e²·⅟3·√2̅+2·e^(-r²·⅟2+2·r)·⅟3)·⅟e²·√2̅+(-8·r·⅟3·⅟√2̅+8·⅟3·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·4·⅟3+8·e^(-2+-r²·⅟2+2·r)·⅟3·⅟√2̅)·√2̅+(((-⅟3·⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-e^(-r²·⅟2+-⅟2+r)·⅟6)·r²·√2̅+((-⅟3·⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-e^(-r²·⅟2+-⅟2+r)·⅟6)·r·√2̅+((d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·⅟3·√2̅·√e̅+-e^(-r²·⅟2+r)·⅟3)·⅟√e̅·√2̅+(-⅟3·⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·⅟3+-e^(-r²·⅟2+-⅟2+r)·⅟3·⅟√2̅)·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·3·[⅟2≠0]·⅟√2̅+(-36·⅟√2̅+12·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+-6·e^(-9·⅟2+-r²·⅟2+3·r)+(((-r·⅟√2̅+√2̅)·(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)+-e^(-2+-r²·⅟2+2·r)·⅟2)·e²+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·[⅟2≠0]·e²·r·⅟√2̅)·⅟e²+(-r·√2̅+6·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+e^(-9·⅟2+-r²·⅟2+3·r)+((-(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅)·r·⅟3·⅟√2̅+⅟6·⅟e^(r²·⅟2))·r²·√2̅+⅟3·⅟e^(r²·⅟2)·√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅)·r·√2̅+⅟e^(r²·⅟2)+(-4·⅟√2̅+4·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-2·e^(-r²·⅟2+-⅟2+r)+(-√2̅+2·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-e^(-r²·⅟2+-⅟2+r)+-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2·[⅟2≠0]·√2̅+(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·3·[⅟2≠0]·⅟√2̅+(((d/dx)⁻¹[e^(-x²)](-r·⅟√2̅)·r·⅟3·⅟√2̅+-⅟6·⅟e^(r²·⅟2))·r²·√2̅+-⅟3·⅟e^(r²·⅟2)·√2̅)·⅟√2̅+(((-3·r·⅟2·⅟√2̅+3·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+3·e^(-r²·⅟2+-⅟2+r)·⅟4)·r·√2̅+((-3·r·⅟2·⅟√2̅+3·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+3·e^(-r²·⅟2+-⅟2+r)·⅟4)·√2̅+-(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·3·⅟2)·√2̅+-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·[⅟2≠0]·√2̅+(((-3·⅟√2̅+3·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)+3·e^(-r²·⅟2+-⅟2+r)·⅟2)·√e̅+-(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·3·[⅟2≠0]·r·⅟√2̅·√e̅)·⅟√e̅+(((-3·⅟√2̅+r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)+e^(-9·⅟2+-r²·⅟2+3·r)·⅟2)·e^(5·⅟2)+-(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·[⅟2≠0]·e^(5·⅟2)·r·⅟√2̅)·⅟e^(5·⅟2)+(((-3·r·⅟2·⅟√2̅+9·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+3·e^(-9·⅟2+-r²·⅟2+3·r)·⅟4)·r·√2̅+(-9·r·⅟2·⅟√2̅+27·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·3·⅟2+9·e^(-9·⅟2+-r²·⅟2+3·r)·⅟2·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅)·r·⅟√2̅+-⅟2·⅟e^(r²·⅟2)+(((-3·⅟√2̅+r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+-e^(-9·⅟2+-r²·⅟2+3·r)·⅟2)·r·√2̅+((-⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+-e^(-9·⅟2+-r²·⅟2+3·r)·⅟6)·r²·√2̅+((d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·2·e^(9·⅟2)·⅟√2̅+-e^(-r²·⅟2+3·r)·⅟3)·⅟e^(9·⅟2)·√2̅+(-9·⅟√2̅+3·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)+-3·e^(-9·⅟2+-r²·⅟2+3·r)·⅟√2̅)·⅟√2̅+(((-r·√2̅+2·√2̅)·(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)+-e^(-2+-r²·⅟2+2·r))·e+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·[⅟2≠0]·e·r·√2̅)·⅟e+(-9·r·⅟√2̅+9·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+9·e^(-2+-r²·⅟2+2·r)·⅟2+(((-4·⅟3·⅟√2̅+r·⅟3·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+-e^(-2+-r²·⅟2+2·r)·⅟3)·r·√2̅+((-⅟3·√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+-e^(-2+-r²·⅟2+2·r)·⅟6)·r²·√2̅+((d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2·e²·⅟3·√2̅+-e^(-r²·⅟2+2·r)·⅟3)·⅟e²·√2̅+(-4·⅟3·√2̅+4·r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2·⅟3+-4·e^(-2+-r²·⅟2+2·r)·⅟3·⅟√2̅)·⅟√2̅+(((-⅟3·⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-e^(-r²·⅟2+-⅟2+r)·⅟6)·r²·√2̅+((-⅟3·⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-e^(-r²·⅟2+-⅟2+r)·⅟6)·r·√2̅+((d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·⅟3·√2̅·√e̅+-e^(-r²·⅟2+r)·⅟3)·⅟√e̅·√2̅+(-⅟3·⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·⅟3+-e^(-r²·⅟2+-⅟2+r)·⅟3·⅟√2̅)·√2̅+(-6·r·⅟√2̅+6·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+3·e^(-2+-r²·⅟2+2·r)+(d/dx)⁻¹[e^(-x²)](r·⅟√2̅)·[⅟2≠0]·r·⅟√2̅+-(d/dx)⁻¹[e^(-x²)](r·⅟√2̅)·r·⅟√2̅+-⅟2·⅟e^(r²·⅟2)".dParse.simplify(one));
	//writeln("[-1/0=0]".dParse.simplify(one));
	//writeln("lim[r → -∞](((-3·r·⅟2·⅟√2̅+3·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+3·e^(-r²·⅟2+-⅟2+r)·⅟4)·r·√2̅+((-3·r·⅟2·⅟√2̅+3·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+3·e^(-r²·⅟2+-⅟2+r)·⅟4)·√2̅+-(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·3·⅟2)·√2̅+(((-3·⅟√2̅+3·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)+3·e^(-r²·⅟2+-⅟2+r)·⅟2)·√e̅+-(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·3·[⅟2≠0]·r·⅟√2̅·√e̅)·⅟√e̅+(((-3·⅟√2̅+r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)+e^(-9·⅟2+-r²·⅟2+3·r)·⅟2)·e^(5·⅟2)+-(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·[⅟2≠0]·e^(5·⅟2)·r·⅟√2̅)·⅟e^(5·⅟2)+(((-r·√2̅+2·√2̅)·(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)+-e^(-2+-r²·⅟2+2·r))·e+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·[⅟2≠0]·e·r·√2̅)·⅟e+(((d/dx)⁻¹[e^(-x²)](-r·⅟√2̅)·r·⅟3·⅟√2̅+-⅟6·⅟e^(r²·⅟2))·r²·√2̅+-⅟3·⅟e^(r²·⅟2)·√2̅)·⅟√2̅+(-6·⅟√2̅+6·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-3·e^(-r²·⅟2+-⅟2+r)+(((-√2̅+r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+-e^(-2+-r²·⅟2+2·r)·⅟2)·r·√2̅+(-2·√2̅+2·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)+-e^(-2+-r²·⅟2+2·r)·√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2·[⅟2≠0]·√2̅+(-12·r·⅟√2̅+12·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+6·e^(-2+-r²·⅟2+2·r)+(((-⅟3·√2̅+2·r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-e^(-r²·⅟2+-⅟2+r)·⅟3)·r²·√2̅+((-⅟3·√2̅+2·r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+-e^(-r²·⅟2+-⅟2+r)·⅟3)·r·√2̅+((d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·2·⅟3·√2̅·√e̅+-2·e^(-r²·⅟2+r)·⅟3)·⅟√e̅·√2̅+(-⅟3·√2̅+2·r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·2·⅟3+-e^(-r²·⅟2+-⅟2+r)·⅟3·√2̅)·√2̅+(((-r·⅟3·⅟√2̅+⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+e^(-9·⅟2+-r²·⅟2+3·r)·⅟6)·r²·√2̅+((-r·⅟√2̅+3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+e^(-9·⅟2+-r²·⅟2+3·r)·⅟2)·r·√2̅+(-(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·e^(9·⅟2)·√2̅+e^(-r²·⅟2+3·r)·⅟3)·⅟e^(9·⅟2)·√2̅+(-3·r·⅟√2̅+9·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)+3·e^(-9·⅟2+-r²·⅟2+3·r)·⅟√2̅)·⅟√2̅+(((-6·⅟√2̅+2·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+-e^(-9·⅟2+-r²·⅟2+3·r))·r·√2̅+(-18·⅟√2̅+6·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·2+-6·e^(-9·⅟2+-r²·⅟2+3·r)·⅟√2̅)·⅟√2̅+(((-5·r·⅟2·⅟√2̅+15·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+5·e^(-9·⅟2+-r²·⅟2+3·r)·⅟4)·r·√2̅+(-15·r·⅟2·⅟√2̅+45·⅟2·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·5·⅟2+15·e^(-9·⅟2+-r²·⅟2+3·r)·⅟2·⅟√2̅)·√2̅+(((-4·⅟√2̅+r·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+-e^(-2+-r²·⅟2+2·r))·r·√2̅+((-√2̅+r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+-e^(-2+-r²·⅟2+2·r)·⅟2)·r²·√2̅+((d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2·e²·√2̅+-e^(-r²·⅟2+2·r))·⅟e²·√2̅+(-4·√2̅+4·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2+-4·e^(-2+-r²·⅟2+2·r)·⅟√2̅)·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·3·[⅟2≠0]·⅟√2̅+(((-r·⅟√2̅+√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+e^(-2+-r²·⅟2+2·r)·⅟2)·r²·√2̅+((-r·√2̅+4·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+e^(-2+-r²·⅟2+2·r))·r·√2̅+(-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2·e²·√2̅+e^(-r²·⅟2+2·r))·⅟e²·√2̅+(-4·r·⅟√2̅+4·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·2+4·e^(-2+-r²·⅟2+2·r)·⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅)·r·⅟√2̅+⅟2·⅟e^(r²·⅟2)+-(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·[⅟2≠0]·√2̅+(-3·r·⅟√2̅+3·√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+3·e^(-2+-r²·⅟2+2·r)·⅟2+(((-3·⅟√2̅+r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+-e^(-9·⅟2+-r²·⅟2+3·r)·⅟2)·r·√2̅+((-⅟√2̅+r·⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+-e^(-9·⅟2+-r²·⅟2+3·r)·⅟6)·r²·√2̅+((d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·2·e^(9·⅟2)·⅟√2̅+-e^(-r²·⅟2+3·r)·⅟3)·⅟e^(9·⅟2)·√2̅+(-9·⅟√2̅+3·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)+-3·e^(-9·⅟2+-r²·⅟2+3·r)·⅟√2̅)·√2̅+((-(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅)·r·⅟3·⅟√2̅+⅟6·⅟e^(r²·⅟2))·r²·√2̅+⅟3·⅟e^(r²·⅟2)·√2̅)·√2̅+(-66·⅟√2̅+22·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+-11·e^(-9·⅟2+-r²·⅟2+3·r)+(((-r·⅟√2̅+√2̅)·(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)+-e^(-2+-r²·⅟2+2·r)·⅟2)·e²+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·[⅟2≠0]·e²·r·⅟√2̅)·⅟e²+(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+r·⅟√2̅)·3·[⅟2≠0]·⅟√2̅+(((-r·⅟3·⅟√2̅+⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+e^(-r²·⅟2+-⅟2+r)·⅟6)·r²·√2̅+((-r·⅟3·⅟√2̅+⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)+e^(-r²·⅟2+-⅟2+r)·⅟6)·r·√2̅+(-(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·⅟3·√2̅·√e̅+e^(-r²·⅟2+r)·⅟3)·⅟√e̅·√2̅+(-r·⅟3·⅟√2̅+⅟3·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-⅟√2̅+r·⅟√2̅)·⅟3+e^(-r²·⅟2+-⅟2+r)·⅟3·⅟√2̅)·⅟√2̅+(d/dx)⁻¹[e^(-x²)](r·⅟√2̅)·[⅟2≠0]·r·⅟√2̅+-(d/dx)⁻¹[e^(-x²)](r·⅟√2̅)·r·⅟√2̅+-⅟2·⅟e^(r²·⅟2)+(-12·r·⅟√2̅+36·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+3·⅟√2̅)+6·e^(-9·⅟2+-r²·⅟2+3·r)+(((-8·⅟√2̅+4·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)+-2·e^(-2+-r²·⅟2+2·r))·r·√2̅+(-8·√2̅+8·r·⅟√2̅)·(d/dx)⁻¹[e^(-x²)](-r·⅟√2̅+2·⅟√2̅)·√2̅+(d/dx)⁻¹[e^(-x²)](-√2̅+r·⅟√2̅)·4+-8·e^(-2+-r²·⅟2+2·r)·⅟√2̅)·⅟√2̅".dParse.simplify(one));
	//writeln("lim[r → ∞]e^(r²)·r²".dParse.simplify(one));
	//writeln("lim[r → ∞]e^(r²)·r".dParse.simplify(one));
	//writeln("[-1/0=0]".dParse.simplify(one));
	//writeln("(∫dξ₁((-(d/dx)⁻¹[e^(-x²)](ξ₁·⅟√2̅)·⅟√2̅+⅟√2̅·√π̅)·δ[c]+(d/dx)⁻¹[e^(-x²)](ξ₁·⅟√2̅)·δ[-c+1]·⅟√2̅)·⅟e^(ξ₁²·⅟2))·⅟π".dParse.simplify(one));
	//writeln("lim[r→∞](((d/dx)⁻¹[e^(-x²)](r·⅟√2̅))²·δ[-c+1]·⅟2+(d/dx)⁻¹[e^(-x²)](r·⅟√2̅)·δ[c]·√π̅+-((d/dx)⁻¹[e^(-x²)](r·⅟√2̅))²·δ[c]·⅟2)".dParse.simplify(one));
	//writeln("lim[r → -∞]((d/dx)⁻¹[e^(-x²)](r))²".dParse.simplify(one));
	//writeln("(∫dx((d/dx)⁻¹[e^(-x²)](-skill1·⅟√3̅0̅+x·⅟√3̅0̅)·e^(skill1²·⅟30)·⅟600·√3̅0̅+-e^(skill1²·⅟30)·⅟600·√3̅0̅·√π̅)·(d/dx)⁻¹[e^(-x²)](-y·⅟√3̅0̅+x·⅟√3̅0̅)·e^(-x²·⅟30+skill1·x·⅟15))".dParse.simplify(one));
	//writeln("[d≠0]·(-[d≠0]·log(d)³·⅟2+4·[d≤0]·log(0)³·⅟3+log([d≠0])·log(d)²+log(d)³·⅟3)·([-1+d≤0]·[d≠0]+[d≤0])·[-d≤0]".dParse.simplify(one));
	//writeln("([-a+b≤0]·[-b≤0]·[a≠0]·⅟a+[a=0]·δ[b])·[-1+a≤0]·[-a≤0]".dParse.simplify(one));
	//writeln("∫dx 1/x·[-2≤x]·[x≤-1]".dParse.simplify(one));// TODO: fix!
	//writeln("log(x^2)".dParse.simplify(one));
	//writeln("(∫dξ₁[-1+-ξ₁≤0]·[-ξ₁≠0]·[ξ₁≤0]·log(-ξ₁))".dParse.simplify(one));
	//writeln("∫dx log(x^2)·[-1≤x]·[x≤1]".dParse.simplify(one));
	//writeln("∫dX1∫dX2∫dX3(([-X2+-X3+X2·X3≤0]·⅟(-X2·X3+X2+X3)+[-X2·X3+X2+X3≠0]·[-X2·X3+X2+X3≤0]·⅟(-X2+-X3+X2·X3))·[(-X2·X3+X2+X3)·X4≠0]·[-X2·X3·X4+X2·X4+X3·X4≠0]·[-X2≤0]·[-X3≤0]·[-X4≤0]·[-r·⅟(-X2·X3·X4+X2·X4+X3·X4)≤0]·[X4≠0]·e^(-X2+-X3+-X4+-r·⅟(-X2·X3·X4+X2·X4+X3·X4))·δ[-lambda+1]·δ[-r·⅟(-X2·X3·X4+X2·X4+X3·X4)+X1]·⅟X4+[(-X2·X3+X2+X3)·X4=0]·[-X1≤0]·[-X2·X3·X4+X2·X4+X3·X4≠0]·[-X2≤0]·[-X3≤0]·[-X4≤0]·[X4≠0]·e^(-X1+-X2+-X3+-X4)·δ[-lambda+1]+[-X1≤0]·[-X2·X3·X4+X2·X4+X3·X4=0]·[-X2≤0]·[-X3≤0]·[-X4≤0]·e^(-X1+-X2+-X3+-X4)·δ[-lambda+1]·δ[r])".dParse.simplify(one));
	//writeln("∫dξ₁[-ξ₁≤0]·ξ₁²·⅟e^ξ₁".dParse.simplify(one));
	//writeln("lim[ξ₁ → ∞](-ξ₁²·⅟e^ξ₁)".dParse.simplify(one));
	//writeln("[(-1)·0≠0]".dParse.simplify(one));
	//writeln("∑_x[0≤x]·[x≤1]·δ[x-y]".dParse.simplify(one));
	//writeln("-x".dParse.simplify("[-x+__u₁=0]".dParse));
	//writeln(dInt("w".dVar,"(-∫dξ₁[-1+ξ₁≤0]·[-ξ₁+w≤0]·[-ξ₁≤0]·[ξ₁≠0]·log(⅟ξ₁)·⅟ξ₁)·[-w≤0]·[w≠0])".dParse).simplify(one));
	//writeln(tryGetAntiderivative("x".dVar,"log(1/x)".dParse,one).antiderivative.simplify(one));
	/+DExpr e=one;
	int n=160;
	import std.conv;
	foreach(i;0..n) e=e*dBounded!"[]"(dVar("x"~to!string(i)),zero,one+one);
	foreach(i;0..n) e=dInt(dVar("x"~to!string(i)),e);
	writeln(e);
	writeln(e.simplify(one));+/
	//writeln("∫dx log(2*x+1)^2·[1≤x]·[x≤2]".dParse.simplify(one));
	//writeln(dInt("filter".dVar,dInt("__r₁".dVar,"(∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·δ___r₁[{.x ↦ ξ₁}])·q(γ⃗)·δ_filter[__r₁]·δ[r-filter.x]".dParse)).simplify(one));
	//writeln(dInt("__r₁".dVar,"(∫dξ₁[-1+ξ₁≤0]·[-ξ₁≤0]·δ___r₁[{.x ↦ ξ₁}])·q(γ⃗)·δ_filter[__r₁]".dParse).simplify(one));
	/+auto e="∫dx(∫dy(∫dzδ_x[{.x ↦ y+z,.a ↦ z}]·⅟e^(z²·⅟2))·⅟e^(y²·⅟2))·δ_filter[x]".dParse;
	dw(e);
	writeln(e.simplify(one));+/
	//auto e="(∫dx(∫dy(∫dzδ_filter[{.x ↦ z,.a ↦ z}]·⅟e^(z²·⅟2))·q(γ⃗)·⅟√2̅·⅟√π̅·δ_y[filter]·(∫dzδ_x[y{.a ↦ z}]·⅟e^(z²·⅟2)))·δ___r₃[x{.x ↦ x.a+x.x}])·⅟√2̅·⅟√π̅".dParse;
	/*auto e="(∫dxδ___r₃[filter{.a ↦ x}{.x ↦ filter{.a ↦ x}.a+filter{.a ↦ x}.x}]·⅟e^(x²·⅟2))·(∫dxδ_filter[{.x ↦ x,.a ↦ x}]·⅟e^(x²·⅟2))·q(γ⃗)·⅟2·⅟π".dParse;
	dw(e);
	writeln(dInt("filter".dVar,e).simplify(one));*/
	/+auto e="∫dx f₁(x)·(∫dy f₂(x,y))·(∫dy f₂'(x,y))".dParse;
	dw(e);
	writeln(e.simplify(one));+/
	//auto e="(δ[-a+1]+δ[a])·δ[-b+[a≠0]]".dParse;
	//writeln(e.simplify(one));
	//writeln("δ[x-1]·[x=1]".dParse.simplify(one));
	/+auto e="lim[k→ -∞](((d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+k·⅟√2̅)·3·e^(5·⅟2)·⅟√2̅+-e^(-2+-k²·⅟2+3·k)·⅟2)·⅟e^(5·⅟2)+((d/dx)⁻¹[e^(-x²)](-⅟√2̅+k·⅟√2̅)·⅟3·√2̅·√e̅+-e^(-k²·⅟2+k)·⅟3)·⅟√e̅+(-(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+k·⅟√2̅)·6·e^(9·⅟2)·⅟√2̅+e^(-k²·⅟2+3·k))·⅟e^(9·⅟2)+(-(d/dx)⁻¹[e^(-x²)](-√2̅+k·⅟√2̅)·2·e²·⅟3·√2̅+e^(-k²·⅟2+2·k)·⅟3)·⅟e²+(-(d/dx)⁻¹[e^(-x²)](-√2̅+k·⅟√2̅)·2·e·√2̅+e^(-1+-k²·⅟2+2·k))·⅟e+(d/dx)⁻¹[e^(-x²)]((-k+1)·⅟√2̅)·10·k·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)]((-k+1)·⅟√2̅)·2·k³·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)]((-k+1)·⅟√2̅)·2·⅟√2̅+(d/dx)⁻¹[e^(-x²)]((-k+1)·⅟√2̅)·k·⅟3·√2̅+(d/dx)⁻¹[e^(-x²)]((-k+2)·⅟√2̅)·8·k²·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)]((-k+2)·⅟√2̅)·8·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-3·⅟√2̅+k·⅟√2̅)·3·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅)·k³·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅)·k·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+2·⅟√2̅)·17·⅟3·√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+2·⅟√2̅)·4·k²·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+3·⅟√2̅)·2·k·√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+3·⅟√2̅)·6·k·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+3·⅟√2̅)·6·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+3·⅟√2̅)·k²·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+3·⅟√2̅)·k³·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+⅟√2̅)·2·k·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+⅟√2̅)·2·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+⅟√2̅)·k³·⅟3·⅟√2̅+(d/dx)⁻¹[e^(-x²)](-√2̅+k·⅟√2̅)·6·⅟√2̅+-(d/dx)⁻¹[e^(-x²)]((-k+1)·⅟√2̅)·7·⅟3·√2̅+-(d/dx)⁻¹[e^(-x²)]((-k+1)·⅟√2̅)·k²·√2̅+-(d/dx)⁻¹[e^(-x²)]((-k+2)·⅟√2̅)·4·k·⅟√2̅+-(d/dx)⁻¹[e^(-x²)]((-k+2)·⅟√2̅)·k²·⅟3·√2̅+-(d/dx)⁻¹[e^(-x²)]((-k+2)·⅟√2̅)·k³·⅟3·⅟√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅)·k³·⅟3·√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅)·k·√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+2·⅟√2̅)·25·k·⅟3·⅟√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+2·⅟√2̅)·4·k·⅟3·√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+2·⅟√2̅)·k³·⅟3·√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+3·⅟√2̅)·2·k²·√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+3·⅟√2̅)·9·√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+⅟√2̅)·k²·⅟√2̅+-(d/dx)⁻¹[e^(-x²)](-k·⅟√2̅+⅟√2̅)·√2̅+-(d/dx)⁻¹[e^(-x²)](-⅟√2̅+k·⅟√2̅)·⅟3·√2̅+-(d/dx)⁻¹[e^(-x²)](-√2̅+k·⅟√2̅)·⅟3·√2̅+-2·e^(-2+-k²·⅟2+2·k)·k+-7·e^(-9·⅟2+-k²·⅟2+3·k)·⅟3+-7·e^(-k²·⅟2+-⅟2+k)·⅟6+-e^(-9·⅟2+-k²·⅟2+3·k)·k²·⅟6+-e^(-k²·⅟2+-⅟2+k)·k²·⅟2+5·e^(-2+-k²·⅟2+2·k)·⅟3+e^(-2+-k²·⅟2+2·k)·k²·⅟2+e^(-9·⅟2+-k²·⅟2+3·k)·k+e^(-k²·⅟2+-⅟2+k)·k+k²·⅟6·⅟e^(k²·⅟2)+⅟3·⅟e^(k²·⅟2))".dParse; // TODO: make limit evaluation faster
	dw(e);
	writeln(e.simplify(one));+/
}

/*
[([x=0]+x)·(1+[x=0])≤0]

[x≠0][x≤0]


[x=0]·[(1+x)·(1+[x=0]≤0]

// [([x=0]+x)·(1+[x=0])≤0]

/// [x=0] */
