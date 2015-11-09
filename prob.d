import std.stdio, std.path, std.array, std.string, std.algorithm;
import file=std.file;
import util;
import lexer, parser, expression, error;

import analysis, distrib, dexpr;

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
	scope(exit){ // TODO: get rid of globals
		analysis.functions=(FunctionDef[string]).init;
		analysis.summaries=(Distribution[string]).init;
	}
	if(err.nerrors) return 1;
	if(functions.length==1) foreach(_,x;functions){ functions["main"]=x; break; }
	if("main" !in functions){
		err.error("missing program entry point 'main'",Location(src.code.ptr[0..1],1));
		return 1;
	}
	auto fd=functions["main"];
	auto dist=analyze(fd,err);
	import approximate;
	//import hashtable; dist.distribution=approxLog(dist.freeVars.element);
	// dist.distribution=dist.distribution.killIntegrals();
	auto str=dist.toString();
	//writeln((cast(DPlus)dist.distribution).summands.length);
	if(str.length<10000) writeln(str);
	else{
		writeln("writing output to temporary file...");
		auto f=File("tmp.deleteme","w");
		f.writeln(str);
	}
	bool plotCDF=false;
	if(str.canFind("δ")) plotCDF=true;
	import hashtable;
	if(formatting==Format.matlab && dist.freeVars.length==1){
		if(plotCDF){
			dist=dist.dup();
			auto freeVar=dist.freeVars.element;
			auto nvar=dist.declareVar("foo");
			dist.distribute(dIvr(DIvr.Type.leZ,-freeVar-20)*dIvr(DIvr.Type.leZ,freeVar-nvar));
			dist.marginalize(freeVar);
		}
		writeln("plotting... ",(plotCDF?"(CDF)":"(PDF)"));
		matlabPlot(dist.distribution.toString(),dist.freeVars.element.toString());
	}
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
	foreach(x;args) if(auto r=run(x)) return r;
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
	//writeln("(∫dx((d/dx)⁻¹[e^(-x²)](-10·⅟3·√3̅0̅+x·⅟√3̅0̅))·e^(-x²·⅟30+20·x·⅟3))".dParse.simplify(one));
}

/*
[([x=0]+x)·(1+[x=0])≤0]

[x≠0][x≤0]


[x=0]·[(1+x)·(1+[x=0]≤0]

// [([x=0]+x)·(1+[x=0])≤0]

/// [x=0] */
