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
	auto expr=parseExpression(src,err);
	writeln(expr);
	if(auto fd=cast(FunctionDef)expr){
		analyze(fd,err);
	}else err.error("only single function definition supported",expr.loc);
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
	/*import dparse;
	auto x="x".dVar,y="y".dVar,a="a".dVar,b="b".dVar;
	auto e="(δ[-x+1+[-b+a<0]]·δ[-y+1+[-b+a<0]]·⅟4+δ[-x+[-b+a<0]]·δ[-y+[-b+a<0]]·⅟4)·e^(-a²·⅟2+-b²·⅟2)·δ[-r+[-x+y=0]]·⅟π".dParse;
	//auto e2=dInt(y,dInt(x,e));
	//writeln(dInt(a,dInt(b,e2)));
	//auto e2=dInt(a,e);
	//writeln(e2);
	auto e2="((∫dξ₁δ[-x+1+[-b+ξ₁<0]]·δ[-y+1+[-b+ξ₁<0]]·⅟e^(ξ₁²·⅟2))·⅟4+(∫dξ₁δ[-x+[-b+ξ₁<0]]·δ[-y+[-b+ξ₁<0]]·⅟e^(ξ₁²·⅟2))·⅟4)·δ[-r+[-x+y=0]]·⅟e^(b²·⅟2)·⅟π".dParse;
	writeln(dInt(x,e2));*/
}
