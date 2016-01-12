import dexpr, util;
import std.conv;

bool extremelySimple = true;

DExpr readSpline(string filename){
    import std.file,std.path;
    filename=buildPath(dirName(thisExePath),filename);
    import std.stdio,std.exception,std.conv,std.string,std.range,std.algorithm,std.format;
    auto f=File(filename,"r");
    string s,d;
    DExpr r=zero;
    while(!f.eof){
        double a,b;
        f.readf("Interval: %s %s\n",&a,&b);
        f.readln();
        f.readf("Breaks:\n");
		string ln = f.readln().strip();
        double[] dbreaks = ln.split().map!(a=>a.to!double).array;
        DExpr[] breaks = ln.split().map!(a=>a.to!double.dFloat).array;
        DExpr[] polys;
        f.readln();
        f.readf("Coefs:\n");
        int idx = 0;
        while(!f.eof){
            s=f.readln().strip();
            if(!s.length) break;
            auto as = s.split().map!(q=>q.strip().to!double).array;

            //array conversion:
            double bb = dbreaks[idx];
            double[4] aa;
            aa[0] = as[0];
            aa[1] = -3*as[0]*bb+as[1];
            aa[2] = 3*as[0]*bb*bb-2*as[1]*bb+as[2];
            aa[3] = -as[0]*bb*bb*bb+as[1]*bb*bb-as[2]*bb+as[3];

            polys~=aa.getPoly("x".dVar);
            idx++;

        }
        enforce(breaks.length==polys.length+1);
        DExpr cur=zero;
        foreach(i,p;polys)
            cur=cur+dBounded!"[)"("x".dVar,breaks[i],breaks[i+1])*p;
        r=r+dBounded!"[)"("x".dVar,a.dFloat,b.dFloat)*cur;
    }
    return r;
}
/+
DExpr readSpline(string filename){
	import std.file,std.path;
	filename=buildPath(dirName(thisExePath),filename);
	import std.stdio,std.exception,std.conv,std.string,std.range,std.algorithm,std.format;
	auto f=File(filename,"r");
	string s,d;
	DExpr r=zero;
	while(!f.eof){
		double a,b;
		f.readf("Interval: %s %s\n",&a,&b);
		f.readln();
		f.readf("Breaks:\n");
		DExpr[] breaks=f.readln().strip().split().map!(a=>a.to!double.dFloat).array;
		DExpr[] polys;
		f.readln();
		f.readf("Coefs:\n");
		while(!f.eof){
			s=f.readln().strip();
			if(!s.length) break;
			polys~=s.split().map!(a=>a.strip().to!double).array.getPoly("x".dVar);
		}
		enforce(breaks.length==polys.length+1);
		DExpr cur=zero;
		foreach(i,p;polys)
			cur=cur+dBounded!"[)"("x".dVar,breaks[i],breaks[i+1])*p;
		r=r+dBounded!"[)"("x".dVar,a.dFloat,b.dFloat)*cur;
	}
	return r;
}
+/
DExpr getPoly(double[] coeff,DExpr x){
	DExpr r=zero;
	foreach(c;coeff) r=x*r+c;
	return r;
}

DExpr approxPowEmX2(DExpr e){
	// e^-x²
	auto arg=dAbs(e);
	// range [0, 3]
	auto poly=[0.0422,-0.4013, 1.3594, -1.7601, 0.1268, 1.0000].getPoly(e);
	return dIvr(DIvr.Type.leZ,arg-3)*poly;
}


DExpr approxLog(DExpr e){
	if(extremelySimple) return e;
	static DExpr lowRank(DExpr e){
		// TODO: what about ranges [0, 0.1] and [10, ∞]?
		// range [0.1, 1]
		auto poly1=[629.189738585664, -2557.47417049932, 4210.10819766748,
					-3594.79066567300, 1694.98719011315, -436.987965205420,
					60.1321271299536, -5.16445211851018].getPoly(e);
		// range [1, 10]
		auto poly2=[-0.000711707042556582, 0.0204319245831799,
					-0.220870997847981, 1.20818665998564, -1.00703587967828].getPoly(e);
		return dBounded!"[)"(e,one/10,one)*poly1+dBounded!"[]"(e,one,10.dℕ)*poly2;
	}
	static DExpr highRank(DExpr e){
		// range [0.01,0.1]
		auto poly1=[8.33924931243684e+37,-1.38448847367748e+38,1.09789681049334e+38,5.53588701418023e+37, 1.99333063839673e+37,5.45730392106319e+36,1.18105511385670e+36,2.07390259366921e+35,3.00968010207696e+34, 3.65818105425341e+33,3.76093508104837e+32,3.29429848516511e+31,2.47145334519956e+30,1.59387334453680e+29,8.85668812065035e+27,4.24517303721067e+26,1.75527267593215e+25,6.25438280563899e+23,1.91657090589424e+22, 5.03496788039178e+20,1.12902946108667e+19,2.14860887878946e+17,3.44473649901208e+15,-46095680385144.1,508887785535.922,-4569677562.69449,32852966.9944322,-187203.816939001,891.776443090930,-7.40013399100580].getPoly(e);
		// range [0.1,1]
		auto poly2=[833925419.553065,-13844892647.1214,109789742217.473,553589001959.898,1993331692102.71    -5457306727624.33,11810557042139.8,20739036001901.9,30096815186017.0,36581827216663.7,37609367385805.3,32942998864324.1,24714543576460.5,15938739717878.3,8856691459009.93,4245174564395.46,1755273276041.85,625438482742.261,191657148803.947,50349693064.3232,11290297564.3178,2148609391.69910,344473723.785697,46095689.0873808,5088878.67733246,456967.816871622,32852.9703459790,1872.03829986515,89.1776474903186,5.09754893448038].getPoly(e);
		// range [1,25]
		auto poly3=[3.53883870298634e-30,-1.39051713013730e-27,2.60129465817788e-25,-3.08339600313628e-23,2.60005170389296e-21,-1.66015333978385e-19,8.34181012769820e-18,-3.38439271515543e-16,1.12877822908676e-14,-3.13497679999116e-13,7.31812433947678e-12,-1.44543971123940e-10,2.42682189780325e-09,-3.47368427979986e-08,4.24537661554150e-07,-4.43124175838952e-06,3.94655964815207e-05,-0.000299298091796461,0.00192660626516797,-0.0104803912313830,0.0479053974936664,-0.182686444312484,0.576106041396074,-1.48616969106739,3.09518676628554,-5.12323876048504,6.62433183808435,-6.61517043746744,5.37544545199921,-2.30288278239982].getPoly(e);
		// range [25,100]
		auto poly4=[1.22006951245921e-24,-1.07927540176132e-21,4.37186257885746e-19,-1.07448940838427e-16,1.78967261746471e-14,-2.13700141853378e-12,1.88717903657241e-10,-1.25332347685452e-08,6.30391369802035e-07,-2.40080715004789e-05,0.000688824677924401,-0.0148663128031954,0.256332158354622,0.736225462997239].getPoly(e);
		// range [100,500]
		auto poly5=[2.43542340628601e-33,-1.03529597572680e-29,2.00828921842591e-26,-2.35465763987871e-23,1.86314524468595e-20,-1.05206393763891e-17,4.37181002325059e-15,-1.35893249391710e-12,3.18083386744081e-10, -5.60323855913639e-08,7.38859803452352e-06,-0.000728017086549864,0.0569203721761814,2.23760191982052].getPoly(e);
		// range [500,3000]
		auto poly6=[3.64797006769141e-43,-9.05410980815970e-39,1.02265987367689e-34,-6.96047538865881e-31,3.18636659549754e-27,-1.03704347483133e-23,2.47351714069082e-20,-4.39299907920198e-17,5.84575749289629e-14,-5.82271150576115e-11,4.31642109915334e-08,-2.37648818759322e-05,0.0103170845178250,3.94224075426239].getPoly(e);
		return dBounded!"[)"(e,one/100,one/10)*poly1
			+ dBounded!"[)"(e,one/10,one)*poly2
			+ dBounded!"[)"(e,one,25.dℕ)*poly3
			+ dBounded!"[)"(e,25.dℕ,100.dℕ)*poly4
			+ dBounded!"[)"(e,100.dℕ,500.dℕ)*poly5
			+ dBounded!"[]"(e,500.dℕ,3000.dℕ);
	}
	static DExpr discretize(DExpr e,double left,double right,int steps){
		DExpr r=zero;
		double dx=(right-left)/steps;
		for(double x=left;x<right;x+=dx){
			import std.math: log;
			r=r+log(x)*dBounded!"[)"(e,x.dFloat,(x+dx).dFloat);
		}
		return r;
	}
	//return lowRank(e);
	//return highRank(e);
	//return discretize(e,0.00001,2,20);
	static DExpr logSpline=null;
	if(!logSpline) logSpline=readSpline("approximations/logSpline.txt");
	return logSpline.substitute("x".dVar,e);
}

DExpr approxGaussInt(DExpr e){
	if(extremelySimple) return e*dBounded!"[]"(e,one/10000,one);
	static DExpr scaledErfSpline=null;
	if(!scaledErfSpline){
		scaledErfSpline=readSpline("approximations/erfSpline.txt");
		scaledErfSpline=scaledErfSpline-scaledErfSpline.substitute("x".dVar,-"x".dVar);
		scaledErfSpline=(scaledErfSpline+1)/2;
	}
	return scaledErfSpline.substitute("x".dVar,e);
}


// TODO: get rid of code duplication here?
DExpr approxInvX(DExpr e){
	if(extremelySimple) return e*dBounded!"[]"(e,zero,one);
	static DExpr invxSpline=null;
	if(!invxSpline){
		invxSpline=readSpline("approximations/invxSpline.txt");
		invxSpline=invxSpline-invxSpline.substitute("x".dVar,-"x".dVar);
	}
	return invxSpline.substitute("x".dVar,e);
}

DExpr approxInvSqrt(DExpr e){
	if(extremelySimple) return e*dBounded!"[]"(e,zero,one);
	static DExpr invSqrtSpline=null;
	if(!invSqrtSpline)
		invSqrtSpline=readSpline("approximations/invSqrtSpline.txt");
	return invSqrtSpline.substitute("x".dVar,e);
}

DExpr approxSqrt(DExpr e){
	if(extremelySimple) return e*dBounded!"[]"(e,zero,one);
	static DExpr sqrtSpline=null;
	if(!sqrtSpline)
		sqrtSpline=readSpline("approximations/sqrtSpline.txt");
	return sqrtSpline.substitute("x".dVar,e);
}

DExpr approximate(DExpr e){
	static DExpr doIt(DExpr e, bool necessary)out(r){ assert(e !is r,text(e));}body{
		if(auto p=cast(DPlus)e){
			DExprSet summands=p.summands.dup;
			foreach(s;p.summands){
				if(auto k=doIt(s,necessary)){
					summands.remove(s);
					DPlus.insert(summands,k);
					return dPlus(summands);
				}
			}
		}
		if(auto m=cast(DMult)e){
			DExprSet factors=m.factors.dup;
			foreach(f;m.factors){
				if(auto k=doIt(f,necessary)){
					factors.remove(f);
					DMult.insert(factors,k);
					return dMult(factors);
				}
			}
		}
		if(auto p=cast(DPow)e){
			if(auto k=doIt(p.operands[0],necessary)) return k^^p.operands[1];
			if(auto k=doIt(p.operands[1],necessary)) return p.operands[0]^^k;
		}
		if(auto ivr=cast(DIvr)e){
			if(auto r=doIt(ivr.e,necessary))
				return dIvr(ivr.type,r);
		}
		if(auto delta=cast(DDelta)e){
			if(auto r=doIt(delta.e,necessary))
				return dDelta(r);
		}
		if(auto intg=cast(DInt)e){
			auto tmpvar=new DVar("tmp"); // TODO: get rid of this!
			auto intExpr=intg.getExpr(tmpvar);
			if(auto r=doIt(intExpr,true))
				return dInt(tmpvar,r);
		}
		if(necessary){
			if(auto l=cast(DLog)e){
				return approxLog(l.e);
			}
			if(auto g=cast(DGaussInt)e){
				return approxGaussInt(g.x);
			}
			if(auto p=cast(DPow)e){
				if(!e.isFraction()){
					if(p.operands[1] is mone){
						return approxInvX(p.operands[0]);
					}else if(p.operands[1] is -(one/2)){
						return approxInvSqrt(p.operands[0]);
					}else if(p.operands[1] is one/2){
						return approxSqrt(p.operands[0]);
					}
					if(auto k=doIt(p.operands[0],necessary))
						return k^^p.operands[1];
					if(auto k=doIt(p.operands[1],necessary))
						return p.operands[0]^^k;
				}
			}
		}
		return null;
	}
	return doIt(e,false);
}

DExpr killIntegrals(DExpr e){
	for(;;){
		if(auto r=e.approximate()){
			e=r.simplify(one);
		}else break;
	}
	return e;
}



DExpr approxGaussianPDF(DVar var,DExpr μ,DExpr σsq){
	auto dist=3*one/(4*(5*σsq)^^(one/2))*(1-(var-μ)^^2/(5*σsq))*dBounded!"[]"(var-μ,-(5*σsq)^^(one/2),(5*σsq)^^(one/2));
	return dIvr(DIvr.Type.neqZ,σsq)*dist+dIvr(DIvr.Type.eqZ,σsq)*dDelta(var-μ);
}

