// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.uni, std.array, std.string, std.conv, std.algorithm, std.range;
import dexpr,util;

struct DParser{
	string code;
	int numBinders=0;
	void skipWhitespace(){
		while(!code.empty&&code.front.isWhite())
			next();
	}
	dchar cur(){
		skipWhitespace();
		if(code.empty) return 0;
		return code.front;
	}
	void next(){ code.popFront(); }
	void expect(dchar c,bool consume=true){
		if(cur()==c){ if(consume) next(); }
		else throw new Exception("expected '"~to!string(c)~"' at \""~code~"\"");
	}
	DExpr parseDIvrRhs(DExpr exp){
		DIvr.Type ty;
		DExpr cexp,nexp;
		void doIt(DIvr.Type t,bool negate){
			next();
			cexp=parseDExpr();
			nexp=exp-cexp;
			ty=t;
			if(negate) nexp=-nexp;
		}
		switch(cur()) with(DIvr.Type){
			case '=': doIt(eqZ,false); break;
			case '≠','!':
				if(cur()=='!'){ next(); expect('=',false); } doIt(neqZ,false); break;
			case '<','>':
				bool b=cur()=='>';
				if(code.length>=2&&code[1]=='='){
					next(); doIt(leZ,b);
				}else doIt(lZ,b); break;
			case '≤','≥': doIt(leZ,cur=='≥'); break;
			default: expect('<'); assert(0);
		}
		if(util.among(cur(),'<','>','≤','≥','=','≠'))
			return dIvr(ty,nexp)*parseDIvrRhs(cexp);
		expect(']');
		return dIvr(ty,nexp);
	}
	DExpr parseDIvr(){
		expect('[');
		auto exp=parseDExpr();
		return parseDIvrRhs(exp);
	}
	DExpr parseDFloor(){
		expect('⌊');
		auto exp=parseDExpr();
		expect('⌋');
		return dFloor(exp);
	}
	DExpr parseDCeil(){
		expect('⌈');
		auto exp=parseDExpr();
		expect('⌉');
		return dCeil(exp);
	}
	DExpr parseDDelta(){
		if(code.startsWith("delta")) code=code["delta".length..$];
		else expect('δ');
		bool round=false;
		auto expr=parseParenthesized('(',')');
		auto var=parseParenthesized('[',']');
		return expr is zero?dDelta(var):dDiscDelta(expr,var);
	}
		
	DExpr parseSqrt(){
		DExpr e=one/2;
		if(cur()=='∛'){ next(); e=one/3; }
		else if(cur()=='∜'){ next(); e=one/4; }
		else expect('√');
		if(code.startsWith("(") && !code.startsWith("(̅"))
			return parseParenthesized('(',')')^^e;
		string arg;
		dchar cur=0;
		string tmp=code;
		for(int i=0;!tmp.empty;){
			dchar c=tmp.front;
			if(i&1){
				if(c=='̅'){
					arg~=cur;
				}else break;
			}else cur=c;
			tmp.popFront();
			if(i&1) code=tmp;
			i++;
		}
		return dParse(arg)^^e;
	}

	DExpr parseDAbs(){
		if(code.startsWith("abs")){
			code=code["abs".length..$];
			auto arg=parseParenthesized('(',')');
			return dAbs(arg);
		}
		expect('|');
		auto l=code.indexOf('|');
		if(l==-1) l=code.length;
		auto arg=DParser(code[0..l]).parseDExpr();
		code=code[l..$];
		expect('|');
		return dAbs(arg);
	}

	DExpr parseLog()in{assert(code.startsWith("log"));}body{
		code=code["log".length..$];
		auto e=parseParenthesized('(',')');
		return dLog(e);
	}

	DExpr parseGaussInt()in{assert(code.startsWith("(d/dx)⁻¹[e^(-x²)]"));}body{
		if(code.startsWith("(d/dx)⁻¹[e^(-x²)]⁻¹")){
			code=code["(d/dx)⁻¹[e^(-x²)]⁻¹".length..$];
			auto e=parseParenthesized('(',')');
			return dGaussIntInv(e);
		}
		code=code["(d/dx)⁻¹[e^(-x²)]".length..$];
		auto e=parseParenthesized('(',')');
		return dGaussInt(e);
	}

	DExpr parseDInt(){
		expect('∫');
		expect('d');
		++numBinders;
		auto iVar=parseDVar();
		if(!cast(DDeBruijnVar)iVar) --numBinders;
		auto iExp=parseMult();
		if(cast(DDeBruijnVar)iVar) --numBinders;
		if(auto dbv=cast(DDeBruijnVar)iVar){
			assert(dbv.i==1);
			return dInt(iExp);
		}
		return dInt(iVar,iExp);
	}

	DExpr parseDSum(){
		if(code.startsWith("sum")){
			code=code["sum".length..$];
		}else expect('∑');
		expect('_');
		++numBinders;
		auto iVar=parseDVar();
		if(!cast(DDeBruijnVar)iVar) --numBinders;
		auto iExp=parseMult();
		if(cast(DDeBruijnVar)iVar) --numBinders;
		if(auto dbv=cast(DDeBruijnVar)iVar){
			assert(dbv.i==1);
			return dSum(iExp);
		}
		return dSum(iVar,iExp);
	}

	DExpr parseLim()in{assert(code.startsWith("lim"));}body{
		code=code["lim".length..$];
		expect('[');
		++numBinders;
		auto var=parseDVar();
		--numBinders;
		expect('→');
		auto e=parseDExpr();
		expect(']');
		if(cast(DDeBruijnVar)var) ++numBinders;
		auto x=parseMult();
		if(cast(DDeBruijnVar)var) --numBinders;
		return dLim(var,e,x);
	}

	DExpr parseDiff()in{assert(code.startsWith("d/d"));}body{
		code=code["d/d".length..$];
		++numBinders;
		auto var=parseDVar();
		--numBinders;
		expect('[');
		if(cast(DDeBruijnVar)var) ++numBinders;
		auto e=parseDExpr();
		if(cast(DDeBruijnVar)var) --numBinders;
		expect(']');
		DExpr x;
		if(cur()=='('){
			next();
			x=parseDExpr();
			expect(')');
		}else x=var;
		return dDiff(var,e,x);
	}
	
	DExpr parseNumber()in{assert('0'<=cur()&&cur()<='9');}body{
		ℤ r=0;
		while('0'<=cur()&&cur()<='9'){
			r=r*10+cast(int)(cur()-'0');
			next();
		}
		if(cur()=='.'){
			string s="0.";
			for(next();'0'<=cur()&&cur()<='9';next()) s~=cur();
			return (s.to!real+toReal(r)).dFloat; // TODO: this is a hack
		}
		return dℚ(r);
	}

	bool isIdentifierChar(dchar c){
		if(c=='δ') return false; // TODO: this is quite crude
		if(c.isAlpha()) return true;
		if(lowDigits.canFind(c)) return true;
		if(c=='₋') return true;
		if(c=='_') return true;
		if(c=='`') return true; // for "`q"
		return false;
	}

	string parseIdentifier(){
		skipWhitespace();
		string r;
		while(!code.empty&&(isIdentifierChar(code.front)||!r.empty&&'0'<=code.front()&&code.front<='9')){
			r~=code.front;
			code.popFront();
		}
		while(!code.empty&&code.front=='\''){
			r~=code.front;
			code.popFront();
		}
		if(r=="") expect('ξ');
		return r;
	}

	private DVar varOrBound(string s){
		if(s.startsWith("ξ")){
			auto i=0;
			auto rest=s["ξ".length..$];
			bool neg=false;
			if(!rest.empty&&rest.front=='₋'){ neg=true; rest.popFront(); }
			for(;!rest.empty();rest.popFront())
				i=10*i+cast(int)indexOf(lowDigits,rest.front);
			if(neg) i=-i;
			return dDeBruijnVar(numBinders-i+1);
		}
		return dVar(s);
	}
	
	DVar parseDVar(){
		string s=parseIdentifier();
		return varOrBound(s);
	}

	DExpr parseDLambda(){
		expect('λ');
		if(cur()=='('){
			DVar[] args;
			do{
				next();
				if(cur()!=')') args~=parseDVar();
			}while(cur()==',');
			expect(')');
			expect('.');
			auto expr=parseDExpr();
			return dTupleLambda(args,expr);
		}
		++numBinders;
		auto var=parseDVar();
		if(!cast(DDeBruijnVar)var) --numBinders;
		expect('.');
		auto expr=parseDExpr();
		if(cast(DDeBruijnVar)var) --numBinders;
		return dLambda(var,expr);
	}

	DExpr parseDDistLambda(){
		expect('Λ');
		++numBinders;
		auto var=parseDVar();
		if(!cast(DDeBruijnVar)var) --numBinders;
		expect('.');
		auto expr=parseDExpr();
		if(cast(DDeBruijnVar)var) --numBinders;
		return dDistLambda(var,expr);
	}

	
	DVal parseDVal()in{assert(code.startsWith("val"));}body{
		code=code["val".length..$];
		auto e=parseParenthesized('(',')');
		return dVal(e);
	}

	DErr parseDErr(){
		expect('⊥');
		return dErr();
	}

	DMCase parseDMCase()in{assert(code.startsWith("case"));}body{
		code=code["case".length..$];
		auto e=parseParenthesized('(',')');
		expect('{');
		skipWhitespace();
		if(!code.startsWith("val"))
			throw new Exception("expected 'val' case");
		code=code["val".length..$];
		expect('(');
		++numBinders;
		auto var=parseDVar();
		if(!cast(DDeBruijnVar)var) --numBinders;
		expect(')');
		expect('⇒');
		auto val=parseDExpr();
		if(cast(DDeBruijnVar)var) --numBinders;
		expect(';');
		expect('⊥');
		expect('⇒');
		auto err=parseDExpr();
		expect('}');
		// TODO: create a dMCase constructor?
		if(var==db1) return dMCase(e,val,err);
		return dMCase(e,val.incDeBruijnVar(1,0).substitute(var,db1),err);
	}

	DExpr parseParenthesized(dchar left,dchar right){
		expect(left);
		if(cur()==right) return dTuple([]);
		auto r=parseDExpr();
		if(cur()==','){
			auto values=[r];
			while(cur()==','){
				next();
				if(cur()==right) break;
				values~=parseDExpr();
			}
			expect(right);
			return dTuple(values);
		}
		expect(right);
		return r;
	}

	DExpr parseBase(){
		if(code.startsWith("(d/dx)⁻¹[e^(-x²)]")) return parseGaussInt();
		if(cur()=='(') return parseParenthesized('(',')');
		if(cur()=='['){
			if(code.length>=2 && code[1]==']'){
				code=code[2..$];
				return dArray(zero);
			}
			int nesting=0;
			foreach(i,c;code){
				if(c=='[') nesting++;
				if(c==']') nesting--;
				if(nesting) continue;
				auto p=DParser(code[i+1..$]);
				if(p.cur()!='(') break;
				next();
				++numBinders;
				auto var=parseDVar();
				expect('↦');
				if(!cast(DDeBruijnVar)var) --numBinders;
				auto expr=parseDExpr();
				if(cast(DDeBruijnVar)var) --numBinders;
				expect(']');
				expect('(');
				auto len=parseDExpr();
				expect(')');
				return dArray(len,dLambda(var,expr));
			}
		}
		if(cur()=='⌊') return parseDFloor();
		if(cur()=='⌈') return parseDCeil();
		if(cur()=='{'){
			next();
			DExpr[string] values;
			while(cur()=='.'){
				next();
				auto f=parseIdentifier();
				expect('↦');
				auto e=parseDExpr();
				values[f]=e;
				if(cur()==',') next();
				else break;
			}
			expect('}');
			return dRecord(values);
		}
		if(cur()=='∞'){ next(); return dInf; }
		if(cur()=='[') return parseDIvr();
		if(cur()=='δ'||code.startsWith("delta")) return parseDDelta();
		if(cur()=='∫') return parseDInt();
		if(cur()=='∑'||code.startsWith("sum")) return parseDSum();
		if(cur()=='λ') return parseDLambda();
		if(cur()=='Λ') return parseDDistLambda();
		if(util.among(cur(),'√','∛','∜')) return parseSqrt();
		if(cur()=='|'||code.startsWith("abs")) return parseDAbs();
		if(code.startsWith("log")) return parseLog();
		if(code.startsWith("lim")) return parseLim();
		if(code.startsWith("d/d")) return parseDiff();
		if(code.startsWith("val")) return parseDVal();
		if(code.startsWith("⊥")) return parseDErr();
		if(code.startsWith("case")) return parseDMCase();
		if(cur()=='⅟'){
			next();
			return 1/parseFactor();
		}
		if('0'<=cur()&&cur()<='9')
			return parseNumber();
		if(cur()=='e'){
			next();
			return dE;
		}
		if(cur()=='π'){
			next();
			return dΠ;
		}
		return parseDVar();
	}

	bool isDIvr(){
		try DParser(this.tupleof).parseDIvr(); // TODO: improve
		catch(Exception) return false;
		return true;
	}

	DExpr parsePostfix(){
		auto e=parseBase();
		while(cur()=='('||cur()=='['||code.startsWith("@[")||cur()=='{'||cur()=='.'){
			if(isDIvr()) return e;
			if(cur()=='('){
				DExpr[] args;
				bool isTuple=false;
				for(;;){
					next();
					if(cur()!=')') args~=parseDExpr();
					if(cur()==',') isTuple=true;
					else break;
				}
				expect(')');
				if(!args.length) isTuple=true;
				e=dApply(e,isTuple?dTuple(args):args[0]);
			}else if(cur()=='['){
				DExpr[] args;
				bool isTuple=false;
				for(;;){
					next();
					if(cur()!=']') args~=parseDExpr();
					if(cur()==',') isTuple=true;
					else break;
				}
				expect(']');
				e=dDistApply(e,isTuple?dTuple(args):args[0]);
			}else if(code.startsWith("@[")){
				code=code["@[".length..$];
				auto i=parseDExpr();
				if(cur()=='↦'){
					next();
					auto n=parseDExpr();
					e=dIUpdate(e,i,n);
				}else e=dIndex(e,i);
				expect(']');
			}else if(cur()=='{'){
				next();
				expect('.');
				auto f=parseIdentifier();
				expect('↦');
				auto n=parseDExpr();
				e=dRUpdate(e,f,n);
				expect('}');
			}else{
				assert(cur()=='.');
				next();
				auto i=parseIdentifier();
				e=dField(e,i);
			}
		}
		return e;
	}
	

	DExpr parseDPow(){
		auto e=parsePostfix();
		if(cur()=='^'){
			next();
			return e^^parseFactor();
		}
		ℤ exp=0;
		if(highDigits.canFind(cur())){
			do{
				exp=10*exp+highDigits.indexOf(cur());
				next();
			}while(highDigits.canFind(cur));
			return e^^exp;
		}
		return e;
	}

	DExpr parseFactor(){
		if(cur()=='-'){
			next();
			return -parseFactor();
		}
		if(cur()=='+'){
			next();
			return parseFactor();
		}
		return parseDPow();
	}

	static bool isBinaryOp(dchar c){
		return isMultChar(c)||isDivChar(c)||isAddChar(c)||isSubChar(c)||
			c == '↦' || c == '!' || c == '=' || c == '≠' ||
			c == '≤' || c == '≥' || c == '<' || c == '>';
	}
	
	bool hasFactor(){
		return code.length && !isBinaryOp(cur())
			&& cur()!=')' && cur()!='}' && cur()!=']' && cur() != '⌋' && cur() != '⌉' && cur!=',' && cur != ';';
	}

	DExpr parseJMult(){
		DExpr f=parseFactor();
		while(hasFactor())
			f=f*parseFactor();
		return f;
	}
	
	static bool isMultChar(dchar c){
		return "·*"d.canFind(c);
	}
	static bool isDivChar(dchar c){
		return "÷/"d.canFind(c);
	}

	static bool isAddChar(dchar c){
		return c=='+';
	}
	static bool isSubChar(dchar c){
		return c=='-';
	}

	DExpr parseMult(){
		DExpr f=parseJMult();
		while(isMultChar(cur())||isDivChar(cur())){
			if(isMultChar(cur())){
				next();
				f=f*parseJMult();
			}else{
				next();
				f=f/parseJMult();
			}
		}
		return f;
	}

	DExpr parseAdd(){
		DExpr s=parseMult();
		while(isAddChar(cur())||isSubChar(cur())){
			auto x=cur();
			next();
			auto c=parseMult();
			if(x=='-') c=-c;
			s=s+c;
		}
		return s;
	}

	DExpr parseDExpr(){
		return parseAdd();
	}
}
DExpr dParse(string s){ // TODO: this is work in progress, usually updated in order to speed up debugging
	return DParser(s).parseDExpr();
}

