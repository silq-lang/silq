import std.array, std.typetuple, std.algorithm, std.conv;
import std.traits: EnumMembers;
import lexer, error, util, expression, type, declaration;
// (re-purposed D parser, a little bit messy for now.)


enum unaryOps = ["&", "*", "-", "++", "--", "+", "!", "~"];
enum postfixOps=[/*".",*/"++", "--","(","["];
//alias canFind!("a==b",TokenType[],TokenType) _canFind;
enum binaryOps=mixin({string r="[";
		foreach(x;EnumMembers!TokenType)if(getLbp(x)!=-1&&!canFind([Tok!"++",Tok!"--",Tok!"(",Tok!"["],x)) r~=`"`~TokenTypeToString(x)~`",`;
		return r~"]";
	}());

bool isRelationalOp(TokenType op){
	switch(op){
		// relational operators
		case Tok!"==",Tok!"!=",Tok!">",Tok!"<":
		case Tok!">=",Tok!"<=",Tok!"!>",Tok!"!<":
		case Tok!"!>=",Tok!"!<=",Tok!"<>",Tok!"!<>":
		case Tok!"<>=", Tok!"!<>=":
			return true;
		default: return false;
	}
}

// expression parser:

// left binding power
template lbp(TokenType type){enum lbp=getLbp(type);}
// right binding power: ^^, (op)=, ? bind weaker to the right than to the left, '.' binds only primaryExpressions
template rbp(TokenType type){enum rbp=type==Tok!"."?180:lbp!type-(type==Tok!"^"||lbp!type==30||type==Tok!"?");}

int getLbp(TokenType type) pure{ // operator precedence
	switch(type){
	//case Tok!"..": return 10; // range operator
	case Tok!",":  return 10; // comma operator
	// assignment operators
	case Tok!":": // type annotation
		return 20;
	case Tok!"/=",Tok!"&=",Tok!"|=",Tok!"-=":
	case Tok!"+=",Tok!"<<=",Tok!">>=", Tok!">>>=":
	case Tok!"=",Tok!"*=",Tok!"%=",Tok!"^=":
	case Tok!"&&=", Tok!"||=", Tok!"~=":
	case Tok!":=":
		return 30;
	// logical operators
	case Tok!"?":  return 40; // conditional operator
	case Tok!"||": return 50; // logical OR
	case Tok!"&&": return 60; // logical AND
	// relational operators
	case Tok!"==",Tok!"!=",Tok!">",Tok!"<":
	case Tok!">=",Tok!"<=",Tok!"!>",Tok!"!<":
	case Tok!"!>=",Tok!"!<=",Tok!"<>",Tok!"!<>":
	case Tok!"<>=", Tok!"!<>=":
		return 100;
	// shift operators
	case Tok!">>", Tok!"<<":
	case Tok!">>>": return 110;
	// additive operators
	case Tok!"+",Tok!"-",Tok!"~":
		return 120;
	// multiplicative operators
	case Tok!"*",Tok!"/",Tok!"%":
		return 130;
	/*/ prefix operators
	case Tok!"&",Tok!"++",Tok!"--",Tok!"*":
	case Tok!"-",Tok!"+",Tok!"!",Tok!"~":
		return 140;  */
	case Tok!"^":  return 150; // power
	// postfix operators
	case Tok!".",Tok!"++",Tok!"--":
	case Tok!"(", Tok!"[": // function call and indexing
		return 160;
	// template instantiation
	case Tok!"=>": return 165; // goesto
	case Tok!"!":  return 170;
	//case Tok!"i": return 45; //infix
	default: return -1;
	}
}
// unary exp binding power
enum nbp=140;


alias Code=Lexer;
private alias GCAlloc Alloc;

private template doParseImpl(bool d,T...){
	static if(T.length==0) enum doParseImpl="";
	else static if(is(typeof(T[0]):string)) enum doParseImpl={
			static if(T[0].length>3 && T[0][0..3]=="OPT") return doOptParse!(TTfromStr!(T[0][3..$]))~doParseImpl!(d,T[1..$]);
			else switch(T[0]){
				case "_": return "nextToken();\n"~doParseImpl!(d,T[1..$]);
				default: return "expect(Tok!\""~T[0]~"\");\n"~doParseImpl!(d,T[1..$]);
			}
		}();
	else static if(is(T[0]==Existing)) alias doParseImpl!(d,T[2..$]) doParseImpl;
	else enum doParseImpl=(d?"auto ":"")~T[1]~" = "~getParseProc!T.prc~";\n"~doParseImpl!(d,T[getParseProc!T.off..$]);
}

private template doParse(T...){ alias doParseImpl!(true,T) doParse; }
private template doParseNoDef(T...){ alias doParseImpl!(false,T) doParseNoDef; }

private template parseDefOnly(T...){
	static if(T.length==0) enum parseDefOnly="";
	else static if(is(typeof(T[0]):string)){
		static if(T[0]=="OPT") alias parseDefOnly!(T[1..$]) parseDefOnly;
		else alias parseDefOnly!(T[1..$]) parseDefOnly;
	}else static if(is(T[0]==Existing)) alias parseDefOnly!(T[2..$]) parseDefOnly;
	else enum parseDefOnly="typeof("~getParseProc!T.prc~") "~T[1]~"=typeof("~getParseProc!T.prc~").init;\n"~parseDefOnly!(T[2..$]);
}
private template doOptParse(T...){
	static assert(is(typeof(T[0]):const(char)[]));
	//static assert(is(typeof(T[0]):string)); // TODO: reduce bug
	enum doOptParse=parseDefOnly!T~"if(ttype==Tok!\""~T[0]~"\"){\n"~doParseImpl!(false,"_",T[1..$])~"}\n";
}

enum literals=["``","``c","``w","``d","' '","0","0U","0L","0LU",".0f",".0",".0L",".0fi",".0i",".0Li","true","false"];
private string getTTCases(string[] s,string[] excl = []){
	string r="case ";
	foreach(x;s) if(!excl.canFind(x)) r~="Tok!\""~x~"\",";
	return r[0..$-1]~":";
}

private template getParseProc(T...){
	static if(is(T[0]==AssignExp)) enum prc=`parseExpression(rbp!(Tok!","))`, off=2;
	else static if(is(T[0]==OrOrExp)) enum prc=`parseExpression(rbp!(Tok!"?"))`, off=2;
	else static if(is(T[0]==ArgumentList)){ // ArgumentList, AssocArgumentList can take optional parameters
		enum name = T[0].stringof;
		static if(T[2][0]=='('&&T[2][$-1]==')')
			enum prc=`parse`~name~`!`~T[3].stringof~T[2], off=3;
		else enum prc=`parse`~name~`!`~T[2].stringof~"()", off=2;
	}else enum prc="parse"~T[0].stringof~"()", off=2;
}
private struct Existing{}
private struct AssignExp{}
private struct OrOrExp{}
private struct ArgumentList{}

private template fillParseNamesImpl(int n,string b,T...){ // val: new TypeTuple, off: that many names have been filled in
	static if(T.length==0){alias T val; enum off=0;}
	else static if(is(typeof(T[0]):const(char)[])){// ==string. TODO: reduce bug
		static if(T[0].length>3 && T[0][0..3]=="OPT"){
			private alias fillParseNamesImpl!(n,b,TTfromStr!(T[0][3..$])) a;
			enum strip = a.val.stringof[0..6]=="tuple(" ? 6 : 1; // workaround for DMDs inconsistent tuple formatting
			alias TypeTuple!("OPT"~a.val.stringof[strip..$-1],fillParseNamesImpl!(n+a.off,b,T[1..$]).val) val;
			alias a.off off;
		}else{
			private alias fillParseNamesImpl!(n,b,T[1..$]) rest;
			alias TypeTuple!(T[0],rest.val) val;enum off=rest.off;
		}
	}else static if(is(T[0]==Existing)){
		private alias fillParseNamesImpl!(n,b,T[2..$]) rest;
		alias TypeTuple!(T[0],T[1],rest.val) val; enum off=rest.off;
	}else{
		private alias fillParseNamesImpl!(n+1,b,T[1..$]) rest;
		alias TypeTuple!(T[0],b~to!string(n),rest.val) val;enum off=rest.off+1;
	}
}

private template fillParseNames(string base,T...){
	alias fillParseNamesImpl!(0,base,T).val fillParseNames;
}
private template getParseNames(T...){
	static if(T.length==0) enum getParseNames=""; // next line: ':' instead of '==string' is workaround
	else static if(!is(typeof(T[0]):const(char)[])) enum getParseNames=T[1]~","~getParseNames!(T[2..$]);
	else{
		static if(T[0].length>3 && T[0][0..3]=="OPT") enum getParseNames=getParseNames!(TTfromStr!(T[0][3..$]))~getParseNames!(T[1..$]);
		else enum getParseNames=getParseNames!(T[1..$]);
	}
}
private template GetStringOf(T){enum GetStringOf=T.stringof;} // Workaround for strange compiler limitations
private template rule(T...){ // applies a grammar rule and returns the result
	enum rule={
		alias fillParseNames!("e",T[1..$]) a;
		return doParse!(a)~"return res=New!("~GetStringOf!(T[0])~")("~getParseNames!a~");";
	}();
}


private template SetLoc(T: Node){
	enum SetLoc=T.stringof~q{
		res=null;
		Location begin=tok.loc;
		scope(success){
			if(res) res.loc=begin.to(code.buffer[code.n-1&code.buffer.length-1].loc);
		}
	};
}

bool isClosingToken(TokenType type){
	return type==Tok!")" || type==Tok!"}" || type==Tok!"]" || type==Tok!";";
}

private immutable arrLbp=mixin({string r="[";foreach(t;EnumMembers!TokenType) r~=to!string(isRelationalOp(t)?-2:getLbp(t))~",";return r~"]";}());

struct Parser{
	alias Alloc.New New;
	alias Alloc.appender appender;
	enum filename = "tt.d";
	Code code;
	ErrorHandler handler;
	int muteerr=0;
	bool displayExpectErr = true;
	this(Code code, ErrorHandler handler){
		this.code = code;
		//_tok=&code.front();
		ttype=tok.type;
		this.handler = handler;
	}
	@property ref Token tok(){return code.buffer[code.n];};
	@property ref const(Token) ptok(){return code.buffer[code.n-1&code.buffer.length-1];};
	TokenType ttype;
	void nextToken(){
		if(ttype==Tok!"EOF") return;
		code.popFront();
		ttype=tok.type;
		if(!code.errors.length || muteerr) return;
		while(code.errors.length&&code.errors[0].loc.rep.ptr<tok.loc.rep.ptr){
			// a lexer error amidst expect errors is likely to be uninteresting
			if(displayExpectErr) handler.error(code.errors[0].str,code.errors[0].loc);
			code.errors.popFront();
		}
	}
	void error(string err, Location loc=Location.init){
		if(code.errors.length&&code.errors[0].loc.rep.ptr==loc.rep.ptr) return; // don't re-report lexer errors
		if(!loc.line) loc=tok.loc;
		handler.error(err,loc);
	}
	auto saveState(){muteerr++; return code.pushAnchor();} // saves the state and mutes all error messages until the state is restored
	void restoreState(Anchor state){
		muteerr--; code.popAnchor(state);
		ttype=tok.type;
	}
	Token peek(int x=1){
		if(x<code.e-code.s) return code.buffer[code.n+x & code.buffer.length-1]; // breaking encapsulation for efficiency
		auto save = saveState();
		foreach(i;0..x) nextToken();
		auto t=tok;
		restoreState(save);
		return t;
	}
	Token peekPastParen(){
		auto save = saveState();
		nextToken();
		skipToUnmatched();
		nextToken();
		auto t=tok;
		restoreState(save);
		return t;
	}
	bool skipToUnmatched(bool skipcomma=true)(){
		int pnest=0, cnest=0, bnest=0; // no local templates >:(
		for(;;nextToken()){
			switch(ttype){
				case Tok!"(": pnest++; continue;
				case Tok!"{": cnest++; continue;
				case Tok!"[": bnest++; continue;
				case Tok!")": if(pnest--) continue; break;
				case Tok!"}": if(cnest--) continue; break;
				case Tok!"]": if(bnest--) continue; break;
				static if(!skipcomma) case Tok!",": if(pnest) continue; break;
				case Tok!";": if(cnest) continue; break;
				case Tok!"EOF": return false;
				//case Tok!"..": if(bnest) continue; break;
				default: continue;
			}
			break;
		}
		return true;
	}
	static class ParseErrorException: Exception{this(string s){super(s);}} alias ParseErrorException PEE;
	void expect(TokenType type){
		// if(type==Tok!";"){if(ttype==Tok!";") nextToken(); return;} //optional semicolons :)
		if(ttype==type){displayExpectErr=true; nextToken(); return;}
		// employ some bad heuristics to avoid cascading error messages. TODO: make this better
		if(!displayExpectErr) return;
		displayExpectErr=false;
		bool rd=isClosingToken(type);
		Location loc=tok.loc;
		import utf=std.utf;
		// give error for missing ';', '}', ')' etc at the right place:
		if(rd){
			loc=code.buffer[code.n-1&code.buffer.length-1].loc;
			foreach(dchar x;loc.rep) if(isNewLine(x)) loc.line++;
			loc.rep=(loc.rep.ptr+loc.rep.length)[0..utf.stride(loc.rep.ptr[loc.rep.length..loc.rep.length+4],0)];
		}
		auto tt=peek().type;
		if(tt!=Tok!"i"&&tt==type){
			error("stray '"~tok.toString()~"' in program",tok.loc);
			nextToken(); nextToken();
			return;
		}
		if(rd||ttype==Tok!"__error") error("expected '"~TokenTypeToString(type)~"'",loc);
		else error("found '" ~ tok.toString() ~ "' when expecting '" ~ TokenTypeToString(type) ~"'",loc);
		if(type!=Tok!";" && type!=Tok!"}"){
			while(ttype != Tok!";" && ttype != Tok!"}" && ttype != Tok!"EOF") nextToken();
			if(ttype == Tok!";") nextToken();
		}//else nextToken(); // TODO: ok?
	}
	void expectErr(string what)(){
		if(!displayExpectErr) return;
		if(ttype==Tok!"__error") error("expected "~what,tok.loc);
		else error("found '" ~ tok.toString() ~ "' when expecting " ~ what,tok.loc);
		if(ttype!=Tok!")" && ttype!=Tok!"}" && ttype!=Tok!"]" && ttype!=Tok!";") nextToken();
		displayExpectErr = false;
	}
	bool skip(TokenType type){
		if(ttype != type) return false;
		nextToken(); return true;
	}
	bool skip(){nextToken(); return true;}
	Identifier parseIdentifier(){ // Identifier(null) is the error value
		string name;
		if(ttype==Tok!"i") name=tok.name;
		else{expectErr!"identifier"(); auto e=New!Identifier(string.init); e.loc=tok.loc; return e;}
		displayExpectErr=true;
		auto e=New!Identifier(name);
		e.loc=tok.loc;
		nextToken();
		return e;
	}

	Parameter parseParameter(){
		auto i=parseIdentifier();
		Expression t=null;
		if(ttype==Tok!":"){
			nextToken();
			t=parseType();
		}
		return New!Parameter(i,t);
	}
	
	Expression[] parseArgumentList(string delim, bool nonempty=false, Entry=AssignExp, T...)(T args){
		auto e=appender!(Expression[])();
		foreach(x;args) e.put(x); // static foreach
		static if(args.length){if(ttype==Tok!",") nextToken(); else return e.data;}
		static if(!nonempty) if(ttype==Tok!delim) return e.data;
		do{
			mixin(doParse!(Entry,"e1")); e.put(e1);
			if(ttype==Tok!",") nextToken();
			else break;
		}while(ttype!=Tok!delim && ttype!=Tok!"EOF");
		return e.data;
	}

	// Operator precedence expression parser
	// null denotation
	Expression nud(){
		mixin(SetLoc!Expression);
		switch(ttype){
			case Tok!"i": return parseIdentifier();
			case Tok!"?": nextToken(); return res=New!PlaceholderExp(parseIdentifier());
			case Tok!"``", Tok!"``c", Tok!"``w", Tok!"``d": // adjacent string tokens get concatenated
				Token t=tok;
				for(nextToken();;nextToken()){
					if(ttype==t.type||ttype==Tok!"``"){}
					else if(t.type==Tok!"``" && Tok!"``c"<=ttype && ttype<=Tok!"``d") t.type=ttype; // EXTENSION
					else break;
					t.str~=tok.str; // TODO: make more efficient than simple append
				}
				mixin(rule!(LiteralExp,Existing,"t"));
			mixin(getTTCases(literals,["``","``c","``w","``d","true","false"])); {res=New!LiteralExp(tok); nextToken(); return res;}
			case Tok!"true":
				nextToken();
				auto tok=Token(Tok!"0");
				tok.str="1";
				return res=New!LiteralExp(tok);
			case Tok!"false":
				nextToken();
				auto tok=Token(Tok!"0");
				tok.str="0";
				return res=New!LiteralExp(tok);
			case Tok!"(":
				auto state=saveState();
				nextToken();
				skipToUnmatched();
				nextToken();
				switch(ttype){
					case Tok!":":
						nextToken();
						if(skipType() && ttype == Tok!"=>")
							goto case;
						break;
					case Tok!"{",Tok!"=>":
						restoreState(state);
						return parseLambdaExp();
					default: break;
				}
				restoreState(state);
				nextToken();
				if(ttype==Tok!")"){
					nextToken();
					res=New!TupleExp(Expression[].init);
				}else{
					res=parseExpression(rbp!(Tok!","));
					if(ttype==Tok!","){
						auto tpl=[res];
						while(ttype==Tok!","){
							nextToken();
							if(ttype==Tok!")") break;
							tpl~=parseExpression(rbp!(Tok!","));
						}
						expect(Tok!")");
						res=New!TupleExp(tpl);
					}else{
						expect(Tok!")");
						res.brackets++;
					}
				}
				return res;
			case Tok!"[":
				nextToken();
				res=New!ArrayExp(parseArgumentList!"]"());
				expect(Tok!"]");
				return res;
			case Tok!"-":
				nextToken();
				return res=New!(UnaryExp!(Tok!"-"))(parseExpression(nbp));
			case Tok!"!":
				nextToken();
				return res=New!(UnaryExp!(Tok!"!"))(parseExpression(nbp));
			case Tok!"__error": mixin(rule!(ErrorExp,"_"));
			//case Tok!"[": mixin(rule!(ArrayLiteralExp,"_","OPT",ArgumentList,"]"));
			//case Tok!"assert": mixin(rule!(AssertExp,"_","(",ArgumentList,")"));
			default: throw new PEE("invalid unary operator '"~tok.toString()~"'");
		}
	}

	LambdaExp parseLambdaExp(){
		mixin(SetLoc!LambdaExp);
		return res=New!LambdaExp(parseFunctionDef!true);
	}
	
	// left denotation
	Expression led(Expression left){
		Expression res=null;
		//Location loc=tok.loc;
		//scope(success) if(res) res.loc=loc;
		Location loc=left.loc;
		scope(success) if(res) res.loc=loc.to(ptok.loc);
		switch(ttype){
			//case Tok!"i": return New!CallExp(New!BinaryExp!(Tok!".")(left,New!Identifier(self.name)),parseExpression(45));// infix
			//case Tok!"?": mixin(rule!(TernaryExp,"_",Existing,"left",Expression,":",OrOrExp));
			case Tok!"[":
				nextToken();
				if(ttype==Tok!"]"){loc=loc.to(tok.loc); nextToken(); mixin(rule!(IndexExp,Existing,q{left,(Expression[]).init}));}
				auto l=parseExpression(rbp!(Tok!","));
				res=New!IndexExp(left,parseArgumentList!"]"(l));
				loc=loc.to(tok.loc); expect(Tok!"]");
				return res;
			case Tok!"(":
				nextToken();
				auto a=parseArgumentList!")"();
				loc=loc.to(tok.loc); expect(Tok!")");
				mixin(rule!(CallExp,Existing,"left,a"));
			case Tok!".":
				auto r=left;
				while(ttype==Tok!"."){
					nextToken();
					auto f=parseIdentifier();
					r=new FieldExp(r,f);
					r.loc=loc.to(tok.loc);
				}
				return r;
			case Tok!":":
				nextToken();
				auto t=parseType();
				res=New!TypeAnnotationExp(left,t);
				return res;
			mixin({string r;
				foreach(x;binaryOps)
					if(x!="=>" && x!="." && x!="!" && x!="?" && x!=":")
						r~=mixin(X!q{case Tok!"@(x)":
							nextToken();
							auto right=parseExpression(rbp!(Tok!"@(x)"));
							return res=New!(BinaryExp!(Tok!"@(x)"))(left,right);
						});
				return r;
			}());
			//pragma(msg,TokenTypeToString(cast(TokenType)61));
			mixin({string r;
				foreach(x;postfixOps)
					if(x!="(" && x!="[")
						r~=mixin(X!q{case Tok!"@(x)":nextToken();return res=New!(PostfixExp!(Tok!"@(x)"))(left);});
				return r;
			}());
			default:
				auto str="invalid binary operator '"~tok.toString()~"'";
				nextToken();
				throw new PEE(str);
		}
	}
	Expression parseExpression(int rbp = 0){
		switch(ttype){
			case Tok!"def": return parseFunctionDef();
			case Tok!"dat": return parseDatDecl();
			case Tok!"return": return parseReturn();
			case Tok!"if": return parseIte();
			case Tok!"repeat": return parseRepeat();
			case Tok!"for": return parseFor();
			case Tok!"while": return parseWhile();
			case Tok!"assert": return parseAssert();
			case Tok!"observe": return parseObserve();
			case Tok!"cobserve": return parseCObserve();
			default: break;
		}
		Expression left;
		try left = nud();catch(PEE err){error("found '"~tok.toString()~"' when expecting expression");nextToken();return new ErrorExp();}
		return parseExpression2(left, rbp);
	}
	auto parseType(bool showErrors=true)(){
		Expression parsePrimary()(){
			if(ttype==Tok!"("){
				nextToken();
				auto r=parseIt();
				expect(Tok!")");
				if(r) r.brackets++;
				return r;
			}
			if(ttype==Tok!"i"){
				auto r=parseIdentifier();
				r.brackets++; // TODO: solve more elegantly
				return r;
			}
			if(ttype==Tok!"0"){
				auto id=new Identifier(tok.toString());
				id.loc=tok.loc;
				nextToken();
				return id;
			}
			static if(showErrors) error("found '"~tok.toString()~"' when expecting type");
			nextToken();
			return null;			
		}
		Expression parseBase()(){
			auto t=parsePrimary();
			if(!t) return null;
			while(ttype==Tok!"["){
				nextToken();
				expect(Tok!"]");
				auto n=New!IndexExp(t,Expression[].init);
				n.loc=t.loc.to(ptok.loc);
				t=n;
			}
			return t;
		}
		Expression parseProduct()(){
			auto l=parseBase();
			while(ttype==Tok!"×"||(ttype==Tok!"i"&&tok.str=="x")){
				nextToken();
				auto r=parseBase();
				if(!r) return null;
				auto next=New!(BinaryExp!(Tok!"×"))(l,r);
				next.loc=l.loc.to(r.loc);
				l=next;
			}
			return l;
		}
		Expression parseIt(){ return parseProduct(); }
		auto r=parseProduct();
		static if(showErrors) return r?r:new ErrorTy();
		else return !!r;
	}
	alias skipType=parseType!false;
	Expression parseExpression2(Expression left, int rbp = 0){ // left is already known
		while(rbp < arrLbp[ttype])
		loop: try left = led(left); catch(PEE err){error(err.msg);}
		if(arrLbp[ttype] == -2 && rbp<lbp!(Tok!"==")){
			try left = led(left); catch(PEE err){error(err.msg);}
			if(rbp<arrLbp[ttype]) goto loop;
		}
		return left;
	}
	T parseCompoundExp(T=CompoundExp)(){
		mixin(SetLoc!T);
		expect(Tok!"{");
		auto s=appender!(Expression[])();
		while(ttype!=Tok!"}" && ttype!=Tok!"EOF"){
			auto e=parseExpression();
			s.put(e);
			if(!e.isCompound()&&ttype!=Tok!"}"||ttype==Tok!";")
			   expect(Tok!";");
			if(auto r=cast(ReturnExp)e){
				if(ttype==Tok!"expected"){
					r.expected=tok.str;
					nextToken();
				}
			}
		}
		expect(Tok!"}");
		return res=New!T(s.data);
	}
	FunctionDef parseFunctionDef(bool lambda=false)(){
		mixin(SetLoc!FunctionDef);
		static if(!lambda){
			expect(Tok!"def");
			auto name=parseIdentifier();
		}else Identifier name=null; // TODO
		expect(Tok!"(");
		auto args=cast(Parameter[])parseArgumentList!(")",false,Parameter)();
		expect(Tok!")");
		Expression ret=null;
		if(ttype==Tok!":"){
			nextToken();
			ret=parseType();
		}
		CompoundExp body_;
		if(ttype == Tok!"=>"){
			nextToken();
			auto e=parseExpression();
			auto r=New!ReturnExp(e);
			r.loc=e.loc;
			body_= New!CompoundExp([cast(Expression)r]);
			body_.loc=e.loc;
			static if(!lambda) expect(Tok!";");			
		}else body_=parseCompoundExp();
		return res=New!FunctionDef(name,args,ret,body_);
	}
	DatDecl parseDatDecl(){
		mixin(SetLoc!DatDecl);
		expect(Tok!"dat");
		auto name=parseIdentifier();
		auto body_=parseCompoundExp!CompoundDecl();
		return res=New!DatDecl(name,body_);
	}
	ReturnExp parseReturn(){
		mixin(SetLoc!ReturnExp);
		expect(Tok!"return");
		Expression exp;
		if(ttype!=Tok!";") exp=parseExpression();
		else exp=New!TupleExp(Expression[].init);
		return res=New!ReturnExp(exp);
	}
	Expression parseCondition(){
		mixin(SetLoc!Expression);
		if(ttype==Tok!"("){ nextToken(); auto r=parseExpression(); expect(Tok!")"); return r; }
		return parseExpression();
	}
	IteExp parseIte(){
		mixin(SetLoc!IteExp);
		expect(Tok!"if");
		auto cond=parseCondition();
		auto then=parseCompoundExp();
		CompoundExp othw=null;
		if(ttype == Tok!"else"){
			nextToken();
			if(ttype==Tok!"if"){
				Expression o=parseIte();
				othw=New!CompoundExp([o]);
				othw.loc=o.loc;
			}else othw=parseCompoundExp();
		}
		return res=New!IteExp(cond,then,othw);
	}
	RepeatExp parseRepeat(){
		mixin(SetLoc!RepeatExp);
		expect(Tok!"repeat");
		auto num=parseCondition();
		auto bdy=parseCompoundExp();
		return res=New!RepeatExp(num,bdy);
	}
	WhileExp parseWhile(){
		mixin(SetLoc!WhileExp);
		expect(Tok!"while");
		auto num=parseCondition();
		auto bdy=parseCompoundExp();
		return res=New!WhileExp(num,bdy);
	}
	ForExp parseFor(){
		mixin(SetLoc!ForExp);
		expect(Tok!"for");
		auto var=parseIdentifier();
		expect(Tok!"in");
		bool leftExclusive=false,rightExclusive=false;
		if(tok.type==Tok!"("){ leftExclusive=true; nextToken(); }
		else expect(Tok!"[");
		auto left=parseExpression();
		expect(Tok!"..");
		auto right=parseExpression();
		if(tok.type==Tok!")"){ rightExclusive=true; nextToken(); }
		else expect(Tok!"]");
		auto bdy=parseCompoundExp();
		return res=New!ForExp(var,leftExclusive,left,rightExclusive,right,bdy);
	}
	AssertExp parseAssert(){
		mixin(SetLoc!AssertExp);
		expect(Tok!"assert");
		expect(Tok!"(");
		auto exp=parseExpression();
		expect(Tok!")");
		return res=New!AssertExp(exp);
	}
	ObserveExp parseObserve(){
		mixin(SetLoc!ObserveExp);
		expect(Tok!"observe");
		expect(Tok!"(");
		auto exp=parseExpression();
		expect(Tok!")");
		return res=New!ObserveExp(exp);
	}
	CObserveExp parseCObserve(){
		mixin(SetLoc!CObserveExp);
		expect(Tok!"cobserve");
		expect(Tok!"(");
		auto var=parseExpression(rbp!(Tok!","));
		expect(Tok!",");
		auto val=parseExpression(rbp!(Tok!","));
		expect(Tok!")");
		return res=New!CObserveExp(var,val);
	}
};

Expression parseExpression(Source source, ErrorHandler handler){
	return Parser(lex(source),handler).parseExpression();
}

Expression[] parseFile(Source source, ErrorHandler handler){
	auto p=Parser(lex(source),handler);
	auto s=appender!(Expression[])();
	while(p.ttype!=Tok!"EOF") s.put(p.parseExpression());
	return s.data;
}
