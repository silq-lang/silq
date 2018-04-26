// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.typetuple, std.algorithm, std.conv;
import std.traits: EnumMembers;
import std.typecons: Q=Tuple,q=tuple;
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
		case Tok!"==",Tok!"=",Tok!"!=",Tok!"≠",Tok!">",Tok!"<":
		case Tok!">=",Tok!"≥",Tok!"<=",Tok!"≤",Tok!"!>",Tok!"!<":
		case Tok!"!>=",Tok!"!≥",Tok!"!<=",Tok!"!≤",Tok!"<>",Tok!"!<>":
		case Tok!"<>=", Tok!"!<>=":
			return true;
		default: return false;
	}
}

// expression parser:

// left binding power
template lbp(TokenType type){enum lbp=getLbp(type);}
// right binding power: ^^, (op)=, ? bind weaker to the right than to the left, '.' binds only primaryExpressions
template rbp(TokenType type){enum rbp=type==Tok!"."?180:lbp!type-(lbp!type==30||util.among(type,Tok!"^",Tok!"?",Tok!"->",Tok!"→",Tok!"⇒",Tok!"↦",Tok!"=>"));}

int getLbp(TokenType type) pure{ // operator precedence
	switch(type){
	//case Tok!"..": return 10; // range operator
	case Tok!",":  return 10; // comma operator
	// assignment operators
	case Tok!"←":
	case Tok!"/=",Tok!"div=",Tok!"&=",Tok!"∧=",Tok!"⊕=",Tok!"|=",Tok!"∨=",Tok!"-=":
	case Tok!"/←",Tok!"div←",Tok!"&←",Tok!"∧←",Tok!"⊕←",Tok!"|←",Tok!"∨←",Tok!"-←":
	case Tok!"+=",Tok!"<<=",Tok!">>=", Tok!">>>=":
	case Tok!"+←",Tok!"<<←",Tok!">>←", Tok!">>>←":
	case Tok!"*=",Tok!"%=",Tok!"^=":
	case Tok!"*←",Tok!"·←",Tok!"%←",Tok!"^←":
	case Tok!"&&=", Tok!"||=", Tok!"~=":
	case Tok!"&&←", Tok!"||←", Tok!"~←":
	case Tok!":=":
		return 20;
	case Tok!":": // type annotation
		return 30;
	// logical operators
	case Tok!"?":  return 40; // conditional operator
	case Tok!"||": return 50; // logical OR
	case Tok!"&&": return 60; // logical AND
	// bitwise operators
	case Tok!"|",Tok!"∨": return 70;
	case Tok!"⊕": return 80;
	case Tok!"&",Tok!"∧": return 90;
	// relational operators
	case Tok!"==",Tok!"=",Tok!"!=",Tok!"≠",Tok!">",Tok!"<":
	case Tok!">=",Tok!"≥",Tok!"<=",Tok!"≤",Tok!"!>",Tok!"!<":
	case Tok!"!>=",Tok!"!≥",Tok!"!<=",Tok!"!≤",Tok!"<>",Tok!"!<>":
	case Tok!"<>=", Tok!"!<>=":
		return 100;
	// shift operators
	case Tok!">>", Tok!"<<":
	case Tok!">>>": return 110;
	case Tok!"->",Tok!"→": // exponential type
	// case Tok!"⇒",Tok!"↦",Tok!"=>": return 115; // goesto
	// additive operators
	case Tok!"+",Tok!"-",Tok!"~":
		return 120;
	case Tok!"×": // product type
	// multiplicative operators
	case Tok!"*",Tok!"·",Tok!"/",Tok!"%",Tok!"div":
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
	foreach(x;s) if(!excl.canFind(x)) r~=`Tok!"`~x~`",`;
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
			error("stray \""~tok.toString()~"\" in program",tok.loc);
			nextToken(); nextToken();
			return;
		}
		if(rd||ttype==Tok!"__error") error("expected \""~TokenTypeToString(type)~"\"",loc);
		else error("found \"" ~ tok.toString() ~ "\" when expecting \"" ~ TokenTypeToString(type) ~"\"",loc);
		if(type!=Tok!";" && type!=Tok!"}"){
			while(ttype != Tok!";" && ttype != Tok!"}" && ttype != Tok!"EOF") nextToken();
			if(ttype == Tok!";") nextToken();
		}//else nextToken(); // TODO: ok?
	}
	void expectErr(string what)(){
		if(!displayExpectErr) return;
		if(ttype==Tok!"__error") error("expected "~what,tok.loc);
		else error("found \"" ~ tok.toString() ~ "\" when expecting " ~ what,tok.loc);
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
		mixin(SetLoc!Parameter);
		auto i=parseIdentifier();
		Expression t=null;
		if(ttype==Tok!":"){
			nextToken();
			t=parseType();
		}
		return res=New!Parameter(i,t);
	}
	
	Q!(Expression[],bool) parseArgumentList(bool nonempty=false, Entry=AssignExp, T...)(TokenType delim, T args){
		auto e=appender!(Expression[])();
		foreach(x;args) e.put(x); // static foreach
		bool trailingComma=false;
		static if(args.length){if(ttype==Tok!","){ nextToken(); trailingComma=true; }else return q(e.data,trailingComma); }
		static if(!nonempty) if(ttype==delim) return q(e.data,trailingComma);
		do{
			trailingComma=false;
			mixin(doParse!(Entry,"e1")); e.put(e1);
			if(ttype==Tok!","){ nextToken(); trailingComma=true; }
			else break;
		}while(ttype!=delim && ttype!=Tok!"EOF");
		return q(e.data,trailingComma);
	}

	Expression parseParenthesized()in{assert(ttype==Tok!"(");}body{
		mixin(SetLoc!Expression);
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
	}
	
	// Operator precedence expression parser
	// null denotation
	Expression nud(bool allowLambda){
		mixin(SetLoc!Expression);
		Token t; // DMD 2.072.1: hoisted to satisfy buggy deprecation code
		switch(ttype){
			case Tok!"i": return parseIdentifier();
			case Tok!"*": auto r=New!Identifier("*"); r.loc=tok.loc; nextToken(); return r;
			case Tok!"?": nextToken(); return res=New!PlaceholderExp(parseIdentifier());
			case Tok!"``", Tok!"``c", Tok!"``w", Tok!"``d": // adjacent string tokens get concatenated
				t=tok;
				for(nextToken();;nextToken()){
					if(ttype==t.type||ttype==Tok!"``"){}
					else if(t.type==Tok!"``" && Tok!"``c"<=ttype && ttype<=Tok!"``d") t.type=ttype; // EXTENSION
					else break;
					t.str~=tok.str; // TODO: make more efficient than simple append
				}
				mixin(rule!(LiteralExp,Existing,"t"));
			mixin(getTTCases(literals,["``","``c","``w","``d","true","false"])); {res=New!LiteralExp(tok); nextToken(); return res;}
			case Tok!"true",Tok!"⊤":
				nextToken();
				auto tok=Token(Tok!"0");
				tok.str="1";
				res=New!LiteralExp(tok);
				res.type=Bool;
				return res;
			case Tok!"false",Tok!"⊥":
				nextToken();
				auto tok=Token(Tok!"0");
				tok.str="0";
				res=New!LiteralExp(tok);
				res.type=Bool;
				return res;
			case Tok!"(",Tok!"[":
				if(allowLambda){
					auto state=saveState();
					while(util.among(ttype,Tok!"(",Tok!"[")){
						nextToken();
						skipToUnmatched();
						nextToken();
					}
					switch(ttype){
						case Tok!"{",Tok!"⇒",Tok!"↦",Tok!"=>":
							restoreState(state);
							return parseLambdaExp();
						default: break;
					}
					restoreState(state);
				}
				if(ttype==Tok!"("){
					return res=parseParenthesized();
				}else{
					assert(ttype==Tok!"[");
					nextToken();
					res=New!ArrayExp(parseArgumentList(Tok!"]")[0]);
					expect(Tok!"]");
					return res;
				}
			case Tok!"Π", Tok!"Pi":
				nextToken();
				Expression parseProduct(){
					bool isSquare=false;
					if(ttype==Tok!"[") isSquare=true;
					expect(isSquare?Tok!"[":Tok!"(");
					auto params=parseArgumentList!(false,Parameter)(isSquare?Tok!"]":Tok!")");
					expect(isSquare?Tok!"]":Tok!")");
					Expression cod;
					if(ttype!=Tok!"["&&ttype!=Tok!"("){
						expect(Tok!".");
						cod = parseType();
					}else cod=parseProduct();
					auto isTuple=params[1]||params[0].length!=1;
					return res=New!RawProductTy(cast(Parameter[])params[0],cod,isSquare,isTuple);
				}
				return parseProduct();
			case Tok!"-":
				nextToken();
				return res=New!(UnaryExp!(Tok!"-"))(parseExpression(nbp));
			case Tok!"!",Tok!"¬":
				nextToken();
				return res=New!(UnaryExp!(Tok!"¬"))(parseExpression(nbp));
			case Tok!"~":
				nextToken();
				return res=New!(UnaryExp!(Tok!"~"))(parseExpression(nbp));
			case Tok!"__error": mixin(rule!(ErrorExp,"_"));
			//case Tok!"[": mixin(rule!(ArrayLiteralExp,"_","OPT",ArgumentList,"]"));
			//case Tok!"assert": mixin(rule!(AssertExp,"_","(",ArgumentList,")"));
			default: throw new PEE("invalid unary operator \""~tok.toString()~"\"");
		}
	}

	LambdaExp parseLambdaExp(bool semicolon=false)(){
		mixin(SetLoc!LambdaExp);
		return res=New!LambdaExp(parseFunctionDef!(true,semicolon));
	}
	
	// left denotation
	Expression led(Expression left,bool statement=false){
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
				if(ttype==Tok!"]"){loc=loc.to(tok.loc); nextToken(); mixin(rule!(IndexExp,Existing,q{left,(Expression[]).init,false}));}
				auto l=parseExpression(rbp!(Tok!","));
				if(ttype==Tok!".."){
					nextToken();
					auto r=parseExpression();
					expect(Tok!"]");
					return res=new SliceExp(left,l,r);
				}
				res=New!IndexExp(left,parseArgumentList(Tok!"]",l).expand);
				expect(Tok!"]");
				return res;
			case Tok!"(":
				auto a=parseParenthesized();
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
			case Tok!":":{
				nextToken();
				auto t=parseType(statement);
				res=New!TypeAnnotationExp(left,t);
				return res;
			}mixin({string r;
				foreach(x;binaryOps)
					if(!util.among(x,"=>",".","!","?",":","*","=","==","<=","!<=",">=","!>=","!=","*=","/=","div=","&=","⊕=","|=","-=","+=","<<=",">>=",">>>=","*=","·=","%=","^=","&&=","||=","~=","&","&=","&←","∧=","|","|=","|←","∨=")){
						r~=mixin(X!q{case Tok!"@(x)":
							nextToken();
							auto right=parseExpression(rbp!(Tok!"@(x)"),"@(x)"=="←"||"@(x)"==":=",statement&&"@(x)"==",");
							static if("@(x)"=="->")
								alias BE=BinaryExp!(Tok!"→");
							else alias BE=BinaryExp!(Tok!"@(x)");
							return res=New!BE(left,right);
						});
					}
				return r;
			}());
			static foreach(x;["/=","div=","&=","⊕=","|=","-=","+=","<<=",">>=",">>>=","%=","^=","&&=","||=","~="])
				case Tok!x: goto case Tok!(x[0..$-1]~"←");
			case Tok!"=":
				if(statement) goto case Tok!"←";
				goto case;
			case Tok!"==":
				nextToken();
				auto right=parseExpression(rbp!(Tok!"=="),true);
				return res=New!(BinaryExp!(Tok!"="))(left,right);
			case Tok!"*": goto case Tok!"·";
			case Tok!"*=",Tok!"·=": goto case Tok!"·←";
			case Tok!"<=": goto case Tok!"≤";
			case Tok!"!<=": goto case Tok!"!≤";
			case Tok!">=": goto case Tok!"≥";
			case Tok!"!>=": goto case Tok!"!≥";
			case Tok!"!=": goto case Tok!"≠";
			case Tok!"&": goto case Tok!"∧";
			case Tok!"&←",Tok!"∧=": goto case Tok!"∧←";
			case Tok!"|": goto case Tok!"∨";
			case Tok!"|←",Tok!"∨=": goto case Tok!"∨←";
			case Tok!"i":
				switch(tok.str){ // TODO: clean this up using code generation
					case "div":
						auto id=tok;
						nextToken();
						if((ttype==Tok!"←"||ttype==Tok!"=") && id.loc.rep.ptr+id.loc.rep.length==tok.loc.rep.ptr){
							nextToken();
							auto right=parseExpression(rbp!(Tok!"div="),false);
							return res=New!(BinaryExp!(Tok!"div←"))(left,right);
						}else{
							auto right=parseExpression(rbp!(Tok!"div"),false);
							return res=New!(BinaryExp!(Tok!"div"))(left,right);
						}
					case "xorb":
						auto id=tok;
						nextToken();
						if((ttype==Tok!"←"||ttype==Tok!"=") && id.loc.rep.ptr+id.loc.rep.length==tok.loc.rep.ptr){
							nextToken();
							auto right=parseExpression(rbp!(Tok!"⊕="),false);
							return res=New!(BinaryExp!(Tok!"⊕←"))(left,right);
						}else{
							auto right=parseExpression(rbp!(Tok!"⊕"),false);
							return res=New!(BinaryExp!(Tok!"⊕"))(left,right);
						}
					case "x":
						nextToken();
						auto right=parseExpression(rbp!(Tok!"×"),false);
						return res=New!(BinaryExp!(Tok!"×"))(left,right);
					default: break;
				}
				goto default;
			//pragma(msg,TokenTypeToString(cast(TokenType)61));
			mixin({string r;
				foreach(x;postfixOps)
					if(x!="(" && x!="[")
						r~=mixin(X!q{case Tok!"@(x)":nextToken();return res=New!(PostfixExp!(Tok!"@(x)"))(left);});
				return r;
			}());
			default:
				auto str="invalid binary operator \""~tok.toString()~"\"";
				nextToken();
				throw new PEE(str);
		}
	}
	Expression parseExpression(int rbp = 0,bool allowLambda=true,bool statement=false){
		switch(ttype){
			case Tok!"def": return parseFunctionDef();
			case Tok!"dat": return parseDatDecl();
			case Tok!"import": return parseImport();
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
		try left = nud(allowLambda);catch(PEE err){error("found \""~tok.toString()~"\" when expecting expression");nextToken();return new ErrorExp();}
		return parseExpression2(left, rbp, statement);
	}
	auto parseType(bool statement=false){ return parseExpression(rbp!(Tok!":"),true,statement); }
	Expression parseExpression2(Expression left, int rbp = 0, bool statement=false){ // left is already known
		int clbp(){
			if(ttype==Tok!"i"){
				if(tok.str=="div")
					return arrLbp[peek().type==Tok!"="?Tok!"div=":Tok!"div"];
				if(tok.str=="xorb")
					return arrLbp[peek().type==Tok!"="?Tok!"⊕=":Tok!"⊕"];
				if(tok.str=="x")
					return arrLbp[Tok!"×"];
			}
			if(statement && ttype==Tok!"=")
				return arrLbp[Tok!"←"];
			return arrLbp[ttype];
		}
		while(rbp < clbp())
		loop: try left = led(left,statement); catch(PEE err){error(err.msg);}
		if(clbp() == -2 && rbp<lbp!(Tok!"==")){
			try left = led(left,statement); catch(PEE err){error(err.msg);}
			if(rbp<arrLbp[ttype]) goto loop;
		}
		return left;
	}
	T parseCompoundExp(T=CompoundExp)(){
		mixin(SetLoc!T);
		expect(Tok!"{");
		auto s=appender!(Expression[])();
		while(ttype!=Tok!"}" && ttype!=Tok!"EOF"){
			auto e=parseExpression(0,true,true);
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
	FunctionDef parseFunctionDef(bool lambda=false,bool semicolon=!lambda)(){
		mixin(SetLoc!FunctionDef);
		static if(!lambda){
			expect(Tok!"def");
			auto name=parseIdentifier();
		}else Identifier name=null; // TODO
		bool isSquare=false;
		if(ttype==Tok!"[") isSquare=true;
		expect(isSquare?Tok!"[":Tok!"(");
		auto params=parseArgumentList!(false,Parameter)(isSquare?Tok!"]":Tok!")");
		expect(isSquare?Tok!"]":Tok!")");
		Expression ret=null;
		if(ttype==Tok!":"){
			nextToken();
			ret=parseType();
		}
		CompoundExp body_;
		if(util.among(ttype,Tok!"⇒",Tok!"↦",Tok!"=>",Tok!"(",Tok!"[")){
			Expression e;
			if(ttype==Tok!"("||ttype==Tok!"["){
				e=parseLambdaExp!semicolon();
			}else{
				nextToken();
				e=parseExpression(rbp!(Tok!(",")));
				static if(semicolon) expect(Tok!";");			
			}
			auto r=New!ReturnExp(e);
			r.loc=e.loc;
			body_= New!CompoundExp([cast(Expression)r]);
			body_.loc=e.loc;
		}else body_=parseCompoundExp();
		res=New!FunctionDef(name,cast(Parameter[])params[0],params[1]||params[0].length!=1,ret,body_);
		res.isSquare=isSquare;
		return res;
	}
	DatDecl parseDatDecl(){
		mixin(SetLoc!DatDecl);
		expect(Tok!"dat");
		auto name=parseIdentifier();
		Q!(Expression[],bool) params;
		bool hasParams=false;
		if(ttype==Tok!"["){
			nextToken();
			hasParams=true;
			params=parseArgumentList!(false,Parameter)(Tok!"]");
			expect(Tok!"]");
		}
		auto body_=parseCompoundExp!CompoundDecl();
		return res=New!DatDecl(name,hasParams,cast(Parameter[])params[0],params[1]||params[0].length!=1,body_);
	}
	ImportExp parseImport(){
		mixin(SetLoc!ImportExp);
		expect(Tok!"import");
		Expression parsePath(){
			Expression path=parseIdentifier();
			while(ttype==Tok!"."){
				nextToken();
				auto next=parseIdentifier();
				path=new BinaryExp!(Tok!("."))(path,next);
				path.loc=path.loc.to(next.loc);
			}
			return path;
		}
		Expression[] paths=[parsePath()];
		while(ttype==Tok!","){
			nextToken();
			if(ttype==Tok!";") break;
			paths~=parsePath();
		}
		return res=New!ImportExp(paths);
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
		if(ttype==Tok!"("||ttype==Tok!"["){
			auto state=saveState();
			while(ttype==Tok!"("||ttype==Tok!"["){
				nextToken();
				skipToUnmatched();
				nextToken();
			}
			if(ttype==Tok!"{"){
				nextToken();
				skipToUnmatched();
				nextToken();
				if(ttype!=Tok!"("&&ttype!=Tok!"["){
					restoreState(state);
					return parseExpression(0,false);
				}
			}
			restoreState(state);
		}
		return parseExpression();
	}
	IteExp parseIte(){
		mixin(SetLoc!IteExp);
		expect(Tok!"if");
		auto cond=parseCondition();
		CompoundExp then,othw=null;
		if(ttype==Tok!"then"){
			nextToken();
			auto thenExp = parseExpression();
			expect(Tok!"else");
			auto othwExp = parseExpression(rbp!(Tok!","));
			then=New!CompoundExp([thenExp]);
			then.loc=thenExp.loc;
			othw=New!CompoundExp([othwExp]);
			othw.loc=othwExp.loc;
		}else{
			then=parseCompoundExp();
			if(ttype == Tok!"else"){
				nextToken();
				if(ttype==Tok!"if"){
					Expression o=parseIte();
					othw=New!CompoundExp([o]);
					othw.loc=o.loc;
				}else othw=parseCompoundExp();
			}
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
	while(p.ttype!=Tok!"EOF"){
		auto e=p.parseExpression();
		if(!e.isCompound()) p.expect(Tok!";");
		s.put(e);
	}
	return s.data;
}


import std.stdio, file=std.file;
string readCode(File f){
	// TODO: use memory-mapped file with 4 padding zero bytes
	auto app=mallocAppender!(char[])();
	foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
	app.put("\0\0\0\0"); // insert 4 padding zero bytes
	return cast(string)app.data;
}
string readCode(string path){ return readCode(File(path)); }

@property string preludePath(){
	// TODO: use conditional compilation within prelude.psi instead
	import options;
	if(opt.noCheck) return "prelude-nocheck.psi";
	return "prelude.psi";
}
int parseFile(string path,ErrorHandler err,ref Expression[] r,Location loc=Location.init){
	string code;
	try code=readCode(path);
	catch(Exception){
		string error;
		if(!file.exists(path)){
			// bake prelude into binary as a fallback
			if(path==preludePath()){
				assert(path=="prelude.psi" || path=="prelude-nocheck.psi");
				if(path=="prelude.psi") code = import("prelude.psi") ~ "\0\0\0\0";
				else code=import("prelude-nocheck.psi") ~ "\0\0\0\0";
			}else error = path ~ ": no such file";
		}else error = path ~ ": error reading file";
		if(error){
			if(loc.line) err.error(error,loc);
			else stderr.writeln("error: "~error);
			return 1;
		}
	}
	auto src=new Source(path, code);
	r=parser.parseFile(src,err);
	return 0;
}
