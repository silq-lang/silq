// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module util;

// FOR DEBUGGING ONLY
public import std.stdio;
debug bool dwguard=true;
void dw(T...)(lazy T args){
	debug{
		if(dwguard){
			dwguard=false;
			writeln(args);
			dwguard=true;
		}
	}
	else static assert(0,"debugging output call in release mode");
}
int crash()(int x=0){
	debug return 1/x;
	else static assert(0, "crash instruction in release mode");
}
/////////////////////

import core.stdc.stdlib;
import core.stdc.string;

import std.traits;
import utf=std.utf, uni=std.uni;
import std.algorithm, std.conv;
import std.array;
import std.string;
import std.typetuple;

import core.memory;

template ID(alias a){alias a ID;}
template Apply(alias a,T...){alias a!T Apply;}

template ToTuple(alias a){
	static if(a.length){enum val = a[0];alias TypeTuple!(val,ToTuple!(a[1..$])) ToTuple;}
	else alias TypeTuple!() ToTuple;
}

template Seq(T...) { alias T Seq; }

/+enum Ternary: ubyte{
	no = 0,
	yes = 1,
	dunno = 2,
}
alias Ternary.no no;
alias Ternary.yes yes;
alias Ternary.dunno dunno;+/


// escape a string
S escape(S)(S i,bool isc=false)if(isSomeString!S){ // TODO: COW, replace with std lib one as soon as available
	S r;
	foreach(dchar x;i){
		switch(x){
			case '"': if(isc) goto default; r~="\\\""; break;
			case '\'': if(!isc) goto default; r~="\\'"; break;
			case '\\': r~="\\\\"; break;
			case '\a': r~="\\a"; break;
			case '\b': r~="\\b"; break;
			case '\f': r~="\\f"; break;
			case '\n': r~="\\n"; break;
			case '\r': r~="\\r"; break;
			case '\t': r~="\\t"; break;
			case '\v': r~="\\v"; break;
			case '\0': r~="\\0"; break;
			case ' ':  r~=" "; break;
			default:
				if(uni.isWhite(x)) r~=format("\\u%4.4X",cast(uint)x); // wtf?
				else r~=x; break;
		}
	}
	return r;
}

string indent(string code){
	import std.string;
	auto sl=splitLines(code);if(!sl.length) return "";
	string r="    "~sl[0];
	foreach(x;sl[1..$]) r~="\n    "~x;
	return r;
}

bool isNewLine(dchar c){
	return c=='\u000A'||c=='\u000B'||c=='\u000C'||c=='\u000D'||c=='\u0085'||c=='\u2028'||c=='\u2029';
}

// useful for getting naming conventions right in string mixins:
string lowerf(string s){
	if('A'<=s[0]&&s[0]<='Z') return cast(char)(s[0]+('a'-'A'))~s[1..$];
	return s;
}

string upperf(string s){
	if('a'<=s[0]&&s[0]<='z') return cast(char)(s[0]+('A'-'a'))~s[1..$];
	return s;
}



// memory allocation stuff

import std.container;

auto tmpArray(R)(R elems){
	Array!(ElementType!R) r;
	r.insertBack(elems);
	return r;
}

struct MallocAppender(T:T[]){ // NO RAII. Loosely compatible to the std.array.appender interface.
	static MallocAppender create(size_t initial=16){//pure
		MallocAppender app;
		app._length=initial;
		//extern(C)void*malloc(size_t)pure; // =D
		app._data=cast(Unqual!T*)malloc(T.sizeof*app._length);
		app._clength=0;
		return app;
	}
	void put(const(Unqual!T) x){//pure
		_clength++;
		if(_clength>=_length){
			_length*=2;
			//extern(C)void*realloc(void*,size_t)pure;
			_data=cast(Unqual!T*)realloc(cast(void*)_data, T.sizeof*_length);
		}
		_data[_clength-1]=x;
	}
	static if(is(Unqual!T==char)){
		void put(const(dchar) x){
			Unqual!T[4] encoded;
			auto len = utf.encode(encoded, x);
			put(encoded[0..len]);
		}
	}
	void put(const(Unqual!T)[] x){
		_clength+=x.length;
		if(_clength>=_length){
			do _length*=2; while(_clength>_length);
			_data=cast(Unqual!T*)realloc(cast(void*)_data, T.sizeof*_length);
		}
		memcpy(_data+_clength-x.length, x.ptr, T.sizeof*x.length);
	}
	@property T[] data(){return (cast(T*)_data)[0.._clength];}
private:
	Unqual!T* _data;
	size_t _length;
	size_t _clength;
}

auto mallocAppender(T)(size_t initial=1){
	return MallocAppender!T.create(initial);
}

struct NoOpAppender(T:T[]){
	static NoOpAppender create(size_t initial=16){
		NoOpAppender app;
		return app;
	}
	void put(const(Unqual!T) x){
	}
	static if(is(Unqual!T==char)){
		void put(const(dchar) x){
		}
	}
	void put(const(Unqual!T)[] x){
	}
	@property T[] data(){return null;}
}

auto noOpAppender(T)(size_t initial=1){
	return NoOpAppender!T.create(initial);
}

alias GCAlloc.New New; // transparently replace allocator

int ctag;
int[void*] tag;

struct GCAlloc{
	static:
	auto New(T,A...)(A args){
		return new T(args);
	}
	struct AppWrap(T){
		std.array.Appender!T pl;
		auto length(){return pl.data.length;}
		alias pl this;
	}
	auto appender(T)(){return AppWrap!T(std.array.appender!T());}
}
private void[] _mlp;
struct ChunkGCAlloc{
	static:
	auto New(T,A...)(A args){ // Simple chunk allocator on top of the GC. Way faster, but not precise
		auto dg={A a; return new T(a);};
		static assert(__traits(compiles, {A a;return new T(a);}), "cannot create instance of class "~T.stringof);
		return emplace!T(NewImpl(__traits(classInstanceSize, T)),args);
	}
	void[] NewImpl()(size_t size){
		enum size_t alignm=size_t.sizeof, chunksize=1024*1024;
		auto offs=cast(void*)(cast(size_t)(_mlp.ptr+alignm-1)&~(cast(size_t)alignm-1))-_mlp.ptr;
		if(_mlp.length>=size+offs){
			Lok:
			auto r=_mlp[offs..size+offs];
			_mlp=_mlp[size+offs..$];
			return r;
		}else{
			auto allocs=max(size+alignm,chunksize);
			//_mlp=malloc(allocs)[0..allocs];
			_mlp=new void[](allocs);
			offs=cast(void*)(cast(size_t)(_mlp.ptr+alignm-1)&~(cast(size_t)alignm-1))-_mlp.ptr;
			goto Lok;
		}
	}
	struct Appender(T:T[]){
		static Appender create(){
			Appender r;
			// workaround for GDC bug:
			r._data=(cast(Unqual!T[])NewImpl(T.sizeof*initsize))[0..initsize];
			//r._data=cast(Unqual!T[])NewImpl(T.sizeof*initsize);
			r.len=0;
			return r;
		}
		void put(T x){
			if(len>=_data.length) _data.length=_data.length*2;
			_data[len++]=x;
		}
		static if(is(Unqual!T==char)){ // hack to allow appending dchar to a string
			void put(const(dchar) x){
				Unqual!T[4] encoded;
				auto len = utf.encode(encoded, x);
				put(encoded[0..len]);
			}
		}
		void put(const(Unqual!T)[] x){
			if(len+x.length<initsize) _data[len..len+x.length]=cast(Unqual!T[])x;
			else _data~=cast(Unqual!T[])x;
			len+=x.length;
		}
		@property auto length(){return len;}
		@property auto data(){return cast(T[])_data[0..len];}
	private:
		enum initsize=8;
		Unqual!T[] _data;
		size_t len;
	}
	auto appender(T)(){return Appender!T.create();}
	// TODO: FIX BUG
	/+
	 struct AppWrap(T){
		std.array.Appender!T pl;
		auto length(){return pl.data.length;}
		alias pl this;
	}
	auto appender(T)(){return AppWrap!T(std.array.appender!T());}+/
}

string toEngNum(uint i){ // pure
	static string[] a=["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven",
	                   "twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];
	static string[] b=[null,"ten","twenty","thirty","forty","fifty","sixty","seventy","eighty","ninety"];
	if(i>=1000000) return to!string(i);
	if(i>=1000) return toEngNum(i/1000)~" thousand"~(i%1000?" "~toEngNum(i%1000):"");
	if(i>=100) return toEngNum(i/100)~" hundred"~(i%100?" and "~toEngNum(i%100):"");
	if(i>=10) return i<20?a[i]:b[i/10]~(i%10?"-"~toEngNum(i%10):"");
	return a[i];
}

// a really fast downcast. only works if the argument is of the exact class type T
T fastCast(T,R)(R x) if(isFinal!T){return typeid(x) is typeid(T)?cast(T)cast(void*)x:null;}

struct AAbyIdentity(K,V){
	V[K] x;
	size_t opHash()const @trusted pure nothrow{ return cast(size_t)cast(void*)x; }
	int opEquals(const ref AAbyIdentity rhs)const @safe pure nothrow{ return x is rhs.x; }
}
auto byid(K,V)(V[K] x){ return AAbyIdentity!(K,V)(x); }

// compile time file facilites:
template FileExists(string name){enum FileExists = is(typeof(import(name)));}

// file writing, works together with the ctwriter app. Example: dmd foo.d | ./ctwriter

enum CTWriteMode{
	clear,
	append
}

template WriteTo(string name, alias data, CTWriteMode mode=CTWriteMode.clear){ // bug: data cannot contain some forms of XML code
	enum writedata = is(typeof(data):string)?'`'~data~'`':data;
	pragma(msg,"<ctwriter filename=`"~name~"` mode=`"~to!string(mode)~"`>");
	pragma(msg,writedata);
	pragma(msg,"</ctwriter>");
	alias data X;
}
// save the result of templates to speed up compilation and to require less memory
// If a template is changed, the temp/memoized folder has to be cleared.

private template fname(alias T,A...){ enum fname=("tmp/memoize/"~T.stringof~'!'~A.stringof[5..$])[0..min($,100)]~".memoize"; }

template MemoizeTemplate(alias T){
	template MemoizeTemplate(A...){
		static if(FileExists!(fname!(T,A))) enum MemoizeTemplate = mixin(import(fname!(T,A)));
		else{
			enum MemoizeTemplate=WriteTo!(fname!(T,A), T!A, CTWriteMode.clear).X;
		}
	}
}


string _dgliteral(T...)(){string r;foreach(t;T) r~=t.stringof ~ " is"~t.stringof~"(){return null;}"; return r;}
mixin template DownCastMethods(T...){
	mixin(_dgliteral!T()); // DMD bug
}

mixin template DownCastMethod(){
	mixin(`override `~typeof(this).stringof~` is`~typeof(this).stringof~`(){return this;}`);
}

private string Ximpl(string x){
	string r=`"`;
	for(size_t i=0;i<x.length;i++){
		if(x[i]=='@'&&i+1<x.length&&x[i+1]=='('){
			auto start = ++i, nest=1;
			while(nest){
				i++;
				if(x[i]=='(') nest++;
				else if(x[i]==')') nest--;
			}
			r~=`"~`~x[start..i+1]~`~"`;
		}else{
			if(x[i]=='"'||x[i]=='\\') r~="\\";
			r~=x[i];
		}
	}
	return r~`"`;
}

template X(string x){
	enum X = Ximpl(x);
}

template XX(string x){
	enum XX = mixin(Ximpl(x));
}

auto maybe(alias a, alias b, T)(T arg){
	if(arg !is null) return a(arg);
	return b();
}
auto maybe(alias a, T)(T arg){
	return maybe!(a, ()=>typeof(a(arg)).init)(arg);
}

auto or(T)(T t, lazy T s){ if(t) return t; return s; }
S and(T,S)(T t, lazy S s){ if(!t) return null; return s; }

import std.range;
bool any(alias a=(bool _)=>_,R)(R range)if(!isInputRange!R&&isIterable!R){
	foreach(x;range) if(a(x)) return true;
	return false;
}
bool all(alias a=(bool _)=>_,R)(R range)if(!isInputRange!R&&isIterable!R){
	foreach(x;range) if(!a(x)) return false;
	return true;
}

bool among(S,T...)(S arg,T args){
	foreach(ref x; args)
		if(arg == x) return true;
	return false;
}

string digitRep(T)(T i,dstring digits,dchar minus){
	string r;
	string tmp=to!string(i);
	foreach(dchar c;tmp){
		if(c=='-') r~=minus;
		else if('0'<=c&&c<='9') r~=digits[c-'0'];
		else r~=c;
	}
	return r;
}

immutable dstring lowDigits="₀₁₂₃₄₅₆₇₈₉";
immutable dstring highDigits="⁰¹²³⁴⁵⁶⁷⁸⁹";
string lowNum(T)(T i){ return digitRep(i,lowDigits,'₋'); }
string highNum(T)(T i){ return digitRep(i,highDigits,'⁻'); }

immutable dstring lowLetters="ₐ___ₑ__ₕᵢⱼₖₗₘₙₒₚ_ᵣₛₜᵤᵥ_ₓ__";
static assert(lowLetters.length==26);

string toLow(string s)in{assert(s.length);}body{
	string r;
	foreach(dchar c;s){
		switch(c){
			case 'a': .. case 'z':
				if(lowLetters[c-'a']=='_') return null;
				r~=lowLetters[c-'a'];
				break;
			case '0': .. case '9':
				r~=lowDigits[c-'0'];
				break;
			case '-':
				r~='₋';
				break;
			case '+':
				r~='₊';
				break;
			default: return null;
		}
	}
	return r;
}

string asciify(string s){
	auto t=s.to!dstring; // TODO: why necessary? Phobos bug?
	t=t.replace("ξ"d,"xi"d);
	t=t.replace("α"d,"alpha"d);
	t=t.replace("β"d,"beta"d);
	t=t.replace("μ"d,"mu"d);
	t=t.replace("ν"d,"nu"d);
	t=t.replace("λ"d,"lambda"d);
	t=t.replace("δ"d,"delta"d); //TODO assert that the final string does only contain ascii characters.
	t=t.replace("₋"d,"m");
	//TODO also pass as a second argument the format, so that the greek-letters can get tex names.

	//pragma(msg, cast(dchar)('₀'+1));
	foreach(x;0..10)
		t=t.replace(""d~cast(dchar)('₀'+x),""d~cast(dchar)('0'+x));
	return t.to!string;

}

string overline(string s){
	string r;
	import std.uni;
	// TODO: some fonts appear to require the opposite order?
	foreach(dchar d;s){ if(!combiningClass(d)) r~="\u0305"; r~=d; }
	return r;
}
string underline(string s){
	string r;
	import std.uni;
	// TODO: some fonts appear to require the opposite order?
	foreach(dchar d;s){ if(!combiningClass(d)) r~="\u0332"; r~=d; }
	return r;
}
import util.hashtable;
//alias setxEq=ID!((a,b)=>a==b);
//alias setxToHash=ID!(a=>a.toHash());
//alias SetX(T)=HSet!(T,setxEq,setxToHash);
//alias setx=hset!(setxToHash,setxEq);
template SetX(T) if(is(T==class)){ alias SetX=SHSet!T; }
template SetX(T) if(!is(T==class)){ alias SetX=HSet!(T,(a,b)=>a is b,a=>typeid(T).getHash(&a)); }
alias setx=shset;
alias MapX(K,V) = HashMap!(K,V,(a,b)=>a==b,a=>a.toHash());

auto singleton(T)(T arg){
	SetX!T s;
	s.insert(arg);
	return s;
}

struct TupleX(T...){
	T expand;
	alias expand this;
	private static hash_t getHash(T)(ref T x,hash_t b){
		static if(is(T==class)) return FNV(x?x.toHash():0,b);
		else static if(is(T==struct)) return FNV(x.toHash(),b);
		else static if(is(T==string)||is(T==int)) return FNV(typeid(T).getHash(&x),b);
		else static if(is(T==S[],S)||is(T==S[n],S,size_t n)){
			auto r=b;
			foreach(ref y;x) r=getHash(y,r);
			return r;
		}else static if(is(T==U[V],U,V)){
			hash_t r=0;
			foreach(k,v;x) r+=getHash(k,getHash(v,0));
			return FNV(r,b);
		}else static if(is(typeof(cast(hash_t)x))){
			return FNV(cast(hash_t)x,b);
		}else static assert(0,T.stringof);
	}
	hash_t toHash(){
		auto r=fnvb;
		foreach(i,ref x;expand) r=getHash(x,r);
		return r;
	}
}
auto tuplex(T...)(T t){ return TupleX!T(t); }

int opCmp(T)(T a,T b)if(is(typeof(a<b))){
	return a<b?-1:a==b?0:1;
}

import std.bigint;
alias ℤ=BigInt;

ℤ pow(ℤ a,ℤ b)in{assert(b>=0);}body{
	ℤ r=1;
	for(;b;b/=2,a*=a)
		if(b&1) r*=a;
	return r;
}

ℤ gcd(ℤ a,ℤ b){
	if(b<0) return a<0?-gcd(-a,-b):gcd(a,-b);
	ℤ f=1;
Lstart:;
	if(a==b) return a*f;
	if(b>a) swap(a,b);
	if(b==0) return a*f;

	/+if(!(a%2)&&!(b%2)) return 2*gcd(a/2,b/2);
	else if(!(b%2)) return gcd(a,b/2);
	else if(!(a%2)) return gcd(a/2,b);
	return gcd(a-b,b);+/
	if(!(a%2)&&!(b%2)){f*=2; a/=2; b/=2; goto Lstart;}
	else if(!(b%2)){b/=2; goto Lstart;}
	else if(!(a%2)){a/=2; goto Lstart;}
	a-=b; goto Lstart;

}

ℤ lcm(ℤ a,ℤ b){ return a*(b/gcd(a,b)); }

struct ℚ{
	ℤ num=0,den=1;
	this(long num){
		this(num.ℤ);
	}
	this(long num,long den){
		this(num.ℤ,den.ℤ);
	}
	this(ℤ num){
		this.num=num;
	}
	this(ℤ num,ℤ den){
		if(den<0){ num=-num; den=-den; }
		auto d=gcd(abs(num),den);
		num/=d, den/=d;
		this.num=num;
		this.den=den;
	}
	ℚ opUnary(string op:"-")(){
		return ℚ(-num,den);
	}
	ℚ opUnary(string op:"/")(){
		return ℚ(den,num);
	}
	ℚ opBinary(string op:"+")(ℚ r){
		return ℚ(num*r.den+r.num*den,den*r.den);
	}
	ℚ opBinary(string op:"-")(ℚ r){
		return this+-r;
	}
	ℚ opBinary(string op:"*")(ℚ r){
		return ℚ(num*r.num,den*r.den);
	}
	ℚ opBinary(string op:"/")(ℚ r){
		return this*r.opUnary!"/"();
	}
	bool opEquals(long r){
		return num==r*den;
	}
	bool opEquals(ℤ r){
		return num==r*den;
	}
	bool opEquals(ℚ r){
		return num==r.num && den==r.den;
	}
	int opCmp(long r){
		return num.opCmp(den*r);
	}
	int opCmp(ℤ r){
		return num.opCmp(den*r);
	}
	int opCmp(ℚ r){
		if(r.num==0) return num.opCmp(0);
		return (num*r.den).opCmp(den*r.num);
	}
	string toString(){
		if(den==1) return text(num);
		return text(num,"/",den);
	}
	hash_t toHash(){
		return FNV(num.toHash(),FNV(den.toHash()));
	}
}

ℚ pow(ℚ a,ℤ b){
	if(b<0){
		b=-b;
		a=a.opUnary!"/";
	}
	return ℚ(pow(a.num,b),pow(a.den,b));
}

long toLong(ℤ a){ return a.to!string.to!long; } // TODO: do properly
double toDouble(ℤ a){ return a.to!string.to!double; } // TODO: do properly
double toDouble(ℚ a){ return toReal(a.num)/toReal(a.den); } // TODO: do properly
real toReal(ℤ a){ return a.to!string.to!real; } // TODO: do properly
real toReal(ℚ a){ return toReal(a.num)/toReal(a.den); } // TODO: do properly

ℚ toℚ(T)(T arg)if(is(T==float)||is(T==double)||is(T==real)){
	import std.numeric;
	enum precision=64, exponentWidth=15, flags=CustomFloatFlags.signed;
	enum bias=2^^(exponentWidth-1)-1;
	CustomFloat!(precision,exponentWidth,flags,bias) tmp=arg;
	return ℚ((tmp.sign?-1:1)*ℤ(tmp.significand))*pow(ℚ(2),ℤ(tmp.exponent)-bias-precision+1);
}

ℤ abs(ℤ x){ return x<0?-x:x; }
ℚ abs(ℚ x){ return ℚ(abs(x.num),x.den); }


ℤ nCr(ℤ n, ℤ r){
	if(r>n) return ℤ(0);
	ℤ c=1;
	for(ℤ k=0;k<r;)
		c*=n-k,c/=++k;
	return c;
}

auto nC(ℤ n){
	static struct NCRange{
		ℤ n,r=0,c=1;
		void popFront(){
			c*=n-r,c/=++r;
		}
		@property bool empty(){ return r>n; }
		@property ℤ front(){ return c; }
	}
	return NCRange(n);
}

ℤ ceildiv(ℤ a,ℤ b){
	bool sign=(a<0)^(b<0);
	a=abs(a), b=abs(b);
	if(!sign) return (a+b-1)/b;
	return -a/b;
}

ℤ floordiv(ℤ a,ℤ b){
	bool sign=(a<0)^(b<0);
	a=abs(a), b=abs(b);
	if(!sign) return a/b;
	return -(a+b-1)/b;
}

ℤ ceil(ℚ x){
	return ceildiv(x.num,x.den);
}

ℤ floor(ℚ x){
	return floordiv(x.num,x.den);
}

ℤ round(ℚ x){
	return floor(x+ℚ(1,2));
}

struct BitInt(bool signed=true){
	size_t nbits;
	ℤ val;
	this(size_t nbits,ℤ val){
		this.nbits=nbits;
		this.val=val;
		wrap();
	}
	void wrap(){
		val&=(ℤ(1)<<nbits)-1;
		static if(signed) if(nbits&&val&(ℤ(1)<<(nbits-1))) val-=(ℤ(1)<<nbits);
	}
	BitInt opBinary(string op)(BitInt r)if(!op.among("<<",">>"))in{
		assert(nbits==r.nbits);
	}do{
		return BitInt(nbits,mixin(`val `~op~` r.val`));
	}
	BitInt opBinary(string op)(size_t r)if(op.among("<<",">>")){
		// TODO: shortcut for r>=nbits?
		return BitInt(nbits,mixin(`val `~op~` r`));
	}
	BitInt opUnary(string op)(){
		return BitInt(nbits,mixin(op~` val`));
	}
	bool opEquals(bool signed)(BitInt!signed rhs){
		return val==rhs.val;
	}
	int opCmp(bool signed)(BitInt!signed rhs){
		return val.opCmp(rhs.val);
	}
	bool opEquals(T)(T rhs)if(!is(rhs==BitInt)&&is(typeof(val==ℤ(rhs)))){
		return val==ℤ(rhs);
	}
	int opCmp(T)(T rhs)if(!is(rhs==BitInt)&&is(typeof(val.opCmp(ℤ(rhs))))){
		return val.opCmp(rhs);
	}
	bool opEquals(double rhs){
		return toReal(val)==rhs; // TODO: improve?
	}
	int opCmp(double rhs){
		return toReal(val).opCmp(rhs); // TODO: improve?
	}
	bool opEquals(ℚ rhs){
		return rhs==val;
	}
	int opCmp(ℚ rhs){
		return -rhs.opCmp(val);
	}
	string toString(){
		return text(val);
	}
	hash_t toHash(){
		return FNV(nbits,FNV(val.toHash()));
	}
}


template tryImport(string filename,string alt=""){
	static if(__traits(compiles,import(filename))) enum tryImport = import(filename)[0..$-1];
	else enum tryImport = alt;
}

string capitalize(string s){ // (only works with ascii for now)
	if(!s.length) return s;
	return s[0].toUpper().to!string~s[1..$];
}
string uncapitalize(string s){
	if(!s.length) return s;
	return s[0].toLower().to!string~s[1..$];
}

int displayWidth(dchar dc){
	return 1; // TODO: actually use width of characters
}
int displayWidth(string s){
	return s.map!(c=>displayWidth(c)).fold!"a+b"(0);
}
