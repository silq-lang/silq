// Written in the D programming language.

// FOR DEBUGGING ONLY
public import std.stdio;
void dw(T...)(T args){
	debug writeln(args);
	else static assert(0,"debugging output call in release mode");
}
int crash()(int x=0){
	debug return 1/x;
	else static assert(0, "crash instruction in release mode");
}
/////////////////////

import std.c.stdlib;
import std.c.string;

import std.traits;
import utf=std.utf, uni=std.uni;
import std.algorithm, std.conv;
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

// Versions from Phobos do not work. TODO: reduce and file bug report
import std.range;
bool any(alias a=(bool _)=>_,R)(R range){// if(is(typeof(a(R.front.init)): bool) && isInputRange!R){
	foreach(x;range) if(a(x)) return true;
	return false;
}
bool all(alias a=(bool _)=>_,R)(R range){// if(is(typeof(a(R.front.init)): bool) && isInputRange!R){
	foreach(x;range) if(!a(x)) return false;
	return true;
}

bool among(S,T...)(S arg,T args){
	foreach(ref x; args)
		if(arg == x) return true;
	return false;
}
