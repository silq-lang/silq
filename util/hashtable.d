// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module util.hashtable;

import std.typecons, std.typetuple;
import std.functional, std.algorithm;
import std.conv, std.array;

//import util;

struct HashMap(K_, V_, alias eq_ , alias h_){
	alias K=K_;
	alias V=V_;
	alias binaryFun!eq_ eq;
	alias unaryFun!h_ h;
	struct E{ V v; K k; } // TODO: why can't the two fields be swapped?
	alias E[] B;
	B[] es;
	size_t length;

	enum initialSize = 16;
	enum maxBucketSize = 20;
	enum limitfactor = 32;
	enum incrementFactor = 3;
	enum decrementFactor = 2;
	enum compactLimit = 16;


	private void initialize(){ es = new B[](initialSize); }
	int numrealloc;
	private void realloc(){
		auto ees = es;
		es = new B[](es.length*incrementFactor);
		length = 0;
		foreach(b;ees) foreach(e;b) insert(e);
	}
	
	private void compact(){
		auto ees = es;
		es = new B[](es.length/decrementFactor);
		length = 0;
		foreach(b;ees) foreach(ref e;b) insert(e);
	}

	bool opBinaryRight(string op: "in")(K k){
		if(length){
			foreach(ref e; es[h(k)%$])
				if(eq(k, e.k)) return true;
		}
		return false;
	}

	V get(K k, lazy V alt){
		if(length){
			foreach(ref e; es[h(k)%$])
				if(eq(k, e.k)) return e.v;
		}
		return alt;
	}

	ref V opIndex(K k){ // TODO: get rid of code duplication
		if(length){
			foreach(ref e; es[h(k)%$])
				if(eq(k, e.k)) return e.v;
		}
		static if(is(typeof(text(k)))) assert(0, text("key not found: ",k));
		else assert(0, "key not found");
	}

	bool remove(K k){
		if(!es.length) return false;
		auto b = &es[h(k)%$];
		foreach(ref e; *b)
			if(eq(k, e.k)){
				swap(e, (*b)[$-1]);
				length--;
				*b=(*b)[0..$-1];
				(*b).assumeSafeAppend();
				return true;
			}
		return false;
	}

	private bool insert(E x) /+out{assert(x.k in this, text(es[h(x.k)%$]));}body+/{
		if(!es.length) initialize();
		auto hs=h(x.k);
		auto b = &es[hs%$];
		foreach(ref e; *b)
			if(eq(x.k, e.k)){
				e=x;
				return false;
			}
		length++;
		*b~=x;
		if(b.length>maxBucketSize&&hs!=h((*b)[0].k)&&es.length<2*length) realloc();
		return true;
	}
	
	void opIndexAssign(V v, K k){
		insert(E(v,k));
	}
	void opIndexOpAssign(string op,W)(W w, K k){
		if(length){
			foreach(ref e; es[h(k)%$])
				if(eq(k, e.k)){
					mixin(`e.v `~op~`= w;`);
					return;
				}
		}
		V v; mixin(`v` ~op~`= w;`);
		insert(E(v,k));
	}

	int opApply(scope int delegate(ref V) dg){
		if(es.length>compactLimit*length) compact();
		foreach(ref b;es) foreach(ref e;b) if(auto r=dg(e.v)) return r;
		return 0;
	}
	int opApply(scope int delegate(ref K,ref V) dg){
		if(es.length>compactLimit*length) compact();
		foreach(ref b;es) foreach(ref e;b) if(auto r=dg(e.k, e.v)) return r;
		return 0;
	}
	bool opEquals()(ref HashMap rhs){
		foreach(k,v;this) if(k !in rhs || rhs[k] != v) return false;
		foreach(k,v;rhs) if(k !in this) return false;
		return true;
	}
	hash_t toHash()(){
		hash_t r=0;
		foreach(ref x;es) foreach(ref b;x) r+=FNV(h(b.k),FNV(b.v.toHash(),fnvb)); // TODO: improve
		return r;
	}

	void clear(){ es[]=B.init; length=0; }
	HashMap dup(){
		// return HashMap(es.map!(_=>_.dup).array, length); // fu
		auto oes = es.dup;
		foreach(ref e;oes) e=e.dup;
		return HashMap(oes, length);
	}

	//static if(is(typeof(text(K.init,V.init))))
	string toString(){
		//return text("[",join(map!(_=>text(_.k,":",_.v))(filter!"a.e"(es)),", "),"]");// wtf
		auto r="[";
		foreach(b;es) foreach(e;b) r~=text(e.k,":",e.v)~", ";
		if(r.length>2) r=r[0..$-2];
		//r.assumeSafeAppend();
		r~="]";
		return r;
	}
}

static if(size_t.sizeof==4) enum fnvp = 16777619U, fnvb = 2166136261U;
else static if(size_t.sizeof==8) enum fnvp = 1099511628211LU, fnvb = 14695981039346656037LU;

size_t FNV(size_t data, size_t start=fnvb){
	return (start^data)*fnvp;
}

import std.range;
struct HSet(T_,alias eq, alias h){
	alias T=T_;
	private HashMap!(T,void[0],eq,h) payload;
	hash_t hash=0;
	void clear(){ payload.clear(); }
	auto dup(){ return HSet(payload.dup,hash); }
	@property size_t length(){ return payload.length; }
	hash_t toHash(){ return hash; }
	bool opBinaryRight(string op: "in")(T t){
		return t in payload;
	}
	void insert(T t){
		if(payload.insert(typeof(payload).E([],t)))
			hash+=FNV(h(t));
	}
	void remove(T t){
		if(payload.remove(t))
			hash-=FNV(h(t));
	}
	int opApply(scope int delegate(T) dg){
		foreach(x,_;payload) if(auto r=dg(x)) return r;
		return 0;
	}
	bool opEquals(ref HSet rhs){
		foreach(x;this) if(x !in rhs) return false;
		foreach(x;rhs) if(x !in this) return false;
		return true;
	}
	static if(is(typeof(text(T.init)))) string toString(){
		string r="{";
		foreach(x;this) r~=text(x)~", ";
		if(r.length>2) r=r[0..$-2];
		return r~="}";
	}
}

template hset(alias h,alias eq){
	auto hset(T)(T args){
		alias S=typeof({ foreach(x;args) return x; assert(0); }());
		HSet!(S,eq,h) s;
		foreach(x;args) s.insert(x);
		return s;
	}
}

struct SHSet(T_) if(is(T_==class)){ // small hash set
	alias T=T_;
	bool isSmall=true;
	union{ T[4] small; HSet!(T,(a,b)=>a is b,a=>a.toHash()) large; }
	private this(typeof(large) large){ isSmall=false; this.large=large; }
	void clear(){
		if(isSmall) small[]=null;
		else large.clear();
	}
	auto dup(){
		if(isSmall) return this;
		return SHSet(large.dup);
	}
	@property size_t length(){
		if(isSmall){ size_t r=0; foreach(x;small) if(x !is null) r++; return r; }
		return large.length;
	}
	hash_t toHash(){
		if(isSmall){ hash_t r; foreach(x;small) if(x !is null) r+=FNV(x.toHash()); return r; }
		return large.toHash();
	}
	bool opBinaryRight(string op: "in")(T t){
		if(isSmall){ foreach(x;small) if(x is t) return true; return false; }
		return t in large;
	}
	void insert(T t){
		if(isSmall){
			foreach(x;small) if(x is t) return;
			foreach(ref x;small) if(x is null){ x=t; return; }
			typeof(large) l;
			foreach(x;small) l.insert(x);
			isSmall=false;
			large=l;
		}
		large.insert(t);
	}
	void remove(T t){
		if(isSmall){
			foreach(ref x;small) if(x is t) x=null;
			return;
		}
		large.remove(t);
		if(large.length<=small.length){
			T[small.length] s;
			int i=0;
			foreach(x;large) s[i++]=x;
			isSmall=true;
			small=s;
		}
	}
	int opApply(scope int delegate(T) dg){
		if(isSmall){ foreach(x;small) if(x !is null) if(auto r=dg(x)) return r; return 0; }
		foreach(x;large) if(auto r=dg(x)) return r;
		return 0;
	}
	bool opEquals(ref SHSet rhs){
		foreach(x;this) if(x !in rhs) return false;
		foreach(x;rhs) if(x !in this) return false;
		return true;
	}
	static if(is(typeof(text(T.init)))) string toString(){
		string r="{";
		foreach(x;this) r~=text(x)~", ";
		if(r.length>2) r=r[0..$-2];
		return r~="}";
	}	
}

auto shset(T)(T args){
	alias S=typeof({ foreach(x;args) return x; assert(0); }());
	SHSet!S s;
	foreach(x;args) s.insert(x);
	return s;
}




/+
void main(){
	import std.stdio;
	auto s=hset!(a=>a,(a,b)=>a==b,int)([1,2,3,4]);
	writeln(3 in s);
	auto t=hset!(a=>a.toHash(),(a,b)=>a==b)([s]);
	writeln(s !in t);
}+/

struct Subsets(T){
	typeof(T.init.array) arr;
	int opApply(scope int delegate(T) dg){
		T cur;
		int enumerate(size_t i){
			if(i>=arr.length) return dg(cur.dup);
			if(auto r=enumerate(i+1)) return r;
			cur.insert(arr[i]);
			if(auto r=enumerate(i+1)) return r;
			cur.remove(arr[i]);
			return 0;
		}
		return enumerate(0);
	}
}

auto subsets(T)(T arg){ return Subsets!T(arg.array); }
auto element(T)(T arg)in{assert(arg.length==1);}body{ foreach(x;arg) return x; assert(0); }

T intersect(T)(T a,T b){
	T r;
	foreach(x;a) if(x in b) r.insert(x);
	return r;
}
T unite(T)(T a,T b){
	T r;
	foreach(x;a) r.insert(x);
	foreach(y;b) r.insert(y);
	return r;
}

T setMinus(T)(T a,T b){
	T r;
	foreach(x;a) if(x !in b) r.insert(x);
	return r;
}

