/+
def main(const x:𝔹){}
+/
/+
import qft;

def main(){
	return ([n:!ℕ]⇒reverse(QFT[n]))(QFT(45:int[10]));
}
+/
/+
def main(){
	def fib(n:!ℕ):!ℕ{
		if n<=1{ return n; }
		return fib(n sub 1)+fib(n sub 2);
	}
	return fib(3);
}
+/
/+
def foo(i:!ℤ)(j:!ℤ)(k:!ℤ):!ℕ{
	if i>0{ return 2*foo(i-1)(k)(j); }
	if k>0{ return 3*foo(i)(k-1)(j); }
	if j>0{ return 5*foo(i)(k)(j-1); }
	return 1;
}

def bar(i:!ℤ)qfree{
	x:=2;
	return lambda(j:!ℤ)qfree{
		y:=3;
		return lambda(k:!ℤ)qfree:!ℕ{
			z:=5;
			if i>0{ return x*bar(i-1)(k)(j); }
			if k>0{ return y*bar(i)(k-1)(j); }
			if j>0{ return z*bar(i)(k)(j-1); }
			return 1;
		}
	}
}

def baz(i:!ℤ)qfree{
	x:=2;
	return lambda(j:!ℤ)qfree:!ℤ!→qfree !ℕ{
		y:=3;
		return lambda(k:!ℤ)qfree{
			z:=5;
			if i>0{ return x*baz(i-1)(k)(j); }
			if k>0{ return y*baz(i)(k-1)(j); }
			if j>0{ return z*baz(i)(k)(j-1); }
			return 1;
		}
	}
}

def qux(i:!ℤ)qfree:!ℤ!→qfree!ℤ!→qfree!ℕ{
	x:=2;
	return lambda(j:!ℤ)qfree{
		y:=3;
		return lambda(k:!ℤ)qfree{
			z:=5;
			if i>0{ return x*qux(i-1)(k)(j); }
			if k>0{ return y*qux(i)(k-1)(j); }
			if j>0{ return z*qux(i)(k)(j-1); }
			return 1;
		}
	}
}

def main(){
	return foo(1)(2)(3)+bar(1)(2)(3)+baz(1)(2)(3);
}
+/
/+
def main(){
	print(measure(H(0:𝔹)));
}
+/
/+
def main(){
	x:=0:𝔹;
	forget(x=1:𝔹);
}
+/
/+
def main(){
	def foo(){
		def bar(){
			return 1/0;
		}
		return bar();
	}
	return foo();
}
+/
/+
def main(){
	x:=[H(0:𝔹),H(1:𝔹)];
	y:=x coerce int[3]; // runtime error
	return y;
}
+/
/+
def foo(a:𝔹^2)mfree{
	b:=a[0];
	a[0]:=H(a[0]);
	H(a[0]):=a[0];
	return (a,b);
}
def main()⇒reverse(foo)((1,0):𝔹^2,1:𝔹);
+/
/+
def main(){
	x:=(H(0:𝔹),);
	y:=(x[0..1]:𝔹[]);
	forget((x:𝔹[])=y);
	y[0]:=H(y[0]);
	return y;
}
+/
/+def main(){
	x:=(H(0:𝔹),);
	x:=(x:𝔹[]);
	x[0]:=H(x[0]);
	return x;
}
+/
/+
def main(){
	def foo[a](x:a){
		def id(x:a)mfree⇒(dup(x),x);
		return reverse(id)(dup(x),x);
	}
	return (foo([0,1]),foo(H(0:𝔹)));
}
+/
/+
import qft;

def main(){
	return QFT(([n:!ℕ]⇒reverse(QFT[n]))(1:int[6]));
}
+/
/+
def main(){
	f:=reverse(dup[𝔹^2]);
	g:=([a]⇒reverse(dup[a]))[𝔹^2];
	x:=(H(0:𝔹),H(0:𝔹));
	y:=dup(x);
	f(y,x);
	x:=reverse(g)(y,());
	reverse(reverse(g))(y,x);
	(a,b):=y;
	return (H(a),H(b));
}
+/
//import codeforces.winter19.contest.b1;
/+
def foo()mfree{
	x:=0:!𝔹;
	y:=H(x);
	return y;
}
def main()⇒reverse(foo)(H(0:𝔹));
+/
/+
def foo(const y:𝔹)mfree{
	x:=H(y);
	return x;
}
def main()⇒reverse(foo)(0:!𝔹,H(0:𝔹));
+/
/+
def toW[n:!ℕ]lifted:𝔹^n →mfree 𝔹^n⇒lambda(qs:𝔹^n)mfree:𝔹^n{
	if n==1{ qs[0]:=X(qs[0]); }
	else if n>1{
		(([head] coerce 𝔹^1):𝔹[])~((tail coerce 𝔹^(n sub 1)):𝔹[]):=(qs:𝔹[]);
		θ:=asin(1/sqrt(n));
		head:=rotY(θ,head);
		if !head { tail := toW(tail); }
		qs:=[head]~(tail:𝔹[]) coerce B^n;
	}
	return qs;
};
def solve(qs:𝔹^3):!𝔹{
	if qs[1]{ phase(-2·π/3); }
	if qs[2]{ phase(-4·π/3); }
	qs:=reverse(toW[3])(qs);
	return measure(qs as int[3])!=0;
}
def main(){
	qs:=toW(vector(3,0:𝔹));
	if qs[1]{ phase(2·π/3); }
	if qs[2]{ phase(4·π/3); }
	return solve(qs);
}
+/
/+
def toW[n:!ℕ]lifted:𝔹^n →mfree 𝔹^n⇒lambda(qs:𝔹^n)mfree:𝔹^n{
	if n==1{ qs[0]:=X(qs[0]); }
	else if n>1{
		θ:=asin(1/sqrt(n));
		(([head] coerce 𝔹^1):𝔹[])~((tail coerce 𝔹^(n sub 1)):𝔹[]):=(qs:𝔹[]);
		head:=rotY(θ,head);
		if !head { tail := toW(tail); }
		qs:=[head]~(tail:𝔹[]) coerce B^n;
	}
	return qs;
};

def fromW[n:!ℕ]lifted:𝔹^n→mfree 𝔹^n⇒lambda(qs:𝔹^n)mfree:𝔹^n{
    if n = 1 {
        qs[0] := reverse(X)(qs[0]);
    } else if n > 1 {
        θ := asin(1 / sqrt(n));
        __tmp2 := qs coerce 𝔹[];
        (head,) := __tmp2[0..1] coerce 𝔹^1;
        tail := __tmp2[1..__tmp2.length] coerce 𝔹^((n sub 1));
        forget(__tmp2=[head] ~ (tail: 𝔹[]));
        if ¬head {
            tail := fromW(tail);
        }
        head := reverse(rotY)(θ,head);
        __tmp0 := dup((([head] coerce 𝔹 ^ 1): 𝔹[]) ~ ((tail coerce 𝔹 ^ (n sub 1)): 𝔹[]));
        forget(tail=(__tmp0[1..__tmp0.length]: 𝔹[]) coerce 𝔹 ^ (n sub 1));
        forget((head,)=(__tmp0[0..1]: 𝔹[]) coerce 𝔹 ^ 1);
        qs := __tmp0 coerce 𝔹^n;
    }
    return qs;
};

def solve(qs:𝔹^3):!𝔹{
	if qs[1]{ phase(-2·π/3); }
	if qs[2]{ phase(-4·π/3); }
	qs:=fromW(qs);
 	return measure(qs as int[3])!=0;
}
def main(){
	qs:=toW(vector(3,0:𝔹));
	if qs[1]{ phase(2·π/3); }
	if qs[2]{ phase(4·π/3); }
	return solve(qs);
}
+/
/+
def main(){
	qs:=(H(0:𝔹),H(0:𝔹)) coerce 𝔹^2;
	head:=qs[0];
	tail:=(qs:𝔹[])[1..2] coerce 𝔹^(2 sub 1);
	forget(qs=[head]~(tail:𝔹[]) coerce 𝔹^2);
	qs:=[head]~(tail:𝔹[]) coerce 𝔹^2;
	(qs₀,qs₁):=qs;
	return (H(qs₀),H(qs₁));
}
+/
/+
def main(){
	qs:=(H(0:𝔹),H(0:𝔹)) coerce 𝔹^2;
	head:=qs[0];
	tail:=(qs:𝔹[])[1..2] coerce 𝔹^(2 sub 1);
	forget(qs=[head]~(tail:𝔹[]) coerce 𝔹^2);
	(tail,):=tail coerce 𝔹^1;
	return (H(head),H(tail));
}
+/
/+
def main(){
	qs:=(H(0:𝔹),H(0:𝔹)) coerce 𝔹^2;
	head:=qs[0];
	tail:=(qs:𝔹[])[1..2] coerce 𝔹^(2 sub 1);
	forget(qs=dup([head]~(tail:𝔹[])) coerce 𝔹^2);
	(tail,):=tail coerce 𝔹^1;
	return (H(head),H(tail));
}
+/
/+
def main(){
	qs:=(H(0:𝔹),H(0:𝔹)) coerce 𝔹^2;
	head:=qs[0];
	tail:=(qs:𝔹[])[1..2] coerce 𝔹^(2 sub 1);
	ws:=dup([head]~(tail:𝔹[])) coerce B^2;
	forget(qs=ws);
	forget([head]~(tail:𝔹[])=ws:𝔹[]);
	(ws₀,ws₁):=ws;
	return (H(ws₀),H(ws₁));
}
+/
/+
def main(){
	qs:=(H(0:𝔹),H(0:𝔹)) coerce 𝔹^2;
	head:=qs[0];
	tail:=(qs:𝔹[])[1..2] coerce 𝔹^(2 sub 1);
	ws:=dup([head]~(tail:𝔹[]));
	return (qs,ws,head,tail);
}
+/
/+
def main(){
	x:=[0:𝔹];
	x[0]:=H(x[0]);
	return x;
}
+/
/+
def main(){
	x:=H(0:𝔹);
	qs:=array(1,x);
	forget(x=qs[0]);
	ws:=qs[0..1];
	return (qs,ws);
}
+/
/+
def foo(a:int[32],b:int[32],const c:int[32],const d:int[32])mfree⇒(a,b);
def main(){
	f:=reverse(foo);
	return f;
}
+/
/+
def rev[a](f: const a!→mfree a)⇒reverse(f);
def main(){
	f:=reverse(dup[𝔹^2]); // (const 𝔹^2)×(𝔹^2) !→qfree 𝟙
	g:=rev(dup[𝔹^2]);     // (const 𝔹^2)×(𝔹^2) !→qfree 𝟙
	return (f,g);
}
+/
/+
def foo(){
	x:=(H(false),H(false),H(false),H(false));
	r:=dup(x as uint[4]);
	dup[𝔹^4](r as 𝔹^4):=x;
	return r;
}
//def main()⇒reverse(dup[𝔹^4]);
def main()⇒foo;
+/
/+
def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	for k in [0..n){
		ψ[k] := H(ψ[k]);
		for l in [k+1..n){
			if ψ[l] && ψ[k]{
				phase(2·π·2^(k-l-1));
			}
		}
	}
	return ψ;
}
def main(){
	x:=measure(H(false),H(false),H(false),H(false));
	iQFT:=[n:!ℕ]⇒reverse(QFT[n]);
	r:=iQFT(QFT(x as uint[4]));
	forget(r=(x as uint[4]));
	return (x as !uint[4], reverse(QFT[10]));
}
+/
/+
def main(){
	x:=[H(0:𝔹),];
	(x,):=x coerce 𝔹^1;
	return H(x);
}
+/
/+
def main(){
	x:=(H(0:𝔹),);
	y:=x as int[1];
	(x,):=dup(dup(y) as 𝔹^1);
	forget((x,)=dup(dup(y) as 𝔹^1));
	(x,):=y as 𝔹^1;
	return H(x);
}
+/
/+
def main(){
	x:=(H(0:𝔹),);
	y:=x as int[1];
	(x₀,):=y as 𝔹^1;
	return H(x₀);
}
+/
/+
def main(){
	x:=(H(0:𝔹),H(0:𝔹));
	y:=x as int[2];
	(x₀,x₁):=y as 𝔹^2;
	return (H(x₀),H(x₁));
}
+/
/+
def main(){
	x:=(H(false),H(false),H(false),H(false));
	r:=dup(x as uint[4]);
	forget((r as 𝔹^4)=x);
	(x₀,x₁,x₂,x₃):=x;
	return (H(x₀),H(x₁),H(x₂),H(x₃));
}
+/
/+
def main(){
	x:=measure(H(false),H(false),H(false),H(false));
	r:=dup(x);
	forget((r as 𝔹^4)=x);
}
+/
/+
def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	for k in [0..n){
		ψ[k] := H(ψ[k]);
		for l in [k+1..n){
			if ψ[l] && ψ[k]{
				phase(2·π·2^(k-l-1));
			}
		}
	}
	return ψ;
}
def iQFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in (n..-1..0]{
		for l in (n..-1..k+1]{
			if ψ[l] && ψ[k]{
				phase(2·π·2^(k-l-1)):=();
			}
		}
		H(ψ[k]) := ψ[k];
	}
	for k in (n div 2..-1..0]{
		(ψ[n-k-1],ψ[k]) := (ψ[k],ψ[n-k-1]);
	}
	return ψ;
}
def main(){
	x:=measure(H(false),H(false),H(false),H(false));
	r:=iQFT(QFT(x as uint[4]));
	return (x as uint[4],r);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	x:=rotZ(0.2,x);
	x:=reverse(rotZ)(0.2,x);
	return H(x);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	x:=rotY(0.2,x);
	x:=reverse(rotY)(0.2,x);
	return H(x);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	x:=rotX(0.2,x);
	x:=reverse(rotX)(0.2,x);
	return H(x);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	if x{
		reverse(phase)(π/2,());
		phase(π/2);
	}
	return H(x);
}
+/
/+
def main(){
	return reverse(X)(0:𝔹);
}
+/
/+
def main(){
	return reverse(H)(0:𝔹);
}+/
/+
def main(){
	a:=H(0:𝔹);
	b:=dup(a);
	():=forget(a=b);
	return H(b);
}
+/
/+
def f(x:𝔹)qfree⇒x;
def g(x:𝔹)qfree{
	(f:𝔹!→qfree 𝔹)(y):=x:𝔹;
	return y;
}
def main():!𝔹⇒reverse(g)(0:!𝔹);
+/
/+
def foo(const x:int[32])mfree{
	a:=x:int[32];
	b:=2*x:int[32];
	c:=a+b;
	return (a,b,c);
}

def revFoo(const x:int[32],r:int[32]^3)mfree{
	(a,b,c):=r;
	a+b:=c;
	2*x:int[32]:=b;
	dup[int[32]](x):=a;
	return ();
}

def main(){
	revFoo(1:int[32],(1,2,3):int[32]^3);
	reverse(foo)(1:int[32],(1:int[32],2:int[32],3:int[32]));
	return (foo(1:int[32]),reverse(revFoo)(1:int[32],()));
}
+/

/+
def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	for k in [0..n){
		ψ[k] := H(ψ[k]);
		for l in [k+1..n){
			if ψ[l] && ψ[k]{
				phase(2·π·2^(k-l-1));
			}
		}
	}
	return ψ;
}
def iQFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in (n..-1..0]{
		for l in (n..-1..k+1]{
			if ψ[l] && ψ[k]{
				reverse(phase)(-2·π·2^(k-l-1),()):=();
			}
		}
		reverse(H)(ψ[k]) := ψ[k];
	}
	for k in (n div 2..-1..0]{
		(ψ[n-k-1],ψ[k]) := (ψ[k],ψ[n-k-1]);
	}
	return ψ;
}
def main(){
	x:=measure(H(false),H(false),H(false),H(false));
	r:=iQFT(QFT(x as uint[4]));
	return (x as uint[4],r);
}
+/
/+
def main(){
	a:=[]:ℕ[];
	n:=4;
	for i in [0..1..n){
		a~=[i];
	}
	for i in [n..-1..0]{
		a~=[i];
	}
	return a;
}
+/
/+
def main(){
	def f(const x:𝔹){
		measure(x);
		return ();
	}
	x:=H(0:𝔹);
	reverse(phase)(π/2,()):=f(x);
	phase(-π/2);
	return x;
}
+/
/+
def main(){
	f:=()=>(0,1):𝔹^2;
	id:=(x:𝔹)qfree⇒x;
	(x,reverse(id)(y)):=f();
	return (x,y);
}
+/
/+
def main(){
	(x,(y,z)):=(1,(2,3));
	return (x,y,z);
}
+/
/+
def main(){
	(reverse(H)(x),reverse(H)(y)):=(H(0:𝔹),H(1:𝔹));
	return (x,y);
}
+/
/+
def main(){
	reverse(H)(x):=H(0:𝔹);
	return x;
}
+/
/+
def foo()mfree{
	y:=H(false);
	z:=dup(y);
	dup[𝔹](y):=z;
	k:=0:𝔹;
	dup[𝔹](false):=k;
	return y;
}
def main()⇒reverse(foo);
+/

/+
def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	for k in [0..n){
		ψ[k] := H(ψ[k]);
		for l in [k+1..n){
			if ψ[l] && ψ[k]{
				phase(2·π·2^(k-l-1));
			}
		}
	}
	return ψ;
}
+/
/+
def seq[a,b,c,d](f: !(Π[τ]lifted. a×const d×(b×const d!→mfree τ)!→mfree τ),g: !(Π[τ]lifted. b×const d×(c×const d!→mfree τ)!→mfree τ))[τ](x:a,const k:d,ret:c×const d!→mfree τ)mfree⇒f[τ](x,k,(y:b,const k:d)mfree⇒g[τ](y,k,ret));

def QFT_norm[n:!ℕ]()mfree{
	f:=[τ](ψ: uint[n], const d:𝟙, ret: uint[n]×const 𝟙!→mfree τ)mfree⇒ret(ψ,d);
	for k in [0..n div 2){
		f=seq[uint[n],uint[n],uint[n],𝟙](f,[τ](ψ: uint[n], const d:𝟙, ret: uint[n]×const 𝟙!→mfree τ)mfree{ (ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]); return ret(ψ,d); });
	}
	for k in [0..n){
		f=seq[uint[n],uint[n],uint[n],𝟙](f,[τ](ψ: uint[n], const d:𝟙, ret: uint[n]×const 𝟙!→mfree τ)mfree{ ψ[k] := H(ψ[k]); return ret(ψ,d); });
		for l in [k+1..n){
			f=seq[uint[n],uint[n],uint[n],𝟙](f,[τ](ψ: uint[n], const d:𝟙, ret: uint[n]×const 𝟙!→mfree τ)mfree{
				if ψ[l] && ψ[k]{
					phase(2·π·2^(k-l-1));
				}
				return ret(ψ,d);
			});
		}
	}
	f=seq[uint[n],uint[n],uint[n],𝟙](f,[τ](ψ: uint[n],const d:𝟙,ret: uint[n]×const 𝟙!→mfree τ)mfree⇒ret(ψ,d));
	return ((),f);
}

def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	return QFT_norm[n]()[1][uint[n]](ψ,(),(ψ: uint[n],const d:𝟙)mfree⇒ψ);
}

def iQFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for kr in [0..n){
		k:=n sub 1 sub kr;
		for l in [k+1..n){
			if ψ[l] && ψ[k]{
				phase(-2·π·2^(k-l-1));
			}
		}
		ψ[k] := H(ψ[k]);
	}
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	return ψ;
}

/+
def phaseUint[n:!ℕ](const φ: uint[n])mfree{
	for i in [0..n){ if φ[i]{ phase(2·π·2^i/2^n); } }
}
def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in [0..n){
		j:=n sub 1 sub k;
		ψ[j] := H(ψ[j]); // ψ'[j] = 1/√2(|0⟩+expi(2π·2^k·(ψ&2^j)/2^n)|1⟩)
		if ψ[j]{ phaseUint(2^k·(ψ⊕2^j)); }// ψ''[j] = 1/√2(|0⟩+expi(2π·2^k·ψ/2^n)|1⟩)
	}
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	return ψ;
}
+/
/+
def phaseUint[n:!ℕ](const φ: uint[n])mfree{
	for i in [0..n){ if (φ&2^i)!=0{ phase(2·π·2^(i-n)); } }
}
def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in [0..n){
		j:=n sub 1 sub k;
		ψ[j] := H(ψ[j]);
		if (ψ&2^j)!=0{ phaseUint(2^k*ψ⊕2^(n sub 1)); }
	}
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	return ψ;
}
+/

def main(){
	n:=8;
	/+x:=0:uint[n];
	for i in [0..n){ x[i]:=H(x[i]); }
	def f(x:uint[n])lifted⇒x%5;
	measure(f(x));
	return (measure(iQFT(x)) as !ℕ)/2^n+0.0;+/ // TODO: coerce uint[n] to uint[6]
		//x[1]:=H(x[1]);
	x:=measure(H(false),H(false),H(false),H(false));
	//r:=iQFT(QFT(x as uint[4]));
	r:=([n:!ℕ]⇒reverse(QFT[n]))(QFT(x as uint[4]));
	// forget((x as uint[4])=r); // TODO: fix simulator
	//return measure(x as uint[4])==measure(r);
	return (x as uint[4],r);
	//x[1]:=H(x[1]);
	//return x;
	/+x:=measure(H(false),H(false),H(false),H(false));
	forget(iQFT(QFT(x as uint[4]))=x as uint[4]); // TODO: fix+/
}
+/
/+
def foo()mfree{
	x:=0:𝔹;
	forget(x); // TODO
}
def main()⇒reverse(foo);
+/
/+
def main(){
	reverse(measure[int[32]]); // error
	x:=H(0:𝔹);
	f:=()mfree=>x;
	reverse(f); // error
}
+/
/+def fib[m:!ℕ]:!int[m]→!int[m]{ // TODO: automatically add annotations
	return (n:!int[m]){
		if n<=1{ return n; }
		return fib(n - 1)+fib(n - 2);
	}
}
def main(){
	return fib(10:!int[10]);
}
+/
/+def main(){
	x:=0:𝔹;
	if true:𝔹 {
		forget(x);
		x:=1:𝔹;
	}
	return x;
}+/
/+
def main(){
	f:=(x:𝔹^1)lifted⇒();
	x:=0:uint[1];
	x[0]:=H(x[0]);
	f(x as 𝔹^1);
	x[0]:=H(x[0]);
	return x; // 0
}
+/
/+
import qft;

def main(){
	return QFT(1:int[6]);
}
+/
/+
def main(){
	x:=vector(3,0:𝔹);
	y:=array(3,0:𝔹);
	x=y coerce 𝔹^3;
	return x;
}
+/
/+
def main(){
	H(x):=0; // error
	forget(H(x)=0);
	n:=3;
	x:=(0:int[n]):uint[n]; // error
}
+/
/+
def main(){
	x:=2;
	def f()=>x;
	def g()=>f();
	return g();
}
+/
/+
x:=2;
def main(){
	def f()=>x;
	def g()=>f();
	return g();
}
+/
/+
def main(){
	x:=H(0:𝔹);
	y:=H(0:𝔹);
	def f()=>x;
	g:=dup(f);
	forget(H(y)=0);
	return (f(),g());
}
+/
/+
def main(){
	x:=H(0:𝔹);
	k:=H(0:𝔹);
	f:=()=>x;
	g:=dup(f);
	(x,y):=(f(),g());
	forget(y=x);
	forget(H(x)=0);
	k:=H(k);
	return k; // should be 0
}
+/
/+
def f(const x:B){
	return ()=>x; // error. TODO?
}
def main(){
	a:=H(0:𝔹);
	x:=f(a)();
	forget(a=x);
	return H(x);
}
+/
/+
def f(const x:𝔹){
	y:=H(x);
	return (x,y);
}
def main(){
	return f(0:𝔹);
}
+/
/+
def main(){
	a:=H(0:𝔹);
	b:=1:𝔹;
	c:=H(0:𝔹);
	measure(H(0:𝔹));
	x:=if c then dup(a) else b; // ok
	return (c,x,a);
}
+/
/+
def main(){
	a:=H(0:𝔹); // error
	b:=1:𝔹;
	c:=H(0:𝔹);
	x:=if c then a else b;
	return (c,x,a,b); // error
}
+/
/+def main(){
	a:=0:𝔹;
	b:=1:𝔹;
	c:=H(0:𝔹);
	x:=dup(if c then a else b);
	return (c,x,a,b);
}
+/
/+
def main(){
	a:=0:𝔹;
	b:=1:𝔹;
	c:=H(0:𝔹);
	x:=if c then a else b;
	return (c,x);
}
+/
/+
def main()qfree{
	f:=λ(a:int[2],b:int[2]). (a,b);
	return reverse(H);
}
+/
/+
def main(){
	n:=3;
	n+=1;
	a:=vector(n,0:𝔹); // ok
	n+=1; // error
}
+/
/+
def floor(n:!ℕ)⇒2*n;

def main(){
	x:=0:int[floor(3)];
	return x;
}
+/
/+
def fun[n:!𝔹](x:𝔹^n)⇒x;

def main(){
	x:=fun(0:𝔹,1:𝔹); // error
	y:=fun(); // TODO?
	z:=fun(0:𝔹,); // TODO?
	return (x,y,z);
}
+/
/+import codeforces.summer18.contest.e1;
def main(){
	b:=measure(H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹));
	def makeF[n:!ℕ](b:!𝔹^n)(x:𝔹^n)lifted{
		r:=0:𝔹;
		for k in [0..5){
			r⊕=b[k]&x[k];
		}
		return r;
	};
	f:=makeF(b);
	g:=makeF(solve(f));
	return (f,g);
}
+/
/+
import codeforces.summer18.contest.e1;
def main(){
	b:=measure(H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹));
	f:=(x:𝔹^5)lifted{
		r:=0:𝔹;
		for k in [0..5){
			r⊕=b[k]&x[k];
		}
		return r;
	};
	assert(solve(f)==b);
	return b;
}
+/
/+
import codeforces.summer18.contest.d3;
def main(){
	x:=(H(0:𝔹),H(0:𝔹),H(0:𝔹));
	r:=solve(x);
	return (x,r);
}
+/
/+
import codeforces.summer18.contest.d2;
def main(){
	x:=(H(0:𝔹),H(0:𝔹));
	r:=solve(x,(false,true));
	return (x,r);
}
+/
/+
import codeforces.summer18.contest.d1;
def main(){
	x:=(H(0:𝔹),H(0:𝔹));
	r:=solve(x,(true,true));
	return (x,r);
}
+/
/+
import codeforces.summer18.contest.c2;
def main(){
	r:=measure(H(0:𝔹));
	if r==0{
		x:=0:𝔹;
	}else{
		x:=H(0:𝔹);
	}
	s:=solve(x);
	assert(s=-1||s=r);
	return s;
}
+/
/+
import codeforces.summer18.contest.c1;
def main(){
	r:=measure(H(0:𝔹));
	if r==0{
		x:=0:𝔹;
	}else{
		x:=H(0:𝔹);
	}
	return solve(x)==r;
}
+/
/+
import codeforces.summer18.contest.b4;
def main(){
	for i in [0:!𝔹..1:!𝔹]{
		for j in [0:!𝔹..1:!𝔹]{
			qs:=(H(i:𝔹),H(j:𝔹));
			if qs[0]||qs[1]{ phase(π); }
			assert(solve(qs)==((i,j) as !uint[2]));
		}
	}
}
+/
/+
import codeforces.summer18.contest.b3;
def main(){
	results:=[]:!ℤ[];
	for i in [0:!𝔹..1:!𝔹]{
		for j in [0:!𝔹..1:!𝔹]{
			def prepare()⇒(H(i),H(j));
			assert(solve(prepare())==((j,i) as !uint[2]));
			results~=[solve(prepare())];
			results~=[((j,i) as !uint[2]) as !ℕ];
			assert(results[results.length-2]==results[results.length-1]);
		}
	}
	return results;
}
+/
/+
import codeforces.summer18.contest.b2;
def main(){
	x:=H(0:𝔹);
	ghz:=vector(3,x);
	forget(x=ghz[0]);
	w:=vector(4,0:𝔹);
	i:=(H(0:𝔹),H(0:𝔹)) as uint[2];
	w[i]=1:𝔹;
	forget(i=λ(w:𝔹^4)lifted{
		for i in [0..3){ if w[i]==1{ return i as uint[2]; } }
		return 3:uint[2];
	}(w));
	assert((solve(ghz),solve(w))==(0,1));
}
+/
/+
import codeforces.summer18.contest.b1;
def main(){
	return solve(false,true,false);
	//return solve(H(false),false,false); // TODO!
}
+/
/+
import codeforces.summer18.contest.a4;

def main(){
	return solve(2);
}
+/
/+
def main(){
	i:=H(0:𝔹);
	x:=array(2,0:𝔹);
	x[0] = if i==0 then 1:𝔹 else 0:𝔹;
	k:=if x[0] then 0:𝔹 else 1:𝔹;
	return (x,i,k);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	return ((measure(0)+1)+(x as int[3]),x); // TODO
}
+/
/+
def main(){
	x:=array(2,0:𝔹);
	i:=H(0:𝔹);
	x[i]=1:𝔹;
	forget(i=x[1]);
	return x;
}
+/
/+
def main(){
	x:=array(2,0:uint[2]);
	i:=H(0:𝔹);
	j:=H(0:𝔹);
	x[i][j]=1:𝔹;
	forget(i=if x[0][0]|x[0][1] then 0:𝔹 else 1:𝔹);
	forget(j=if x[0][0]|x[1][0] then 0:𝔹 else 1:𝔹);
	return x;
}
+/
/+
def main(){
	x:=array(2,vector(2,0:𝔹));
	i:=H(0:𝔹);
	j:=H(0:𝔹);
	x[i][j]=1:𝔹;
	forget(i=if x[0][0]|x[0][1] then 0:𝔹 else 1:𝔹);
	forget(j=if x[0][0]|x[1][0] then 0:𝔹 else 1:𝔹);
	return x;
}
+/

/+
def foo(const x:𝔹):!ℕ{
	return if x then 0 else 1; // error
}
+/
/+
def solve(f: 𝔹^2 !→lifted 𝔹){
	x:=vector(1,0:!𝔹);
	return x==vector(1,0:𝔹);
}
def main(){
	g := λ[n:!ℕ](x: 𝔹^n)lifted⇒0:𝔹;
	f := g[2];
	x:=solve(f);
	y:=solve(f);
	return (x,y);
}
+/
/+
def solve(f: 𝔹^0 !→lifted 𝔹){
	x:=vector(1,0:𝔹);
	return measure(x)==vector(1,0:𝔹);
}
def main(){
	g := λ[n:!ℕ](x: 𝔹^n)lifted⇒0:𝔹;
	x:=solve(g[0]);
	return x;
}
+/
/+
def main(){
	x:=(1,2);
	//y:=H(0:𝔹) as int[2]; // TODO
	yb:=H(0:𝔹);
	y:=if yb then 1:int[2] else 0:int[2];
	forget(yb=if y==1 then 1:𝔹 else 0:𝔹);
	x[y]=3; // error
	return y;
}
+/
/+
def main(){
	x:=0:𝔹;
	forget(x=0);
}
+/
/+
def main(){
	n:=measure(H(0:𝔹)):!ℕ;
	def foo(){
		x:=0:int[n];
		return x;
	}
	y:=0:int[n];
	n=3; // error
	x:=measure(foo()) as !ℤ;
	return x;
}
+/
/+import codeforces.summer18.contest.a3; // TODO: make compile without type annotation
def main(){
	return solve((false,true,true),(false,true,false));
}
+/
/+
def main(){
	a:=[[0:𝔹],[1:𝔹,H(0:𝔹)]];
	x:=H(0:𝔹);
	r:=a[x]; // error
	return (r,a,x);
}
+/
/+
def main(){
	x:=H(false);
	if x{
		y:=2:int[3];
	}else{
		y:=3:int[3];
	}
	forget(x=y==2);
	return y;
}
+/
/+
def main(){
	bits:=(true,false,true);
	x:=H(0:𝔹);
	if x { qs₁ := bits:𝔹^3; }else{ qs₁ := vector(3,0:𝔹); }
	qs₂ := if x then bits else vector(3,0:𝔹);
	forget(x=qs₁[0]);
	forget(qs₂=qs₁);
	return qs₁;
}
+/
/+
def main(){
	x:=2:!uint[10];
	y:=dup(x);
	(x[0],x[1])=(x[1],x[0]);
	return x;
}
+/
/+
def main(){
	x:=2:uint[10];
	(x[0],x[1]):=(x[1],x[0]);
	return x;
}
+/
/+
def main(){
	x:=0:!uint[10];
	x[5]=1:!𝔹;
	return x;
}
+/
/+
def main(){
	(x,a):=(0:𝔹,[1:𝔹]);
	(x,a[0]):=(a[0],x);
	return (x,a);
}
+/
/+
def main(){
	return H(reverse(reverse(H))(0:𝔹));
}
+/
/+
def main(){
	x:=vector(1,0:int[1]);
	x[0][0]:=H(x[0][0]);
	return x;
}
+/
/+
def solve[n:!ℕ](bits: !𝔹^n){
	x:=H(0:𝔹);
	qs := if x then bits else (0:int[n]) as 𝔹^n;
	forget(x=qs[0]);
	return qs;
}
// import codeforces.summer18.contest.a2;

def main(){
	return solve((1,0,0,1,0,1):!𝔹^6);
}
+/
/+
import codeforces.summer18.contest.a1;
def main(){
	return solve(3);
}
+/
/+
def main(){
	x:=0:int[1];
	x[0]:=H(x[0]);
	x[0]:=H(x[0]);
	return x;
}
+/
/+
def main(){
	x:=[]:𝔹[];
	y:=H(0:𝔹);
	x~=[y];
	x[0]:=H(x[0]);
	return x;
}
+/
/+
def main(){
	x:=vector(1,0:𝔹);
	x[0] := H(x[0]);
	x[0] := H(x[0]);
	return x;
}
+/
/+
def array2vec[n:!ℕ][τ](a: τ[])qfree:τ^n{ // TODO
	assert(a.length==n);
	if n==0{ return (); } // TODO
	return array2vec[n div 2](a[0..n div 2])~array2vec[(n+1) div 2](a[n div 2..n]); // TODO
}
+/
/+
def main(){
	assert(1:!𝔹);
}
+/
/+
def main(){
	x:=dup((vector(3,1:𝔹) as int[3]) as 𝔹^3);
	return x;
}
+/
/+
def main(){
	x:=(vector(3,1:𝔹) as int[3]) as 𝔹^3;
	return x;
}
+/
/+
def main(){
	x:=((vector(3,1:𝔹) as int[3]) as 𝔹^3):𝔹[];
	return x;
}
+/
/+
def main(){
	x:=(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16):int[4]^16;
	return x;
}
+/
/+
def main(){
	//x:=2:!int[2];
	//y:=x:!ℤ;
	x:=(0:int[3]);
	x[1]:=H(x[1]);
	y:=x as 𝔹^3;
	return y;
}
+/
/+
def main(){
	x:=-3:int[3];
	x+=3;
	return x;
}
+/
/+
def main(){
	x:=0:int[2];
	y:=0:int[3];
	z:=x+y; // error
}
+/
/+
def f(const x:𝔹)lifted⇒dup(x);

def main(){
	y:=f(measure(H(0:𝔹)));
	//__show(__query("dep",y));
}
+/
/+
def foo(const x:𝔹){
	y:=0:𝔹;
	z:=1:𝔹;
	if x{
		return y;
	}else{
		return z;
	}
}

def main(){
	return foo(1:𝔹);
}
+/
/+
def main(){
	x:=0:𝔹;
	y:=0:𝔹;
	while(measure(H(0:𝔹))){ // error
		x=H(y);
	}
	return x;
}
+/
/+def main(){
	x:=H(0:𝔹);
	y:=dup(x);
	while(measure(H(0:𝔹))){ // error
		forget(y);
	}
	return H(x);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	y:=dup(x);
	while(measure(x)){
		forget(y=true);
		x:=H(0:𝔹);
		y:=dup(x);
	}
	return y;
}
+/
/+
def main(){
	x:=H(0:𝔹);
	while(measure(H(0:𝔹))){
		y:=dup(x);
	}
	return H(x);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	if x{
		y:=dup(x);
	}else{
		z:=dup(x);
	}
	return H(x);
}
+/
/+def main(){
	x:=H(0:𝔹);
	y:=dup(x);
	z:=measure(H(0:𝔹));
	if z{
		forget(y=dup(x));
	}
	return (z,H(x));
}
+/
/+
def main(){
	x:=H(0:𝔹);
	y:=0:𝔹;
	return (if x then y else H(y), x);
}+/
/+
def main(){
	x:=H(0:𝔹);
	for i in [0..10){
		y:=dup(x);
	}
	return x;
}
+/
/+def main(){
	x:=H(0:𝔹);
	repeat 10{
		y:=dup(x);
	}
	return H(x);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	if true{
		y:=dup(x);
		//forget(y);
	}
	return H(x);
}
+/
/+def main(){
	x:=H(0:𝔹);
	if true{
		y:=dup(x);
		//forget(y=dup(x));
	}
	r:=H(x);
	return r;
}+/
/+
def main(){
	x:=0:𝔹;
	if x{ x:=X(x); } // error
}
+/
/+
def foo[n:!ℕ](const a:int[n],b:int[n]){
	b+=a;
	return b;
}
def bar[n:!ℕ](a:int[n]){
	foo(a,a); // error
	return a;
}
+/
/+
def add[n:!ℕ](a:int[n],b:int[n]){
	return (a+b,a,b); // ok
}
+/
/+
def main(){
	x:=H(0:𝔹);
	y:=dup(x);
	x⊕=x;
	return (x,y);
}
+/
/+
def main(){
	a:=array(2,[]:𝔹[]);
	x:=measure(H(0:𝔹));
	a[x]~=[0:𝔹];// TODO
	return a;
}
+/
/+
def main(){
	x:=[H(0:𝔹)];
	y:=dup(x);
	return (x,y);
}
+/
/+
def main(){
	x:=[]:𝔹[];
	x:=x~[H(false)];
	y:=dup(x)~[H(false)];
	/*x~=[H(0:𝔹)];
	y:=dup(x);
	y~=[H(0:𝔹)];*/
	return (x,y);
}
+/
/+
def main(){
	x := 0: int[32];
	a := []: 𝔹[];
	for i in [0..10){ a~=[H(false)]; }
	for i in [0..10){ x+=a[i]; }
	x:=measure(x);
	return a;
}
+/
/+
def main(){
	f:=(x:𝔹)qfree⇒ x;
	x:=H(0:𝔹);
	y:=dup(x);
	z:=f(y);
	forget(z);
	y:=dup(x);
	z:=dup(f(y));
	forget(z);
	a:=0:!𝔹;
	b:=f(a);
	b=a;
	return x;
}
+/
/+
def solve(){
	(q₀,q₁):=(1:𝔹,1:𝔹);
	while measure(q₀&q₁){
		measure(q₀,q₁);
		(q₀,q₁):=(H(0:𝔹),H(0:𝔹));
	}
	return (q₀,q₁);
}
+/
/+
def main(){
	φ:=2*asin(0.5);
	return rotY(φ,0:𝔹);
}
+/
/+def main(){
	x:=H(0:𝔹);
	y:=dup(x);
	y=0:𝔹;
	return H(x);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	if true{
		y:=dup(x);
	}
	return H(x); // TODO: ∣0⟩
}
+/
/+def main(n:!ℕ){
	qs:=vector(n,vector(n,0:𝔹));
	def f[a](x:a)⇒x;
	for i in [0..n){
		for j in [0..n){
			(qs[i],qs[j]):=(qs[j],qs[i]);
		}
	}
}
+/
/+
def solve(n:!ℕ){
	qs:=vector(n,0:𝔹);
	for i in [0..n){ qs[i]:=H(qs[i]); }
	return qs;
}
+/
/+
def main(){
	x:=H(0:𝔹);
	y:=dup(x);
	z:=dup(y);
	forget((y,z)=(x,x));
	y:=dup(x);
	z:=dup(y);
	forget(y,z);
	forget(H(x)=0:𝔹);
}
+/
/+
def main(){
	f:=[a]⇒reverse(dup[a]);
	f=3;
}
+/
/+
def main(){
	def id(x:𝔹)lifted⇒dup(x);
	x:=H(0:𝔹);
	id(x);
	x:=H(x);
	return x;
}
+/
/+
def main()qfree{
	def foo(x:𝔹,const y:𝔹)qfree⇒x;
	return reverse(foo)(0:𝔹,0:𝔹);
}
+/
/+import grover;
def main()⇒grover((x:uint[6])lifted⇒x==42);
+/
/+def main(){
	return 2 sub 1;
}+/
/+
import conv;
def main(){
	x:=vector(3,0:𝔹);
	for i in [0..3){ x[i]:=H(x[i]); }
	for i in [0..round(π/4*sqrt(2^3))){
		if ([n:!ℕ]⇒reverse(toVecU[n]))(dup(x))==5{ phase(π); } // TODO
		for k in [0..3){ x[k]:=H(x[k]); }
		if ([n:!ℕ]⇒reverse(toVecU[n]))(dup(x))==0{ phase(π); } // TODO
		for k in [0..3){ x[k]:=H(x[k]); }
	}
	return measure(toUint(x));
}
+/
/+
import conv;
def main(){
	x:=vector(3,0:𝔹);
	for i in [0..3){ x[i]:=H(x[i]); }
	for i in [0..round(π/4*sqrt(2^3))){
		if toUint(dup(x))==5{ phase(π); }
		for k in [0..3){ x[k]:=H(x[k]); }
		if toUint(dup(x))==0{ phase(π); }
		for k in [0..3){ x[k]:=H(x[k]); }
	}
	return measure(toUint(x));
}
+/
/+
def main(){
	x:=0:uint[3];
	for i in [0..3){ x[i]:=H(x[i]); }
	for i in [0..floor(π/4*sqrt(2^3))){
		if x==5{ phase(π); }
		for k in [0..3){ x[k]:=H(x[k]); }
		if x!=0{ phase(π); }
		for k in [0..3){ x[k]:=H(x[k]); }
	}
	return measure(x)==5;
}
+/
/+
def main(){
	x:=H(0:𝔹);
	def f(g: 𝔹→qfree 𝔹)qfree{
		return g(x);
	}
	return H(f((x:𝔹)qfree⇒x));
}
+/
/+
def id[a](x:a)qfree⇒x;

def main(){
	//x:=([a]qfree⇒reverse(id[a]))(id);
	//f:=id;
	y:=0:𝔹;
	x:=id(y);
	//__show(__query("dep",x));
}
+/
/+
def uniform_entangle[n:!ℕ](bits:(!𝔹^n)^4)mfree{
    anc:=0:int[2];
    for j in [0..2){ anc[j]:=H(anc[j]); }
	qs:=vector(n,false:𝔹);

    for i in [0..n-1] {
        for a in [0..3] {
            if anc == a && bits[a][i] {
                qs[i] := X(qs[i]);
            }
        }            
    }
    return (anc, qs);
}

def rev_entangle[n:!ℕ](bits:(!𝔹^n)^4, r:int[2]×𝔹^n)mfree{
	(anc,qs) := r;
    for i in [n - 1..-1..0]{
        for a in [3..-1..0]{
            if anc = a && bits[a][i] {
                qs[i] := X(qs[i]);
            }
        }
    }
    forget(qs=vector[𝔹](n,0: 𝔹));
    for j in (2..-1..0]{
        anc[j] := H(anc[j]);
    }
    forget(anc=0: int[2]);
    return ();
}

def solve[n:!ℕ](bits:(!𝔹^n)^4) {
    (anc, qs) := uniform_entangle(bits);
    //result := dup(qs);
    reverse(uniform_entangle[n])(bits, (anc, qs));
	//rev_entangle(bits, (anc, qs));
    //return result;
}

def main(){
	return solve(((0,0,0),(1,0,0),(0,1,0),(0,0,1)):!(𝔹^3)^4);
}
+/
/+
def solve[n:!ℕ](bits:(!𝔹^n)^4){
    anc:=0:uint[2];
    for j in [0..2){ anc[j]:=H(anc[j]); }
    qs:=(bits:(𝔹^n)^4)[anc];
	for j in [0..3] {
		if qs==bits[j]{
			anc⊕=j;
		}
	}
	forget(anc=0:uint[2]);
    return qs;
}
def main()⇒solve(((0,0,0),(1,0,0),(0,1,0),(0,0,1)):!(𝔹^3)^4);
+/
/+
def main(){
    anc:=0:int[1];
    for j in [0..1){ anc[j]:=H(anc[j]); }
	for j in [0..1){ anc[j]:=H(anc[j]); }
    return forget(anc=0: int[1]);
}
+/
/+
def main(){
	/+x:=0:!int[3];
	x[0]=!x[0];
	x[1]=1:!𝔹;+/
	y:=0:int[3];
	//y[0]:=H(y[0]);
	y[0]=1:𝔹;
	//return (x,y);
	return y;
}
+/
/+
def solve[n:!ℕ](f: 𝔹^n !→lifted 𝔹){
	x:=0:int[n];
	for i in [0..n){ x[i] := H(x[i]); }
	if f(x as 𝔹^n){ phase(π); }
	for i in [0..n){ x[i] := H(x[i]); }
	return measure(x)==0;
}
//import codeforces.summer18.warmup.i;
def main(){
	f := λ[n:!ℕ](x: 𝔹^n)lifted{
		r:=0:𝔹;
		for i in [0..n){
			r⊕=x[i];
		}
		return r;
	};
	g := λ[n:!ℕ](x: 𝔹^n)lifted⇒0:𝔹;
	x:=solve(f[1]);
	y:=solve(g[1]);
	return (x,y);
}
+/
/+
def solve[n:!ℕ](f: 𝔹^n !→lifted 𝔹){
	x:=vector(n,0:𝔹);
	for i in [0..n){ x[i] := H(x[i]); }
	if f(x){ phase(π); }
	for i in [0..n){ x[i] := H(x[i]); }
	return measure(x)==vector(n,0:!𝔹);
}
//import codeforces.summer18.warmup.i;
def main(){
	f := λ[n:!ℕ](x: 𝔹^n)lifted{
		r:=0:𝔹;
		for i in [0..n){
			r⊕=x[i];
		}
		return r;
	};
	g := λ[n:!ℕ](x: 𝔹^n)lifted⇒0:𝔹;
	x:=solve(f[1]);
	y:=solve(g[1]);
	return (x,y);
}
+/
/+def solve(f: 𝟙 !→ 𝟙){
	return (0:!𝔹)==(0:𝔹);
}
def main(){
	g := λ()()⇒();
	x := solve(g());
	y := solve(g());
	return (x,y);
}
+/
/+
def main():!𝔹×!𝔹{
	a:=vector(1,0:!𝔹);
	x:=a==vector(1,0:!𝔹);
	b:=vector(1,0:!𝔹);
	y:=b==vector(1,0:!𝔹);
	return (x,y);
}
+/
/+
def solve(f: 𝔹^1 !→lifted 𝔹){
	x:=vector(1,0:!𝔹);
	return x==vector(1,0:𝔹);
}
def main(){
	g := λ[n:!ℕ](x: 𝔹^n)lifted⇒0:𝔹;
	x := solve(g[1]);
	y := solve(g[1]);
	return (x,y);
}
+/
/+
def main(){
	n:=10;
	y:=measure(H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹),H(0:𝔹));
	x:=vector(10,0:𝔹);
	for i in [0..n){ x[i]:=H(x[i]); }
	r := 0:𝔹;
	for i in [0..n){ r⊕=x[i]&y[i]; }
	if r { phase(π); }
	forget(r);
	for i in [0..n){ x[i]:=H(x[i]); }
	assert(measure(x)==y);
}
+/
/+
def main(){
	n:=4;
	applyPhase:=measure(H(0:𝔹));
	x:=vector(4,0:𝔹);
	for i in [0..n){ x[i]:=H(x[i]); }
	r := 0:𝔹;
	for i in [0..n){ r⊕=x[i]; }
	if r&&applyPhase { phase(π); }
	forget(r);
	for i in [0..n){ x[i]:=H(x[i]); }
	return (applyPhase,measure(x)==vector(4,0:!𝔹)); // TODO: correct type for vectors and tuples
}+/

/+
def main(){
	x:=(0,1,1,0):𝔹^4;
	i:=0:int[2];
	i[0]:=H(i[0]); // TODO
	i[1]:=H(i[1]);
	r:=x[i];
	return (x,r,i);
}
+/
/+import codeforces.summer18.warmup.h;
def main(){
	x := (1,0,1,0,1):𝔹^5;
	r := solve(x);
	return (x,r);
}
+/
/+
import codeforces.summer18.warmup.g;
def main(){
	x:=(0,0,1,0,1):𝔹^5;
	return solve(x,3);
}
+/
/+
def main(){
	x:=(0,1,1,0):𝔹^4;
	x[0]:=H(x[0]);
	return x;
}
+/
/+
def main(){
	x:=(0,1,1,0):𝔹^4;
	a:=0:𝔹;
	(a,x[0]):=(x[0],a);
	a:=H(a);
	(a,x[0]):=(x[0],a);
	forget(a=(0:𝔹));
	return x;
}
+/
/+
def main(){
	x:=(0,1,1,0):𝔹^4;
	x[0]=1:𝔹;
	return x;
}
+/

/+
def id[τ:*](const x:τ)lifted⇒dup(x);

def main(){
	return id(0:𝔹);
}
+/
/+
def sum[n:!ℕ](const a:int[32]^n)lifted{
	r:=0:int[32];
	for i in [0..n){
		r+=a[i];
	}
	return r;
}

def add(n:!ℕ,const x:int[32])lifted{
	r:=0:int[32];
	for i in [0..n){
		r+=x;
	}
	return r;
}

def main(){
	b := H(0:𝔹);
	a := vector(10,b as int[32]); // TODO
	r:=add(10,sum(a));
	return (a,b,r);
}
+/
/+def main(){
	a := 0:𝔹;
	b:=dup(dup(dup(dup(dup(a))))); // TODO: use only two variables
	measure(a,b);
	x:=0;
}
+/
/+
def sum(const a:int[32])lifted{
	//r:=dup(a);
	r:=0:int[32];
	r+=a;
	return r;
}

def main(){
	b := H(0:𝔹);
	a := dup(b as int[32]); // TODO
    r:=sum(sum(sum(a)));
	return measure(a,b,r);
}
+/
/+
def main(){
	b:=H(0:𝔹);
	a:=dup(b);
	return (a,b);
}
+/
/+
def main(){
	b := H(0:𝔹);
	x := b as int[32]; // TODO
	return x;
}
+/
/+
def main(){
	b:=H(0:𝔹);
	a:=dup(b as int[32]); // TODO
	measure(a,b);
	x:=0;
}
+/
/+
def sum(const a:int[32])lifted{
	//r:=0:int[32];
	//r+=a;
	r:=dup(a);
	return r;
}

def main(){
	b := H(0:𝔹);
	a := dup(b as int[32]); // TODO
	r:=sum(a);
	measure(a,b,r);
	x:=0;
}
+/
/+
def f(t:int[32]){
	return t;
}

def main(){
	a := 0:int[32];
	b := 1:int[32];
	x := f(a+b);
	forget(a=(0:int[32]));
	forget(b=(1:int[32]));
	return x;
}
+/
/+
def f()lifted⇒0:int[32];
def main(){
	y:=f()+f();
	return (y);
}
+/
/+
def main(){
	x := H(0:𝔹);
	f := dup(()⇒x); // error
}
+/
//def f[a,b,c](x:a,y:b,z:c)⇒(x,y,z);
/+
def geom(){
	if measure(H(0:𝔹)){ return 0; }
	return 1+geom();
}

def main(){
	return geom();
}
+/
/+
def main(){
	x:=0;
	forget(x);
	return x; // TODO: error?
}
+/
/+
def main(){
	x:=H(0:𝔹);
	z:=H(0:𝔹);
	fy₁:=lambda(const z:𝔹)lifted⇒dup(z);
	fy₂:=lambda(const z:𝔹)lifted⇒!z;
	fy₃:=lambda(const x:𝔹,const z:𝔹)lifted⇒if x then fy₁(z) else fy₂(z);
	if x{
		y:=dup(z);
	}else{
		y:=!z;
	}
	//y:=if x then dup(z) else !z;
	forget(y=fy₃(x,z));
	return (x,z);
}
+/
/+
def main(){
	x:=H(0:𝔹);
	if true{
		y:=dup(x);
		forget(y);
	}
	x:=H(x);
	return x;
}
+/
/+
def main(){
	x:=H(0:𝔹);
	def f(x:𝔹)⇒H(x);
	y:=x;
	y:=f(y);
	return y;
}
+/
/+
def main(){
	x:=1:𝔹;
	if x{
		def f[a,b,c](x:a,y:b,z:c)⇒(x,y,z);
		return (1,2,3);
	}else{
		return (2,3,4);
	}
}
+/
/+def main(){
	x:=vector(3,0:𝔹);
	//x[0]:=H(x[0]);
	return x[1];
}
+/

/+
import codeforces.summer18.warmup.f;
def main(){
	x:=vector(3,0:𝔹);
	x[1]:=X(x[1]);
	bits:=vector(2,vector(3,0:!𝔹));
	bits[0][1]=1:!𝔹;
	r:=solve(x,bits);
	measure(x);
	return r;
	//return solve((0,1,0):𝔹^3,((0,1,0),(1,0,1)):(𝔹^3)^2); // TODO!
}
+/
/+
import codeforces.summer18.warmup.d; 

def main(){
	assert(solve(H(0:𝔹))==1);
	assert(solve(H(1:𝔹))==-1);
}
+/
/+
def fib(f: !ℕ !→ !ℕ)(n:!ℕ){
	if n<=1{ return n; }
	return f(n sub 1)+f(n sub 2);
}

def fix[a](f: (a!→a)!→(a!→a)){
	def g(x:a):a⇒f(g)(x); // TODO
	return g;
}
def main(){
	return fix(fib)(10);
}
+/
/+
def fib(n:!ℕ):!ℕ{
	if n<=1{ return n; }
	return fib(n sub 1)+fib(n sub 2);
}
def main(){
	return fib(10);
}
+/

/+def main(){
	//x := [1,2,3:!ℝ];
	x := vector(3,1);
	y := x;
	r := 0:!ℝ;
	for i in [0..3){
		r+=y[i];
	}
	return r;
}
+/
/+
def add(x:!ℝ,y:!ℝ){
	return x+y;
}

def main(){
	//x := H(0:𝔹);
	//return measure(x);
	x:=1;
	y:=[2.2];
	//return add(1,2);
	return add(x,y[0..1][0]);
}
+/
/+
def todo[n:!ℕ](const x:uint[n]){
	t := (0,0):(uint[n]×uint[n]);
	t[0] = dup(x):uint[n];
	__show(__query("dep",t)); // {x}
	return t;
}
+/
/+def sum[n:!ℕ](const x:uint[n][],const y:uint[n])mfree:uint[n]{
	s := dup(y): uint[n];
	for i in [0..x.length){
		s = s + x[i];
	}
	__show(__query("dep",s));
	return s;
}
+/
/+
def bad[n:!ℕ](x:uint[n])mfree{
	s := x;
	s -= s; // error
	return s;
}
+/
/+
def bad[n:!ℕ](x:uint[n])mfree{
	s := 0: uint[n];
	s = x;
	s = 0; // error
	return s;
}
+/
/+
def f(const a:𝔹[],x:𝔹,y:!𝔹):𝔹{
	if y{
		x := H(x);
	}
	return x;
}
def main(n:!ℕ){
	a := array(n,0:𝔹);
	a[0] := f(a,a[0],true); // error
	return a;
}
+/

/+
def main[n:!ℕ](a: 𝔹[], i: int[n]){
	x := a[i];
	forget(x); // TODO: don't require this
	return (a,i);
}
+/
/+def f[a](const b: a[])[b](const c: b[]){

}+/
/+
def f[a:*,n:!ℕ]: Π(const b: a^n). 1{
	return (const b: a^n){

	}
}

A → B

Π(_: A). B

(const A) → B

Π(const _: A). B.

def grover[n](f: Π(const x: uint[n]). 𝔹){

}

def main(){
	f(x);
	x := 2;
	y := []: ℝ^x;
}
+/

/+
def f(const x:𝔹)lifted{
	phase(π); // error
	return ();
}

def main(){
	x := f(0:𝔹);
	forget(x=f(0:𝔹));
}
+/
/+def abc(){
    b := f(cand);
    if b{
        phase(π);
    }
    forget(b=f(cand));
}
+/
/+
def main(){
	//x := 0:!ℤ;
//repeat 10 { x -= 2; }
//return 2.0*π*2^(-1);
x := 2.0^-1;
x = "";
}
+/
	/+
	def main(){
		x := 1:𝔹;
		if x {
			return 1:𝔹; // TODO: this should be an error!
		}
		return x;
	}
+/
	/+
	def main(x:𝔹^5){
		//x := 0:int[5];
		return x[x:int[5]];
	}
+/
	/+
	def main(){
		x := false:𝔹;
		if x{
			z := H(false):𝔹;
		}
	}
+/
	/+
	def flipWith_Array[l:!N](const p:𝔹^l, q:𝔹^l) mfree : 𝔹^l {
		for i in[0..l) {
			if p[i] { q[i] := X(q[i]); }
		}
		return q;
	}

def a8_FetchT_Array[n:!N, rr:!N, r:!N](const i:int[r], const tt:int[n]^rr) : int[n] {
	ttd := 0:int[n];
	for j in [0..rr) {
		if i == j {
			ttd := flipWith_Array(tt[j]:B^n, ttd:B^n):int[n];
		}	}
	return ttd;
}
+/

/+def flipWith_Array[l:!N](const p:𝔹^l, q:𝔹^l)mfree : 𝔹^l {
	for i in[0..l) {
		if p[i] { q[i] := X(q[i]); }
	}
	return q;
}

def a8_FetchT_Array[n:!N, rr:!N, r:!N](const i:int[r], const tt:int[n]^rr) : int[n] {
	ttd := 0:int[n];
	for j in [0..rr) {
		if i == j {
			ttd := flipWith_Array(tt[j]:B^n, ttd:B^n):int[n];
	}	}
	return ttd;
}
+/

/+
def a12_FetchStoreE[rr:!N,r:!N](const i:int[r], qs: (𝔹^rr)^rr,
	ps: 𝔹^rr) : (𝔹^rr)^rr x 𝔹^rr {

	for j in [0..rr) {
		for l in [0..j) {
			if i == j { (qs[j][l], ps[l]) := (ps[l], qs[j][l]); }
			if i == l { (qs[j][l], ps[j]) := (ps[j], qs[j][l]); }
		}
	}
	return (qs, ps);
}
+/
/+
def main(){
	y := 0:𝔹;
	x := dup(y);
	//forget(y=measure(x)+1);
	z := measure(H(false));
	//forget(y=x);
	//return x;
}
+/

/+
def main(x: 𝔹){
	y := dup(x);
	x := H(x);
	return x;
}
+/
/+def main(x: 𝔹)lifted{
	y := dup(x); // TODO: ok
	return x;
}
+/


/+def Node[k:!ℕ]lifted ⇒ int[k];

def edgeOracle_spec[k:!ℕ]lifted ⇒ ((const int[k] x const int[k] x 𝔹) !-> 𝔹);

def QWTFP_spec[k:!ℕ]lifted ⇒ (!N x !N x edgeOracle_spec[k]);

def a5_SETUP[k:!ℕ](oracle:!QWTFP_spec[k], const tt:int[2^oracle[1]]) : (𝔹^(2^oracle[1]))^(2^oracle[1]) {
    (n, r, edgeOracle) := oracle;
    rr := 2^r;
    ee := vector(2^oracle[1], vector(2^oracle[1], false:𝔹));

    // Todo: CHECK INDICES!
    for k in [0..2^r) {
        for j in [0..2^r) {
            ee[k][j] := edgeOracle(tt[j], tt[k], ee[k][j]);
    }    }

    return ee;
}
+/
/+
def a4_Hadamard_Array[k:!N](q:𝔹^k) : 𝔹^k {
    for j in [0..k) { q[j] := H(q[j]); }
    return q;
}

def a4_Hadamard_Array_Array[k:!N,l:!N](q:(𝔹^k)^l) : (𝔹^k)^l {
    for i in [0..l) {
        q[i] := a4_Hadamard_Array(q[i]);
    }
    return q;
}

// -------------------------------------------------------------

def a7_Diffuse_Array[k:!N](q:𝔹^k) : 𝔹^k {
    q := a4_Hadamard_Array(q);
    if q == array(k,false) { phase(π); }
    q := a4_Hadamard_Array(q);
	return q;
}

// -------------------------------------------------------------

def flipWith_Array[l:!N](const p: 𝔹^l, q:𝔹^l) : 𝔹^l {
    for i in[0..l) {
        if p[i] { q[i] := X(q[i]); }
    }
    return q;
}
+/


/+def QFT[n:!N]lifted(psi:uint[n]) mfree: uint[n];

def inverse[τ,χ]lifted(f: τ !→ mfree χ)lifted(x:χ)mfree ⇒ reverse(λ(x:τ,const _:𝟙)mfree. f(x))(x,());

def PeriodFinding[n:!N](f:!(uint[n] -> lifted uint[n])):!N{
    cand := 0:uint[n];
    //for k in [0..n) { cand[k] := H(cand[k]); }
    ancilla := f(cand);
	cand := inverse(QFT[n])(cand);
    measure(ancilla);
    return measure(cand):!N;
}
+/
/+
def main(){
	x := 0: !int[100];
	//x[0]⊕=1:𝔹;
	x[1]=1:!𝔹;
}
+/
/+
def main(){
	c := H(false);
	if c{
		//x := H(false);
		y := [dup(c),1,2];
	}else{
		//x := H(true);
		y := [dup(c),2];
	}
	c:=H(c);
	forget(c=false);
	return y;
}
+/
/+
def id[x](a:x):x;

def main(){
	x := id(2);
}
+/
/+
def main[n:!ℕ](x: 𝔹^n){
	//y := x[1];
	y := x;
	y[1] := true;
	return (y);
}
+/

/+
def zero(n:!ℕ):int[n]{
	return 0:int[n];
}+/

/+
def main(){
	x := 0: int[64];
	//y := true : !𝔹;
	y := x+1:ℕ;
	//z := measure(y);
	//forget(x=z-1);
}
+/

/+
def f[k:!ℕ](x: int[k]){
	return x;
}

def main(i: int[32]){
	return f(i);
}
+/


/+
def main(x:ℕ){
	f := λ(a:𝟙,const b:𝟙)mfree. x;
	g := dup(f);
	reverse[𝟙,𝟙,ℕ](f)(g((),()),());
}
+/
/+
def main(x:ℕ){
	y := H(false);
	f := λ(x:ℕ,const _:𝟙)mfree.{
		y := y;
		xpy := x+y;
		forget(x=xpy-y);
		return (xpy,y);
	};
	return reverse[ℕ,𝟙,ℕ×𝔹](f)((x,H(false)),());
}
+/
/+
def main(x:𝔹){
	if x{
		y := H(x);
	}else{
		y := H(X(x));
	}
	return y;
}
+/
/+
def main(x:𝔹){
	if x{
		measure(x);
	}else{
		measure(x);
	}
}
+/
/+
def main(){
	x := reverse;
	x = 2;
}
+/
/+
def f(x: 𝔹, y: !𝔹){
	return x;
}

def main(){
	x := (true:𝔹,false:!𝔹);
	return f(x);
}
+/

/+
def f(const x: 𝔹, const y: 𝔹)lifted{
	a:=(dup(x),1);
	return (dup(x),a);
}
+/
/+
def f(const x: 𝔹)lifted{
	y := x;
	return ()=>y;
}
+/
/+
def f(const x: 𝔹){
	y := x;
	return y;
}
+/
/+
def f(const x: 𝔹){
	f:=()=>x;
	return f;
}
+/
/+
def CNOT(x:𝔹,const y:𝔹){
	return (x,y);
}

def main(){
	k := (false,false): 𝔹×𝔹;
	return CNOT(k);
}
+/
/+
def main(x: 𝔹){
	x := x;
	return (){ x:=x; y:=x+1; forget(x=y-1); return y; }
}
+/

/+def main(const x: 𝔹){
	return x+1;
}
+/
/+def main(const x: 𝔹){
	return ()⇒x+1;
}
+/

/+
def main(const x: 𝔹){
	def f(){ def g()⇒x; return g; }
	return f;
	//return ()=>x;
}
+/

/+
def main(){
	x := false:!𝔹;
	def f(){ return x; }
	y := x;
	return (f(),f());
}
+/
/+
def main(){
	x := false:𝔹;
	f := ()=>x;
	//def f(){ return x; }
	y := x; // error
	//return f;
	return (f,f); // error
}
+/
/+
def main():!(ℕ[]){
	return dup[ℕ[]]([1,2,3]):!ℕ[];
}
+/
/+
def main():!ℕ×!ℕ{
	return dup[ℕ×ℕ](1,2);
}
+/
/+def main():!ℕ{
	return dup[ℕ](1);
}
+/
/+def main(){
	f := lambda(x:ℝ)lifted. { return x; };
	x:=2;
	return f(x);
}
+/
/+def main(x: 𝔹)mfree{
	measure(x);
}
+/

/+def foo()mfree:ℕ{
	n := 0:ℕ;
	if H(false){
		n+=foo();
	}
	return n;
}
+/

/+def main(){

}+/

/+
def main(x: 𝔹,y: 𝔹){
	return H(x)||H(y);
}
+/
/+
def main(x: 𝔹)mfree{
	y := dup(H(x));
	return y;
}
+/
/+def main(x: 𝔹){
	if measure(dup(x)){
		y:=H(x);
	}else{
		y:=H(x);
		//y := H(true);
		//measure(x);
		//forget(x=z);
		//z := H(x);
	}
    return y;
}
+/
/+
def main(x: !𝔹){
	/+f := lambda(i:const ℕ, ee:𝔹[][]) . {
		return (ee, tt);
	};+/
	y := 3;
	return x;
}
+/
/+def main(){
	if !x{

	}
	if !(triTestT == 0 && triTestTw == 0) {
		phase(pi);
	}
}
+/

/+
rbar := 5;

def f(const x:𝔹){
	y := x;
	//if measure(x){ y:=hadamard(y); } // TODO: error
	if x{ y:=hadamard(y); } // TODO: ok
	return y; // TODO: ok
}

def main(){
	a := hadamard(false);
	b := hadamard(false);
	return f(a&&b);
}
+/

/+
//x:=2;

def main(const n: !Int[32],b:!ℤ)lifted:𝟙{
	x := false:𝔹;
	x := H(x):𝔹;
	//y := main : !Int[32]×!𝔹 →lifted 𝟙;
	//y := main : Π(consumed n: Int[32],x: !𝔹). lifted 𝟙;
	//y := main: const Int[32] × !𝔹 →mfree 𝟙;
	m := n: Int[32];
	def foo(f: !(𝔹 → 𝔹)){
		return f: (𝔹 → 𝔹);
	}
	/+y = 2;
	if x{

	}+/
}
+/
