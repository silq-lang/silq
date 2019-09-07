// https://codeforces.com/contest/1116/problem/D6
def swap[n:!ℕ](a:!𝔹^n,b:!𝔹^n,x:𝔹^n){
	def f(x:𝔹^n)lifted⇒if x==a then b else if x==b then a else dup(x);
	y:=f(x);
	forget(x=f(y));
	return y;
}
def embed2x2[n:!ℕ](i:!ℕ,j:!ℕ,f:𝔹 !→ 𝔹,x:𝔹^n){
	(zero,one):=((0:!uint[n]) as !𝔹^n,(1:!uint[n]) as !𝔹^n);
	(a,b):=((i as !uint[n]) as !𝔹^n,(j as !uint[n]) as !𝔹^n);
	x:=swap(a,zero,x);
	x:=swap(if b!=zero then b else a,one,x);
	x[0]:=f(x[0]);
	x:=swap(if b!=zero then b else a,one,x);
	x:=swap(a,zero,x);
	return x;
}
def solve[n:!ℕ](qs:𝔹^n){
	for i in [0..2^n sub 1){
		qs:=embed2x2(2^n sub 2 sub i,2^n sub 1 sub i,H,qs);
	}
	return qs;
}
