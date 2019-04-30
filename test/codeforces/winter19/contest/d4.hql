// https://codeforces.com/contest/1116/problem/D4
def solve[n:!ℕ](qs:𝔹^n){
	x:=(qs:𝔹[])[0..n-1]:int[n sub 1];
	y:=qs[n-1];
	forget(qs=(x:𝔹[])~[y]);
	for i in [0..n-1){
		x[i]:=X(x[i]);
	}
	x+=y;
	for i in [0..n-1){
		if y{ x[i]:=X(x[i]); }
	}
	y:=H(y);
	for i in [0..n-1){
		if y{ x[i]:=X(x[i]); }
	}
	qs:=(x:𝔹[])~[y]:𝔹^n;
	forget(x=(((qs:𝔹[])[0..n-1]):int[n sub 1]));
	forget(y=qs[n-1]);
	return qs;
}
