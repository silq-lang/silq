// https://codeforces.com/contest/1116/problem/D4
def solve[n:!ℕ](qs:𝔹^n){
	x~(y,):=qs;
	x:=x as int[n sub 1];
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
	qs:=(x as 𝔹^(n sub 1))~(y,);
	return qs;
}
