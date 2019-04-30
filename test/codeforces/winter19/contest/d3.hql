// https://codeforces.com/contest/1116/problem/D3
def solve[n:!ℕ](qs:𝔹^n){
	x:=0:𝔹;
	(x,qs[0]):=(qs[0],x);
	if x{
		for i in [1..n){
			qs[i]:=X(qs[i]);
		}
	}
	x:=H(x);
	if x{
		for i in [1..n){
			qs[i]:=X(qs[i]);
		}
	}
	(qs[0],x):=(x,qs[0]);
	forget(x=0);
	return qs;
}
