// https://codeforces.com/contest/1116/problem/D5
def solve(qs:𝔹^3){
	x:=qs:int[3];
	x+=2;
	c:=x[2];
	if !c{ x[1]:=H(x[1]); }
	forget(c=x[2]);
	c:=x[0]&x[2];
	if c{ x[1]:=X(x[1]); }
	forget(c=(x[0]&x[2]));
	x-=2;
	for i in [0..3){ x[i]:=X(x[i]); }
	qs:=x:𝔹^3;
	return qs;
}
