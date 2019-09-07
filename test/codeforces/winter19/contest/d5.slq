// https://codeforces.com/contest/1116/problem/D5
def solve(qs:𝔹^3){
	x:=qs as int[3];
	x+=2;

	c:=x[2];
	if !c{ x[1]:=H(x[1]); }
	forget(c=x[2]);
	
	c:=x[0]&x[2];
	if c{ x[1]:=X(x[1]); }
	forget(c=(x[0]&x[2]));

	x[0] := H(x[0]);
	x-=2;
	for i in [0..3){ x[i]:=X(x[i]); }
	qs:=x as 𝔹^3;
	return qs;
}

// def solve(qs:𝔹^3){
// 	(x0, x1, x2) := qs;
// 	if x1 { x2 := X(x2); }
// 	if x2 { x0 := X(x0); }
// 	if x0 && x2 { x1 := X(x1); }
// 	if !x2 { x1 := H(x1); }
// 	x0 := H(x0);
// 	if x1 { x2 := X(x2); }
// }
