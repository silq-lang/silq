// https://codeforces.com/contest/1116/problem/B1
def toW[n:!ℕ](qs:𝔹^n)mfree:𝔹^n{
	if n==1{ qs[0]:=X(qs[0]); }
	else if n>1{
		θ:=2·asin(1/sqrt(n));
		(head,)~tail:=qs;
		head:=rotY(θ,head);
		if !head { tail := toW(tail); }
		qs:=(head,)~tail;
	}
	return qs;
}

def solve(qs:𝔹^3):!𝔹{
	if qs[1]{ phase(-2·π/3); }
	if qs[2]{ phase(-4·π/3); }
	qs:=reverse(toW[3])(qs);
 	return measure(qs as int[3])!=0;
}
