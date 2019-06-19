// https://codeforces.com/contest/1116/problem/B1
def asin(x:!ℝ)lifted:!ℝ;
def sqrt(x:!ℝ)lifted:!ℝ;
def toW[n:!ℕ]lifted:𝔹^n →mfree 𝔹^n⇒lambda(qs:𝔹^n)mfree:𝔹^n{
	if n==0{ return ((0:int[0]):𝔹[]):𝔹^n; }
	if n==1{ return [1:𝔹]:𝔹^n; }
	θ:=asin(1/sqrt(n));
	head:=qs[0];
	tail:=(qs:𝔹[])[1..n]:𝔹^(n sub 1);
	forget(qs=(([head]~(tail:𝔹[])):𝔹^n));
	head:=rotY(θ,head);
	if !head { tail := toW(tail); }
	result:=([head]~(tail:𝔹[])): 𝔹^n;
	forget(head=result[0]);
	forget(tail=((result:𝔹[])[1..n]:𝔹^(n sub 1)));
	return result;
};

def solve(qs:𝔹^3):ℕ{
	if qs[1]{ phase(-2·π/3); }
	if qs[2]{ phase(-4·π/3); }
	qs:=reverse(toW[3])(qs);
	return measure(qs:int[3])!=0;
}
