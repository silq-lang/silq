// https://codeforces.com/contest/1116/problem/B2
def solve(q:𝔹){
	a:=0:𝔹;
	if q {
		phase(π);
	}
	if q{ a:=H(a); }
	if a{ phase(π/4); }
	q:=X(q);
	if !a{ q:=rotY(-2·acos(sqrt(2/3)),q); }
	q⊕=a;
	if q{ a:=H(a); }
	q⊕=a;
	(r₀,r₁):=measure(a,q);
	return 2·r₁+r₀;
}
