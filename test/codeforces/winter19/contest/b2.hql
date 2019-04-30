// https://codeforces.com/contest/1116/problem/B2
def acos(x:!ℝ)lifted:!ℝ;
def sqrt(x:!ℝ)lifted:!ℝ;
def solve(q:𝔹){
	a:=0:𝔹;
	q:=Z(q);
	if q{ a:=H(a); }
	if a{ phase(π/4); }
	q:=X(q);
	if !a{ q:=rotY(q,-2·acos(sqrt(2/3))); }
	q⊕=a;
	if q{ a:=H(a); }
	q⊕=a;
	(r₀,r₁):=(measure(a),measure(q));
	return 2·r₁+r₀;
}
