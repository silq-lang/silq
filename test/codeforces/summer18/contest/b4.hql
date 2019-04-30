// https://codeforces.com/contest/1002/problem/B4
def solve(q₀:𝔹,q₁:𝔹){
	if !q₀&&!q₁{ phase(π); }
	(b₀,b₁):=measure(H(q₀),H(q₁));
	return 2·b₁+b₀;
}
