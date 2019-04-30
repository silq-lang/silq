// https://codeforces.com/contest/1002/problem/B3
def solve(q₀:𝔹,q₁:𝔹){
	(b₁,b₀):=measure(H(q₀),H(q₁));
	return 2·b₁+b₀;
}
