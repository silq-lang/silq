// https://codeforces.com/contest/1115/problem/G2
def solve[n:!ℕ](x:𝔹^n)lifted{
	y:=0:𝔹;
	for i in [0..n){
		y|=x[i];
	}
	return y;
}
