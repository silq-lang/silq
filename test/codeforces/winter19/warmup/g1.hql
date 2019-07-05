// https://codeforces.com/contest/1115/problem/G1
def solve[n:!ℕ](x:𝔹^n)lifted{
	y:=1:𝔹;
	for i in [0..n){
		y&=x[i];
	}
	return y;
}
