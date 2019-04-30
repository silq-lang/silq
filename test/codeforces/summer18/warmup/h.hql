// https://codeforces.com/contest/1001/problem/H
def solve[n:!ℕ](const x:𝔹^n)lifted{
	y := 0:𝔹;
	for i in [0..n){
		y⊕=x[i];
	}
	return y;
}
