// https://codeforces.com/contest/1002/problem/D2
def solve[n:!ℕ](x:𝔹^n,b:!𝔹^n)lifted{
	y:=0:𝔹;
	for i in [0..n){
		y⊕=b[i]==x[i];
	}
	return y;
}
