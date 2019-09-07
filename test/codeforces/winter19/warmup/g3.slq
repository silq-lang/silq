// https://codeforces.com/contest/1115/problem/G3
def solve[n:!ℕ](x:𝔹^n)lifted{
	y:=1:𝔹;
	for i in [0..n div 2){
		y&=x[i]==x[n-1-i];
	}
	return y;
}
