// https://codeforces.com/contest/1116/problem/C2
def solve[n:!ℕ](x:𝔹^n)lifted{
	y:=0:𝔹;
	for p in [(n+1) div 2..n){
		z := 1:𝔹;
		for i in [0..n-p){
			z&=x[i]==x[i+p];
		}
		y|=z;
	}
	return y;
}
