// https://codeforces.com/contest/1002/problem/E2
def solve[n:!ℕ](f: 𝔹^n !→lifted 𝔹){
	b:=vector(n,0:!𝔹);
	b[0]=(n%2!=0)⊕measure(f((0:int[n]):𝔹^n));
	return b;
}
