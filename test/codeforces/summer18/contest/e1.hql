// https://codeforces.com/contest/1002/problem/E1
def solve[n:!ℕ](f: 𝔹^n !→lifted 𝔹){
	x:=0:int[n];
	for i in [0..n){ x[i] := H(x[i]); }
	if f(x as 𝔹^n){ phase(π); }
	for i in [0..n){ x[i] := H(x[i]); }
	return measure(x) as !𝔹^n;
}
