// https://codeforces.com/contest/1116/problem/C3
def solve[n:!ℕ](const x:𝔹^n)lifted{
	(z,o,t):=(1:𝔹,0:𝔹,0:𝔹);
	for i in [0..n){
		if x[i]{
			(o,t,z):=(z,o,t);
		}
	}
	return z;
}
