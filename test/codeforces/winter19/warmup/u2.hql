// https://codeforces.com/contest/1115/problem/U2
def solve[n:!ℕ](qs:𝔹^n)mfree{
	for i in [0..n){
		if i!=1{
			qs[i]:=H(qs[i]);
		}
	}
	return qs;
}
