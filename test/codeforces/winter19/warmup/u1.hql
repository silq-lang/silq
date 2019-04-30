// https://codeforces.com/contest/1115/problem/U1
def solve[n:!ℕ](qs:𝔹^n)mfree{
	for i in [0..n){ qs[i]:=X(qs[i]); }
	return qs;
}
