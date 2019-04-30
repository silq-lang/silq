// https://codeforces.com/contest/1001/problem/F
def solve[n:!ℕ](const qs:𝔹^n,bits:(!𝔹^n)^2):!ℤ{
	return measure(qs==bits[1]);
}
