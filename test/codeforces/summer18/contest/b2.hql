// https://codeforces.com/contest/1002/problem/B2
def solve[n:!ℕ](qs:𝔹^n){
	x:=measure(qs);
	for i in [1..n){
		if x[0]!=x[i]{
			return 1;
		}
	}
	return 0;
}
