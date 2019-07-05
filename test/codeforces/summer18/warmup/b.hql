// https://codeforces.com/contest/1001/problem/B
def solve(index:!ℤ){
	i := index as int[2];
	q₀ := H(i[0]);
	q₁ := q₀⊕i[1];
	return (q₀,q₁);
}
