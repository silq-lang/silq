https://codeforces.com/contest/1002/problem/A3
def solve[n:!ℕ](bits: (!𝔹^n)^2){
	k := 0;
	for j in [1..n){
		if bits[0][j]!=bits[1][j]{
			k=j;
		}
	}
	i:=H(0:𝔹);
	qs:=bits[i];
	forget(i=(qs[k]==bits[1][k]));
	return qs;
}
