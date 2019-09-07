// https://codeforces.com/contest/1115/problem/U3
def solve[n:!ℕ](qs:𝔹^n){
	last:=qs[n-1];
	for i in [0..n-1){
		if !last{
			qs[i]:=X(qs[i]);
		}else{
			qs[i]:=H(qs[i]);
		}
	}
	forget(last=qs[n-1]);
	return qs;
}
