// https://codeforces.com/contest/1116/problem/D2
def solve[n:!ℕ](qs:𝔹^n){
	seen:=0:𝔹;
	for i in [1..n){
		bit:=qs[n-i];
		if !seen&&bit{
			for j in [0..n-i){
				qs[j]:=H(qs[j]);
			}
		}
		forget(bit=qs[n-i]);
		seen|=qs[n-i];
	}
	forget(seen);
	return qs;
}
