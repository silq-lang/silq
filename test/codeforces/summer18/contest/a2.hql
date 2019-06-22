//https://codeforces.com/contest/1002/problem/A2
def solve[n:!ℕ](bits: !𝔹^n){
	x:=H(0:𝔹);
	qs := if x then bits else (0:int[n]):𝔹^n;
	forget(x=qs[0]);
	return qs;
}
