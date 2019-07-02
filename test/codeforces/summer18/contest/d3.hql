// https://codeforces.com/contest/1002/problem/D3
def solve(x:𝔹^3)lifted{
	s:=0:uint[2];
	for i in [0..3){
		s+=x[i];
	}
	return s>=2;
}
