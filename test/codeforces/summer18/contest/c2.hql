// https://codeforces.com/contest/1002/problem/C2
def solve(q:𝔹){
	if measure(H(0:𝔹)){
		return if measure(H(q)) then 0 else -1;
	}else{
		return if measure(q) then 1 else -1;
	}
}
