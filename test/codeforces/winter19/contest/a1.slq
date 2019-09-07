// https://codeforces.com/contest/1116/problem/A1
def solve(){
	(q₀,q₁):=(1:𝔹,1:𝔹);
	done:=false;
	while !done{
		measure(q₀,q₁);
		(q₀,q₁):=(H(0:𝔹),H(0:𝔹));
		done=!measure(q₀&q₁);
	}
	return (q₀,q₁);
}

// def solve(){
// 	(q₀,q₁):=(1:𝔹,1:𝔹);
// 	while measure(q₀&q₁){
// 		measure(q₀,q₁);
// 		(q₀,q₁):=(H(0:𝔹),H(0:𝔹));
// 	}
// 	return (q₀,q₁);
// }