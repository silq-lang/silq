// (longer solution for F that uses fewer quantum operations)
def solve[n:!ℕ](const qs:𝔹^n,bits:(!𝔹^n)^2):!ℤ{
	for i in [0..n){
		if bits[0][i]!=bits[1][i]{
			return if measure(qs[i])==bits[0][i] then 0 else 1;
		}
	}
	return -1;
}
