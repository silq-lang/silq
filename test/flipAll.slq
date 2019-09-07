def flipAll1[n:!ℕ]lifted(const a: 𝔹^n)lifted{
	x := dup(a);
	for i in [0..n){
		x[i] = !x[i];
	}
	return x;
}

def flipAll2[n:!ℕ]lifted(a: 𝔹^n)mfree{
	for i in [0..n){
		a[i] := X(a[i]);
	}
	return a;
}
