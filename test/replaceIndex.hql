def main(n: !ℕ){
	a := array(n, 0:𝔹);
	for i in [0..n){
		a[(i+1)%n] := X(a[(i+1)%n]);
		a[i] := H(a[i]);
		a[0] := X(H(a[0]));
	}
	f:=λ()lifted. 0;
	a[f()]:=a[f()];
	return a;
}
