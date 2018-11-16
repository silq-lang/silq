def swapFirst[n:!ℕ,m:!ℕ](x: 𝔹^n, y: 𝔹^m){
	(x[0],y[0]) := (y[0],x[0]);
	return (x,y);
}
