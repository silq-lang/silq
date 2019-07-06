def QFT[n:!ℕ](ψ: uint[n])mfree: uint[n]{
	for k in [0..n div 2){
		(ψ[k],ψ[n-k-1]) := (ψ[n-k-1],ψ[k]);
	}
	for k in [0..n){
		ψ[k] := H(ψ[k]);
		for l in [k+1..n){
			if ψ[l] && ψ[k]{
				phase(2*π * 2^(k-l-1));
			}
		}
	}
	return ψ;
}
