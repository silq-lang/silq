def groverDiffusion[n:!ℕ](cand:uint[n])mfree: uint[n]{
	for k in [0..n) { cand[k] := H(cand[k]); }
	if cand!=0{ phase(π); }
	for k in [0..n) { cand[k] := H(cand[k]); }
	return cand;
}
