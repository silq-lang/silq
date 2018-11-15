import groverDiffusion;

def round(x:!R) lifted :!ℕ;
def sqrt(x:!R) lifted :!ℝ;

def grover[n:!N](f: const uint[n] !→ lifted 𝔹):!ℕ{
	nIterations:= round(π / 4 * sqrt(2^n));
	cand:=0:uint[n];
    for k in [0..n) { cand[k] := H(cand[k]); }
	
	for k in [0..nIterations){
		if f(cand){
			phase(π);
		}
		cand:=groverDiffusion(cand);
	}
	return measure(cand):!ℕ;
}
