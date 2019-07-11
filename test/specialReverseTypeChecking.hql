def foo[n:!ℕ](psi:uint[n],const l: uint[n]) mfree: uint[n]×uint[n];
def bar[n:!ℕ](psi:uint[n],phi:uint[n],const l: uint[n],const k: uint[n]) mfree: uint[n];

def test1[n:!ℕ](f: uint[n] !-> lifted uint[n]):!ℕ{
	cand1 := 0: uint[n];
	cand2 := 0: uint[n];
    cand := reverse(foo[n])((cand1,cand2),0:uint[n]);
    return measure(cand) as !ℕ;
}
def test2[n:!ℕ](f: uint[n] !-> lifted uint[n]):!ℕ×!ℕ{
	cand := 0: uint[n];
    (cand1,cand2) := reverse(bar[n])(cand,0:uint[n],0:uint[n]);
    return measure(cand1,cand2) as !ℕ×!ℕ;
}
