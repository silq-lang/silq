def solve[n:!ℕ](bits:(!𝔹^n)^4){
    anc:=0:uint[2];
    for j in [0..2){ anc[j]:=H(anc[j]); }
    qs:=(bits:(𝔹^n)^4)[anc];
	for j in [0..3] {
		if qs==bits[j]{
			anc⊕=j;
		}
	}
	forget(anc=0:uint[2]);
    return qs;
}

