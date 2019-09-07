def a10_FetchStoreT[rr:!N, r:!N](const i:int[r], tt:B^rr, ttd:𝔹) : 𝔹^rr x 𝔹 {
	for j in [0..rr) {
		if i == j {
			(tt[j], ttd) := (ttd, tt[j]);
		}
	}
	return (tt, ttd);
}
