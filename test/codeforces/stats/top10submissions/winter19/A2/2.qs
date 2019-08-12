namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
        using (anc=Qubit[2]) {
			let n = Length(qs);
			H(anc[0]); H(anc[1]);

			X(anc[0]); X(anc[1]);
			for (i in 0..n-1){
				if (bits[0][i] == true) {
					CCNOT(anc[0], anc[1], qs[i]);
				}
			}
			X(anc[0]); X(anc[1]);

			X(anc[0]);
			for (i in 0..n-1){
				if (bits[1][i] == true) {
					CCNOT(anc[0], anc[1], qs[i]);
				}
			}
			X(anc[0]);

			X(anc[1]);
			for (i in 0..n-1){
				if (bits[2][i] == true) {
					CCNOT(anc[0], anc[1], qs[i]);
				}
			}
			X(anc[1]);

			for (i in 0..n-1){
				if (bits[3][i] == true) {
					CCNOT(anc[0], anc[1], qs[i]);
				}
			}



			for (i in 0..n-1) {
				if (bits[1][i] == false) {
					X(qs[i]);
				}
			}
			(Controlled X) (qs[0..n-1], anc[1]);
			for (i in 0..n-1) {
				if (bits[1][i] == false) {
					X(qs[i]);
				}
			}

			for (i in 0..n-1) {
				if (bits[2][i] == false) {
					X(qs[i]);
				}
			}
			(Controlled X) (qs[0..n-1], anc[0]);
			for (i in 0..n-1) {
				if (bits[2][i] == false) {
					X(qs[i]);
				}
			}

			for (i in 0..n-1) {
				if (bits[3][i] == false) {
					X(qs[i]);
				}
			}
			(Controlled X) (qs[0..n-1], anc[0]);
			(Controlled X) (qs[0..n-1], anc[1]);
			for (i in 0..n-1) {
				if (bits[3][i] == false) {
					X(qs[i]);
				}
			}
		}
    }
}
