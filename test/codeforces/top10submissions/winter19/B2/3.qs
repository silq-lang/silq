namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;
	open Microsoft.Quantum.Extensions.Diagnostics;


	// operation MakeState (q : Qubit, number: Double) : Unit {
	// 	body (...) { 
	// 		let theta = 2.0*PI()/3.0;
	// 		H(q);
	// 		R1(theta*number, q);
	// 	}
	// 	adjoint auto;
    // }

	// operation WState (qs : Qubit[]) : Unit {
    //     body (...) {
    //         let n = Length(qs);
    //         if (n == 1) {
    //             X(qs[0]);
    //         } else {
    //             let theta = ArcSin(1.0 / Sqrt(ToDouble(n)));
    //             Ry(2.0 * theta, qs[0]);
                
    //             X(qs[0]);
    //             Controlled WState(qs[0 .. 0], qs[1 .. n - 1]);
    //             X(qs[0]);
    //         }
	// 	}       
	// 	adjoint invert;
    //     controlled distribute;
    //     controlled adjoint distribute;
    // }


	// operation Gen2 (qs : Qubit[]) : Unit {
	// 	body (...) {
	// 		using (t = Qubit[1]) {
	// 			WState([qs[0], qs[1], t[0]]);
	// 			X(qs[0]); X(qs[1]);
	// 			Controlled X (qs, t[0]);
	// 			X(qs[0]); X(qs[1]);
	// 		}
	// 	}
	// 	adjoint auto;
    // }

	operation U1d (q : Qubit) : Unit {
		body (...) {
			Z(q);
			H(q);
		}
		adjoint auto;
		controlled auto;
	}

	operation U2d (q : Qubit) : Unit {
		body (...) {
			let theta = -2.0*ArcCos(1.0/Sqrt(3.0));
			Ry(theta, q);
		}
		adjoint auto;
		controlled auto;
	}

	operation U3 (q : Qubit) : Unit {
		body (...) {
			 H(q); S(q); X(q);
		}
		adjoint auto;
		controlled auto;
	}

	operation U (qs : Qubit[]) : Unit {
		body (...) {			
			CNOT(qs[1], qs[0]); Controlled U3([qs[0]], qs[1]); Z(qs[1]); CNOT(qs[1], qs[0]);
			X(qs[0]); Controlled U2d([qs[0]], qs[1]); X(qs[0]);
			CNOT(qs[1], qs[0]); Controlled U1d([qs[0]], qs[1]); CNOT(qs[1], qs[0]);
		}
		adjoint auto;
	}


    operation Solve (q : Qubit) : Int {
		body (...) {
			let theta = 2.0*PI()/3.0;
			mutable state = 0;
			using (t = Qubit[1]) { 
				U([q]+t);
				if (M(q) == One) {set state = state + 1;}
				if (M(t[0]) == One) {set state = state + 2;} 
				ResetAll(t);
			}
			return state;
		}
    }
}