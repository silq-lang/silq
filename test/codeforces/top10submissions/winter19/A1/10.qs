namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	
	// operation Set (desired: Result, q1: Qubit) : Unit {
    //         let current = M(q1);
    //         if (desired != current) {
    //             X(q1);
    //         }
    // }
	
	// operation Bell (q : Qubit[], sign : Int) : Unit {
	// 		if((sign&&&2) == 2){
	// 			Set(One, q[1]);
	// 			//Z(q[1]);
	// 		}
	// 		if((sign&&&1) == 1){
	// 			X(q[0]);
	// 		}
	// 		H(q[0]);
	// 		CNOT(q[0], q[1]);
    // }
	
	// operation PM (q : Qubit, sign : Int) : Unit {
	// 		if(sign == -1){
	// 			X(q);
	// 		}
	// 		H(q);
    // }


    // operation GG (q : Qubit[], p : Qubit, k : Int) : Unit {
	// 		CNOT(q[k], p);
    // }     
	// operation GG1 (q : Qubit[], p : Qubit) : Unit {
	// 		CNOT(q[1], p);
    // }    
	// operation Popcount (q : Qubit[], p : Qubit) : Unit {
	// 		for(i in 0..Length(q)-1){
	// 			GG(q, p, i);
	// 		}
    // } 	
	// operation S0 (q : Qubit[], p : Qubit) : Unit {
	// 		Set(Zero, p);
    // } 
	// operation S1 (q : Qubit[], p : Qubit) : Unit {
	// 		Set(One, p);
    // } 
	operation Solve (qs : Qubit[]) : Unit {
			let amplitudes = [1.0, 1.0, 1.0, 0.0];
			let fun = StatePreparationPositiveCoefficients(amplitudes);
			let qsBE = BigEndian(qs);
			fun(qsBE);
    }
	

	// operation MMain(sign: Int) : String {
	// 		mutable mess = "";
	// 		using (qubit = Qubit[sign]) {
	// 			Solve(qubit);
				
	// 			DumpMachine("");
				
	// 			set mess = mess + $"0={sign};#";
	// 			ResetAll(qubit);
	// 		}
	// 		return mess;
	// }
}