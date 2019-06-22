namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	
	operation Set (desired: Result, q1: Qubit) : Unit {
            let current = M(q1);
            if (desired != current) {
                X(q1);
            }
    }
	
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
	operation Solve (qs : Qubit[], bits: Bool[][]) : Unit {
			using (tmp = Qubit[2]) {
				repeat{
					H(tmp[0]);
					H(tmp[1]);
					//DumpMachine("");
					for(i in 0..Length(bits)-1){
						if((i&&&1) == 0){ X(tmp[0]); }
						if((i&&&2) == 0){ X(tmp[1]); }
						for(j in 0..Length(qs)-1){
							if(bits[i][j]){
								CCNOT(tmp[0], tmp[1], qs[j]);
							}
						}
						if((i&&&1) == 0){ X(tmp[0]); }
						if((i&&&2) == 0){ X(tmp[1]); }
						//DumpMachine("");
					}
					
					H(tmp[0]);
					H(tmp[1]);
					let r1 = M(tmp[0]);
					let r2 = M(tmp[1]);
				} until(r1 == Zero && r2 == Zero)
				fixup{
					ResetAll(tmp);
					ResetAll(qs);
				}
				//DumpMachine("");
			}
    }
	

	// operation MMain(sign: Int) : String {
	// 		mutable mess = "";
	// 		let bits = [[true, false, false], [false, true, false], [false, false, true], [false, false, false]];
	// 		//let bits = [[false, false, false, false], [false, true, true, false], [false, false, true, false], [true, false, false, true]];
	// 		using (qubit = Qubit[sign]) {
	// 			Solve(qubit, bits);
				
	// 			DumpMachine("");
				
	// 			set mess = mess + $"0={sign};#";
	// 			ResetAll(qubit);
	// 		}
	// 		return mess;
	// }
}