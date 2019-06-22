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
	// python code to gen table:
	//
	//res = [[[true]]]*2
	//for n in range(2, 8):
	//	now = []
	//	for i in range(2**n):
	//		s = list(('{0:0>'+str(n)+'b}').format(i))
	//		for j in range(1, n):
	//			if s[j:] == s[:-j]:
	//				now.append([true if e=='1' else false for e in s])
	//				# now.append(''.join(s))
	//				break
	//	res.append(now)
	//print(res)

	//operation Solve_TLE (x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		let pool = [[[true]], [[true]], [[false, false], [true, true]], [[false, false, false], [false, true, false], [true, false, true], [true, true, true]], [[false, false, false, false], [false, false, true, false], [false, true, false, false], [false, true, false, true], [false, true, true, false], [true, false, false, true], [true, false, true, false], [true, false, true, true], [true, true, false, true], [true, true, true, true]], [[false, false, false, false, false], [false, false, false, true, false], [false, false, true, false, false], [false, false, true, true, false], [false, true, false, false, false], [false, true, false, false, true], [false, true, false, true, false], [false, true, true, false, false], [false, true, true, false, true], [false, true, true, true, false], [true, false, false, false, true], [true, false, false, true, false], [true, false, false, true, true], [true, false, true, false, true], [true, false, true, true, false], [true, false, true, true, true], [true, true, false, false, true], [true, true, false, true, true], [true, true, true, false, true], [true, true, true, true, true]], [[false, false, false, false, false, false], [false, false, false, false, true, false], [false, false, false, true, false, false], [false, false, false, true, true, false], [false, false, true, false, false, false], [false, false, true, false, false, true], [false, false, true, false, true, false], [false, false, true, true, false, false], [false, false, true, true, true, false], [false, true, false, false, false, false], [false, true, false, false, false, true], [false, true, false, false, true, false], [false, true, false, true, false, false], [false, true, false, true, false, true], [false, true, false, true, true, false], [false, true, true, false, false, false], [false, true, true, false, false, true], [false, true, true, false, true, false], [false, true, true, false, true, true], [false, true, true, true, false, false], [false, true, true, true, false, true], [false, true, true, true, true, false], [true, false, false, false, false, true], [true, false, false, false, true, false], [true, false, false, false, true, true], [true, false, false, true, false, false], [true, false, false, true, false, true], [true, false, false, true, true, false], [true, false, false, true, true, true], [true, false, true, false, false, true], [true, false, true, false, true, false], [true, false, true, false, true, true], [true, false, true, true, false, true], [true, false, true, true, true, false], [true, false, true, true, true, true], [true, true, false, false, false, true], [true, true, false, false, true, true], [true, true, false, true, false, true], [true, true, false, true, true, false], [true, true, false, true, true, true], [true, true, true, false, false, true], [true, true, true, false, true, true], [true, true, true, true, false, true], [true, true, true, true, true, true]], [[false, false, false, false, false, false, false], [false, false, false, false, false, true, false], [false, false, false, false, true, false, false], [false, false, false, false, true, true, false], [false, false, false, true, false, false, false], [false, false, false, true, false, true, false], [false, false, false, true, true, false, false], [false, false, false, true, true, true, false], [false, false, true, false, false, false, false], [false, false, true, false, false, false, true], [false, false, true, false, false, true, false], [false, false, true, false, true, false, false], [false, false, true, false, true, true, false], [false, false, true, true, false, false, false], [false, false, true, true, false, false, true], [false, false, true, true, false, true, false], [false, false, true, true, true, false, false], [false, false, true, true, true, true, false], [false, true, false, false, false, false, false], [false, true, false, false, false, false, true], [false, true, false, false, false, true, false], [false, true, false, false, true, false, false], [false, true, false, false, true, false, true], [false, true, false, false, true, true, false], [false, true, false, true, false, false, false], [false, true, false, true, false, false, true], [false, true, false, true, false, true, false], [false, true, false, true, true, false, false], [false, true, false, true, true, false, true], [false, true, false, true, true, true, false], [false, true, true, false, false, false, false], [false, true, true, false, false, false, true], [false, true, true, false, false, true, false], [false, true, true, false, false, true, true], [false, true, true, false, true, false, false], [false, true, true, false, true, false, true], [false, true, true, false, true, true, false], [false, true, true, true, false, false, false], [false, true, true, true, false, false, true], [false, true, true, true, false, true, false], [false, true, true, true, false, true, true], [false, true, true, true, true, false, false], [false, true, true, true, true, false, true], [false, true, true, true, true, true, false], [true, false, false, false, false, false, true], [true, false, false, false, false, true, false], [true, false, false, false, false, true, true], [true, false, false, false, true, false, false], [true, false, false, false, true, false, true], [true, false, false, false, true, true, false], [true, false, false, false, true, true, true], [true, false, false, true, false, false, true], [true, false, false, true, false, true, false], [true, false, false, true, false, true, true], [true, false, false, true, true, false, false], [true, false, false, true, true, false, true], [true, false, false, true, true, true, false], [true, false, false, true, true, true, true], [true, false, true, false, false, false, true], [true, false, true, false, false, true, false], [true, false, true, false, false, true, true], [true, false, true, false, true, false, true], [true, false, true, false, true, true, false], [true, false, true, false, true, true, true], [true, false, true, true, false, false, true], [true, false, true, true, false, true, false], [true, false, true, true, false, true, true], [true, false, true, true, true, false, true], [true, false, true, true, true, true, false], [true, false, true, true, true, true, true], [true, true, false, false, false, false, true], [true, true, false, false, false, true, true], [true, true, false, false, true, false, true], [true, true, false, false, true, true, false], [true, true, false, false, true, true, true], [true, true, false, true, false, false, true], [true, true, false, true, false, true, true], [true, true, false, true, true, false, true], [true, true, false, true, true, true, false], [true, true, false, true, true, true, true], [true, true, true, false, false, false, true], [true, true, true, false, false, true, true], [true, true, true, false, true, false, true], [true, true, true, false, true, true, true], [true, true, true, true, false, false, true], [true, true, true, true, false, true, true], [true, true, true, true, true, false, true], [true, true, true, true, true, true, true]]];
	//		if(Length(x) >= 2){
	//			let mask = pool[Length(x)];
	//			for(it in 0..Length(mask)-1){
	//				let fun = ControlledOnBitString(mask[it], X);
	//				fun(x, y);
	//			}
	//		}
    //    }
    //    adjoint auto;
    //}
	// WA3
	//operation Solve (x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		let pool = [[false], [false], [false, false], [false, false, false], [false, false, false, false], [false, false, false, false, false], [false, false, false, false, false, false], [false, false, false, false, false, false, false]];
	//		let pers = [[0], [0], [1], [2], [1, 2, 3], [1, 3, 4], [3, 4, 5], [1, 2, 4, 5, 6]];
	//		for(l in pers[Length(x)]){
	//			let mask = pool[Length(x)-l];
	//			let fun = ControlledOnBitString(mask, X);
	//			for(k in 0..Length(x)-l-1){
	//				CNOT(x[k+l], x[k]);
	//			}
	//			//DumpMachine("");
	//			fun(x[0..Length(x)-l-1], y);
	//			for(k in 0..Length(x)-l-1){
	//				CNOT(x[Length(x)-1-k], x[Length(x)-1-k-l]);
	//			}	
	//		}
    //    }
    //    adjoint auto;
    //}
	
	//operation Solve (x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		let pool = [[false], [false], [false, false], [false, false, false], [false, false, false, false], [false, false, false, false, false], [false, false, false, false, false, false], [false, false, false, false, false, false, false]];
	//		let pers = [[0], [0], [1], [2], [2, 3], [3, 4], [3, 4, 5], [2, 4, 5, 6]];
	//		for(l in pers[Length(x)]){
	//			let mask = pool[Length(x)-l];
	//			let fun = ControlledOnBitString(mask, X);
	//			for(k in 0..Length(x)-l-1){
	//				CNOT(x[k+l], x[k]);
	//			}
	//			//DumpMachine("");
	//			fun(x[0..Length(x)-l-1], y);
	//			for(k in 0..Length(x)-l-1){
	//				CNOT(x[Length(x)-1-k], x[Length(x)-1-k-l]);
	//			}	
	//		}
    //    }
    //    adjoint auto;
    //}
	
	//operation Solve (x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		let pool = [[[true]], [[true]], [[false]], [[false, false], [true, false]], [[false, false, false], [false, true, false], [true, false, false], [true, false, true], [true, true, false]], [[false, false, false, false], [false, false, true, false], [false, true, false, false], [false, true, true, false], [true, false, false, false], [true, false, false, true], [true, false, true, false], [true, true, false, false], [true, true, false, true], [true, true, true, false]], [[false, false, false, false, false], [false, false, false, true, false], [false, false, true, false, false], [false, false, true, true, false], [false, true, false, false, false], [false, true, false, false, true], [false, true, false, true, false], [false, true, true, false, false], [false, true, true, true, false], [true, false, false, false, false], [true, false, false, false, true], [true, false, false, true, false], [true, false, true, false, false], [true, false, true, false, true], [true, false, true, true, false], [true, true, false, false, false], [true, true, false, false, true], [true, true, false, true, false], [true, true, false, true, true], [true, true, true, false, false], [true, true, true, false, true], [true, true, true, true, false]], [[false, false, false, false, false, false], [false, false, false, false, true, false], [false, false, false, true, false, false], [false, false, false, true, true, false], [false, false, true, false, false, false], [false, false, true, false, true, false], [false, false, true, true, false, false], [false, false, true, true, true, false], [false, true, false, false, false, false], [false, true, false, false, false, true], [false, true, false, false, true, false], [false, true, false, true, false, false], [false, true, false, true, true, false], [false, true, true, false, false, false], [false, true, true, false, false, true], [false, true, true, false, true, false], [false, true, true, true, false, false], [false, true, true, true, true, false], [true, false, false, false, false, false], [true, false, false, false, false, true], [true, false, false, false, true, false], [true, false, false, true, false, false], [true, false, false, true, false, true], [true, false, false, true, true, false], [true, false, true, false, false, false], [true, false, true, false, false, true], [true, false, true, false, true, false], [true, false, true, true, false, false], [true, false, true, true, false, true], [true, false, true, true, true, false], [true, true, false, false, false, false], [true, true, false, false, false, true], [true, true, false, false, true, false], [true, true, false, false, true, true], [true, true, false, true, false, false], [true, true, false, true, false, true], [true, true, false, true, true, false], [true, true, true, false, false, false], [true, true, true, false, false, true], [true, true, true, false, true, false], [true, true, true, false, true, true], [true, true, true, true, false, false], [true, true, true, true, false, true], [true, true, true, true, true, false]]];
	//		for(i in 1..Length(x)-1){
	//			CNOT(x[0], x[i]);
	//		}
	//		let mask = pool[Length(x)];
	//		for(it in 0..Length(mask)-1){
	//			let fun = ControlledOnBitString(mask[it], X);
	//			fun(x[1..Length(x)-1], y);
	//		}
	//		for(i in 1..Length(x)-1){
	//			CNOT(x[0], x[i]);
	//		}
    //    }
    //    adjoint auto;
    //}	
	//operation Solve_small (x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		let pool0 = [[[true]], [[false]], [[false, false]], [[false, false, false], [true, true, true]], [[false, false, false, false], [false, true, true, true], [true, false, true, true], [true, true, false, true], [true, true, true, false]], [[false, false, false, false, false], [false, false, true, true, true], [false, true, false, true, true], [false, true, true, false, true], [false, true, true, true, false], [true, false, false, true, true], [true, false, true, false, true], [true, false, true, true, false], [true, true, false, false, true], [true, true, false, true, false], [true, true, true, false, false]], [[false, false, false, false, false, false], [false, false, false, true, true, true], [false, false, true, false, true, true], [false, false, true, true, false, true], [false, false, true, true, true, false], [false, true, false, false, true, true], [false, true, false, true, false, true], [false, true, false, true, true, false], [false, true, true, false, false, true], [false, true, true, false, true, false], [false, true, true, true, false, false], [true, false, false, false, true, true], [true, false, false, true, false, true], [true, false, false, true, true, false], [true, false, true, false, false, true], [true, false, true, false, true, false], [true, false, true, true, false, false], [true, true, false, false, false, true], [true, true, false, false, true, false], [true, true, false, true, false, false], [true, true, true, false, false, false], [true, true, true, true, true, true]]];
    //
	//		
	//		if(Length(x) > 0){
	//			let mask = pool0[Length(x)];
	//			for(it in 0..Length(mask)-1){
	//				let fun = ControlledOnBitString(mask[it], X);
	//				fun(x[0..Length(x)-1], y);
	//			}
	//		} else {
	//			X(y);
	//		}
	//	}
    //    adjoint auto;
	//	controlled auto;
	//}
	//operation Solve_small_1(x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		//let pool0 = [[[true]], [[false]], [[false, false]], [[false, false, false], [true, true, true]], [[false, false, false, false], [false, true, true, true], [true, false, true, true], [true, true, false, true], [true, true, true, false]], [[false, false, false, false, false], [false, false, true, true, true], [false, true, false, true, true], [false, true, true, false, true], [false, true, true, true, false], [true, false, false, true, true], [true, false, true, false, true], [true, false, true, true, false], [true, true, false, false, true], [true, true, false, true, false], [true, true, true, false, false]], [[false, false, false, false, false, false], [false, false, false, true, true, true], [false, false, true, false, true, true], [false, false, true, true, false, true], [false, false, true, true, true, false], [false, true, false, false, true, true], [false, true, false, true, false, true], [false, true, false, true, true, false], [false, true, true, false, false, true], [false, true, true, false, true, false], [false, true, true, true, false, false], [true, false, false, false, true, true], [true, false, false, true, false, true], [true, false, false, true, true, false], [true, false, true, false, false, true], [true, false, true, false, true, false], [true, false, true, true, false, false], [true, true, false, false, false, true], [true, true, false, false, true, false], [true, true, false, true, false, false], [true, true, true, false, false, false], [true, true, true, true, true, true]]];
	//		let pool1 = [[[true]], [[true]], [[false, true], [true, false]], [[false, false, true], [false, true, false], [true, false, false]], [[false, false, false, true], [false, false, true, false], [false, true, false, false], [true, false, false, false], [true, true, true, true]], [[false, false, false, false, true], [false, false, false, true, false], [false, false, true, false, false], [false, true, false, false, false], [false, true, true, true, true], [true, false, false, false, false], [true, false, true, true, true], [true, true, false, true, true], [true, true, true, false, true], [true, true, true, true, false]], [[false, false, false, false, false, true], [false, false, false, false, true, false], [false, false, false, true, false, false], [false, false, true, false, false, false], [false, false, true, true, true, true], [false, true, false, false, false, false], [false, true, false, true, true, true], [false, true, true, false, true, true], [false, true, true, true, false, true], [false, true, true, true, true, false], [true, false, false, false, false, false], [true, false, false, true, true, true], [true, false, true, false, true, true], [true, false, true, true, false, true], [true, false, true, true, true, false], [true, true, false, false, true, true], [true, true, false, true, false, true], [true, true, false, true, true, false], [true, true, true, false, false, true], [true, true, true, false, true, false], [true, true, true, true, false, false]]];
	//		//let pool2 = [[[true]], [[true]], [[true, true]], [[false, true, true], [true, false, true], [true, true, false]], [[false, false, true, true], [false, true, false, true], [false, true, true, false], [true, false, false, true], [true, false, true, false], [true, true, false, false]], [[false, false, false, true, true], [false, false, true, false, true], [false, false, true, true, false], [false, true, false, false, true], [false, true, false, true, false], [false, true, true, false, false], [true, false, false, false, true], [true, false, false, true, false], [true, false, true, false, false], [true, true, false, false, false], [true, true, true, true, true]], [[false, false, false, false, true, true], [false, false, false, true, false, true], [false, false, false, true, true, false], [false, false, true, false, false, true], [false, false, true, false, true, false], [false, false, true, true, false, false], [false, true, false, false, false, true], [false, true, false, false, true, false], [false, true, false, true, false, false], [false, true, true, false, false, false], [false, true, true, true, true, true], [true, false, false, false, false, true], [true, false, false, false, true, false], [true, false, false, true, false, false], [true, false, true, false, false, false], [true, false, true, true, true, true], [true, true, false, false, false, false], [true, true, false, true, true, true], [true, true, true, false, true, true], [true, true, true, true, false, true], [true, true, true, true, true, false]]];
	//		
	//		
	//		if(Length(x) > 0){
	//			let mask = pool1[Length(x)];
	//			for(it in 0..Length(mask)-1){
	//				let fun = ControlledOnBitString(mask[it], X);
	//				fun(x[0..Length(x)-1], y);
	//			}
	//		}
	//	}
    //    adjoint auto;
	//	controlled auto;
	//}
	//operation Solve_small_2(x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		//let pool0 = [[[true]], [[false]], [[false, false]], [[false, false, false], [true, true, true]], [[false, false, false, false], [false, true, true, true], [true, false, true, true], [true, true, false, true], [true, true, true, false]], [[false, false, false, false, false], [false, false, true, true, true], [false, true, false, true, true], [false, true, true, false, true], [false, true, true, true, false], [true, false, false, true, true], [true, false, true, false, true], [true, false, true, true, false], [true, true, false, false, true], [true, true, false, true, false], [true, true, true, false, false]], [[false, false, false, false, false, false], [false, false, false, true, true, true], [false, false, true, false, true, true], [false, false, true, true, false, true], [false, false, true, true, true, false], [false, true, false, false, true, true], [false, true, false, true, false, true], [false, true, false, true, true, false], [false, true, true, false, false, true], [false, true, true, false, true, false], [false, true, true, true, false, false], [true, false, false, false, true, true], [true, false, false, true, false, true], [true, false, false, true, true, false], [true, false, true, false, false, true], [true, false, true, false, true, false], [true, false, true, true, false, false], [true, true, false, false, false, true], [true, true, false, false, true, false], [true, true, false, true, false, false], [true, true, true, false, false, false], [true, true, true, true, true, true]]];
	//		//let pool1 = [[[true]], [[true]], [[false, true], [true, false]], [[false, false, true], [false, true, false], [true, false, false]], [[false, false, false, true], [false, false, true, false], [false, true, false, false], [true, false, false, false], [true, true, true, true]], [[false, false, false, false, true], [false, false, false, true, false], [false, false, true, false, false], [false, true, false, false, false], [false, true, true, true, true], [true, false, false, false, false], [true, false, true, true, true], [true, true, false, true, true], [true, true, true, false, true], [true, true, true, true, false]], [[false, false, false, false, false, true], [false, false, false, false, true, false], [false, false, false, true, false, false], [false, false, true, false, false, false], [false, false, true, true, true, true], [false, true, false, false, false, false], [false, true, false, true, true, true], [false, true, true, false, true, true], [false, true, true, true, false, true], [false, true, true, true, true, false], [true, false, false, false, false, false], [true, false, false, true, true, true], [true, false, true, false, true, true], [true, false, true, true, false, true], [true, false, true, true, true, false], [true, true, false, false, true, true], [true, true, false, true, false, true], [true, true, false, true, true, false], [true, true, true, false, false, true], [true, true, true, false, true, false], [true, true, true, true, false, false]]];
	//		let pool2 = [[[true]], [[true]], [[true, true]], [[false, true, true], [true, false, true], [true, true, false]], [[false, false, true, true], [false, true, false, true], [false, true, true, false], [true, false, false, true], [true, false, true, false], [true, true, false, false]], [[false, false, false, true, true], [false, false, true, false, true], [false, false, true, true, false], [false, true, false, false, true], [false, true, false, true, false], [false, true, true, false, false], [true, false, false, false, true], [true, false, false, true, false], [true, false, true, false, false], [true, true, false, false, false], [true, true, true, true, true]], [[false, false, false, false, true, true], [false, false, false, true, false, true], [false, false, false, true, true, false], [false, false, true, false, false, true], [false, false, true, false, true, false], [false, false, true, true, false, false], [false, true, false, false, false, true], [false, true, false, false, true, false], [false, true, false, true, false, false], [false, true, true, false, false, false], [false, true, true, true, true, true], [true, false, false, false, false, true], [true, false, false, false, true, false], [true, false, false, true, false, false], [true, false, true, false, false, false], [true, false, true, true, true, true], [true, true, false, false, false, false], [true, true, false, true, true, true], [true, true, true, false, true, true], [true, true, true, true, false, true], [true, true, true, true, true, false]]];
	//		
	//		if(Length(x) > 1){
	//			let mask = pool2[Length(x)];
	//			for(it in 0..Length(mask)-1){
	//				let fun = ControlledOnBitString(mask[it], X);
	//				fun(x[0..Length(x)-1], y);
	//			}
	//		}
	//	}
    //    adjoint auto;
	//	controlled auto;
	//}
	
	operation Modinc(anc : Qubit[]) : Unit {
		body (...) {
			let cnt = LittleEndian(anc);
			IntegerIncrementLE(1, cnt);
			X(anc[0]);
			SWAP(anc[0], anc[1]);
			X(anc[0]);
		}
		controlled adjoint auto;
	}
	
	operation Sumup(x : Qubit[], anc : Qubit[]) : Unit {
		body (...) {
			for(i in 0..Length(x)-1){
				let cnt = LittleEndian(anc);
				(Controlled Modinc)([x[i]], (anc));
			}
		}
        adjoint auto;
	
	}
			
	operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
			using (anc = Qubit[2]){
				Sumup(x, anc);
				ApplyToEachCA(X, anc);
				CCNOT(anc[0], anc[1], y);
				ApplyToEachCA(X, anc);
				(Adjoint Sumup)(x, anc);
			}
        }
        adjoint auto;
    }

	// operation MMain(sign: Int) : String {
	// 		mutable mess = "";
	// 		let bits = [[true, false, false], [false, true, false], [false, false, true], [false, false, false]];
	// 		//let bits = [[false, false, false, false], [false, true, true, false], [false, false, true, false], [true, false, false, true]];
	// 		using (qubit = Qubit[sign]) {
	// 			using (qout = Qubit[1]){
	// 				for(i in 0..Length(qubit)-1){
	// 					H(qubit[i]);
	// 				}
	// 				Solve(qubit, qout[0]);
					
	// 				DumpMachine("");
					
	// 				set mess = mess + $"0={sign};#";
	// 				ResetAll(qubit);
	// 				ResetAll(qout);
	// 			}
	// 		}
	// 		return mess;
	// }
}