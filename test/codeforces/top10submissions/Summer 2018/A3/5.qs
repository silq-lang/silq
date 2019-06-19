namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : ()
    {
        body
        {
		mutable N = Length(qs);
            mutable firstDiff = 0;

		for(i in 1..N){
			if(bits0[N - i] != bits1[N - i]){
				set firstDiff = N - i;
			}
		}

		for(i in 0..(firstDiff - 1)){
			if(bits0[i] == true){
				X(qs[i]);
			}
		}

		H(qs[firstDiff]);

		for(i in (firstDiff + 1)..(N - 1)){
			if(bits0[i] == true){
				if(bits0[firstDiff] == false){
					X(qs[firstDiff]);
				}
				CNOT(qs[firstDiff], qs[i]);
				if(bits0[firstDiff] == false){
					X(qs[firstDiff]);
				}
			}
			if(bits1[i] == true){
				if(bits1[firstDiff] == false){
					X(qs[firstDiff]);
				}
				CNOT(qs[firstDiff], qs[i]);
				if(bits1[firstDiff] == false){
					X(qs[firstDiff]);
				}
			}
		}
        }
    }
}