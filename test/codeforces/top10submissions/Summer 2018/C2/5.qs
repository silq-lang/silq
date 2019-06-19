namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            mutable swap = true;

			using(r = Qubit[1]){
				H(r[0]);
				if(M(r[0]) == One){
					set swap = false;
				}

				ResetAll(r);
			}

			if(swap == false){
				mutable res = M(q);
				if(res == One){
					return(1);
				}
				return(-1);
			}

			else{
				H(q);
				mutable res = M(q);
				if(res == One){
					return(0);
				}
				return(-1);
			}
        }
    }
}