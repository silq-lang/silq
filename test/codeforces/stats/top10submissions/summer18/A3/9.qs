namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : ()
    {
        body
        {
			let n = Length(qs);

			mutable i = -1;
			mutable second = false;

			for (j in 0..n-1)
			{
				if (bits0[j] && bits1[j])
				{
					X(qs[j]);
				}
				if (bits0[j] != bits1[j] && i == -1)
				{
					set i = j;
					H(qs[i]);
					if (bits1[j])
					{
						set second = true;
					}
				}
			}

			if (i != -1)
			{
				for (j in i+1..n-1)
				{
					if (bits0[j] != bits1[j])
					{
						if (second != bits1[j])
						{
							X(qs[j]);
						}
						CNOT(qs[i], qs[j]);
					}
				}
			}
        }
    }

	// operation BellTest (count: Int) : Int[]
    // {
    //     body
    //     {
    //         mutable cnt = new Int[8];
    //         using (qs = Qubit[3])
    //         {
    //             for (test in 1..count)
    //             {
	// 				Solve(qs, [true; false; false], [false; true; true]);

    //                 let res = ResultAsInt([M(qs[0]); M(qs[1]); M(qs[2])]);//; M(qs[3]); M(qs[4])]);

	// 				set cnt[res] = cnt[res] + 1;

    //                 ResetAll (qs);
    //             }
    //         }
    //         return cnt;
    //     }
    // }
}