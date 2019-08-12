namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Diagnostics;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
			H(qs[0]);
			H(qs[1]);
			mutable res = ResultAsInt(MultiM(qs));
			if (0 < res && res < 3)
			{
				set res = 3 - res;
			}
			return res;
        }
    }

	// operation BellTest (count: Int) : Int[]
    // {
    //     body
    //     {
    //         mutable cnt = new Int[4];
    //         using (qs = Qubit[2])
    //         {
	// 			X(qs[0]);
	// 			H(qs[0]);
	// 			H(qs[1]);
	// 			DumpMachine("C:/Users/vilim/source/repos/CFSummer18/B3/dump");

    //             for (test in 1..count)
    //             {
	// 				set cnt[Solve(qs)] = cnt[Solve(qs)] + 1;
    //             }

	// 			ResetAll(qs);
    //         }
    //         return cnt;
    //     }
    // }
}