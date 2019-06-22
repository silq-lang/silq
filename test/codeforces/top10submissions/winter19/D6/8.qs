namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Diagnostics;
            
    operation IntToBoolArr(val: Int, dim: Int) : Bool[]
    {
        mutable rv = new Bool[0];

        for (i in 0 .. dim-1) {
            if ((val &&& (2 ^ i)) == 0) {
                set rv = rv + [false];
            }
            else {
                set rv = rv + [true];
            }
        }

        return rv;
    }

    operation Move (qs: Qubit[], src: Int, dst: Int) : Unit
    {
        let dim = Length(qs);

        mutable srcBool = IntToBoolArr(src-1, dim);
        let dstBool = IntToBoolArr(dst-1, dim);

        for (index in 0 .. dim-1) {
            if (srcBool[index] != dstBool[index]) {
                
                for (k in 0 .. dim-1) {
                    if (srcBool[k] == false) {
                        X(qs[k]);
                    }
                }

                let splitted = SplitArray([index, 1], qs);

                (Controlled X)(splitted[0]+splitted[2], qs[index]);

                for (k in 0 .. dim-1) {
                    if (srcBool[k] == false) {
                        X(qs[k]);
                    }
                }

                set srcBool[index] = dstBool[index];
            }
        }
    }

    operation A(q: Qubit) : Unit
    {
        body (...)
        {
            Ry(1.4, q);
        }
        
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }
    
    // guessed.
    operation Solve (qs: Qubit[]) : Unit
    {
        let l = Length(qs);

        if (l == 2) {
            Solve2(qs);
        }
        if (l == 3) {
            Solve3(qs);
        }
        if (l == 4) {
            Solve4(qs);
        }
    }
    operation Solve2 (qs: Qubit[]) : Unit
    {
        X(qs[0]);
        X(qs[1]);
        Move(qs,1,4);
        Move(qs,1,4);
        Move(qs,3,1);

        (Controlled A)([qs[0]], qs[1]);
        Move(qs,2,1);
        (Controlled A)([qs[0]], qs[1]);
        Move(qs,4,1);
        (Controlled A)([qs[0]], qs[1]);

        Move(qs,4,1);

    }
    operation Solve3 (qs: Qubit[]) : Unit
    {
        Move(qs,1,2);
        Move(qs,1,3);
        Move(qs,2,6);
        Move(qs,1,6);
        Move(qs,3,7);
        Move(qs,4,7);
        Move(qs,1,2);
        Move(qs,2,3);
        Move(qs,7,5);

        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,4,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,5,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,6,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,8,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,5,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,6,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,8,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,5,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,6,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,8,1);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,3,4);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,1,7);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        Move(qs,2,8);
        (Controlled A)([qs[0], qs[1]], qs[2]);
        
        Move(qs,8,1);
        Move(qs,4,2);
        Move(qs,4,3);
        Move(qs,5,4);
        Move(qs,6,5);
    }
    operation Solve4 (qs: Qubit[]) : Unit
    {        
        X(qs[0]);
        X(qs[1]);
        X(qs[2]);
        X(qs[3]);

        Move(qs,15,16);
        Move(qs,13,16);
        Move(qs,12,16);
        Move(qs,11,12);
        Move(qs,9,16);
        Move(qs,8,16);
        Move(qs,7,8);
        Move(qs,6,16);
        Move(qs,5,16);
        Move(qs,4,8);
        Move(qs,3,4);
        Move(qs,2,16);
        Move(qs,1,16);

        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,1,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,1,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,1,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,3,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,5,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,5,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,7,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,9,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,9,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,9,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,11,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,13,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,13,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        Move(qs,15,16);
        (Controlled A)([qs[0], qs[1], qs[2]], qs[3]);
        
        Move(qs,8,15);
        Move(qs,7,14);
        Move(qs,6,13);
        Move(qs,5,12);
        Move(qs,4,11);
        Move(qs,3,10);
        Move(qs,2,9);
        Move(qs,1,8);
        
        X(qs[0]);
        X(qs[1]);
        X(qs[2]);
        X(qs[3]);
    }
    
    // operation DumpUnitaryToFiles (N : Int, unitary : (Qubit[] => Unit)) : Unit {
    //     let size = 1 <<< N;
        
    //     using (qs = Qubit[N]) {
    //         for (k in 0 .. size - 1) {                
    //             // Prepare k-th basis vector
    //             let binary = BoolArrFromPositiveInt(k, N);
                
    //             //Message($"{k}/{N} = {binary}");
    //             // binary is little-endian notation, so the second vector tried has qubit 0 in state 1 and the rest in state 0
    //             ApplyPauliFromBitString(PauliX, true, binary, qs);
                
    //             // Apply the operation
    //             Solve(qs);
                
    //             // Dump the contents of the k-th column
    //             DumpMachine($"DU_{N}_{k}.txt");
                
    //             ResetAll(qs);
    //         }
    //     }
    // }

    // // The operation which is called from C# code
    // operation CallDumpUnitary (N : Int) : Unit {
    //     // make sure the operation passed to DumpUnitaryToFiles matches the number of qubits set in Driver.cs
    //     let unitary = ApplyToEach(I, _);

    //     DumpUnitaryToFiles(N, unitary);
    // }
}
