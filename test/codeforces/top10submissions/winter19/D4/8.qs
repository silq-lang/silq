// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT license.

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
        if (l == 5) {
            Solve5(qs);
        }
    }
    

    operation Solve2 (qs : Qubit[]) : Unit 
    {    
        let l = Length(qs);

        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }

        H(qs[0]);
        
        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }       
    }
    operation Solve3 (qs : Qubit[]) : Unit 
    {
        let l = Length(qs);

        ApplyToEach(X, qs[0..l-2]);

        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }

        H(qs[0]);
        
        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }        
         
        for (i in 0..l-2) {
            (Controlled X)([qs[l-1]], qs[i]);
        }
        
        Move(qs, 8, 6);
        
        ApplyToEach(X, qs); 

        for (i in 0..l-2) {
            (Controlled X)([qs[l-1]], qs[i]);
        }
        
        Move(qs, 8, 6);
    }    
    operation Solve4 (qs : Qubit[]) : Unit 
    {
        let l = Length(qs);

        ApplyToEach(X, qs[0..l-2]);

        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }

        H(qs[0]);
        
        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }        
         
        for (i in 0..l-2) {
            (Controlled X)([qs[l-1]], qs[i]);
        }
        
        Move(qs, 16, 10);
        Move(qs, 15, 11);
        Move(qs, 16, 12);
        Move(qs, 16, 14); 
        
        ApplyToEach(X, qs); 
                 
        for (i in 0..l-2) {
            (Controlled X)([qs[l-1]], qs[i]);
        }
        
        Move(qs, 16, 10);
        Move(qs, 15, 11);
        Move(qs, 16, 12);
        Move(qs, 16, 14);         
    }
    operation Solve5 (qs : Qubit[]) : Unit 
    {
        let l = Length(qs);

        ApplyToEach(X, qs[0..l-2]);

        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }

        H(qs[0]);
        
        for (q in qs[1..l-1]) {
            CNOT(qs[0], q);
        }        
         
        for (i in 0..l-2) {
            (Controlled X)([qs[l-1]], qs[i]);
        }
        
        Move(qs, 32, 18);
        Move(qs, 31, 19);
        Move(qs, 32, 20);
        Move(qs, 29, 21);
        Move(qs, 32, 22);
        Move(qs, 31, 23);
        Move(qs, 32, 24);
        Move(qs, 32, 26);
        Move(qs, 31, 27);
        Move(qs, 32, 28);
        Move(qs, 32, 30);

        ApplyToEach(X, qs); 
                        
        for (i in 0..l-2) {
            (Controlled X)([qs[l-1]], qs[i]);
        }
        
        Move(qs, 32, 18);
        Move(qs, 31, 19);
        Move(qs, 32, 20);
        Move(qs, 29, 21);
        Move(qs, 32, 22);
        Move(qs, 31, 23);
        Move(qs, 32, 24);
        Move(qs, 32, 26);
        Move(qs, 31, 27);
        Move(qs, 32, 28);
        Move(qs, 32, 30);
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
