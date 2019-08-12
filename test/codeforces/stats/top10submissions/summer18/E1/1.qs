namespace Solution {
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Extensions.Diagnostics;

    // operation DM() : () {
    //     body {
    //         DumpMachine("/dev/stdout");
    //     }
    // }

    // operation Bell (qs: Qubit[], idx: Int) : () {
    //     body {
    //         if (Length(qs) != 2) { fail "BELL TWO"; }
    //         H(qs[0]);
    //         CNOT(qs[0],qs[1]);
    //         if((idx&&&1)!=0) {Z(qs[1]);}
    //         if((idx&&&2)!=0) {X(qs[1]);}
    //     }
    // }
    // operation BellM (qs: Qubit[]) : Int {
    //     body {
    //         mutable z = 0;
    //         CNOT(qs[0],qs[1]);
    //         H(qs[0]);
    //         let m1 = M(qs[0]);
    //         let m2 = M(qs[1]);
    //         if(m1==One) {set z=z|||1;}
    //         if(m2==One) {set z=z|||2;}
    //         return z;
    //     }
    // }
    // operation UBitSum(x: Qubit[], y: Qubit) : () {
    //     body {
    //         for(i in 0..Length(x)-1) {
    //             CNOT(x[i],y);
    //         }
    //     }
    // }
    // operation UConstZero(x: Qubit[], y: Qubit) : () {
    //     body {
    //     }
    // }
    // operation UConstOne(x: Qubit[], y: Qubit) : () {
    //     body {
    //         X(y);
    //     }
    // }
    // operation UIndex(x: Qubit[], y: Qubit, k: Int) : () {
    //     body {
    //         CNOT(x[k],y);
    //     }
    // }

    // operation DJ(n: Int, Uf: ((Qubit[],Qubit)=>())) : Bool {
    //     body {
    //         mutable ans=true;
    //         using(qs=Qubit[n+1]) {
    //             let y=qs[n];
    //             let xs=qs[0..n-1];
    //             for(i in 0..n-1) { H(xs[i]); }
    //             X(y); H(y);
    //             Uf(xs,y);
    //             for(i in 0..n-1) { H(xs[i]); }
    //             for(i in 0..n-1) {
    //                 let z=M(xs[i]);
    //                 if(z==One) { set ans=false; }
    //             }
    //             ResetAll(qs);
    //         }
    //         return ans;
    //     }
    // }

    // operation AllStates(qs: Qubit[]) : () {
    //     body {
    //         for(i in 0..Length(qs)-1) {
    //             H(qs[i]);
    //         }
    //     }
    // }

    // operation A3(qs: Qubit[],b1: Bool[],b2: Bool[]) : () {
    //     body {
    //         let n=Length(qs);
    //         mutable j=-1;
    //         for(i in 0..n-1) {
    //             if(b1[i] != b2[i]) {
    //                 set j=i;
    //             }
    //         }

    //         H(qs[j]);
    //         for(i in 0..n-1) {
    //             if(i!=j) {
    //                 if(b1[i] && b2[i]) {
    //                     X(qs[i]);
    //                 } elif(b1[i] || b2[i]) {
    //                     CNOT(qs[j],qs[i]);
    //                     if(b2[i]!=b2[j]) {
    //                         X(qs[i]);
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }


    // // operation W(qs: Qubit,k: Int) : () {
    // //     if(k==0) {
    // //         Z(qs[0]);
    // //         return;
    // //     }
    // //     let m=1<<<(k-1);
    // //     using(qq=Qubit[1]) {
    // //         let q=qq[0];

    // //     }
    // // }
    // // operation A4(qs: Qubit[]) : () { body {
    // //     mutable k=-1;
    // //     let n=Length(qs);
    // //     if(n==1) { set k=0; }
    // //     if(n==2) { set k=1; }
    // //     if(n==4) { set k=2; }
    // //     if(n==8) { set k=3; }
    // //     if(n==16) { set k=4; }

    // //     W(qs,k);
    // // }}

    // operation D1(x: Qubit[], y: Qubit,b: Int[]) : () {
    //     body {
    //         for(i in 0..Length(b)-1) {
    //             if(b[i]==1) {
    //                 CNOT(x[i],y);
    //             }
    //         }
    //     }
    // }
    // operation D2(x: Qubit[], y: Qubit,b: Int[]) : () {
    //     body {
    //         for(i in 0..Length(b)-1) {
    //             if(b[i]==1) {
    //                 CNOT(x[i],y);
    //             } else {
    //                 X(x[i]);
    //                 CNOT(x[i],y);
    //                 X(x[i]);
    //             }
    //         }
    //     }
    // }

    operation Solve(n: Int, Uf: ((Qubit[],Qubit)=>())) : Int[] {
        body {
        mutable ans=new Int[n];
            using(qs=Qubit[n+1]) {
                let y=qs[n];
                let xs=qs[0..n-1];
                for(i in 0..n-1) { H(xs[i]); }
                X(y); H(y);
                Uf(xs,y);
                for(i in 0..n-1) { H(xs[i]); }
                for(i in 0..n-1) {
                    set ans[i]=0;
                    if(M(xs[i])==One) { set ans[i]=1; }
                }
                ResetAll(qs);
            }
            return ans;
        }
    }

    // operation Tester() : () {
    //     body {
    //         let e1z=Solve(5,D1(_,_,[0;1;1;0;1]));
    //         Message($"{e1z}");

    //         using(qs2=Qubit[2]) {
    //             A3(qs2,[true;true],[true;false]);
    //             DM();ResetAll(qs2);
    //         }
    //         // let uf=UIndex(_,_,4);
    //         let uf=D2(_,_,[0;0;1;1;0]);
    //         let z5=DJ(5,uf);
    //         // let z6=DJ(6,uf);
    //         Message($"{z5}");
    //         // Message($"{z5} {z6}");
    //         using(qs=Qubit[2]) {
    //             for(k in 0..3) {
    //                 Bell(qs,k);
    //                 let z=BellM(qs);
    //                 Message($"{k}: {z}");
    //                 ResetAll(qs);
    //             }
    //         }
    //     }
    // }
}
