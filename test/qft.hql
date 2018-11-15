def QFT[n:!N](psi:int[n]) mfree: int[n] {
   for k in [0..n){
       psi[k] := H(psi[k]);
       for l in [k+1..n){
           if psi[l] && psi[k] {
               phase(2 * 3.14 * 2^(k-l-1));
           }
   }   }
   for k in [0..n div 2) {
       (psi[k],psi[n-k-1]) := (psi[n-k-1],psi[k]);
   }
   return psi;
}
