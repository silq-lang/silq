// https://codeforces.com/contest/1116/problem/A2
def solve[n:!ℕ](bits:(!𝔹^n)^4){
	i:=0:int[2];
	for j in [0..2){ i[j]:=H(i[j]); }
	qs:=(bits:(𝔹^n)^4)[i];
	forget(i=if qs==bits[0] then 0:int[2]
	    	 else if qs==bits[1] then 1:int[2]
	    	 else if qs==bits[2] then 2:int[2]
	         else 3:int[2]);
	return qs;
}
