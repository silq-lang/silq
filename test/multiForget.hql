
def main(){
	(x,y) := (H(false),H(false));
	(a,b) := dup(x,y);
	(a,b) := (b,a);
	(c,d) := dup(a,b);
	forget((a,b)=(c,d));
	forget((d,c)=dup(x,y));
	return (x,y);
}
