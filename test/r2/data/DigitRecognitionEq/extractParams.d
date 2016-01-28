import std.stdio, std.file, std.conv;

void main(){
	auto fin=File("nbParams.csv","r");
	foreach(i;1..11) File(text("nbParams",i,".csv"),"w").writeln(fin.readln());
}
