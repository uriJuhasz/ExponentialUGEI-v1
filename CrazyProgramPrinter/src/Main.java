import java.io.PrintWriter;
import java.util.HashMap;


public class Main {
	public final int k = 8; 
	public static void main(String[] args) throws Exception{
		
//		try{
			PrintWriter w = new PrintWriter("P.bpl", "UTF-8");
			try{
				Dumper d = new Dumper(w,3);
				d.dump();
			}finally{
				w.flush();
				w.close();
			}
//		}catch (Exception e){
//			System.out.println("Exception " + e.toString());
//		}
		
	}
	
	static class Dumper
	{
		final  PrintWriter f;
		final int kk;
		final int n;
		public Dumper(PrintWriter w,int k)
		{
			this.f=w;
			this.kk=k;
			this.n = pow2(k);
		}
		final String labelName = "l";
		private int labelIndex = 0;
		private int roundNum = 0;
		public void dump()
		{
			dumpPre();
			String r0 = dumpRound();
			String r1 = dumpRound();
			f.println("   assert " + r0 + "=" + r1);
			dumpPost();
		}
		public String dumpRound()
		{
			String joinLabel = "j_" + Integer.toString(roundNum);
			String[] labelNames = new String[n];
			String[] varNames = new String[n];
			String zName = "z_" + Integer.toString(roundNum);
			for (int i=0;i<n;i++)
			{
				String varName = "x_" + Integer.toString(roundNum) + "_" + Integer.toString(i);
				declareVariable(varName);
				varNames[i] = varName;
				String ln = labelName + Integer.toString(roundNum) + "_" + Integer.toString(i);
				labelNames[i] = ln;
			}
			
			dumpGoto(labelNames);

			for (int i=0;i<n;i++)
				printJoinee(i,labelNames[i],joinLabel,zName,varNames);
			
			dumpLabel(joinLabel);
			roundNum++;
			return zName;
			
		}
		private void dumpLabel(String l) {
			f.println("   " + l + ":");
		}
		private void printJoinee(int i,String l,String joinLabel,String zName,String[] varNames) {
			dumpLabel(l);
			String a = dumpA(i);
			dumpAssignment(zName,a);
			f.println("   goto " + joinLabel + ";");
		}
		private void dumpAssignment(String zName, String a) {
			f.println("   assume " + zName + " == " + a + ";");
		}
/*		private int log2(int x)
		{
			return (int)(Math.log(x)/Math.log(2));
		}
	*/	private int pow2(int x)
		{
			int r = 1;
			for (int i=0; i<x;i++)
				r*=2;
			return r;
		}
		private String dumpA(int i) {
			String[] Si1 = getS(i,1);
			String[] Si2 = getS(i,2);
			String CSi1 = dumpT(kk+1,0,2*n-1,Si1);
			String CSi2 = dumpT(kk+1,0,2*n-1,Si2);
			String A = dumpA(i,CSi1,CSi2);
			return A;
		}
		String[] getS(int i,int b)
		{
			assert(b==1 || b==2);
			String[] r = new String[2*n];
			for (int j=0;j<2*n;j++)
				r[j]="0";
			r[2*i+b-1] = "1";
			return r;
		}
		private String dumpT(int i, int s, int e, String[] S) {
			assert (i>=0);
			assert (s>=0);
			assert (e>s);
			assert S.length >= e+1;
			String rr;
			if (i==1)
			{
				assert (e==s+1);
				rr = dumpF(S[s],S[e]);
			}else{
				int m = s+(e+1-s)/2;
				if (m-s!=e+1-m)
					System.out.print("");
				assert (m-1-s==e-m);
				String l = dumpT(i-1,s,m-1,S);
				String r = dumpT(i-1,m,e,S);
				rr = dumpF(l,r);
			}
			return rr;
		}
		private String dumpA(int i, String CSi1, String CSi2) {
			String b1 = dumpL(i,CSi1);
			String b2 = dumpL(i,CSi2);
			String j  = dumpF(b1,b2);
			String a  = dumpL(n-i,j);
			return a;
		}
		private String dumpL(int i, String e) {
			assert(i>=0);
			String r =  e;
			for (int j=0;j<i;j++)
				r = dumpF(r,r);
			return r;
		}
		private HashMap<String,String> fMap = new HashMap<String,String>();
		private int fIndex = 0;
		private String dumpF(String r1, String r2) {
			String rep = "F(" + r1  + "," + r2 + ")";
			if (fMap.containsKey(rep))
				return fMap.get(rep);
			String name = "f_" + Integer.toString(fIndex);
			fIndex++;
			f.println("   " + name + " := " + rep + ";");
			fMap.put(rep, name);
			return name;
		}
		private void dumpGoto(String[] labelNames) {
			f.print("goto ");
			boolean b = true;
			for (String ln : labelNames)
			{
				if (b)
					f.print(",");
				f.print(ln);
			}
			f.println(";");
		}
		private void declareVariable(String name) {
			f.println("   var " + name + " : Int");
		}
		private void dumpPre() {
			f.println("procedure P()");
			f.println("{");
		}
		private void dumpPost() {
			f.println("}");
		}
	}

}
