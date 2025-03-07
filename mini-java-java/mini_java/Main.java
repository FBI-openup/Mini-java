package mini_java;

public class Main {

  static boolean parse_only  = false;
  static boolean type_only   = false;
  static boolean debug       = false;
  static String  file        = null;

  static void usage() {
    System.err.println("minijava [--parse-only] [--type-only] file.java");
    System.exit(1);
  }

  public static void main(String[] args) throws Exception {
     for (String arg : args)
      if (arg.equals("--parse-only"))
        parse_only = true;
      else if (arg.equals("--type-only"))
        type_only = true;
      else if (arg.equals("--debug")) {
        debug = true;
        Typing.debug = true;
        Compile.debug = true;
      } else {
        if (file != null)
          usage();
        if (!arg.endsWith(".java"))
          usage();
        file = arg;
      }
    if (file == null)
      file = "C:\\Users\\zhang\\Downloads\\mini-java-java\\mini-java-java\\test.java";

    java.io.Reader reader = new java.io.FileReader(file);
    Lexer lexer = new Lexer(reader);
    MyParser parser = new MyParser(lexer);
    try {
      PFile f = (PFile) parser.parse().value;
      if (parse_only)
        System.exit(0);
      TFile tf = Typing.file(f);
      if (type_only)
        System.exit(0);
      X86_64 asm = Compile.file(tf);
      String file_s = file.substring(0, file.length() - 2) + ".s";
      asm.printToFile(file_s);
    } catch (Exception e) {
      System.out.println(file + ":" + e.getMessage());
      System.exit(1);
    } catch (Error e) {
      System.out.println(file + ":" + e.getMessage());
      System.exit(1);
    }
  }

}
