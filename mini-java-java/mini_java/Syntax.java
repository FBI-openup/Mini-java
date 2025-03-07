package mini_java;
import java.util.LinkedList;
import java.util.HashMap;

/* Abstract Syntax of Mini Java */

/* Parsed trees.
   This is the output of the parser and the input of the type checker. */

/** Location in source file */
class Location {
  final int line;
  final int column;

  Location(int line, int column) {
    this.line = line+1;
    this.column = column;
  }

  @Override
  public String toString() {
    return this.line + ":" + this.column + ":";
  }
}

/** Parsed Identifier (name and location) */
class Ident {
  final String id;
  final Location loc;

  Ident(String id) {
    this.id = id;
    this.loc = null;
  }
  Ident(String id, Location loc) {
    this.id = id;
    this.loc = loc;
  }
}

/** Parsed Type */
abstract class PType {
  abstract void accept(Visitor v);
}
class PTboolean extends PType {
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PTint extends PType {
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PTident extends PType {
  final Ident x;
  PTident(Ident x) {
    this.x = x;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}

/** Unary operator */
enum Unop {
  Uneg /** -e */,
  Unot /** !e */,
  Upreinc /** ++e */, Upostinc /** e++ */,
  Upredec /** --e */, Upostdec /** e-- */,
  Ustring_of_int /** integer to string conversion,
                     introduced during type checking */
}

/** Binary operator */
enum Binop {
  Badd , Bsub , Bmul , Bdiv , Bmod,   /** + - * / % */
  Beq , Bneq , Blt , Ble , Bgt , Bge, /** == != &lt; &lt;= &gt; &gt;= */
  Band , Bor,  /** &amp;&amp; || */
  Badd_s /** string concatenation, introduced during type checking */
}

/** Constant

  This is shared between parsed and typed trees. */
abstract class Constant {
  abstract void accept(Visitor v);
}

class Cbool extends Constant {
  final boolean b;
  Cbool(boolean b) {
    this.b = b;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class Cstring extends Constant {
  final String s;
  Cstring(String s) {
    this.s = s;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class Cint extends Constant {
  final long i;
  Cint(long i) {
    this.i = i;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}

/** Parsed Expression */
abstract class PExpr {
  abstract void accept(Visitor v);
}
class PEcst extends PExpr {
  final Constant c;
  PEcst(Constant c) {
    this.c = c;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEbinop extends PExpr {
  final Binop op;
  final PExpr e1, e2;
  PEbinop(Binop op, PExpr e1, PExpr e2) {
    super();
    this.op = op;
    this.e1 = e1;
    this.e2 = e2;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEunop extends PExpr {
  final Unop op;
  final PExpr e;
  PEunop(Unop op, PExpr e) {
    super();
    this.op = op;
    this.e = e;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEthis extends PExpr {
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEnull extends PExpr {
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEident extends PExpr {
  final Ident id;

  PEident(Ident id) {
    super();
    this.id = id;
  }

  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEdot extends PExpr {
  final PExpr e;
  final Ident id;

  PEdot(PExpr e, Ident id) {
    super();
    this.e = e;
    this.id = id;
  }

  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEassignIdent extends PExpr {
  final Ident id;
  final PExpr e;

  PEassignIdent(Ident id, PExpr e) {
    super();
    this.id = id;
    this.e = e;
  }

  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEassignDot extends PExpr {
  final PExpr e1;
  final Ident id;
  final PExpr e2;

  PEassignDot(PExpr e1, Ident id, PExpr e2) {
    super();
    this.e1 = e1;
    this.id = id;
    this.e2 = e2;
  }

  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEnew extends PExpr {
  final Ident c;
  final LinkedList<PExpr> l;
  PEnew(Ident c, LinkedList<PExpr> l) {
    super();
    this.c = c;
    this.l = l;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEcall extends PExpr {
  final PExpr e;
  final Ident id;
  final LinkedList<PExpr> l;
  PEcall(PExpr e, Ident id, LinkedList<PExpr> l) {
    super();
    this.e = e;
    this.id = id;
    this.l = l;
  }
  PEcall(Ident id, LinkedList<PExpr> l) {
    this(new PEthis(), id, l);
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEcast extends PExpr {
  final PType ty;
  final PExpr e;
  PEcast(PType ty, PExpr e) {
    super();
    this.ty = ty;
    this.e = e;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PEinstanceof extends PExpr {
  final PExpr e;
  final PType ty;
  PEinstanceof(PExpr e, PType ty) {
    super();
    this.e = e;
    this.ty = ty;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}


/** Parsed Statement */
abstract class PStmt {
  abstract void accept(Visitor v);
}
class PSexpr extends PStmt {
  final PExpr e;

  PSexpr(PExpr e) {
    super();
    this.e = e;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PSvar extends PStmt {
  final PType ty;
  final Ident x;
  final PExpr e; //@ null if absent
  PSvar(PType ty, Ident x, PExpr e) {
    super();
    this.ty = ty;
    this.x = x;
    this.e = e;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PSif extends PStmt {
  final PExpr e;
  final PStmt s1, s2;
  PSif(PExpr e, PStmt s1, PStmt s2) {
    super();
    this.e = e;
    this.s1 = s1;
    this.s2 = s2;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PSreturn extends PStmt {
  final PExpr e; //@ null if absent

  PSreturn(PExpr e) {
    super();
    this.e = e;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PSblock extends PStmt {
  final LinkedList<PStmt> l;
  PSblock() {
    this.l = new LinkedList<PStmt>();
  }
  PSblock(LinkedList<PStmt> l) {
    super();
    this.l = l;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PSfor extends PStmt {
  final PStmt s1;
  final PExpr e;
  final PStmt s2;
  final PStmt s3;
  PSfor(PStmt s1, PExpr e, PStmt s2, PStmt s3) {
    super();
    this.s1 = s1;
    this.e  = e;
    this.s2 = s2;
    this.s3 = s3;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}

/** Parsed Parameter */
class PParam {
  final PType ty;
  final Ident x;
  PParam(PType ty, Ident x) {
    super();
    this.ty = ty;
    this.x  = x;
  }
}

/** Parsed Declaration (attribute, constructor, or method) */
abstract class PDecl {
  abstract void accept(Visitor v);
}
class PDattribute extends PDecl {
  final PType ty;
  final Ident x;

  PDattribute(PType ty, Ident x) {
    super();
    this.ty = ty;
    this.x  = x;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PDconstructor extends PDecl {
  final Ident x;
  final LinkedList<PParam> l;
  final PStmt s;

  PDconstructor(Ident x, LinkedList<PParam> l, PStmt s) {
    super();
    this.x = x;
    this.l = l;
    this.s = s;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}
class PDmethod extends PDecl {
  final PType ty; //@ or null if void
  final Ident x;
  final LinkedList<PParam> l;
  final PStmt s;

  PDmethod(PType ty, Ident x, LinkedList<PParam> l, PStmt s) {
    super();
    this.ty = ty;
    this.x = x;
    this.l = l;
    this.s = s;
  }
  @Override
  void accept(Visitor v) { v.visit(this); }
}

/** Parsed Class */
class PClass {
  final Ident name;
  final Ident ext; //@ extends, or null if none
  final LinkedList<PDecl> l;
  PClass(Ident name, Ident ext, LinkedList<PDecl> l) {
    super();
    this.name = name;
    this.ext = ext;
    this.l = l;
  }
}

class PFile {
  final LinkedList<PClass> l;

  PFile(LinkedList<PClass> l) {
    super();
    this.l = l;
  }
}

/** Visitor for the parsed trees

   (feel free to modify it for your needs) */
interface Visitor {
  void visit(PTboolean t);
  void visit(PTint t);
  void visit(PTident t);

  void visit(Cbool c);
  void visit(Cstring c);
  void visit(Cint c);

  void visit(PEcst e);
  void visit(PEbinop e);
  void visit(PEunop e);
  void visit(PEthis e);
  void visit(PEnull e);
  void visit(PEident e);
  void visit(PEassignIdent e);
  void visit(PEdot e);
  void visit(PEassignDot e);
  void visit(PEnew e);
  void visit(PEcall e);
  void visit(PEcast e);
  void visit(PEinstanceof e);

  void visit(PSexpr s);
  void visit(PSvar s);
  void visit(PSif s);
  void visit(PSreturn s);
  void visit(PSblock s);
  void visit(PSfor s);

  void visit(PDattribute s);
  void visit(PDconstructor s);
  void visit(PDmethod s);
}

/* Typed trees.

   This is the output of the type checker and the input of the code
   generation.

   In the typed trees, identifiers (objects of class `Ident` above)
   are now turned into objects of class `Variable` / `Method` /
   `Class_` / `Attribute`.
*/

/** Typed Type */
abstract class TType {
  abstract void accept(TVisitor v);
}
class TTvoid extends TType {
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TTnull extends TType {
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TTboolean extends TType {
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TTint extends TType {
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TTclass extends TType {
  final Class_ c;
  TTclass(Class_ c) {
    this.c = c;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}

/** Typed Class

 (Called Class_ to avoid the confusion with java.lang.Class.) */
class Class_ {
  final String name;
  Class_ extends_;
  final HashMap<String, Method> methods;
  final HashMap<String, Attribute> attributes;

  Class_(String name) {
    this.name = name;
    this.extends_ = null;
    this.methods = new HashMap<>();
    this.attributes = new HashMap<>();
  }
}

/** Method */
class Method {
  final String name;
  final TType type;
  final LinkedList<Variable> params;

  Method(String name, TType type, LinkedList<Variable> params) {
    this.name = name;
    this.type = type;
    this.params = params;
  }
}

/** Variable

   In the typed trees, all the occurrences of the same variable
   point to a single object of the following class. */
class Variable {
  final String name; //@ for debugging purposes
  final TType ty;    //@ type
  int ofs;           //@ position wrt %rbp, to be set later

  Variable(String name, TType ty) {
    this.name = name;
    this.ty   = ty;
    this.ofs  = -1; // will be set later, during code generation
  }
}

/** Attribute

  Similarly, all the occurrences of a given attribute
   point to a single object of the following class. */
class Attribute {
  final String name;
  final TType ty;
  int ofs;           //@ position within the object

  Attribute(String name, TType ty) {
    this.name = name;
    this.ty   = ty;
    this.ofs  = -1; // will be set later, during code generation
  }
}

/** Typed Expression */
abstract class TExpr {
  abstract void accept(TVisitor v);
}
class TEcst extends TExpr {
  final Constant c;
  TEcst(Constant c) {
    this.c = c;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEbinop extends TExpr {
  final Binop op;
  final TExpr e1, e2;
  TEbinop(Binop op, TExpr e1, TExpr e2) {
    super();
    this.op = op;
    this.e1 = e1;
    this.e2 = e2;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEunop extends TExpr {
  final Unop op;
  final TExpr e;
  TEunop(Unop op, TExpr e) {
    super();
    this.op = op;
    this.e = e;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEthis extends TExpr {
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEnull extends TExpr {
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEvar extends TExpr {
  final Variable x;
  TEvar(Variable x) {
    this.x = x;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEassignVar extends TExpr {
  final Variable x;
  final TExpr e;
  TEassignVar(Variable x, TExpr e) {
    this.x = x;
    this.e = e;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEattr extends TExpr {
  final TExpr e;
  final Attribute a;
  TEattr(TExpr e, Attribute a) {
    this.e = e;
    this.a = a;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEassignAttr extends TExpr {
  final TExpr e1;
  final Attribute a;
  final TExpr e2;
  TEassignAttr(TExpr e1, Attribute a, TExpr e2) {
    this.e1 = e1;
    this.a = a;
    this.e2 = e2;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEnew extends TExpr {
  final Class_ cl;
  final LinkedList<TExpr> l;
  TEnew(Class_ cl, LinkedList<TExpr> l) {
    super();
    this.cl = cl;
    this.l = l;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEcall extends TExpr {
  final TExpr e;
  final Method m;
  final LinkedList<TExpr> l;
  TEcall(TExpr e, Method m, LinkedList<TExpr> l) {
    super();
    this.e = e;
    this.m = m;
    this.l = l;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEcast extends TExpr {
  final TType ty;
  final TExpr e;

  TEcast(TType ty, TExpr e) {
    super();
    this.ty = ty;
    this.e = e;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEinstanceof extends TExpr {
  final TExpr e;
  final TType ty;

  TEinstanceof(TExpr e, TType ty) {
    super();
    this.e = e;
    this.ty = ty;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TEprint extends TExpr {
  final TExpr e;

  TEprint(TExpr e) {
    super();
    this.e = e;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}

/** Typed Statement */
abstract class TStmt {
  abstract void accept(TVisitor v);
}
class TSexpr extends TStmt {
  final TExpr e;
  TSexpr(TExpr e) {
    super();
    this.e = e;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TSvar extends TStmt {
  final Variable v;
  final TExpr e;
  TSvar(Variable v, TExpr e) {
    super();
    this.v = v;
    this.e = e;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TSif extends TStmt {
  final TExpr e;
  final TStmt s1, s2;
  TSif(TExpr e, TStmt s1, TStmt s2) {
    super();
    this.e = e;
    this.s1 = s1;
    this.s2 = s2;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TSreturn extends TStmt {
  final TExpr e;

  TSreturn(TExpr e) {
    super();
    this.e = e;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TSblock extends TStmt {
  final LinkedList<TStmt> l;
  TSblock() {
    this.l = new LinkedList<TStmt>();
  }
  TSblock(LinkedList<TStmt> l) {
    super();
    this.l = l;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TSfor extends TStmt {
  final TExpr e;
  final TStmt s1, s2, s3;
  TSfor(TExpr e, TStmt s1, TStmt s2, TStmt s3) {
    super();
    this.e = e;
    this.s1 = s1;
    this.s2 = s2;
    this.s3 = s3;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}


/** Typed Declaration */
abstract class TDecl {
  abstract void accept(TVisitor v);
}
class TDconstructor extends TDecl {
  final LinkedList<Variable> params;
  final TStmt s;

  TDconstructor(LinkedList<Variable> params, TStmt s) {
    super();
    this.params = params;
    this.s = s;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}
class TDmethod extends TDecl {
  final Method m;
  final TStmt s;

  TDmethod(Method m, LinkedList<Variable> params, TStmt s) {
    super();
    this.m = m;
    this.s = s;
  }
  @Override
  void accept(TVisitor v) { v.visit(this); }
}

/** Declaration of a class, with its own declarations inside. */
class TDClass {
  final Class_ c;
  final LinkedList<TDecl> l;

  TDClass(Class_ c, LinkedList<TDecl> l) {
    super();
    this.c = c;
    this.l = l;
  }
}

/** Typed File */
class TFile {
  final LinkedList<TDClass> l;

  TFile(LinkedList<TDClass> l) {
    super();
    this.l = l;
  }
}

/* visitor for the typed trees
   (feel free to modify it for your needs) */

interface TVisitor {
  void visit(TTvoid t);
  void visit(TTnull t);
  void visit(TTboolean t);
  void visit(TTint t);
  void visit(TTclass t);

  void visit(Cbool c);
  void visit(Cstring c);
  void visit(Cint c);

  void visit(TEcst e);
  void visit(TEbinop e);
  void visit(TEunop e);
  void visit(TEthis e);
  void visit(TEnull e);
  void visit(TEvar e);
  void visit(TEassignVar e);
  void visit(TEattr e);
  void visit(TEassignAttr e);
  void visit(TEnew e);
  void visit(TEcall e);
  void visit(TEcast e);
  void visit(TEinstanceof e);
  void visit(TEprint e);

  void visit(TSexpr s);
  void visit(TSvar s);
  void visit(TSif s);
  void visit(TSreturn s);
  void visit(TSblock s);
  void visit(TSfor s);

  void visit(TDconstructor d);
  void visit(TDmethod d);
}
