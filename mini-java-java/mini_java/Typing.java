package mini_java;

import java.util.HashMap;
import java.util.LinkedList;
/** Typing作用: 从未检查的 AST (PFile/PClass/...) -> 生成类型化 AST (TFile/TDClass/...) */
class Typing {

  static boolean debug = false;
  static boolean hasMain = false;
  //符号表，用于存储所有已声明的类
  static HashMap<String, Class_> classTable = new HashMap<>();

  //============================================================
  // 入口：对整个文件进行类型检查，返回 TFile
  //============================================================
  static TFile file(PFile f) {
    // 1) 声明所有类 (同时检查重复声明、检查Main)
    declareClasses(f.l);

    // 2) 解析继承 (补 Object, 禁继承String, 检测环等)
    resolveInheritance(f);

    // 3) 把各个类的内容(构造函数/方法/语句等)做类型检查并构造 TDClass 列表
    LinkedList<TDClass> typedClassList = new LinkedList<>();
    for (PClass pClass : f.l) {
      TDClass tdC = typeCheckClass(pClass);
      typedClassList.add(tdC);
    }
    // 4) 最后再统一检查 Main 类 (及其 main 方法的要求)
    checkMainClass();

    // 全部完成后，返回新的 TFile
    return new TFile(typedClassList);
  }
  // 声明所有类并检查它们的唯一性
  //============================================================
  // 第一步：声明所有类
  //============================================================
  private static void declareClasses(LinkedList<PClass> classes) {
    for (PClass pc : classes) {
      String className = pc.name.id;
      // 检测重名
      if (classTable.containsKey(className)) {
        error(null, "Duplicate class: " + className);
      }
      // 创建 Class_ (还未设置 extends_)
      Class_ c_ = new Class_(className);
      classTable.put(className, c_);

      // 检查是否是 Main 类
      if ("Main".equals(className)) {
        hasMain = true;
        // 可能还要禁止 Main 继承其他类:
        if (pc.ext != null) {
          error(pc.name.loc, "Main class cannot extend another class");
        }
      }
    }
    // 如果最终没 Main，就报错
    if (!hasMain) {
      error(null, "Missing required Main class");
    }
  }
  //============================================================
  // 第二步：解析继承
  //============================================================
  private static void resolveInheritance(PFile f) {
    // 先给系统预定义类 Object, String
    classTable.putIfAbsent("Object", new Class_("Object"));
    classTable.putIfAbsent("String", new Class_("String"));

    // 遍历 table，看看有没有显式 extends
    for (Class_ c_ : classTable.values()) {
      // 跳过 Object、String 自身
      if ("Object".equals(c_.name) || "String".equals(c_.name)) {
        continue;
      }
      // 找到对应的PClass以获取它的 extends

      PClass pClass = findPClass(c_.name,f.l);
      if (pClass == null) {
        // 如果允许“有些类已放进 classTable，却在 pf.l 中没有找到”，那么 改为 continue 就可以
         error(null, "Class " + c_.name + " not found in PFile");
      }
      if (pClass.ext != null) {
        String parentName = pClass.ext.id;
        // 禁止继承String
        if ("String".equals(parentName)) {
          error(pClass.ext.loc, "Cannot inherit from String");
        }
        // 父类必须在 table 里
        Class_ parent = classTable.get(parentName);
        if (parent == null) {
          error(pClass.ext.loc, "Undefined superclass: " + parentName);
        }
        // 检测循环继承
        for (Class_ cur = parent; cur != null; cur = cur.extends_) {
          if (cur == c_) {
            error(pClass.ext.loc, "Cycle in inheritance: " + c_.name);
          }
          cur = cur.extends_;
        }
        // 设置 extends_
        c_.extends_ = parent;
      } else {
        // 没写 extends的类， 默认继承 Object（且自己不是 Object）
          c_.extends_ = classTable.get("Object");
      }
    }
  }
  private static PClass findPClass(String className, LinkedList<PClass> classes) {
    for (PClass pc : classes) {
      if (pc.name.id.equals(className)) {
        return pc;
      }
    }
    return null;
  }

  //====================================================
  // 第 3 步：类型检查每个类 -> 生成 TDClass
  //====================================================
  private static TDClass typeCheckClass(PClass pc) {
    // 从 table 里拿到 typed Class_
    Class_ c_ = classTable.get(pc.name.id);
    if (c_ == null) {
      error(pc.name.loc, "Class not found in classTable: " + pc.name.id);
    }

    // 用来存放构造函数、方法的 typed 形式 (TDconstructor/TDmethod)
    LinkedList<TDecl> decls = new LinkedList<>();

    // 遍历本类的声明列表 (属性 / 构造 / 方法)
    for (PDecl pd : pc.l) {
      if (pd instanceof PDattribute) {
        // 属性声明
        PDattribute attr = (PDattribute) pd;
        TType attType = mapPType(attr.ty);
        String attName = attr.x.id;

        // 检测重复
        if (c_.attributes.containsKey(attName)) {
          error(attr.x.loc, "Duplicate attribute: " + attName);
        }
        // 新建 typed Attribute，放进 c_.attributes
        Attribute a_ = new Attribute(attName, attType);
        c_.attributes.put(attName, a_);
        // 属性不会出现在 TDecl 里，也不需要生成 TDxxxx
      }
      else if (pd instanceof PDconstructor) {
        // 构造函数
        PDconstructor pdc = (PDconstructor) pd;
        TDconstructor tdc = typeCheckConstructor(pdc, c_);
        decls.add(tdc);
      }
      else if (pd instanceof PDmethod) {
        // 方法
        PDmethod pdm = (PDmethod) pd;
        TDmethod tdm = typeCheckMethod(pdm, c_);
        decls.add(tdm);
        // 记录到 c_.methods 中
        c_.methods.put(tdm.m.name, tdm.m);
      }
    }

    // 返回 TDClass
    return new TDClass(c_, decls);
  }

  // 构造函数检查 -> 生成 TDconstructor
  private static TDconstructor typeCheckConstructor(PDconstructor pdcon, Class_ c_) {
    // 1) 形参
    LinkedList<Variable> params = new LinkedList<>();
    for (PParam ppa : pdcon.l) {
      TType pty = mapPType(ppa.ty);
      Variable v = new Variable(ppa.x.id, pty);
      params.add(v);
    }

    // 2) 构造一个局部 env (包括形参和 this)
    HashMap<String,Variable> env = new HashMap<>();
    for (Variable v : params) {
      env.put(v.name, v);
    }
    env.put("this", new Variable("this", new TTclass(c_)));

    // 3) 类型检查构造函数体 (pdcon.s)
    TStmt body = typeCheckStmt(pdcon.s, env, c_, null/*构造函数无返回*/);

    // 4) 生成 TDconstructor
    return new TDconstructor(params, body);
  }

  // 方法检查 -> 生成 TDmethod
  private static TDmethod typeCheckMethod(PDmethod pdm, Class_ c_) {
    // 1) 如果 pdm.ty == null，说明是 void，否则用 mapPType
    TType retType = (pdm.ty == null) ? new TTvoid() : mapPType(pdm.ty);

    // 2) 方法名 + 形参
    String methodName = pdm.x.id;
    LinkedList<Variable> params = new LinkedList<>();
    HashMap<String,Variable> env = new HashMap<>();

    for (PParam pa : pdm.l) {
      TType pty = mapPType(pa.ty);
      Variable v = new Variable(pa.x.id, pty);
      params.add(v);
      env.put(v.name, v);
    }
    // 加上 this
    env.put("this", new Variable("this", new TTclass(c_)));

    // 3) 检查方法体
    TStmt body = typeCheckStmt(pdm.s, env, c_, retType);

    // 4) 新建 Method + TDmethod
    Method m_ = new Method(methodName, retType, params);
    return new TDmethod(m_, params, body);
  }

  //====================================================
  // 类型检查 stmt
  //====================================================
  private static TStmt typeCheckStmt(
          PStmt pst,
          HashMap<String, Variable> env,
          Class_ currentClass,
          TType methodRetType)
  {
    if (pst instanceof PSblock) {
      // 语句块
      PSblock pb = (PSblock) pst;
      LinkedList<TStmt> blockList = new LinkedList<>();
      // 子作用域
      HashMap<String,Variable> subEnv = new HashMap<>(env);
      for (PStmt s : pb.l) {
        TStmt t = typeCheckStmt(s, subEnv, currentClass, methodRetType);
        blockList.add(t);
      }
      return new TSblock(blockList);
    }
    else if (pst instanceof PSexpr) {
      // 表达式语句
      PSexpr psexpr = (PSexpr) pst;
      TExpr e = typeCheckExpr(psexpr.e, env, currentClass);
      return new TSexpr(e);
    }
    else if (pst instanceof PSvar) {
      // 变量声明
      PSvar sv = (PSvar) pst;
      TType vty = mapPType(sv.ty);
      Variable v = new Variable(sv.x.id, vty);

      TExpr init = null;
      if (sv.e != null) {
        init = typeCheckExpr(sv.e, env, currentClass);
        // TODO：检查 init 的类型是否能赋值给 vty
      }
      // 放进 env
      env.put(v.name, v);
      return new TSvar(v, init);
    }
    else if (pst instanceof PSif) {
      // if (e) s1 else s2
      PSif psif = (PSif) pst;
      TExpr cond = typeCheckExpr(psif.e, env, currentClass);
      // 要求 cond 的类型是 boolean
      TStmt s1 = typeCheckStmt(psif.s1, env, currentClass, methodRetType);
      TStmt s2 = null;
      if (psif.s2 != null) {
        s2 = typeCheckStmt(psif.s2, env, currentClass, methodRetType);
      }
      return new TSif(cond, s1, s2);
    }
    else if (pst instanceof PSreturn) {
      // return ...
      PSreturn psret = (PSreturn) pst;
      if (psret.e == null) {
        // return;
        if (!(methodRetType instanceof TTvoid)) {
          error(null, "Return void but method is not void");
        }
        return new TSreturn(null);
      } else {
        // return e;
        TExpr e = typeCheckExpr(psret.e, env, currentClass);
        // TODO：检查 e 的类型是否子类型于 methodRetType
        return new TSreturn(e);
      }
    }
    else if (pst instanceof PSfor) {
      // for (s1; e; s2) s3
      PSfor psfor = (PSfor) pst;
      TStmt s1 = (psfor.s1 == null)
              ? null
              : typeCheckStmt(psfor.s1, env, currentClass, methodRetType);
      TExpr cond = (psfor.e == null)
              ? null
              : typeCheckExpr(psfor.e, env, currentClass);
      TStmt s2 = (psfor.s2 == null)
              ? null
              : typeCheckStmt(psfor.s2, env, currentClass, methodRetType);
      TStmt s3 = (psfor.s3 == null)
              ? null
              : typeCheckStmt(psfor.s3, env, currentClass, methodRetType);
      return new TSfor(cond, s1, s2, s3);
    }
    error(null, "Unimplemented statement kind: " + pst.getClass());
    return null;
  }

  //====================================================
  // 类型检查 expr
  //====================================================
  private static TExpr typeCheckExpr(
          PExpr pe,
          HashMap<String, Variable> env,
          Class_ currentClass)
  {
    if (pe instanceof PEcst) {
      // 常量
      PEcst cst = (PEcst) pe;
      return new TEcst(cst.c);
    }
    else if (pe instanceof PEbinop) {
      // 二元运算
      PEbinop bin = (PEbinop) pe;
      TExpr e1 = typeCheckExpr(bin.e1, env, currentClass);
      TExpr e2 = typeCheckExpr(bin.e2, env, currentClass);
      // TODO：检查 e1,e2 类型与 bin.op 匹配
      return new TEbinop(bin.op, e1, e2);
    }
    else if (pe instanceof PEident) {
      // 标识符
      PEident pid = (PEident) pe;
      Variable v = env.get(pid.id.id);
      if (v == null) {
        // 如果没在局部变量里，可能是当前类的属性？
        Attribute a_ = currentClass.attributes.get(pid.id.id);
        if (a_ != null) {
          // 访问属性 -> TEattr( this, a_ ) ？
          // 也可以直接保留PEdot形式
          return new TEattr(new TEthis(), a_);
        }
        error(pid.id.loc, "Unknown variable or field: " + pid.id.id);
      }
      return new TEvar(v);
    }
    // ...
    error(null, "Unimplemented expr kind: " + pe.getClass());
    return null;
  }

  //====================================================
  // PType -> TType
  //====================================================
  private static TType mapPType(PType pt) {
    if (pt instanceof PTint) {
      return new TTint();
    }
    else if (pt instanceof PTboolean) {
      return new TTboolean();
    }
    else if (pt instanceof PTident) {
      // 类类型
      PTident pid = (PTident) pt;
      String cname = pid.x.id;
      Class_ c_ = classTable.get(cname);
      if (c_ == null) {
        error(pid.x.loc, "Unknown class type: " + cname);
      }
      return new TTclass(c_);
    }
    error(null, "Unsupported PType: " + pt.getClass());
    return null; // unreachable
  }

  //====================================================
  // 第 4 步：检查 Main 类 (main 方法)
  //====================================================
  private static void checkMainClass() {
    Class_ mainClass = classTable.get("Main");
    if (mainClass == null) {
      // 理论上不会，因为 hasMain = true
      error(null, "Missing Main class");
    }
    // 在 mainClass.methods 中找 "main"
    Method mainMethod = mainClass.methods.get("main");
    if (mainMethod == null) {
      error(null, "Main class must have a main() method");
    }
    // 判断是否返回 void
    if (!(mainMethod.type instanceof TTvoid)) {
      error(null, "main() must return void");
    }
    // 校验参数等细节
    if (mainMethod.params.size() != 1) {
      error(null, "main() must have exactly 1 parameter");
    }
    // ...
  }

  //============================================================
  // 工具方法：throw error
  //============================================================
  private static void error(Location loc, String msg) {
    String prefix = (loc == null) ? "" : (loc.toString() + " ");
    throw new Error(prefix + "Typing Error: " + msg);
  }
}
