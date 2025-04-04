package mini_java;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
public class Compile {
  static boolean debug=false;
  static int labelCount=0;
  static String currentReturnType=null;
  private static Map<String, ClassInfo> classInfoMap = new HashMap<>();
  private static class ClassInfo{
    String name;
    String parent;
    Map<String, Integer> attributeOffsets = new HashMap<>();
    Map<String, Integer> methodOffsets = new HashMap<>();
    Map<String, String> methodReturnTypes = new HashMap<>();
    Map<String, List<String>> methodParamTypes = new HashMap<>();
    int attributeCount = 0;
    int methodCount = 0;
  }
  public static X86_64 file(TFile file){
    X86_64 code = new X86_64();
    buildClassDescriptors(file);
    addLibraryWrappers(code);
    generateClassDescriptors(code);
    generateClassCode(file,code);
    return code;
  }
  private static void buildClassDescriptors(TFile file) {
    for (TDClass tdc : file.l) {
      ClassInfo ci = new ClassInfo();
      ci.name = tdc.c.name;
      ci.parent = (tdc.c.extends_ != null) ? tdc.c.extends_.name : "Object";
      classInfoMap.put(tdc.c.name, ci);
      computeOffsets(tdc);
    }
  }
  private static void computeOffsets(TDClass tdc) {
    ClassInfo ci = classInfoMap.get(tdc.c.name);
    if (!ci.parent.equals("Object")) {
      ClassInfo parentInfo = classInfoMap.get(ci.parent);
      ci.attributeCount = parentInfo.attributeCount;
      ci.attributeOffsets.putAll(parentInfo.attributeOffsets);
      ci.methodCount = parentInfo.methodCount;
      ci.methodOffsets.putAll(parentInfo.methodOffsets);
      ci.methodReturnTypes.putAll(parentInfo.methodReturnTypes);
      ci.methodParamTypes.putAll(parentInfo.methodParamTypes);
    }
    for (String attrName : tdc.c.attributes.keySet()) {
      if (!ci.attributeOffsets.containsKey(attrName)) {
        ci.attributeOffsets.put(attrName, ci.attributeCount+1); 
        ci.attributeCount++;
      }
    }
    for (String methodName : tdc.c.methods.keySet()) {
      Method method = tdc.c.methods.get(methodName);
      if (!ci.methodOffsets.containsKey(methodName)) {
        ci.methodOffsets.put(methodName, ci.methodCount);
        ci.methodCount++;
      }
      ci.methodReturnTypes.put(methodName, typeToString(method.type));
      List<String> paramTypes = new ArrayList<>();
      for (Variable param : method.params) {
        paramTypes.add(typeToString(param.ty));
      }
      ci.methodParamTypes.put(methodName, paramTypes);
    }
    for (TDecl decl : tdc.l) {
      if (decl instanceof TDconstructor) {
        TDconstructor constructor = (TDconstructor) decl;
        List<String> paramTypes = new ArrayList<>();
        for (Variable param : constructor.params) {
          paramTypes.add(typeToString(param.ty));
        }
        ci.methodParamTypes.put(tdc.c.name, paramTypes);
        break;
      }
    }
  }
  private static String typeToString(TType type) {
    if (type instanceof TTvoid) return "void";
    if (type instanceof TTnull) return "null";
    if (type instanceof TTboolean) return "boolean";
    if (type instanceof TTint) return "int";
    if (type instanceof TTclass) return ((TTclass)type).c.name;
    return "unknown";
  }
  private static void generateClassDescriptors(X86_64 code) {
    for (Map.Entry<String, ClassInfo> entry : classInfoMap.entrySet()) {
      String className = entry.getKey();
      ClassInfo ci = entry.getValue();
      code.dlabel("class_" + className);
      code.data(".quad class_" + ci.parent);
      String[] table = new String[ci.methodCount];
      for (Map.Entry<String, Integer> e : ci.methodOffsets.entrySet()) {
        table[e.getValue()] = className + "_" + e.getKey();
      }
      for (int i = 0; i < table.length; i++) {
        code.data(".quad " + table[i]);
      }
    }
    if (!classInfoMap.containsKey("String")) {
      code.dlabel("class_String");
      code.data(".quad class_Object");
    }
    if (!classInfoMap.containsKey("Object")) {
      code.dlabel("class_Object");
      code.data(".quad 0");
    }
  }
  private static void generateClassCode(TFile file, X86_64 code) {
  for (TDClass tdc : file.l) {
    boolean hasConstructor = false;
    ClassInfo ci = classInfoMap.get(tdc.c.name);
    Map<String, Boolean> processedMethods = new HashMap<>();
    for (TDecl decl : tdc.l) {
      if (decl instanceof TDconstructor) {
        TDconstructor constructor = (TDconstructor) decl;
        generateConstructor(tdc, constructor, code);
        hasConstructor = true;
      } else if (decl instanceof TDmethod) {
        TDmethod tdMethod = (TDmethod) decl;
        String methodName = tdMethod.m.name;
        processedMethods.put(methodName, true);
        generateMethod(tdc, tdMethod, code);
      }
    }
    if (!hasConstructor) {
      generateDefaultConstructor(tdc, code);
    }
  }
    generateMainFunction(file, code);
  }
private static void generateDefaultConstructor(TDClass tdc, X86_64 code) {
  ClassInfo ci = classInfoMap.get(tdc.c.name);
  if (ci == null) {
    return;
  }
  String label = ci.name + "_" + ci.name;
  code.label(label);
  code.pushq("%rbp");
  code.pushq("%r12");
  code.movq("%rsp", "%rbp");
  int objectSize = (ci.attributeCount + 1) * 8;
  code.movq("$" + objectSize, "%rdi");
  code.call("my_malloc");
  String allocOkLabel = freshLabel("alloc_ok");
  code.cmpq("$0", "%rax");
  code.jne(allocOkLabel);
  generateRuntimeError(code, "memory allocation failed");
  code.label(allocOkLabel);
  code.movq("$class_" + ci.name, "(%rax)");
  code.movq("%rax", "%r12");
  for (Map.Entry<String, Integer> attr : ci.attributeOffsets.entrySet()) {
    code.movq("$0", attr.getValue() * 8 + "(%r12)");
  }
  if (!ci.parent.equals("Object")) {
    code.movq("%r12", "%rdi");  
    code.call(ci.parent + "_" + ci.parent);
  }
  code.movq("%r12", "%rax");
  code.movq("%rbp", "%rsp");
  code.popq("%r12");  
  code.popq("%rbp");
  code.ret();
}
  private static void generateConstructor(TDClass tdc, TDconstructor constructor, X86_64 code) {
    ClassInfo ci = classInfoMap.get(tdc.c.name);
    if (ci == null) {
      generateRuntimeError(code, "Class info not found: " + tdc.c.name);
      return;
    }
    String label = ci.name + "_" + ci.name;
    code.label(label);
    code.pushq("%rbp");
    code.pushq("%r12");  
    code.movq("%rsp", "%rbp");
    Map<String, Integer> localVarOffsets = new HashMap<>();
    int localVarCount = 0;
    for (int i = 0; i < constructor.params.size(); i++) {
      Variable param = constructor.params.get(i);
      localVarOffsets.put(param.name, 24+i*8);
    }
    if (constructor.s instanceof TSblock) {
      TSblock block = (TSblock)constructor.s;
      for (TStmt stmt : block.l) {
        localVarCount = countLocalVariables(stmt, localVarOffsets, localVarCount);
      }
    } else {
      localVarCount = countLocalVariables(constructor.s, localVarOffsets, localVarCount);
    }
    if (localVarCount > 0) {
      code.subq("$"+(localVarCount*8), "%rsp");
    }
    int objectSize = (ci.attributeCount + 1) * 8;  
    code.movq("$" + objectSize, "%rdi");
    code.call("my_malloc");
    String allocOkLabel = freshLabel("alloc_ok");
    code.cmpq("$0", "%rax");
    code.jne(allocOkLabel);
    generateRuntimeError(code, "memory allocation failed");
    code.label(allocOkLabel);
    code.movq("$class_" + ci.name, "(%rax)");
    code.movq("%rax", "%r12");
    for (Map.Entry<String, Integer> attr : ci.attributeOffsets.entrySet()) {
      code.movq("$0", attr.getValue() * 8 + "(%r12)");
    }
    if (!ci.parent.equals("Object")) {
      ClassInfo parentInfo = classInfoMap.get(ci.parent);
      List<String> parentParamTypes = parentInfo.methodParamTypes.get(ci.parent);
      int parentParamCount = (parentParamTypes != null) ? parentParamTypes.size() : 0;
      String[] paramRegs = {"%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"};
      code.movq("%r12", paramRegs[0]);
      int paramLimit = Math.min(parentParamCount, Math.min(5, constructor.params.size()));
      for (int i = 0; i < paramLimit; i++) {
        code.movq(localVarOffsets.get(constructor.params.get(i).name) + "(%rbp)", paramRegs[i+1]);
      }
      if (parentParamCount > 6) {
        for (int i = Math.min(parentParamCount, constructor.params.size()) - 1; i >= 6; i--) {
          code.movq(localVarOffsets.get(constructor.params.get(i).name) + "(%rbp)", "%rax");
          code.pushq("%rax");
        }
      }
      code.call(ci.parent + "_" + ci.parent);
      if (parentParamCount > 6) {
        int stackParams = Math.min(parentParamCount - 6, constructor.params.size() - 6);
        if (stackParams > 0) {
          code.addq("$" + (stackParams * 8), "%rsp");
        }
      }
    }
    if (constructor.s instanceof TSblock) {
      TSblock block = (TSblock)constructor.s;
      for (TStmt stmt : block.l) {
        generateStmt(stmt, code, localVarOffsets, ci.name);
      }
    } else {
      generateStmt(constructor.s, code, localVarOffsets, ci.name);
    }
    code.movq("%r12", "%rax");
    code.movq("%rbp", "%rsp");
    code.popq("%r12");  
    code.popq("%rbp");
    code.ret();
  }
  private static void generateMethod(TDClass c, TDmethod method, X86_64 code) {
    Method m = method.m;
    String label = c.c.name + "_" + m.name;
    code.label(label);
    currentReturnType = typeToString(m.type);
    code.pushq("%rbp");
    code.movq("%rsp", "%rbp");
    Map<String, Integer> localVarOffsets = new HashMap<>();
    int localVarCount = 0;
    localVarOffsets.put("this", 16);  
    for (int i = 0; i < m.params.size(); i++) {
      Variable param = m.params.get(i);
      localVarOffsets.put(param.name, 16 + (i + 1) * 8);  
    }
    if (method.s instanceof TSblock) {
      TSblock block = (TSblock)method.s;
      for (TStmt stmt : block.l) {
        localVarCount = countLocalVariables(stmt, localVarOffsets, localVarCount);
      }
    } else {
      localVarCount = countLocalVariables(method.s, localVarOffsets, localVarCount);
    }
    if (localVarCount > 0) {
      code.subq("$"+(localVarCount*8), "%rsp");
    }
    generateStmt(method.s, code, localVarOffsets, c.c.name);
    if (typeToString(m.type).equals("void")) {
      code.leave();
      code.ret();
    }
    currentReturnType = null;
  }
  private static void generateMainFunction(TFile file, X86_64 code) {
    code.globl("main");
    code.label("main");
    code.pushq("%rbp");
    code.movq("%rsp", "%rbp");
    boolean foundMainMethod = false;
    for (TDClass tdc : file.l) {
      if (tdc.c.name.equals("Main")) {
        for (TDecl decl : tdc.l) {
          if (decl instanceof TDmethod) {
            TDmethod tdMethod = (TDmethod) decl;
            if (tdMethod.m.name.equals("main") && 
                tdMethod.m.type instanceof TTvoid &&
                (tdMethod.m.params == null || tdMethod.m.params.isEmpty())) {
              foundMainMethod = true;
              code.call("Main_main");
              break;
            }
          }
        }
        break;
      }
    }
    if (!foundMainMethod) {
        code.emit("; No main method found in Main class");
    }
    code.movq("$0", "%rax");
    code.leave();
    code.ret();
}
  private static int countLocalVariables(TStmt stmt, Map<String, Integer> offsets, int count) {
    if (stmt instanceof TSblock) {
      TSblock block = (TSblock) stmt;
      for (TStmt s : block.l) {
        count = countLocalVariables(s, offsets, count);
      }
    } else if (stmt instanceof TSif) {
      TSif ifStmt = (TSif) stmt;
      count = countLocalVariables(ifStmt.s1, offsets, count);
      if (ifStmt.s2 != null) {
        count = countLocalVariables(ifStmt.s2, offsets, count);
      }
    } else if (stmt instanceof TSfor) {
      TSfor forStmt = (TSfor) stmt;
      count = countLocalVariables(forStmt.s1, offsets, count);
      count = countLocalVariables(forStmt.s2, offsets, count);
      count = countLocalVariables(forStmt.s3, offsets, count);
    } else if (stmt instanceof TSvar) {
      TSvar varDecl = (TSvar) stmt;
      if (!offsets.containsKey(varDecl.v.name)) {
        offsets.put(varDecl.v.name, -(++count) * 8);  
      }
    }
    return count;
  }
  /**
   * Generate code for a statement
   */
  private static void generateStmt(TStmt stmt, X86_64 code, Map<String, Integer> localVars, String className) {
    if (stmt instanceof TSexpr) {
      TSexpr exprStmt = (TSexpr) stmt;
      generateExpression(exprStmt.e, code, localVars, className);
      code.addq("$8", "%rsp");
    }
    else if (stmt instanceof TSvar) {
      TSvar varDecl = (TSvar) stmt;
      if (varDecl.e != null) {
        generateExpression(varDecl.e, code, localVars, className);
        code.popq("%rax");
        code.movq("%rax", localVars.get(varDecl.v.name) + "(%rbp)");
      }
    }
    else if (stmt instanceof TSif) {
      TSif ifStmt = (TSif) stmt;
      String elseLabel = freshLabel("else");
      String endLabel = freshLabel("endif");
      generateExpression(ifStmt.e, code, localVars, className);
      code.popq("%rax");
      code.cmpq("$0", "%rax");
      code.je(elseLabel);
      generateStmt(ifStmt.s1, code, localVars, className);
      code.jmp(endLabel);
      code.label(elseLabel);
      if (ifStmt.s2 != null) {
        generateStmt(ifStmt.s2, code, localVars, className);
      }
      code.label(endLabel);
    } else if (stmt instanceof TSfor) {
      TSfor forStmt = (TSfor) stmt;
      String startLabel = freshLabel("for_start");
      String bodyLabel = freshLabel("for_body");
      String updateLabel = freshLabel("for_update");
      String endLabel = freshLabel("for_end");
      generateStmt(forStmt.s1, code, localVars, className);  
      code.jmp(startLabel);
      code.label(startLabel);
      generateExpression(forStmt.e, code, localVars, className);  
      code.popq("%rax");
      code.cmpq("$0", "%rax");
      code.je(endLabel);
      code.jmp(bodyLabel);
      code.label(bodyLabel);
      generateStmt(forStmt.s2, code, localVars, className);  
      code.jmp(updateLabel);
      code.label(updateLabel);
      generateStmt(forStmt.s3, code, localVars, className);  
      code.jmp(startLabel);
      code.label(endLabel);
    } else if (stmt instanceof TSblock) {
      TSblock block = (TSblock) stmt;
      for (TStmt s : block.l) {
        generateStmt(s, code, localVars, className);
      }
    } else if (stmt instanceof TSreturn) {
      TSreturn ret = (TSreturn) stmt;
      if (ret.e != null) {
        generateExpression(ret.e, code, localVars, className);
        code.popq("%rax");
      } else {
        code.xorq("%rax", "%rax");
      }
      code.leave();
      code.ret();
    }
  }
  private static void generateExpression(TExpr expr, X86_64 code, Map<String, Integer> localVars, String className) {
    if (expr instanceof TEcst) {
      TEcst cstExpr = (TEcst) expr;
      Constant c = cstExpr.c;
      if (c instanceof Cint) {
        Cint intConst = (Cint) c;
        code.pushq("$" + intConst.i);
      } else if (c instanceof Cstring) {
        Cstring strConst = (Cstring) c;
        String stringLabel = freshLabel("str");
        code.dlabel(stringLabel);
        code.string(strConst.s);
        code.movq("$16", "%rdi");  
        code.call("my_malloc");
        code.movq("$class_String", "(%rax)");
        code.movq("$" + stringLabel, "8(%rax)");
        code.pushq("%rax");
      } else if (c instanceof Cbool) {
        Cbool boolConst = (Cbool) c;
        code.pushq("$" + (boolConst.b ? 1 : 0));
      }
    } else if (expr instanceof TEnull) {
      code.pushq("$0");  
    } else if (expr instanceof TEthis) {
      code.movq(localVars.get("this") + "(%rbp)", "%rax");
      code.pushq("%rax");
    } else if (expr instanceof TEvar) {
      TEvar varExpr = (TEvar) expr;
      String name = varExpr.x.name;
      if (name.equals("System")) {
        if (!classInfoMap.containsKey("System")) {
          ClassInfo systemInfo = new ClassInfo();
          systemInfo.name = "System";
          systemInfo.parent = "Object";
          systemInfo.attributeOffsets.put("out", 1);
          systemInfo.attributeCount = 1;
          classInfoMap.put("System", systemInfo);
          code.dlabel("class_System");
          code.data(".quad class_Object");
        }
        code.movq("$16", "%rdi");  
        code.call("my_malloc");
        code.movq("$class_System", "(%rax)");
        code.movq("$16", "%rdi");
        code.call("my_malloc");
        code.movq("$class_PrintStream", "(%rax)");
        code.pushq("%rax");
        return;
      }
      if (localVars.containsKey(name)) {
        code.movq(localVars.get(name) + "(%rbp)", "%rax");
      } else {
        code.movq(localVars.get("this") + "(%rbp)", "%rax");
        ClassInfo ci = classInfoMap.get(className);
        if (ci == null) {
            generateRuntimeError(code, "Class not found: " + className);
            code.pushq("$0");  
            return;
        }
        if (!ci.attributeOffsets.containsKey(name)) {
            generateRuntimeError(code, "Attribute not found: " + name + " in class " + className);
            code.pushq("$0");  
            return;
        }
        int offset = ci.attributeOffsets.get(name);
        code.movq(offset * 8 + "(%rax)", "%rax");
      }
      code.pushq("%rax");
    } else if (expr instanceof TEattr) {
      TEattr attrExpr = (TEattr) expr;
      generateExpression(attrExpr.e, code, localVars, className);
      code.popq("%rax");
      String nonNullLabel = freshLabel("non_null");
      code.cmpq("$0", "%rax");
      code.jne(nonNullLabel);
      generateRuntimeError(code, "null pointer exception");
      code.label(nonNullLabel);
      code.movq("(%rax)", "%rcx");
      int offset = attrExpr.a.ofs;
      code.movq(offset * 8 + "(%rax)", "%rax");
      code.pushq("%rax");
    } else if (expr instanceof TEassignVar) {
      TEassignVar assignExpr = (TEassignVar) expr;
      String name = assignExpr.x.name;
      generateExpression(assignExpr.e, code, localVars, className);
      if (localVars.containsKey(name)) {
        code.popq("%rax");
        code.movq("%rax", localVars.get(name) + "(%rbp)");
        code.pushq("%rax");
      } else {
        code.popq("%rax");  
        code.movq(localVars.get("this") + "(%rbp)", "%rcx");
        ClassInfo ci = classInfoMap.get(className);
        int offset = ci.attributeOffsets.get(name);
        code.movq("%rax", offset * 8 + "(%rcx)");
        code.pushq("%rax");
      }
    } else if (expr instanceof TEassignAttr) {
      TEassignAttr attrAssignExpr = (TEassignAttr) expr;
      generateExpression(attrAssignExpr.e1, code, localVars, className);
      generateExpression(attrAssignExpr.e2, code, localVars, className);
      code.popq("%rax");  
      code.popq("%rcx");  
      String nonNullLabel = freshLabel("non_null");
      code.cmpq("$0", "%rcx");
      code.jne(nonNullLabel);
      generateRuntimeError(code, "null pointer exception");
      code.label(nonNullLabel);
      int offset = attrAssignExpr.a.ofs;
      code.movq("%rax", offset * 8 + "(%rcx)");
      code.pushq("%rax");
    }else if (expr instanceof TEcall) {
      TEcall callExpr = (TEcall) expr;
      generateVirtualMethodCall(callExpr, code, localVars, className);
    }else if (expr instanceof TEnew) {
      TEnew newExpr = (TEnew) expr;
      for (int i = newExpr.l.size() - 1; i >= 0; i--) {
        generateExpression(newExpr.l.get(i), code, localVars, className);
      }
      code.call(newExpr.cl.name + "_" + newExpr.cl.name);
      if (newExpr.l.size() > 0) {
        code.addq("$" + (newExpr.l.size() * 8), "%rsp");
      }
      code.pushq("%rax");
    } else if (expr instanceof TEunop) {
      TEunop unaryExpr = (TEunop) expr;
      generateExpression(unaryExpr.e, code, localVars, className);
      code.popq("%rax");
      if (unaryExpr.op == Unop.Uneg) {
        code.negq("%rax");
      } else if (unaryExpr.op == Unop.Unot) {
        code.xorq("$1", "%rax");  
      }
      code.pushq("%rax");
    } else if (expr instanceof TEbinop) {
      TEbinop binExpr = (TEbinop) expr;
      generateExpression(binExpr.e1, code, localVars, className);
      generateExpression(binExpr.e2, code, localVars, className);
      code.popq("%rbx");  
      code.popq("%rax");  
      switch (binExpr.op) {
        case Badd:
          code.addq("%rbx", "%rax");
          break;
        case Bsub:
          code.subq("%rbx", "%rax");
          break;
        case Bmul:
          code.imulq("%rbx", "%rax");
          break;
        case Bdiv:
          String nonZeroLabel = freshLabel("non_zero");
          code.cmpq("$0", "%rbx");
          code.jne(nonZeroLabel);
          generateRuntimeError(code, "division by zero");
          code.label(nonZeroLabel);
          code.cqto();  
          code.idivq("%rbx");  
          break;
        case Bmod:
          String nonZeroMod = freshLabel("non_zero_mod");
          code.cmpq("$0", "%rbx");
          code.jne(nonZeroMod);
          generateRuntimeError(code, "division by zero");
          code.label(nonZeroMod);
          code.cqto();  
          code.idivq("%rbx");  
          code.movq("%rdx", "%rax");  
          break;
        case Beq:
          code.cmpq("%rbx", "%rax");
          code.sete("%al");
          code.movzbq("%al", "%rax");
          break;
        case Bneq:
          code.cmpq("%rbx", "%rax");
          code.setne("%al");
          code.movzbq("%al", "%rax");
          break;
        case Blt:
          code.cmpq("%rbx", "%rax");
          code.setl("%al");
          code.movzbq("%al", "%rax");
          break;
        case Ble:
          code.cmpq("%rbx", "%rax");
          code.setle("%al");
          code.movzbq("%al", "%rax");
          break;
        case Bgt:
          code.cmpq("%rbx", "%rax");
          code.setg("%al");
          code.movzbq("%al", "%rax");
          break;
        case Bge:
          code.cmpq("%rbx", "%rax");
          code.setge("%al");
          code.movzbq("%al", "%rax");
          break;
        case Band:
          String falseLabel = freshLabel("and_false");
          String endLabel = freshLabel("and_end");
          code.cmpq("$0", "%rax");
          code.je(falseLabel);
          code.cmpq("$0", "%rbx");
          code.je(falseLabel);
          code.movq("$1", "%rax");
          code.jmp(endLabel);
          code.label(falseLabel);
          code.xorq("%rax", "%rax");
          code.label(endLabel);
          break;
        case Bor:
          String trueLabel = freshLabel("or_true");
          String endOrLabel = freshLabel("or_end");
          code.cmpq("$0", "%rax");
          code.jne(trueLabel);
          code.cmpq("$0", "%rbx");
          code.jne(trueLabel);
          code.xorq("%rax", "%rax");
          code.jmp(endOrLabel);
          code.label(trueLabel);
          code.movq("$1", "%rax");
          code.label(endOrLabel);
          break;
        case Badd_s:
          generateStringConcat(binExpr, code, localVars, className);
          return;
      }
      code.pushq("%rax");
    }
  }
  private static void generateVirtualMethodCall(TEcall callExpr, X86_64 code, Map<String, Integer> localVars, String className) {
    generateExpression(callExpr.e, code, localVars, className);
    int argCount = callExpr.l.size();
    for (int i = argCount - 1; i >= 0; i--) {
      generateExpression(callExpr.l.get(i), code, localVars, className);
    }
    String methodName = callExpr.m.name;
    int methodOffset = -1;
    ClassInfo ci = classInfoMap.get(className);
    if (ci != null && ci.methodOffsets.containsKey(methodName)) {
      methodOffset = ci.methodOffsets.get(methodName);
    } else {
      ClassInfo currentCi = classInfoMap.get(className);
      while (currentCi != null && methodOffset == -1) {
        if (currentCi.methodOffsets.containsKey(methodName)) {
          methodOffset = currentCi.methodOffsets.get(methodName);
          break;
        }
        if ("Object".equals(currentCi.parent)) {
          currentCi = classInfoMap.get("Object");
          if (currentCi != null && currentCi.methodOffsets.containsKey(methodName)) {
            methodOffset = currentCi.methodOffsets.get(methodName);
          }
          break;
        }
        currentCi = classInfoMap.get(currentCi.parent);
      }
      if (methodOffset == -1) {
        generateRuntimeError(code, "Method not found: " + methodName);
        return;
      }
    }
    String[] paramRegs = {"%rsi", "%rdx", "%rcx", "%r8", "%r9"};
    for (int i = 0; i < Math.min(5, argCount); i++) {
      code.popq(paramRegs[i]);
    }
    code.popq("%rdi");
    String nonNullLabel = freshLabel("non_null");
    String continueLabel = freshLabel("continue_after_call");
    code.cmpq("$0", "%rdi");
    code.jne(nonNullLabel);
    code.pushq("%rdi");  
    generateRuntimeError(code, "null pointer exception");
    code.popq("%rdi");   
    code.jmp(continueLabel);  
    code.label(nonNullLabel);
    code.movq("(%rdi)", "%rax");
    code.movq(((methodOffset + 1) * 8) + "(%rax)", "%r10");
    code.callstar("%r10");
    code.label(continueLabel);
    code.pushq("%rax");
  }
 
  private static void generateStringConcat(TEbinop expr, X86_64 code, Map<String, Integer> localVars, String className) {
    generateExpression(expr.e1, code, localVars, className);  
    generateExpression(expr.e2, code, localVars, className);  
    code.popq("%rsi");  
    code.popq("%rdi");  
    code.call("my_string_concat");
    code.pushq("%rax");
  }

  private static void generateRuntimeError(X86_64 code, String message) {
    String errorLabel = freshLabel("error_msg");
    code.dlabel(errorLabel);
    code.string(message);
    code.movq("$" + errorLabel, "%rdi");
    code.call("my_error");
  }
  private static String freshLabel(String prefix) {
    return prefix + "_" + (labelCount++);
  }
  private static void addLibraryWrappers(X86_64 code) {
    // my_malloc
    code.label("my_malloc");
    code.pushq("%rbp");
    code.movq("%rsp", "%rbp");
    code.call("malloc");
    code.leave();
    code.ret();
    // my_error
    code.label("my_error");
    code.pushq("%rbp");
    code.movq("%rsp", "%rbp");
    code.call("puts");
    code.movq(1, "%rdi");
    code.call("exit");
    code.leave();
    code.ret();
    // my_string_concat
    code.label("my_string_concat");
    code.pushq("%rbp");
    code.movq("%rsp", "%rbp");
    code.cmpq(0, "%rdi");

    String firstNotNull = freshLabel("first_not_null");
    code.jne(firstNotNull);
    code.movq("%rsi", "%rax");
    code.leave();
    code.ret();
    code.label(firstNotNull);
    code.cmpq(0, "%rsi");

    String secondNotNull = freshLabel("second_not_null");
    code.jne(secondNotNull);
    code.movq("%rdi", "%rax");
    code.leave();
    code.ret();
    code.label(secondNotNull);
    code.pushq("%rdi");
    code.pushq("%rsi");
    code.movq("8(%rdi)", "%rdi");
    code.call("strlen");
    code.movq("%rax", "%r12");
    code.popq("%rdi");
    code.movq("8(%rdi)", "%rdi");
    code.call("strlen");
    code.movq("%rax", "%r13");
    code.movq("%r12", "%rdi");
    code.addq("%r13", "%rdi");
    code.incq("%rdi");
    code.call("malloc");
    code.movq("%rax", "%r14");
    code.popq("%rdi");
    code.movq("8(%rdi)", "%rsi");
    code.movq("%r14", "%rdi");
    code.call("strcpy");
    code.popq("%rdi");
    code.movq("8(%rdi)", "%rsi");
    code.movq("%r14", "%rdi");
    code.addq("%r12", "%rdi");
    code.call("strcpy");
    code.movq(16, "%rdi");
    code.call("malloc");
    code.movq("$class_String", "(%rax)");
    code.movq("%r14", "8(%rax)");
    code.leave();
    code.ret();
  }

}
