package mini_java;

import java.util.*;

public class Typing {
    static boolean debug = false;
    static HashMap<String, Class_> classTable = new HashMap<>();

    static void ClassTableAdd(String name, Class_ class_) {
        classTable.put(name, class_);
    }

    static Class_ ClassTableSearch(String name) {
        return classTable.get(name);
    }

    static ArrayList<Class_> Sort(ArrayList<Class_> classes, HashMap<Class_, Class_> inheritanceMap) {
        HashMap<Class_, Integer> inDegree = new HashMap<>();
        HashMap<Class_, ArrayList<Class_>> children = new HashMap<>();

        for (Class_ c : classes) {
            inDegree.put(c, 0);
            children.put(c, new ArrayList<>());
        }

        for (Class_ child : classes) {
            Class_ parent = inheritanceMap.get(child);
            if (parent != null) {
                children.get(parent).add(child);
                inDegree.put(child, inDegree.get(child) + 1);
            }
        }

        LinkedList<Class_> queue = new LinkedList<>();
        classes.stream().filter(c -> inDegree.get(c) == 0).forEach(queue::add);

        ArrayList<Class_> sortedClasses = new ArrayList<>();
        while (!queue.isEmpty()) {
            Class_ current = queue.remove();
            sortedClasses.add(current);

            for (Class_ child : children.get(current)) {
                inDegree.put(child, inDegree.get(child) - 1);
                if (inDegree.get(child) == 0) {
                    queue.add(child);
                }
            }
        }

        return sortedClasses;
    }

    static LinkedList<TDClass> typedClass = new LinkedList<>();
    static HashMap<Class_, TDClass> classToTDClass = new HashMap<>();
    static HashMap<Class_, TDconstructor> classToConstructor = new HashMap<>();
    static HashMap<Method, TDecl> methodToDecl = new HashMap<>();
    static HashMap<Attribute, Class_> attrToClass = new HashMap<>();

    private static void initClassTable() {
        ClassTableAdd("Object", new Class_("Object"));
        ClassTableAdd("Integer", IntegerClass);
        ClassTableAdd("String", StringClass);

        Variable equalsParam = new Variable("equalParam", new TTclass(StringClass));
        LinkedList<Variable> equalsParams = new LinkedList<>();
        equalsParams.add(equalsParam);
        StringClass.methods.put("equals", new Method("equals", new TTboolean(), equalsParams));
    }

    private static HashMap<Class_, Class_> processInheritance(ListIterator<PClass> it,
            HashMap<Class_, LinkedList<PDecl>> classDecls) {
        HashMap<Class_, Class_> inheritanceMap = new HashMap<>();

        while (it.hasNext()) {
            PClass pclass = it.next();
            Ident className = pclass.name;
            Ident fatherClassName = pclass.ext;
            LinkedList<PDecl> classDecl = pclass.l;

            Class_ class_ = ClassTableSearch(className.id);
            classDecls.put(class_, classDecl);

            if (fatherClassName != null) {
                Class_ fatherClass_ = ClassTableSearch(fatherClassName.id);
                if (fatherClass_ == null) {
                    error(className.loc, "Class " + className.id +
                            " inherits from unknown class called: " + fatherClassName.id);
                    return null;
                }
                class_.extends_ = fatherClass_;
                inheritanceMap.put(class_, fatherClass_);
            }
        }

        return inheritanceMap;
    }

    static void error(Location loc, String msg) {
        String l = (loc == null) ? " unknown" : " " + loc;
        throw new Error(l + "\n error: " + msg);
    }

    static Class_ IntegerClass = new Class_("Integer");
    static Class_ StringClass = new Class_("String");

    static TFile file(PFile f) {
        typedClass = new LinkedList<>();
        classTable = new HashMap<>();
        initClassTable();
        Visitors visitors = new Visitors();

        ArrayList<Class_> allClasses = new ArrayList<>();
        ListIterator<PClass> it = f.l.listIterator();

        while (it.hasNext()) {
            PClass pclass = it.next();
            Ident className = pclass.name;

            if (ClassTableSearch(className.id) != null) {
                error(className.loc, "Class named: " + className.id + " duplicated");
                return null;
            }

            Class_ class_ = new Class_(className.id);
            ClassTableAdd(className.id, class_);

            TDClass tdclass = new TDClass(class_, new LinkedList<>());
            typedClass.add(tdclass);
            classToTDClass.put(class_, tdclass);
            allClasses.add(class_);
        }

        HashMap<Class_, LinkedList<PDecl>> classDecls = new HashMap<>();
        it = f.l.listIterator();
        HashMap<Class_, Class_> inheritanceMap = processInheritance(it, classDecls);

        if (inheritanceMap == null)
            return null;

        ArrayList<Class_> sortedClasses = Sort(allClasses, inheritanceMap);
        if (sortedClasses.size() < typedClass.size()) {
            error(null, "cyclic inheritance");
            return null;
        }

        processClassDeclarations(sortedClasses, classDecls, visitors);

        processMethodBodies(sortedClasses, classDecls, visitors);

        return new TFile(typedClass);
    }

    private static void processClassDeclarations(ArrayList<Class_> sortedClasses,
            HashMap<Class_, LinkedList<PDecl>> classDecls,
            Visitors visitors) {
        for (Class_ class_ : sortedClasses) {
            LinkedList<PDecl> classDecl = classDecls.get(class_);

            inheritParentMembers(class_);

            TDClass currentTDclass = classToTDClass.get(class_);

            for (Method method : class_.methods.values()) {
                currentTDclass.l.add(methodToDecl.get(method));
            }

            Visitors.setClass_(currentTDclass);
            Visitors.withConstructor = false;

            Visitors.disableBodyProcessing();
            for (PDecl pdecl : classDecl) {
                pdecl.accept(visitors);
            }

            if (!Visitors.withConstructor()) {
                TDconstructor tdconstructor = new TDconstructor(new LinkedList<>(), new TSblock());
                classToConstructor.put(class_, tdconstructor);
                currentTDclass.l.add(tdconstructor);
            }
        }
    }

    private static void processMethodBodies(ArrayList<Class_> sortedClasses,
            HashMap<Class_, LinkedList<PDecl>> classDecls,
            Visitors visitors) {
        for (Class_ class_ : sortedClasses) {
            LinkedList<PDecl> classDecl = classDecls.get(class_);
            TDClass currentTDclass = classToTDClass.get(class_);

            Visitors.setClass_(currentTDclass);
            Visitors.enableBodyProcessing();

            for (PDecl pdecl : classDecl) {
                pdecl.accept(visitors);
            }
        }
    }

    private static void inheritParentMembers(Class_ class_) {
        LinkedList<Class_> superClasses = new LinkedList<>();
        Class_ c = class_.extends_;

        if (c != null) {
            // add all superclasses to the list
            while (c != null) {
                superClasses.add(c);
                c = c.extends_;
            }
        } else {
            c = ClassTableSearch("Object");
            class_.extends_ = c;
            superClasses.add(c);
        }
        // merge from the top of the hierarchy
        while (!superClasses.isEmpty()) {
            c = superClasses.pollLast();

            for (Attribute attribute : c.attributes.values()) {
                if (!class_.attributes.containsKey(attribute.name)) {
                    class_.attributes.put(attribute.name, attribute);
                    attrToClass.put(attribute, c);
                } else {
                    System.out.println("Warning: In class " + class_.name + ", attribute '" + attribute.name
                            + "' from parent class " + c.name + " is hidden by a declaration in the subclass.");
                }
            }

            for (Method method : c.methods.values()) {
                if (!class_.methods.containsKey(method.name)) {
                    class_.methods.put(method.name, method);
                }
            }
        }
    }

    public static class Visitors implements Visitor {

        protected static boolean proceed = false;
        protected static boolean withConstructor;
        protected static boolean doRetStmt;
        protected static boolean checkRetStmt;
        protected static TType currentTType;
        protected static TType currentTTypeBinop;
        protected static TType currentTTypeUnop;
        protected static TDClass tdclass;
        protected static TDecl currentTDecl;
        protected static TSblock currentBlock;
        protected static TStmt currentStmt;
        protected static TExpr currentExpr;
        protected static Set<String> keywords = new HashSet<>();
        protected static HashMap<TDecl, TSblock> declToBlock = new HashMap<TDecl, TSblock>();
        protected static HashMap<String, Variable> variables = new HashMap<String, Variable>();
        protected static HashMap<Variable, PType> variableToType = new HashMap<Variable, PType>();
        protected static boolean stringsInvolved;
        protected static String dotAttribute = "";

        public static void disableBodyProcessing() {
            proceed = false;
            return;
        }

        public static void enableBodyProcessing() {
            proceed = true;
            return;
        }

        public static boolean withConstructor() {
            return withConstructor;
        }

        public static void setClass_(TDClass currenTDclass) {
            tdclass = currenTDclass;
            withConstructor = false;
            return;
        }

        public static boolean compatibilityTest(TExpr ei, TType tt) {
            if (tt instanceof TTvoid) {
            } else if (tt instanceof TTnull) {

            } else if (tt instanceof TTboolean) {
                if (ei instanceof TEcst) {
                    Constant c = ((TEcst) ei).c;
                    return (c instanceof Cbool);
                } else {
                    return instanceTE(ei, tt);
                }
            } else if (tt instanceof TTint) {
                if (ei instanceof TEcst) {
                    Constant c = ((TEcst) ei).c;
                    return (c instanceof Cint);
                } else
                    return instanceTE(ei, tt);
            } else if (tt instanceof TTclass) {
                Class_ c = ((TTclass) tt).c;
                if (ei instanceof TEcst) {
                    Constant cte = ((TEcst) ei).c;
                    if (c.equals(Typing.StringClass)) {
                        return (cte instanceof Cstring);
                    }
                    return true;
                } else if (ei instanceof TEbinop) {
                    return currentTTypeBinop.getClass() == tt.getClass();
                } else if (ei instanceof TEunop) {
                    return compatibilityTest(((TEunop) ei).e, tt);
                } else if (ei instanceof TEattr) {
                    Attribute a = ((TEattr) ei).a;
                    TType tt2 = a.ty;
                    if (tt2 instanceof TTclass) {
                        Class_ c2 = ((TTclass) tt2).c;
                        while (!c2.name.equals(c.name) && c2.extends_ != null) {
                            c2 = c2.extends_;
                        }
                        return c2.name.equals(c.name);
                    } else {
                        return false;
                    }
                } else if (ei instanceof TEvar) {
                    Variable v = ((TEvar) ei).x;
                    TType tt2 = v.ty;
                    if (tt2 instanceof TTclass) {
                        Class_ c2 = ((TTclass) tt2).c;
                        while (!c2.name.equals(c.name) && c2.extends_ != null) {
                            c2 = c2.extends_;
                        }
                        return c2.name.equals(c.name);
                    } else {
                        return false;
                    }
                } else if (ei instanceof TEnew) {
                    return true;
                } else if (ei instanceof TEnull) {
                    return true;
                } else if (ei instanceof TEthis) {
                    return tdclass.c.name.equals(c.name);
                } else if (ei instanceof TEassignAttr) {
                    return ((TEassignAttr) ei).a.ty.getClass() == tt.getClass();
                } else if (ei instanceof TEcall) {
                    Method m = ((TEcall) ei).m;
                    return m.type.getClass() == tt.getClass();
                } else if (ei instanceof TEcast) {
                    TEcast castExpr = (TEcast) ei;
                    TType castType = castExpr.ty;
                    if (castType.getClass() == tt.getClass()) {
                        if (castType instanceof TTclass && tt instanceof TTclass) {
                            return ((TTclass) castType).c.name.equals(((TTclass) tt).c.name);
                        }
                        return true;
                    }
                    return isValidCastType(castType, tt);
                } else {
                    return false;
                }
            }
            return true;
        }

        private static boolean isValidCastType(TType sourceType, TType targetType) {
            if (sourceType instanceof TTclass && targetType instanceof TTclass) {
                Class_ source = ((TTclass) sourceType).c;
                Class_ target = ((TTclass) targetType).c;

                if (source == Typing.StringClass) {
                    return target.name.equals("Object") || target == Typing.StringClass;
                }

                if (target == Typing.StringClass) {
                    return source.name.equals("Object") || source == Typing.StringClass;
                }

                if (source.name.equals("Object")) {
                    return true;
                }

                if (isSubclassOf(source, target) || isSubclassOf(target, source)) {
                    return true;
                }

                if (source.name.equals(target.name)) {
                    return true;
                }
            }

            if (sourceType instanceof TTnull && targetType instanceof TTclass) {
                return true;
            }

            return false;
        }

        private static boolean isSubclassOf(Class_ potential_child, Class_ potential_parent) {
            Class_ current = potential_child;
            while (current.extends_ != null) {
                current = current.extends_;
                if (current.name.equals(potential_parent.name)) {
                    return true;
                }
            }
            return false;
        }

        private static boolean instanceTE(TExpr ei, TType tt) {
            if (ei instanceof TEbinop) {
                return currentTTypeBinop.getClass() == tt.getClass();
            } else if (ei instanceof TEunop) {
                return compatibilityTest(((TEunop) ei).e, tt);
            } else if (ei instanceof TEcall) {
                return ((TEcall) ei).m.type.getClass() == tt.getClass();
            } else if (ei instanceof TEvar) {
                Variable v = ((TEvar) ei).x;
                return v.ty.getClass() == tt.getClass();
            } else if (ei instanceof TEattr) {
                Attribute a = ((TEattr) ei).a;
                return a.ty.getClass() == tt.getClass();
            } else {
                return false;
            }
        }

        public Visitors() {
            Collections.addAll(keywords, "public", "return", "static", "class", "extends", "void", "boolean", "int",
                    "while", "for", "if", "else",
                    "else if", "new", "null", "this", "true", "false");
        }

        @Override
        public void visit(PTboolean t) {
            currentTType = new TTboolean();
        }

        @Override
        public void visit(PTint t) {
            currentTType = new TTint();
        }

        @Override
        public void visit(PTident t) {
            String name = t.x.id;

            if (ClassTableSearch(name) == null) {
                Typing.error(t.x.loc, "bad Type for class : " + name);

                return;
            }

            currentTType = new TTclass(ClassTableSearch(name));
        }

        @Override
        public void visit(Cbool c) {
            currentExpr = new TEcst(c);
        }

        @Override
        public void visit(Cstring c) {
            currentExpr = new TEcst(c);
        }

        @Override
        public void visit(Cint c) {
            currentExpr = new TEcst(c);
        }

        @Override
        public void visit(PEcst e) {
            Constant c = e.c;
            c.accept(this);
        }

        @Override
        public void visit(PEbinop e) {
            e.e1.accept(this);
            TExpr te1 = unwrapAssign(currentExpr);
            TType t1 = getExprType(te1);
            e.e2.accept(this);
            TExpr te2 = unwrapAssign(currentExpr);
            TType t2 = getExprType(te2);
            Binop op = e.op;
            Binop typedOp = op;
            TTclass stringType = new TTclass(Typing.StringClass);

            switch (op) {
                case Badd:

                    if ((isStringType(t1) && isIntType(t2)) || (isStringType(t2) && isIntType(t1))
                            || isStringType(t1) && isStringType(t2)) {
                        typedOp = Binop.Badd_s;
                        currentTTypeBinop = stringType;
                    } else if (areIntCompatible(t1, t2)) {
                        currentTTypeBinop = new TTint();
                    } else {
                        Typing.error(null,
                                "bad ADD operation: requires two integer operands or a String / Int concatenation");
                        return;
                    }
                    break;

                case Bsub:
                case Bmul:
                case Bdiv:
                case Bmod:

                    if (!areIntCompatible(t1, t2)) {
                        Typing.error(null, "bad " + op + " operation: requires two integer operands");
                        return;
                    }
                    currentTTypeBinop = new TTint();
                    break;

                case Beq:
                case Bneq:

                    if (!areEqualCompatible(t1, t2)) {
                        Typing.error(null, "bad TEST operation: " + (op == Binop.Beq ? "EQ" : "NEQ")
                                + " requires two compatible operands");
                        return;
                    }
                    currentTTypeBinop = new TTboolean();
                    break;

                case Blt:
                case Ble:
                case Bgt:
                case Bge:

                    if (!areIntCompatible(t1, t2)) {
                        Typing.error(null, "bad Type operation: " + op + " who requires two integer operands");
                    }
                    currentTTypeBinop = new TTboolean();
                    break;

                case Band:
                case Bor:

                    if (!areBoolCompatible(t1, t2)) {
                        Typing.error(null, "bad Type operation :" + op + "  who requires two boolean operands");
                        return;
                    }
                    currentTTypeBinop = new TTboolean();
                    break;

                case Badd_s:

                    currentTTypeBinop = stringType;
                    break;
            }

            currentExpr = new TEbinop(typedOp, te1, te2);

        }

        private TExpr unwrapAssign(TExpr expr) {
            if (expr instanceof TEassignAttr) {
                return ((TEassignAttr) expr).e2;
            } else if (expr instanceof TEassignVar) {
                return ((TEassignVar) expr).e;
            }
            return expr;
        }

        private TType getExprType(TExpr uexpr) {
            uexpr = unwrapAssign(uexpr);

            if (uexpr instanceof TEvar) {
                return ((TEvar) uexpr).x.ty;
            } else if (uexpr instanceof TEattr) {
                return ((TEattr) uexpr).a.ty;
            } else if (uexpr instanceof TEcst) {
                Constant c = ((TEcst) uexpr).c;
                if (c instanceof Cint)
                    return new TTint();
                if (c instanceof Cbool)
                    return new TTboolean();
                if (c instanceof Cstring)
                    return new TTclass(Typing.StringClass);

            } else if (uexpr instanceof TEbinop) {
                return currentTTypeBinop;
            } else if (uexpr instanceof TEunop) {
                return currentTTypeUnop;
            } else if (uexpr instanceof TEthis) {
                return new TTclass(tdclass.c);
            } else if (uexpr instanceof TEcall) {
                return ((TEcall) uexpr).m.type;
            } else if (uexpr instanceof TEnull) {
                return new TTnull();
            } else if (uexpr instanceof TEnew) {

                return new TTclass(((TEnew) uexpr).cl);
            } else if (uexpr instanceof TEcast) {
                TEcast castExpr = (TEcast) uexpr;
                TType targetType = castExpr.ty;
                TType sourceType = getSourceTypeOfCast(castExpr);

                if (sourceType instanceof TTclass && targetType instanceof TTclass) {
                    Class_ sourceClass = ((TTclass) sourceType).c;
                    Class_ targetClass = ((TTclass) targetType).c;

                    if (isSubclassOf(targetClass, sourceClass)) {
                        return new TTnull();
                    }

                    if (castExpr.e instanceof TEattr) {
                        Attribute targetAttribute = ((TEattr) castExpr.e).a;
                        String attrName = targetAttribute.name;

                        boolean targetHas = targetClass.attributes.containsKey(attrName);
                        boolean sourceHas = sourceClass.attributes.containsKey(attrName);

                        if (!targetHas && !sourceHas) {
                            return new TTnull();
                        } else if (targetHas && !sourceHas) {
                            return targetClass.attributes.get(attrName).ty;
                        } else if (!targetHas && sourceHas) {

                            return sourceClass.attributes.get(attrName).ty;
                        } else if (targetHas && sourceHas) {
                            return targetClass.attributes.get(attrName).ty;
                        }
                    } else if (!dotAttribute.isEmpty()) {
                        boolean targetHas = targetClass.attributes.containsKey(dotAttribute);
                        boolean sourceHas = sourceClass.attributes.containsKey(dotAttribute);

                        if (!targetHas && !sourceHas) {
                            return new TTnull();
                        } else if (targetHas && !sourceHas) {
                            return targetClass.attributes.get(dotAttribute).ty;
                        } else if (!targetHas && sourceHas) {
                            return sourceClass.attributes.get(dotAttribute).ty;
                        } else if (targetHas && sourceHas) {
                            return targetClass.attributes.get(dotAttribute).ty;
                        }
                    }
                }

                if (sourceType instanceof TTint && targetType instanceof TTint) {
                    return targetType;
                } else if (sourceType instanceof TTboolean && targetType instanceof TTboolean) {
                    return targetType;
                } else if (sourceType instanceof TTnull || targetType instanceof TTnull) {
                    return targetType;
                }

                return targetType;
            }
            return null;

        }

        private TType getSourceTypeOfCast(TEcast castExpr) {
            if (castExpr == null) {
                return null;
            }

            TExpr sourceExpr = castExpr.e;

            while (sourceExpr instanceof TEcast || sourceExpr instanceof TEattr) {
                if (sourceExpr instanceof TEcast) {
                    sourceExpr = ((TEcast) sourceExpr).e;
                } else if (sourceExpr instanceof TEcst || sourceExpr instanceof TEnew) {
                    break;
                } else if (sourceExpr instanceof TEattr) {
                    sourceExpr = ((TEattr) sourceExpr).e;
                    break;
                }
            }

            return getExprType(sourceExpr);
        }

        private boolean isIntType(TType t) {
            return (t instanceof TTint);
        }

        private boolean isBoolType(TType t) {
            return (t instanceof TTboolean);
        }

        private boolean isNullType(TType t) {
            return (t instanceof TTnull) || (t == null);
        }

        private boolean isStringType(TType t) {
            if (t instanceof TTclass) {
                return ((TTclass) t).c == Typing.StringClass;
            }
            return false;
        }

        private boolean areIntCompatible(TType t1, TType t2) {
            return isIntType(t1) && isIntType(t2);
        }

        private boolean areBoolCompatible(TType t1, TType t2) {
            return isBoolType(t1) && isBoolType(t2);
        }

        private boolean areEqualCompatible(TType t1, TType t2) {

            if (isIntType(t1) && isIntType(t2))
                return true;

            if (isBoolType(t1) && isBoolType(t2))
                return true;

            if (isStringType(t1) && isStringType(t2))
                return true;

            if (isNullType(t1) && isNullType(t2))
                return true;

            if (t1 instanceof TTclass c1 && t2 instanceof TTclass c2) {
                if (c1.c.name.equals(c2.c.name)) {
                    return true;
                }
            }

            return (t1 instanceof TTnull && t2 instanceof TTclass) || (t2 instanceof TTnull && t1 instanceof TTclass);
        }

        @Override
        public void visit(PEunop e) {
            Unop op = e.op;
            PExpr pe = e.e;

            switch (op) {
                case Unot:
                    currentTTypeUnop = new TTboolean();
                    break;
                case Uneg, Upreinc, Upostinc, Upredec, Upostdec:
                    currentTTypeUnop = new TTint();
                    break;
                case Ustring_of_int:
                    currentTTypeUnop = new TTclass(Typing.StringClass);
                    break;
            }

            pe.accept(this);
            currentExpr = new TEunop(op, currentExpr);
        }

        @Override
        public void visit(PEthis e) {
            currentExpr = new TEthis();
        }

        @Override
        public void visit(PEnull e) {
            currentExpr = new TEnull();
        }

        public boolean findParam(TDecl tdecl, Ident id) {
            ListIterator<Variable> it;

            if (tdecl instanceof TDmethod currentMethod) {
                LinkedList<Variable> l = currentMethod.m.params;
                it = l.listIterator();
            } else {
                TDconstructor currentConstructor = (TDconstructor) tdecl;
                LinkedList<Variable> l = currentConstructor.params;
                it = l.listIterator();
            }

            boolean found = false;
            while (it.hasNext()) {
                Variable v = it.next();
                if (v.name.equals(id.id)) {
                    found = true;
                    currentExpr = new TEvar(v);
                }
            }
            return found;
        }

        @Override
        public void visit(PEident e) {
            Ident id = e.id;
            if (keywords.contains(id.id)) {
                Typing.error(id.loc, "bad Identifier: " + id.id + " is a reserved keyword");
                return;
            }

            if (Objects.equals(dotAttribute, "")) {
                boolean found = findParam(currentTDecl, id);

                if (!found) {

                    if (variables.containsKey(id.id)) {
                        currentExpr = new TEvar(variables.get(id.id));
                    } else if (tdclass.c.attributes.containsKey(id.id)) {
                        currentExpr = new TEattr(new TEthis(), tdclass.c.attributes.get(id.id));
                    } else {
                        Typing.error(id.loc, "bad Variable/Attribute: " + id.id + " does not exist");
                        return;
                    }

                }

            } else {

                if (id.id.equals("System") && (dotAttribute.equals("print") || dotAttribute.equals("out"))) {
                    dotAttribute = "System.out";
                    currentExpr = new TEthis();
                    return;
                }

                String callerClass = id.id;
                if (!classTable.containsKey(callerClass)) {
                    if (variables.containsKey(id.id)) {
                        Variable v = variables.get(id.id);
                        PType pt = variableToType.get(v);
                        Class_ class_;
                        if (pt instanceof PTident) {
                            class_ = ClassTableSearch(((PTident) pt).x.id);
                            Attribute a = class_.attributes.get(dotAttribute);
                            currentExpr = new TEattr(new TEvar(v), a);
                        } else if (pt instanceof PType) {
                            currentExpr = new TEvar(v);
                        } else {
                            Typing.error(id.loc, "bad Function Call: call to " + id.id + " is not valid");
                            return;
                        }
                    } else {
                        Typing.error(id.loc, "bad Variable: " + id.id + " does not exist");
                    }
                    dotAttribute = "";
                    return;
                }
                Class_ c = ClassTableSearch(id.id);
                if (c.attributes.containsKey(dotAttribute)) {
                    Attribute res = c.attributes.get(dotAttribute);
                    currentExpr = new TEvar(new Variable(res.name, res.ty));
                    dotAttribute = "";
                } else {
                    Typing.error(id.loc, "bad Attribute: invalid attribute name for class " + id.id);
                    return;
                }

            }
        }

        @Override
        public void visit(PEassignIdent e) {
            Ident id = e.id;
            PExpr pe = e.e;
            pe.accept(this);

            if (variables.containsKey(id.id)) {
                Variable v = variables.get(id.id);
                currentExpr = new TEassignVar(v, currentExpr);
            } else if (tdclass.c.attributes.containsKey(id.id)) {
                Attribute a = tdclass.c.attributes.get(id.id);

                if (!compatibilityTest(currentExpr, a.ty)) {
                    Typing.error(id.loc, "bad Attribute Assignment: invalid type for assignment of attribute " + id.id);
                    return;
                }

                currentExpr = new TEassignAttr(new TEthis(), a, currentExpr);
            } else {
                Typing.error(id.loc, "bad Assignment: attribution not possible for identifier " + id.id);

                return;
            }
        }

        @Override
        public void visit(PEdot e) {
            PExpr pe = e.e;
            Ident id = e.id;
            if (dotAttribute.isEmpty()) {
                dotAttribute = id.id;
            } else {
                dotAttribute = id.id + "_" + dotAttribute;
            }
            pe.accept(this);
        }

        @Override
        public void visit(PEassignDot e) {
            PExpr e1 = e.e1;
            Ident id = e.id;
            PExpr e2 = e.e2;

            e1.accept(this);
            TExpr aux = currentExpr;
            Attribute a = null;
            TType tv;
            if (aux instanceof TEvar) {
                tv = ((TEvar) aux).x.ty;
            } else if (aux instanceof TEattr) {
                tv = ((TEattr) aux).a.ty;
            } else if (aux instanceof TEcast) {
                tv = ((TEcast) aux).ty;
            } else {
                Typing.error(id.loc, "bad Expression: does not identify to an Object");
                return;
            }
            if (tv instanceof TTclass) {
                Class_ c = ((TTclass) tv).c;
                if (c.attributes.containsKey(id.id)) {
                    a = c.attributes.get(id.id);
                } else {
                    Typing.error(id.loc, "bad Attribute: " + id.id + " does not exist in class " + c.name);
                    return;
                }
            }

            e2.accept(this);
            TExpr aux2 = currentExpr;
            if (!compatibilityTest(aux2, a.ty)) {
                Typing.error(id.loc, "bad Attribute Assignment: invalid type for assignment of attribute " + id.id);

                return;
            }

            currentExpr = new TEassignAttr(aux, a, aux2);
        }

        @Override
        public void visit(PEnew e) {
            Ident id = e.c;
            LinkedList<PExpr> pl = e.l;

            if (ClassTableSearch(id.id) == null) {
                Typing.error(id.loc, "bad Class: " + id.id + " does not exist");

                return;
            }
            Class_ class_ = ClassTableSearch(id.id);
            LinkedList<TExpr> tl = new LinkedList<>();

            TDconstructor tdconstructor = Typing.classToConstructor.get(class_);
            LinkedList<Variable> l = tdconstructor.params;

            if (pl.size() != l.size()) {
                Typing.error(null,
                        "bad Constructor Call: wrong number of arguments for constructor of class " + class_.name);

                return;
            }

            ListIterator<PExpr> it = pl.listIterator();
            ListIterator<Variable> it2 = l.listIterator();
            while (it.hasNext()) {
                PExpr pe = it.next();
                Variable expectedParam = it2.next();
                pe.accept(this);
                if (!compatibilityTest(currentExpr, expectedParam.ty)) {
                    Typing.error(id.loc,
                            "bad Constructor Call: wrong type for an argument in constructor of class " + class_.name);
                    return;
                }
                tl.add(currentExpr);
            }

            currentExpr = new TEnew(class_, tl);
        }

        @Override
        public void visit(PEcall e) {
            PExpr pe = e.e;
            Ident id = e.id;
            LinkedList<PExpr> l = e.l;
            stringsInvolved = false;
            LinkedList<TExpr> methodParams = new LinkedList<>();

            dotAttribute = "";
            pe.accept(this);
            TExpr paramExpr = currentExpr;
            TType paramType = getExprType(paramExpr);
            Method m;
            boolean isPrint = false;
            if (dotAttribute.equals("System.out")) {
                LinkedList<Variable> mv = new LinkedList<>();
                mv.add(new Variable("printArg", new TTclass(Typing.StringClass)));
                m = new Method("System.out.print", new TTvoid(), mv);
                isPrint = true;
                dotAttribute = "";
            } else {
                Class_ class_ = ClassTableSearch(dotAttribute);
                if (class_ == null) {
                    if (currentExpr instanceof TEattr) {
                        Attribute a = ((TEattr) currentExpr).a;
                        class_ = Typing.attrToClass.get(a);
                    } else if (currentExpr instanceof TEvar) {
                        Variable v = ((TEvar) currentExpr).x;
                        PType pt = variableToType.get(v);
                        if (pt instanceof PTident) {
                            class_ = ClassTableSearch(((PTident) pt).x.id);
                        } else {
                            Typing.error(id.loc, "bad Function Call: call to " + id.id + " is not valid");
                            return;
                        }
                    } else if (currentExpr instanceof TEthis) {
                        if (tdclass.c.methods.containsKey(id.id)) {
                            class_ = tdclass.c;
                        } else {
                            Typing.error(id.loc,
                                    "bad Method Lookup: class " + tdclass.c.name + " does not have method " + id.id);

                            return;
                        }
                    } else if (currentExpr instanceof TEcall) {
                        if (id.id.equals("equals")) {
                            class_ = Typing.StringClass;
                        }
                    } else if (currentExpr instanceof TEnew) {
                        class_ = ((TEnew) currentExpr).cl;
                    }
                }
                m = class_.methods.get(id.id);
            }
            TEcall tecall = new TEcall(currentExpr, m, methodParams);

            if (l.size() != m.params.size()) {
                Typing.error(id.loc,
                        "bad Function Call: incorrect number of arguments in function " + dotAttribute + "_" + id.id);

                return;
            }

            ListIterator<PExpr> it = l.listIterator();
            ListIterator<Variable> it2 = m.params.listIterator();
            while (it.hasNext()) {
                PExpr ei = it.next();
                ei.accept(this);
                Variable ej = it2.next();

                TType argType = getExprType(currentExpr);

                if (isPrint && !isValidPrintType(argType) && !stringsInvolved) {
                    Typing.error(id.loc, "bad Function Call: wrong argument type for call of Print function");
                    return;
                } else if (!compatibilityTest(currentExpr, ej.ty)) {
                    Typing.error(id.loc, "bad Function Call: wrong argument type for call of function " + dotAttribute
                            + "_" + id.id);
                    return;
                }
                methodParams.add(currentExpr);
            }
            currentExpr = tecall;
        }

        private boolean isValidPrintType(TType t) {
            return isIntType(t) || isBoolType(t) || isStringType(t);
        }

        @Override
        public void visit(PEcast e) {
            e.e.accept(this);
            TExpr sourceExpr = currentExpr;
            TType sourceType = getExprType(sourceExpr);
            e.ty.accept(this);
            TType castType = currentTType;
            if (sourceType instanceof TTclass && castType instanceof TTclass) {
                if (!isValidCastType(sourceType, castType)) {
                    Typing.error(null, "bad Cast Type: target type " + castType.toString() + " to source type "
                            + sourceType.toString());
                    return;
                }
            }

            currentExpr = new TEcast(castType, sourceExpr);
        }

        @Override
        public void visit(PEinstanceof e) {

            e.e.accept(this);
            TExpr instanceExpr = currentExpr;
            TType instanceType = getExprType(instanceExpr);

            e.ty.accept(this);
            TType compareType = currentTType;
            if (!(instanceType instanceof TTclass)) {
                Typing.error(null, "bad Type Check: invalid type in 'instanceof' check: " + instanceType.toString());
                return;
            }

            if (!(compareType instanceof TTclass)) {
                Typing.error(null, "bad Type Check: invalid type in 'instanceof' check: " + compareType.toString());
                return;
            }

            if (instanceType instanceof TTclass && compareType instanceof TTclass) {
                if (!isCompatibleForInstanceof((TTclass) instanceType, (TTclass) compareType)) {
                    Typing.error(null,
                            "bad Type Check: " + instanceType + " cannot possibly be an instance of " + compareType);
                    return;
                }
            }

            currentExpr = new TEinstanceof(instanceExpr, compareType);
        }

        private boolean isCompatibleForInstanceof(TTclass type1, TTclass type2) {
            Class_ c1 = type1.c;
            Class_ c2 = type2.c;

            if (c1.name.equals(c2.name))
                return true;

            Class_ current = c1;
            while (current.extends_ != null) {
                current = current.extends_;
                if (current.name.equals(c2.name))
                    return true;
            }

            return false;
        }

        @Override
        public void visit(PSexpr s) {
            s.e.accept(this);
            currentStmt = new TSexpr(currentExpr);
        }

        @Override
        public void visit(PSvar s) {
            PType ptype = s.ty;
            Ident id = s.x;
            PExpr pexpr = s.e;

            if (variables.containsKey(id.id)) {
                Typing.error(id.loc, "bad Variable Declaration: variable " + id.id + " is a duplicate");

                return;
            }

            ptype.accept(this);

            if (pexpr == null) {
                currentExpr = new TEnull();
            } else {
                pexpr.accept(this);
                ptype.accept(this);
                if (!compatibilityTest(currentExpr, currentTType)) {
                    Typing.error(id.loc,
                            "bad Type Assignment: variable " + id.id + " not compatible with expression type");

                    return;
                }
            }
            Variable var = new Variable(id.id, currentTType);
            variables.put(id.id, var);
            variableToType.put(var, ptype);
            currentStmt = new TSvar(var, currentExpr);

        }

        @Override
        public void visit(PSif s) {
            PExpr e = s.e;
            PStmt s1 = s.s1;
            PStmt s2 = s.s2;

            e.accept(this);
            TExpr ifCondition = currentExpr;

            HashMap<String, Variable> variablesIf = new HashMap<>(variables);
            HashMap<String, Variable> variablesElse = new HashMap<>(variables);
            HashMap<String, Variable> temp = variables;

            boolean checkRetStmtBackup = checkRetStmt;
            boolean ifHasReturnStatement, elseHasReturnStatement;

            variables = variablesIf;
            checkRetStmt = false;
            s1.accept(this);
            ifHasReturnStatement = checkRetStmt;
            TStmt ts1 = currentStmt;

            variables = variablesElse;
            checkRetStmt = false;
            s2.accept(this);
            elseHasReturnStatement = checkRetStmt;
            TStmt ts2 = currentStmt;

            variables = temp;
            checkRetStmt = checkRetStmtBackup || (ifHasReturnStatement && elseHasReturnStatement);
            currentStmt = new TSif(ifCondition, ts1, ts2);
        }

        @Override
        public void visit(PSreturn s) {
            checkRetStmt = true;
            PExpr pe = s.e;

            if ((!doRetStmt && pe != null) || (doRetStmt && pe == null)) {
                Typing.error(null,
                        "bad Return Type: method in class " + tdclass.c.name + " has wrong type in return statement");
                return;
            }
            if (pe == null) {
                currentStmt = new TSreturn(new TEnull());
                return;
            }

            pe.accept(this);
            TDmethod tdmethod = (TDmethod) currentTDecl;
            if (!compatibilityTest(currentExpr, tdmethod.m.type)) {
                Typing.error(null, "bad Return Type: invalid type for return of " + tdmethod.m.name);
                return;
            }
            currentStmt = new TSreturn(currentExpr);
        }

        @Override
        public void visit(PSblock s) {
            LinkedList<PStmt> l = s.l;
            ListIterator<PStmt> it = l.listIterator();

            TSblock subBlock = new TSblock();
            checkRetStmt = false;

            HashMap<String, Variable> variablesBackup = new HashMap<>(variables);
            while (it.hasNext()) {
                PStmt st = it.next();
                st.accept(this);
                subBlock.l.add(currentStmt);
            }
            currentStmt = subBlock;
            variables = variablesBackup;
        }

        @Override
        public void visit(PSfor s) {
            PStmt initStmt = s.s1;
            PExpr loopCondition = s.e;
            PStmt endOfIterStmt = s.s2;
            PStmt loopBody = s.s3;

            initStmt.accept(this);
            TStmt iniStmt_Typed = currentStmt;
            loopCondition.accept(this);
            TExpr loopCondition_Typed = currentExpr;
            if (!compatibilityTest(loopCondition_Typed, new TTboolean())) {
                Typing.error(null, "bad Loop Condition: condition in for loop must be of type boolean");
                return;
            }
            endOfIterStmt.accept(this);
            TStmt endOfIterStmt_Typed = currentStmt;

            if (loopCondition_Typed instanceof TEcst && ((TEcst) loopCondition_Typed).c instanceof Cbool
                    && !((Cbool) ((TEcst) loopCondition_Typed).c).b) {
                currentStmt = new TSfor(loopCondition_Typed, iniStmt_Typed, endOfIterStmt_Typed, new TSblock());
            } else {
                HashMap<String, Variable> variablesBackup = new HashMap<>(variables);
                loopBody.accept(this);
                variables = variablesBackup;
                TStmt loopBodyStmt_Typed = currentStmt;
                currentStmt = new TSfor(loopCondition_Typed, iniStmt_Typed, endOfIterStmt_Typed, loopBodyStmt_Typed);
            }
        }

        @Override
        public void visit(PDattribute s) {
            if (proceed) {
                return;
            } else {
                if (tdclass.c.attributes.get(s.x.id) != null) {
                    Attribute existingAttr = tdclass.c.attributes.get(s.x.id);
                    Class_ declaringClass = Typing.attrToClass.get(existingAttr);

                    if (declaringClass == tdclass.c) {
                        Typing.error(null, "bad Attribute Declaration: class " + tdclass.c.name +
                                " has duplicate attribute " + s.x.id);
                        return;
                    }
                    System.out.println("Warning: attribute '" + s.x.id + "' in class '" +
                            tdclass.c.name + "' hides inherited attribute from class '" +
                            declaringClass.name + "'");
                }

                s.ty.accept(this);
                Attribute attribute = new Attribute(s.x.id, currentTType);

                Typing.attrToClass.put(attribute, tdclass.c);

                tdclass.c.attributes.put(s.x.id, attribute);
            }
        }

        @Override
        public void visit(PDconstructor s) {
            if (withConstructor) {
                Typing.error(null,
                        "bad Constructor Declaration: class " + tdclass.c.name + " constructor must be unique");
                return;
            }
            withConstructor = true;
            if (proceed) {

                HashMap<String, Variable> variablesBackup = new HashMap<>(variables);

                LinkedList<PParam> l = s.l;
                TDconstructor constructor = Typing.classToConstructor.get(tdclass.c);

                if (l != null) {
                    ListIterator<PParam> it = l.listIterator();
                    Set<String> parameterNames = new HashSet<>();
                    while (it.hasNext()) {
                        PParam pparam = it.next();

                        PType ptype = pparam.ty;
                        ptype.accept(this);

                        Variable var = new Variable(pparam.x.id, currentTType);

                        if (parameterNames.contains(pparam.x.id)) {
                            Typing.error(null,
                                    "bad Parameter Declaration: parameter " + pparam.x.id + " is a duplicate");
                            return;
                        }
                        if (constructor.params.contains(var)) {
                            Typing.error(null, "bad Constructor Parameter: class " + tdclass.c.name
                                    + " has constructor " + tdclass.c.name + " with duplicate parameter " + s.x.id);
                            return;
                        }

                        parameterNames.add(pparam.x.id);
                        variables.put(pparam.x.id, var);
                        variableToType.put(var, ptype);
                    }
                }

                currentTDecl = Typing.classToConstructor.get(tdclass.c);
                doRetStmt = false;
                s.s.accept(this);

                currentBlock = declToBlock.get(currentTDecl);
                currentBlock.l.add(currentStmt);

                variables = variablesBackup;

            } else {

                if (!tdclass.c.name.equals(s.x.id)) {
                    Typing.error(null, "bad Constructor Declaration: constructor " + s.x.id
                            + " does not match class name " + tdclass.c.name);
                    return;
                }
                if (tdclass.c.methods.get(s.x.id) != null) {
                    Typing.error(null, "bad Constructor Declaration: class " + tdclass.c.name
                            + " has duplicate constructor " + s.x.id);
                    return;
                }

                LinkedList<PParam> l = s.l;
                ListIterator<PParam> it = l.listIterator();
                LinkedList<Variable> tParams = new LinkedList<>();
                while (it.hasNext()) {
                    PParam pparam = it.next();
                    pparam.ty.accept(this);
                    Variable v = new Variable(pparam.x.id, currentTType);
                    tParams.add(v);
                }

                TSblock tsblock = new TSblock();
                TDconstructor tdconstructor = new TDconstructor(tParams, new TSblock());
                declToBlock.put(tdconstructor, tsblock);
                tdclass.l.add(tdconstructor);
                Typing.classToConstructor.put(ClassTableSearch(s.x.id), tdconstructor);
            }
        }

        @Override
        public void visit(PDmethod s) {
            if (proceed) {
                HashMap<String, Variable> variablesBackup = new HashMap<>(variables);
                LinkedList<PParam> l = s.l;
                Method method = tdclass.c.methods.get(s.x.id);

                if (l != null && method.params.isEmpty()) {
                    ListIterator<PParam> it = l.listIterator();
                    Set<String> parameterNames = new HashSet<>();
                    while (it.hasNext()) {
                        PParam pparam = it.next();

                        PType ptype = pparam.ty;
                        ptype.accept(this);

                        Variable var = new Variable(pparam.x.id, currentTType);

                        if (parameterNames.contains(pparam.x.id)) {
                            Typing.error(null,
                                    "bad Parameter Declaration: parameter " + pparam.x.id + " is a duplicate");

                            return;
                        }
                        if (method.params.contains(var)) {
                            Typing.error(null, "bad Method Parameter: class " + tdclass.c.name + " has method "
                                    + method.name + " with duplicate parameter " + s.x.id);
                            return;
                        }

                        method.params.add(var);
                        parameterNames.add(pparam.x.id);
                        variables.put(pparam.x.id, var);
                        variableToType.put(var, ptype);
                    }
                } else if (l != null) {
                    for (Variable param : method.params) {
                        variables.put(param.name, param);
                        for (PParam pparam : l) {
                            if (pparam.x.id.equals(param.name)) {
                                variableToType.put(param, pparam.ty);
                                break;
                            }
                        }
                    }
                }
                doRetStmt = !(method.type instanceof TTvoid);
                currentTDecl = Typing.methodToDecl.get(method);
                s.s.accept(this);
                currentBlock = declToBlock.get(currentTDecl);
                currentBlock.l.add(currentStmt);
                if (doRetStmt && !checkRetStmt) {
                    Typing.error(null, "bad Method Declaration: method " + method.name + " of " + tdclass.c.name
                            + " is missing a return statement");
                    return;
                }
                variables = variablesBackup;

            } else {// if non procced phase
                Method oldMethod = tdclass.c.methods.get(s.x.id);
                if (oldMethod != null) {
                    if (!isOverrideCompatible(oldMethod, s)) {
                        Typing.error(null,
                                "bad Method Declaration: class " + tdclass.c.name
                                        + " has conflicting method " + s.x.id);
                        return;
                    }
                }

                TType returnType;
                if (s.ty != null) {
                    s.ty.accept(this);
                    returnType = currentTType;
                } else {
                    returnType = new TTvoid();
                }

                LinkedList<Variable> params = new LinkedList<>();
                if (s.l != null) {
                    Set<String> parameterNames = new HashSet<>();
                    for (PParam pparam : s.l) {
                        if (parameterNames.contains(pparam.x.id)) {
                            Typing.error(null,
                                    "bad Parameter Declaration: parameter " + pparam.x.id + " is a duplicate");
                            return;
                        }

                        pparam.ty.accept(this);
                        Variable v = new Variable(pparam.x.id, currentTType);
                        params.add(v);
                        parameterNames.add(pparam.x.id);
                    }
                }

                Method method = new Method(s.x.id, returnType, params);
                tdclass.c.methods.put(s.x.id, method);

                TSblock tsblock = new TSblock();
                TDmethod tdmethod = new TDmethod(method, tsblock);
                declToBlock.put(tdmethod, tsblock);
                tdclass.l.add(tdmethod);
                Typing.methodToDecl.put(method, tdmethod);
            }
        }

        private static boolean isOverrideCompatible(Method oldMethod, PDmethod s) {
            int oldCount = oldMethod.params.size();
            int newCount = (s.l == null ? 0 : s.l.size());
            if (oldCount != newCount) {
                return false;
            }

            TType oldRet = oldMethod.type;
            TType newRet = newTypeFromPType(s.ty);
            if (!sameType(oldRet, newRet)) {
                return false;
            }

            LinkedList<TType> newParamTypes = new LinkedList<>();
            if (s.l != null) {
                for (PParam pparam : s.l) {
                    TType paramTy = newTypeFromPType(pparam.ty);
                    newParamTypes.add(paramTy);
                }
            }
            int i = 0;
            for (Variable oldVar : oldMethod.params) {
                TType oldVarType = oldVar.ty;
                TType newVarType = newParamTypes.get(i++);
                if (!sameType(oldVarType, newVarType)) {
                    return false;
                }
            }
            return true;
        }

        private static TType newTypeFromPType(PType pt) {
            if (pt == null) {
                return new TTvoid();
            }

            Visitors.currentTType = null;
            pt.accept(new Visitors());
            return Visitors.currentTType;
        }

        private static boolean sameType(TType t1, TType t2) {
            if (t1 == null || t2 == null) {
                return t1 == t2;
            }
            if (t1.getClass() != t2.getClass()) {
                return false;
            }
            if (t1 instanceof TTclass c1 && t2 instanceof TTclass c2) {
                return c1.c.name.equals(c2.c.name);
            }
            return true;
        }

    }

}
