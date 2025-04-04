
package mini_java;

import java_cup.runtime.*;
import java.util.*;
import static mini_java.sym.*;

%%

%class Lexer
%unicode
%cup
%cupdebug
%line
%column
%yylexthrow Exception

/* The symbols produced by the lexical analyzer not just integers, but objects
   of type java_cup.runtime.Symbol. To create such an object, one invokes the
   function symbol(), defined below, and supplies an integer constant, which
   identifies a terminal symbol; if necessary, one also supplies a semantic
   value, of an appropriate type -- this must match the type declared for this
   terminal symbol in Parser.cup. */

/* See https://www2.in.tum.de/repos/cup/develop/src/java_cup/runtime/ */

/* Technical note: CUP seems to assume that the two integer parameters
   passed to the Symbol constructor are character counts for the left
   and right positions. Instead, we choose to provide line and column
   information. Accordingly, we will replace CUP's error reporting
   routine with our own. */

%{
    StringBuffer string = new StringBuffer();

    private Symbol symbol(int id)
    {
	return new Symbol(id, yyline, yycolumn);
    }

    private Symbol symbol(int id, Object value)
    {
	return new Symbol(id, yyline, yycolumn, value);
    }

%}
InputCharacter     = [^\r\n]
WhiteSpace         = [ \t\f\r\n]

LineTerminator = \r|\n|\r\n
TraditionalComment   = "/*" ~"*/"
EndOfLineComment   = "//" {InputCharacter}* {LineTerminator}?
Comment = {TraditionalComment} | {EndOfLineComment}

Identifier         = [:jletter:] [:jletterdigit:]*

Integer            = "0" | [1-9] [:digit:]*

%state STRING

%%

/* A specification of which regular expressions to recognize and what
   symbols to produce. */

<YYINITIAL> {

    "="
    { return symbol(EQUAL); }

    ","
    { return symbol(COMMA); }

    "."
    { return symbol(DOT); }

    ";"
    { return symbol(SEMICOLON); }

    "("
    { return symbol(LP); }

    ")"
    { return symbol(RP); }

    "{"
    { return symbol(LBRA); }

    "}"
    { return symbol(RBRA); }

    "["
    { return symbol(LSQ); }

    "]"
    { return symbol(RSQ); }

    "+"
    { return symbol(PLUS); }

    "-"
    { return symbol(MINUS); }

    "*"
    { return symbol(TIMES); }

    "/"
    { return symbol(DIV); }

    "%"
    { return symbol(MOD); }

    "<"
    { return symbol(CMP, Binop.Blt); }

    "<="
    { return symbol(CMP, Binop.Ble); }

    ">"
    { return symbol(CMP, Binop.Bgt); }

    ">="
    { return symbol(CMP, Binop.Bge); }

    "=="
    { return symbol(CMP, Binop.Beq); }

    "!="
    { return symbol(CMP, Binop.Bneq); }

    "&&"
    { return symbol(AND); }

    "||"
    { return symbol(OR); }

    "!"
    { return symbol(NOT); }

    "boolean"
    { return symbol(BOOLEAN); }
    "class"
    { return symbol(CLASS); }
    "else"
    { return symbol(ELSE); }
    "extends"
    { return symbol(EXTENDS); }
    "for"
    { return symbol(FOR); }
    "if"
    { return symbol(IF); }
    "instanceof"
    { return symbol(INSTANCEOF); }
    "int"
    { return symbol(INT); }
    "new"
    { return symbol(NEW); }
    "null"
    { return symbol(NULL); }
    "public"
    { return symbol(PUBLIC); }
    "return"
    { return symbol(RETURN); }
    "static"
    { return symbol(STATIC); }
    "this"
    { return symbol(THIS); }
    "void"
    { return symbol(VOID); }

    "true"
    { return symbol(CST, new Cbool(true)); }

    "false"
    { return symbol(CST, new Cbool(false)); }

    {Identifier}
    { return symbol(IDENT,
                    new Ident(yytext().intern(),
                              new Location(yyline, yycolumn))); }
    // The call to intern() allows identifiers to be compared using == .

    \"
    { string.setLength(0); yybegin(STRING); }

    {Integer}
    { return symbol(CST, new Cint(Long.parseLong(yytext()))); }

    {WhiteSpace}
    { /* ignore */ }
    {Comment}
    { /* ignore */ }

    .
    { throw new Exception (String.format (
        "%d:%d:\nerror: illegal character: '%s'\n", yyline+1, yycolumn, yytext()
      ));
    }

}

<STRING> {
    \"           { yybegin(YYINITIAL);
                   return symbol(CST, new Cstring(string.toString())); }
    [^\n\r\"\\]+ { string.append( yytext() ); }
    \\t          { string.append('\t'); }
    \\n          { string.append('\n'); }

    \\r          { string.append('\r'); }
    \\\"         { string.append('\"'); }
    \\           { string.append('\\'); }
}
