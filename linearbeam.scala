/*
 * AUTHOR: Z.Y.
 *
 * Synchronization Rate : 5%
 */

import scala.collection.immutable.Set

import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

object CW1 {
  type Variable = String
  type Env[A] = Map[Variable,A]

  // Arithmetic expressions

  abstract class Expr
  case class Num(n: Integer) extends Expr
  case class Plus(e1: Expr, e2: Expr) extends Expr
  case class Minus(e1: Expr, e2: Expr) extends Expr
  case class Times(e1: Expr, e2: Expr) extends Expr

  // Booleans
  case class Bool(n: Boolean) extends Expr
  case class Eq(e1: Expr, e2:Expr) extends Expr
  case class IfThenElse(e: Expr, e1: Expr, e2: Expr) extends Expr

   // Strings
  case class Str(s: String) extends Expr
  case class Length(e: Expr) extends Expr
  case class Index(e1: Expr, e2: Expr) extends Expr
  case class Concat(e1: Expr, e2: Expr) extends Expr

  // Variables and let-binding
  case class Var(x: Variable) extends Expr
  case class Let(x: Variable, e1: Expr, e2: Expr) extends Expr
  case class LetFun(f: Variable, arg: Variable, ty: Type, e1:Expr, e2:Expr)
      extends Expr
  case class LetRec(f: Variable, arg: Variable, xty: Type, ty: Type, e1:Expr, e2:Expr)
      extends Expr
  case class LetPair(x: Variable,y: Variable, e1:Expr, e2:Expr) extends Expr

  // Pairing
  case class Pair(e1: Expr, e2: Expr) extends Expr
  case class First(e: Expr) extends Expr
  case class Second(e: Expr) extends Expr

  // Functions
  case class Lambda(x: Variable, ty: Type, e: Expr) extends Expr
  case class Apply(e1: Expr, e2: Expr) extends Expr
  case class Rec(f: Variable, x: Variable, tyx:Type, ty: Type, e: Expr) extends Expr

  // Values
  abstract class Value
  case class NumV(n: Integer) extends Value
  case class BoolV(n: Boolean) extends Value
  case class StringV(s: String) extends Value
  case class PairV(v1: Value, v2: Value) extends Value
  case class ClosureV(env: Env[Value], x: Variable, e: Expr) extends Value
  case class RecV(env: Env[Value], f:Variable, x: Variable, e: Expr) extends Value

  // Types
  abstract class Type
  case object IntTy extends Type
  case object BoolTy extends Type
  case object StringTy extends Type
  case class PairTy(ty1: Type, ty2: Type) extends Type
  case class FunTy(ty1: Type, ty2: Type) extends Type

  // ======================================================================
  // Part 1: Syntactic transformation
  // ======================================================================

  // ======================================================================
  // 1.1: Capture-avoiding substitution
  // ======================================================================

  // This object provides a method to generate a "fresh" variable name
  object Gensym {
    private var id = 0
    def gensym(s: Variable): Variable = {
      val fresh_s = s + "_" + id
      id = id + 1
      fresh_s
    }
  }


  def subst(e1:Expr, e2:Expr, x: Variable): Expr =
    e1 match {
      case Num(e) => Num(e)
      case Plus(t1,t2) => Plus(subst(t1,e2,x),subst(t2,e2,x))
      case Minus(t1,t2) => Minus(subst(t1,e2,x),subst(t2,e2,x))
      case Times(t1,t2) => Times(subst(t1,e2,x),subst(t2,e2,x))

      case Bool(n) => Bool(n)
      case Eq(t1,t2) => Eq(subst(t1,e2,x),subst(t2,e2,x))
      case IfThenElse(t0,t1,t2) =>
        IfThenElse(subst(t0,e2,x),subst(t1,e2,x),subst(t2,e2,x))

      case Str(s) => Str(s)
      case Length(t0) => Length(subst(t0,e2,x))
      case Index(t1,t2) => Index(subst(t1,e2,x),subst(t2,e2,x))
      case Concat(t1,t2) => Concat(subst(t1,e2,x),subst(t2,e2,x))

      case Var(y) =>
        if (x == y) {
          e2
        } else {
          Var(y)
        }

      case Let(y,t1,t2) =>
        if (x == y) { // we can stop early since x is re-bound here
          Let(y,subst(t1,e2,x),t2)
        } else { // otherwise, we freshen y
          val z = Gensym.gensym(y);
          val fresh_t2 = subst(t2,Var(z),y);
          Let(z,subst(t1,e2,x),subst(fresh_t2,e2,x))
        }

      case Pair(t1, t2) => Pair(subst(t1,e2,x),subst(t2,e2,x))

      case First(t1) => First(subst(t1,e2,x))

      case Second(t2) => Second(subst(t2,e2,x))

      case Lambda(y, ty, t0) =>
        if (x == y) {
          Lambda(y, ty, t0)
        } else {
          val z = Gensym.gensym(y);
          val fresh_t0 = subst(t0,Var(z),y);
          Lambda(z, ty, subst(fresh_t0,e2,x))
        }

      case Apply(t1, t2) => Apply(subst(t1,e2,x),subst(t2,e2,x))

      case Rec(f, y, tyx, ty, t0) => {
        if(x == y) Rec(f, y, tyx, ty, t0)
        else if(x == f) Rec(f, y, tyx, ty, t0)
        else {
          val zf = Gensym.gensym(f);
          val zy = Gensym.gensym(y);
          val fresh_t0 = subst(t0,Var(zf),f);
          val fresh_t1 = subst(fresh_t0,Var(zy),y);
          Rec(zf, zy, tyx, ty, subst(fresh_t1,e2,x))
        }
      }
      case _ => sys.error("Error: Subst : Wrong Expression")
    }


  // ======================================================================
  // 1.2: Desugaring let fun, let rec and let pair
  // ======================================================================

  def desugar(e: Expr): Expr = e match {

    case Num(n) => Num(n)
    case Plus(e1,e2) => Plus(desugar(e1),desugar(e2))
    case Minus(e1,e2) => Minus(desugar(e1),desugar(e2))
    case Times(e1,e2) => Times(desugar(e1),desugar(e2))

    case Bool(n) => Bool(n)
    case Eq(e1, e2) => Eq(desugar(e1), desugar(e2))
    case IfThenElse(e,e1,e2) => IfThenElse(desugar(e),desugar(e1),desugar(e2))

    case Str(s) => Str(s)
    case Length(e) => Length(desugar(e))
    case Index(e1, e2) => Index(desugar(e1),desugar(e2))
    case Concat(e1,e2) => Concat(desugar(e1),desugar(e2))

    case Var(x) => Var(x)
    case Let(x, e1, e2) => Let(x, desugar(e1), desugar(e2))
    case LetFun(f, y, ty, e1, e2) =>{
      Let(f, Lambda(y, ty, desugar(e1)), desugar(e2))
    }

    case LetRec(f, y, xty, ty, e1, e2) => {
      Let(f, Rec(f, y, xty, ty, desugar(e1)), desugar(e2))
    }

    case LetPair(x, y, e1, e2) => {
      val z = Gensym.gensym(x+y);
      Let(z,desugar(e1),subst(subst(desugar(e2),Second(Var(z)),y),First(Var(z)), x))
    }

    case Pair(e1, e2) => Pair(desugar(e1),desugar(e2))
    case First(e) => First(desugar(e))
    case Second(e) => Second(desugar(e))

    case Lambda(x, ty, e) => Lambda(x, ty, desugar(e))
    case Apply(e1, e2) => Apply(desugar(e1), desugar(e2))
    case Rec(f, x, tyx, ty, e) => Rec(f,x,tyx,ty,desugar(e))

    case _ => sys.error("Error: Desugar: Imposiible Expression")

  }


  // ======================================================================
  // Part 2: Interpretation
  // ======================================================================

  // ======================================================================
  // 2.1: Primitive operations
  // ======================================================================


  object Value {
    // utility methods for operating on values
    def add(v1: Value, v2: Value): Value = (v1,v2) match {
      case (NumV(v1), NumV(v2)) => NumV (v1 + v2)
      case _ => sys.error("arguments to addition are non-numeric")
    }

    def subtract(v1: Value, v2: Value): Value = (v1,v2) match {
      case (NumV(v1), NumV(v2)) => NumV (v1 - v2)
      case _ => sys.error("arguments to subtract are non-numeric")
    }

    def multiply(v1: Value, v2: Value): Value = (v1, v2) match {
      case (NumV(v1),NumV(v2)) => NumV(v1 * v2)
      case _ => sys.error("arguments to multiply are non-numeric")
    }

    def eq(v1: Value, v2: Value): Value = (v1, v2) match{
      case (NumV(v1),NumV(v2)) => BoolV(v1 == v2)
      case (StringV(v1),StringV(v2)) => BoolV(v1 == v2)
      case (BoolV(v1),BoolV(v2)) => BoolV(v1 == v2)
      case _ =>
        sys.error("arguments to check equal are non-numeric")
    }

    def length(v: Value): Value = v match {
      case StringV(v) => NumV(v.length())
      case _ => sys.error("argument to compute length is not string")
    }


    //Need check
    def index(v1: Value, v2: Value): Value = (v1, v2) match {
      case (StringV(v1),NumV(v2)) => {
        if (v2 >= v1.length() || v2 < 0)
          sys.error("Out of range")
        else
          StringV(v1(v2).toString())
      }
      case _ => sys.error("Cannot be indexed")
    }


    def concat(v1: Value, v2: Value): Value = (v1,v2) match {
      case (StringV(v1),StringV(v2)) => StringV(v1 + v2)
      case _ => sys.error("Cannot be concated")
    }
  }

  // ======================================================================
  // 2.2: Evaluation
  // ======================================================================

  def eval (env: Env[Value], e: Expr): Value =e match {
    // Arithmetic
    case Num(n) => NumV(n)
    case Plus(e1,e2) =>
      Value.add(eval(env,e1),eval(env,e2))
    case Minus(e1,e2) =>
      Value.subtract(eval(env,e1),eval(env,e2))
    case Times(e1,e2) =>
      Value.multiply(eval(env,e1),eval(env,e2))

    case Bool(n) => BoolV(n)

    case Str(str) => StringV(str)

    case Eq(e1,e2) =>
      Value.eq(eval(env,e1),eval(env,e2))

    case Length(e1) =>
      Value.length(eval(env,e1))

    case Index(e1, e2) =>
      Value.index(eval(env,e1),eval(env,e2))

    case Concat(e1,e2) =>
      Value.concat(eval(env,e1),eval(env,e2))

    case Var(x) => env(x)
    //very important!
    /*
    case IfThenElse(e,e1,e2) => eval(env, e) match {
      case BoolV(n) =>
        if (n) eval(env, e1) else eval(env, e2)
      case _ => sys.error("Not an legal boolean value")
    }
    */
    case IfThenElse(e,e1,e2) => eval(env, e) match {
      case BoolV(true) => eval(env, e1)
      case BoolV(false) => eval(env, e2)
      case _ => sys.error("Not an legal boolean value")
    }

    case Let(x,e1,e2) => e1 match {
      case Rec(f, xr, tyx, ty, e)  => {
        val temp = eval(env, e1)
        eval(env + (f -> temp) + (x -> temp), e2)
      }
      //let f0 = rec f(x:int):int = x+1 in f0 12

      case _ => eval(env + (x -> eval(env, e1)), e2)
    }


    case Pair(e1,e2) => PairV(eval(env,e1),eval(env,e2))

    case First(e) => eval(env, e) match {
      case PairV(e1, e2) => e1
      case _ => sys.error("Eval: First: Cannot match such pattern")
    }

    case Second(e) => eval(env, e) match {
      case PairV(e1, e2) => e2
      case _ => sys.error("Eval: Second :Cannot match such pattern")
    }
    //Function

    case Lambda(x, ty, e) => ClosureV(env, x, e)

    case Rec(f, x, tyx, ty, e) => RecV(env, f, x, e)

    case Apply(e1, e2) => eval(env, e1) match {
      case ClosureV(envc, x, e) => eval(envc + (x -> eval(env, e2)), e)
      case RecV(envr, f, x, e)  => eval(envr + (x -> eval(env,e2)) + (f -> env(f)), e)
    }

    case _ => sys.error("Eval: Cannot match such pattern")
  }


  // ======================================================================
  // Part 3: Typechecking
  // ======================================================================

  // ======================================================================
  // 3.1: Typechecker
  // ======================================================================

  // typing: calculate the return type of e, or throw an error
  def tyOf(ctx: Env[Type], e: Expr): Type = e match {
    // Arithmetic
    case Num(n) => IntTy
    case Plus(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("Plus: non-integer arguments to add")
    }

    case Minus(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("Minus: non-integer arguments to minus")
    }
    case Times(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => IntTy
      case _ => sys.error("Times: non-integer arguments to times")
    }

    //Booleans
    case Bool(n) => BoolTy

    case IfThenElse(e,e1,e2) => (tyOf(ctx,e),tyOf(ctx,e1),tyOf(ctx,e2)) match{
      case (BoolTy, t1, t2) =>
        if (t1 == t2) t1 else sys.error("Types of branches must be equal")
      case _ => sys.error("IfThenElse: Type in the first expression mush be boolean")
    }

    case Eq(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (IntTy, IntTy) => BoolTy
      case (StringTy, StringTy) => BoolTy
      case (BoolTy, BoolTy) => BoolTy
      case _ => sys.error("Eq: Types in the Eq must be Int, String or Bool")
    }

    //Strings

    case Str(s) => StringTy

    case Length(e) => tyOf(ctx,e) match {
      case StringTy => IntTy
      case _ => sys.error("Length: cannot find string here")
    }

    case Index(e1, e2) => (tyOf(ctx, e1),tyOf(ctx, e2)) match {
      case (StringTy, IntTy) => StringTy
      case _ => sys.error("Index : cannot find string or int")
    }

    case Concat(e1, e2) => (tyOf(ctx, e1),tyOf(ctx, e2)) match {
      case (StringTy, StringTy) => StringTy
      case _ => sys.error("Concat : must be two strings")
    }

    // Variables and let-binding
    case Var(x) => ctx(x)

    case Let(x,e1,e2) => tyOf(ctx + (x -> (tyOf(ctx,e1))), e2)
    case LetPair(x, y, e1, e2) =>  {
      val e1f = x -> tyOf(ctx, First(e1))
      val e1s = y -> tyOf(ctx, Second(e1))
      tyOf(ctx + e1f + e1s, e2)
    }

    case LetFun(f, arg, ty, e1, e2) => {
      val ctx2 = ctx + (arg -> ty)
      tyOf(ctx2 + (f -> FunTy(ty, tyOf(ctx2, e1))), e2)
    }

    case LetRec(f, arg, xty, ty, e1, e2) =>
      tyOf(ctx + (f -> FunTy(xty, ty)) + (arg -> xty), e2)


    //Pairing

    case Pair(e1,e2) => (tyOf(ctx,e1),tyOf(ctx,e2)) match {
      case (type1, type2) => PairTy(type1, type2)
      case _ => sys.error("Pair: type error")
    }

    case First(e) => tyOf(ctx,e) match {
      case PairTy(t1, t2) => t1
    }

    case Second(e) => tyOf(ctx,e) match {
      case PairTy(t1, t2) => t2
    }

    //Functions

    case Lambda(x, ty, e) => FunTy(ty, tyOf(ctx + (x -> ty), e))

    case Apply(e1,e2) => tyOf(ctx, e1) match {
      case FunTy(t1, t2) =>
        if (t1 == tyOf(ctx, e2))
          t2
        else
          sys.error("Apply: type doesn't match")
      case _ => sys.error("Apply: not a function")
    }

    case Rec(f, x, tyx, ty, e) => FunTy(tyx, tyOf(ctx + (f -> ty) + (x -> tyx),e))

    case _ => sys.error("Amazing Error : No such type")
  }

  class CWParser extends StandardTokenParsers with PackratParsers {

    type P[+A] = PackratParser[A]

    def parseStr(input: String): Expr = {
      phrase(expression)(new lexical.Scanner(input)) match {
        case Success(ast, _) => ast
        case e: NoSuccess => sys.error(e.msg)
      }
    }

    def parse(input: String): Expr = {
      val source = scala.io.Source.fromFile(input)
      val lines = try source.mkString finally source.close()
      parseStr(lines)
    }

    lexical.reserved += ("let", "in", "rec", "if", "then", "else",
      "int","str","bool","true","false","fst","snd","concat",
      "index","length","fun"
    )
    lexical.delimiters += ("=","*", "\\", "+", "-", "(", ")", "==", ":", ".",
      "->", ","
    )

    lazy val expression: P[Expr] =
      simpleExpr

    lazy val lambda: P[Expr] =
      ("\\" ~> ident) ~ (":" ~> typ) ~ ("." ~> expression) ^^ {
        case arg~ty~body => Lambda(arg,ty,body)
      }

    lazy val rec: P[Expr] =
      ("rec" ~> ident) ~
        ("(" ~> ident) ~ (":" ~> typ) ~ ((")" ~ ":") ~> typ) ~
        ("." ~> expression) ^^ {
          case recArg~funArg~funType~recType~body =>
            Rec(recArg,funArg,funType,recType,body)
        }

    lazy val ifExpr: P[Expr] =
      ("if" ~> expression) ~
        ("then" ~> expression) ~
        ("else" ~> expression) ^^ {
          case cond~e1~e2 => IfThenElse(cond,e1,e2)
        }

    lazy val letExpr: P[Expr] =
      ("let" ~> ident) ~ ("=" ~> expression) ~ ("in" ~> expression) ^^ {
        case binder~e1~e2 => Let(binder,e1,e2)
      }

    lazy val letFun: P[Expr] =
      ("let" ~ "fun" ~> ident) ~ ("(" ~> ident) ~
        (":" ~> typ <~ ")") ~ ("=" ~> expression) ~
        ("in" ~> expression) ^^ {
          case fun~binder~ty~e1~e2 => LetFun(fun,binder,ty,e1,e2)
        }

    lazy val letRec: P[Expr] =
      ("let" ~ "rec" ~> ident) ~ ("(" ~> ident) ~
        (":" ~> typ <~ ")") ~ (":" ~> typ) ~ ("=" ~> expression) ~
        ("in" ~> expression) ^^ {
          case fun~binder~xty~ty~e1~e2 => LetRec(fun,binder,xty,ty,e1,e2)
        }

    lazy val letPair: P[Expr] =
      ("let" ~ "(") ~> ident ~ ("," ~> ident <~ ")") ~
        ("=" ~> expression) ~ ("in" ~> expression) ^^ {
          case x~y~e1~e2 => LetPair(x,y,e1,e2)
        }

    lazy val typ: P[Type] =
      funTyp

    lazy val funTyp: P[Type] =
      pairTyp ~ "->" ~ funTyp ^^ {
        case t1~"->"~t2 => FunTy(t1,t2)
      } | pairTyp

    lazy val pairTyp: P[Type] =
      primitiveType ~ "*" ~ pairTyp ^^ {
        case t1~"*"~t2 => PairTy(t1,t2)
      } | primitiveType

    lazy val primitiveType: P[Type] =
      "bool" ^^^ BoolTy | "int" ^^^ IntTy | "str" ^^^ StringTy |  "("~>typ<~")"

    lazy val operations: P[Expr] =
      application |
      ("fst" ~ "(") ~> expression <~ ")" ^^ (x => First(x)) |
        ("snd" ~ "(") ~> expression <~ ")" ^^ (x => Second(x)) |
        ("length" ~ "(") ~> expression <~ ")" ^^ (x => Length(x)) |
        ("concat"  ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
          case e1~e2 => Concat(e1,e2)
        } |
        ("index" ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
          case e1~e2 => Index(e1,e2)
        }

    lazy val arith: P[Expr] =
      eq

    lazy val prod: P[Expr] =
      prod ~ "*" ~ fact ^^ {
        case e1~"*"~e2 => Times(e1,e2)
      } | fact

    lazy val summation: P[Expr] =
      summation ~ "+" ~ prod ^^ {
        case e1~"+"~e2 => Plus(e1,e2)
      } | summation ~ "-" ~ prod ^^ {
        case e1~"-"~e2 => Minus(e1,e2)
      } | prod

    lazy val eq: P[Expr] =
      simpleExpr ~ "==" ~ summation ^^ {
        case e1~"=="~e2 => Eq(e1,e2)
      } | summation

    lazy val application: P[Expr] =
      fact ~ fact ^^ {
        case e1~e2 => Apply(e1,e2)
      }

    lazy val simpleExpr: P[Expr] = (
      lambda |
        rec |
        letExpr |
        letFun |
        letRec |
        letPair |
        ifExpr |
        arith |
        fact
    )

    lazy val pairLit: P[Expr] =
      "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
        case t1~","~t2 => Pair(t1,t2)
      }

    lazy val fact: P[Expr] = (
      operations |
        pairLit |
        (ident ^^ Var) |
        (numericLit ^^ { x => Num(x.toInt) }) |
        (stringLit ^^ Str) |
        ("true" ^^^ Bool(true)) |
        ("false" ^^^ Bool(false)) |
        "("~>expression<~")"
    )

  }

  val parser = new CWParser


  object Main {
    def typecheck(ast: Expr):Type =
      tyOf(Map.empty,ast);

    def evaluate(ast: Expr):Value =
      eval(Map.empty,ast)



    def showResult(ast: Expr) {
      println("AST:  " + ast.toString + "\n")

      try {
        print("Type Checking...");
        val ty = typecheck(ast);
        println("Done!");
        println("Type of Expression: " + ty.toString + "\n") ;
      } catch {
          case e:Throwable => println("Error: " + e)
      }
      println("Desugaring...");
      val core_ast = desugar(ast);
      println("Done!");
      println("Desugared AST: " + core_ast.toString + "\n") ;

      println("Evaluating...");
      println("Result: " + evaluate(core_ast))


    }

    def start(): Unit = {
      println("Welcome to LinearBeam! (5%, October 28, 2015)");
      println("Enter expressions to evaluate, :load <filename.lb> to load a file, or :quit to quit.");
      println("This REPL can only read one line at a time, use :load to load larger expressions.");
      repl()
    }

    def repl(): Unit = {
      print("LinearBeam> ");
      val input = scala.io.StdIn.readLine();
      if(input == ":quit") {
        println("Goodbye!")
      }
      else if (input.startsWith(":load")) {
        try {
          val ast = parser.parse(input.substring(6));
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      } else {
        try {
          val ast = parser.parseStr(input);
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      }
    }

  }
  def main( args:Array[String] ):Unit = {
    if(args.length == 0) {
      Main.start()
    } else {
      try {
        print("Parsing...");
        val ast = parser.parse(args.head)
        println("Done!");
        Main.showResult(ast)
      } catch {
        case e:Throwable => println("Error: " + e)
      }
    }
  }
}
