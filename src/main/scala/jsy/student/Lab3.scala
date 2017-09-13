package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * <Sam Bennetts>
   * 
   * Partner: <D'Artagnan Wake  >
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => if (s == "") Double.NaN else try { s.toDouble } catch {case _ : NumberFormatException => Double.NaN}
      case Function(_, _, _) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Function(_, _, _) => true
      case N(n) => if((n == 0) || (n.isNaN)) false else true
      case S(s) => s match {
        case "" => false
        case _ => true
      }
      case Undefined => false
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case N(n) => if(n.isWhole) n.toInt.toString else n.toDouble.toString
      case B(b) => b.toString
      case Undefined => "undefined"
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case _ => ??? // delete this line when done
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => lookup(env, x)
      case ConstDecl(s: String, e1, e2) => eval(extend(env, s, eval(env, e1)), e2)

      case Unary(uop, e1) => uop match {
        case Neg => N(-1 * toNumber(eval(env, e1)))
        case Not => eval(env, e1) match {
          case B(b) => B(!b)
          case N(0) => B(true)
          case N(1) => B(false)
          case _ => B(false)
        }
      }
      case Binary(bop, e1, e2) => bop match {
        case Plus => (eval(env, e1), eval(env, e2)) match {
          case (S(s1), _) => S(toStr(S(s1)) + toStr(eval(env, e2)))
          case (_, S(s1)) => S(toStr(eval(env,e1)) + toStr(S(s1)))
          case (_, _) => N(toNumber(eval(env,e1)) + toNumber(eval(env, e2)))
        }
        case Minus => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
        case Times => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
        case Div => eval(env,e2) match {
          case N(0) => N(Double.PositiveInfinity)
          case _ => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))
        }
        case And => (eval(env, e1), eval(env, e2)) match {
          case (B(b1), _) =>
            if(B(b1) == B(true)) eval(env, e2)
            else eval(env, e1)
          case (N(0),_) => N(0)
          case (_, B(b2)) => B(b2)
          case (Undefined, _) => Undefined
          case (_, Undefined) => Undefined
          case (_, _) => eval(env, e2)
        }

        case Or => (eval(env, e1), eval(env, e2)) match {
          case (B(b1), _) =>
            if(B(b1) == B(false)) eval(env, e2)
            else B(true)
          case (_, B(b2)) => eval(env, e1)
          case (Undefined, _) => Undefined
          case (_, Undefined) => Undefined
          case (_, _) => eval(env, e1)
        }
        case Eq => (eval(env, e1), eval(env, e2)) match {
          case (Function(_,_,_),_) => throw DynamicTypeError(e1)
          case (_,Function(_,_,_)) => throw DynamicTypeError(e2)
          case (S(s1), S(s2)) => B(toStr(S(s1)) == toStr(S(s2)))
          case (_, _) => B(toNumber(eval(env, e1)) == toNumber(eval(env,e2)))
        }
        case Ne => B(!toBoolean(eval(env,Binary(Eq, e1, e2))))
        case Lt => (eval(env, e1), eval(env, e2)) match {
          case (S(s1), S(s2)) => B(toStr(S(s1)) < toStr(S(s2)))
          case (_, _) => B(toNumber(eval(env,e1)) < toNumber(eval(env, e2)))
        }
        case Le => (eval(env, e1), eval(env, e2)) match {
          case (S(s1), S(s2)) => B(toStr(S(s1)) <= toStr(S(s2)))
          case (_, _) => B(toNumber(eval(env, e1)) <= toNumber(eval(env, e2)))
        }
        case Gt => (eval(env, e1), eval(env, e2)) match {
          case (S(s1), S(s2)) => B(toStr(S(s1)) > toStr(S(s2)))
          case (_, _) => B(toNumber(eval(env, e1)) > toNumber(eval(env, e2)))
        }
        case Ge => (eval(env, e1), eval(env, e2)) match {
          case (S(s1), S(s2)) => B(toStr(S(s1)) >= toStr(S(s2)))
          case (_, _) => B(toNumber(eval(env, e1)) >= toNumber(eval(env, e2)))
        }
        case Seq => eval(env, e1);eval(env, e2)
      }
      case If(e1, e2, e3) => eval(env, e1) match {
        case (B(true)) => eval(env, e2)
        case (B(false)) => eval(env, e3)
        case (N(1)) => eval(env, e2)
        case (N(0)) => eval(env, e3)
      }

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

        // ****** Your cases here

      case Call(e1, e2) => eval(env,e1) match {
        case Function(None, x, ep) => eval(extend(env, x, eval(env, e2)), ep)
        case Function(Some(x1), x2, ep) => {
          eval(extend(extend(env, x1, eval(env, e1)), x2, eval(env, e2)), ep)
        }
        case _ => throw DynamicTypeError(e)
      }
      case _ => ??? // delete this line when done
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None => e
      case Some(expr) => loop(expr, n+1)
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1, v, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1,v,x), substitute(e2,v, x))
      case If(e1, e2, e3) => If(substitute(e1, v, x), substitute(e2, v, x), substitute(e3, v, x))
      case Call(e1, e2) => Call(substitute(e1, v, x), substitute(e2, v, x))
      case Var(y) => if(x == y) v else Var(y) //this is where the switching happens
      case Function(None, y, e1) => {
        if(y == x) Function(None, y, e1)
        else Function(None, y, substitute(e1, v, x))
      }
      case Function(Some(y1), y2, e1) => {
          if(x == y1 || x == y2) Function(Some(y1), y2, e1)
          else Function(Some(y1), y2, substitute(e1, v, x))
      }
      case ConstDecl(y, e1, e2) => if(x == y) ConstDecl(y,substitute(e1, v, x), e2) else ConstDecl(y, substitute(e1, v, x), substitute(e2, v, x))
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      
        // ****** Your cases here
      case Unary(Neg, v1) if isValue(v1) => N(-toNumber(v1))
      case Unary(Not, v1) if isValue(v1) => B(!toBoolean(v1))
      case Binary(Plus, v1, v2) if (isValue(v1) && isValue(v2)) => (v1, v2) match {
        case (S(s1), _) => S(toStr(v1) + toStr(v2))
        case (_, S(s1)) => S(toStr(v1) + toStr(v1))
        case (_, _) => N(toNumber(v1) + toNumber(v2))
      }
      case Binary(Minus, v1, v2) if (isValue(v1) && isValue(v2)) => N(toNumber(v1) - toNumber(v2))
      case Binary(Times, v1, v2) if (isValue(v1) && isValue(v2)) => N(toNumber(v1) * toNumber(v2))
      case Binary(Div, v1, v2) if (isValue(v1) && isValue(v2)) => v2 match {
        case N(0) => N(Double.PositiveInfinity)
        case _ => N(toNumber(v1) / toNumber(v2))
      }
      case Binary(And, v1, e2) if (isValue(v1)) => if(toBoolean(v1)) e2 else v1
      case Binary(Or, v1, e2) if (isValue(v1)) => if(toBoolean(v1)) v1 else e2

      case Binary(Eq, v1, v2) if (isValue(v1) && isValue(v2)) => (v1, v2) match {
        case (Function(_, _, _), _) => throw DynamicTypeError(v1)
        case (_, Function(_, _, _)) => throw DynamicTypeError(v2)
        case (S(s1), S(s2)) => B(toStr(S(s1)) == toStr(S(s2)))
        case (_, _) => B(toNumber(v1) == toNumber(v2))
      }
      case Binary(Ne, v1, v2) if (isValue(v1) && isValue(v2)) => B(!toBoolean(step(Binary(Eq, v1, v2)))) //may be wrong
      case Binary(Lt, v1, v2) if (isValue(v1) && isValue(v2)) => (v1, v2) match {
        case (S(s1), S(s2)) => B(toStr(S(s1)) < toStr(S(s2)))
        case (_, _) => B(toNumber(v1) < toNumber(v2))
      }
      case Binary (Le, v1, v2) if (isValue(v1) && isValue(v2)) => (v1, v2) match {
        case (S(s1), S(s2)) => B(toStr(S(s1)) <= toStr(S(s2)))
        case (_, _) => B(toNumber(v1) <= toNumber(v2))
      }
      case Binary(Gt, v1, v2) if (isValue(v1) && isValue(v2)) => (v1,v2) match {
        case (S(s1), S(s2)) => B(toStr(S(s1)) > toStr(S(s2)))
        case (_, _) => B(toNumber(v1) > toNumber(v2))
      }
      case Binary(Ge, v1, v2) if (isValue(v1) && isValue(v2)) => (v1, v2) match {
        case (S(s1), S(s2)) => B(toStr(S(s1)) >= toStr(S(s2)))
        case (_, _) => B(toNumber(v1) >= toNumber(v2))
      }
      case If(v1, e1,e2) if (isValue(v1)) => v1 match {
        case (B(true)) => e1
        case (B(false)) => e2
        case (N(1)) => e1
        case (N(0)) => e2
      }
      case Binary(Seq, v1, e1) if (isValue(v1)) => v1; e1

      case ConstDecl(x, v1, e1) if (isValue(v1)) => substitute(e1, v1, x)
      case Call(v1, v2) if(isValue(v1) && isValue(v2)) => v1 match {
        case Function(None, x, ep) => substitute(ep, v2, x)
        case Function(Some(x1), x2, ep) => substitute(substitute(ep, v1, x1), v2, x2) //inner sub = sub function name into function body. returns expr. use that as the new body to sub in parameter into body
        case _ => throw DynamicTypeError(v1)
      }

      //case ConstDecl

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      
        // ****** Your cases here
      case Unary(Neg, e1) => Unary(Neg, step(e1))
      case Unary(Not, e1) => Unary(Not, step(e1))
      case Binary(bop, v1, e2) if (isValue(v1)) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2) //evaluate e1 first due to inference rule because of determinism. when it becomes a number then evalutae e2 because of other inference rule. determinism means you know what the next step is and it isn't ambigous
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      case Call(e1 @ Function(_,_,_), e2) => Call(e1, step(e2)) //recursive case
      case Call(v1, e2) if (isValue(v1)) => Call(v1, step(e2)) // none case
      case Call(e1, e2) => Call(step(e1), e2)








      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}