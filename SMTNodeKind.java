/*  FuzzSMT: Fuzzing tool for Satisfiablity Modulo Theories (SMT) benchmarks.
 *  Copyright (C) 2009  Robert Daniel Brummayer
 *
 *  This file is part of FuzzSMT.
 *
 *  FuzzSMT is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  FuzzSMT is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

public enum SMTNodeKind { 

  /* input */
  CONST("constant", 0),
  VAR("variable", 0), 
  /* boolean */
  TRUE("true", 0),
  FALSE("false", 0),
  NOT("not", 1), 
  AND("and", 2),
  OR("or", 2),
  IMPLIES("implies","=>", 2),
  XOR("xor", 2),
  IFF("iff", "=", 2),
  IF_THEN_ELSE("if_then_else", "ite", 3), // if-then-else on boolean operands 
  /* bit-vector operators: */
  /* unary operators */
  BVNOT("bvnot", 1),
  BVNEG("bvneg", 1),
  /* unary operators with index */
  // put a bracket infront of some of these because it's easiest..
  EXTRACT("extract","(_ extract", 1),
  REPEAT("repeat","(_ repeat", 1),
  ZERO_EXTEND("zero_extend","(_ zero_extend", 1),
  SIGN_EXTEND("sign_extend","(_ sign_extend", 1),
  ROTATE_LEFT("rotate_left","(_ rotate_left", 1),
  ROTATE_RIGHT("rotate_right","(_ rotate_right", 1),
  /* commutative binary operators */
  BVAND("bvand", 2),
  BVNAND("bvnand", 2),
  BVOR("bvor", 2),
  BVNOR("bvnor", 2),
  BVXOR("bvxor", 2),
  BVXNOR("bvxnor", 2),
  BVADD("bvadd", 2),
  BVMUL("bvmul", 2),
  BVCOMP("bvcomp", 2),
  /* non-commutative binary operators */
  BVULT("bvult", 2),
  BVULE("bvule", 2),
  BVUGT("bvugt", 2),
  BVUGE("bvuge", 2),
  BVSLT("bvslt", 2),
  BVSLE("bvsle", 2),
  BVSGT("bvsgt", 2),
  BVSGE("bvsge", 2),
  BVSHL("bvshl", 2),
  BVLSHR("bvlshr", 2),
  BVASHR("bvashr", 2),
  BVSUB("bvsub", 2),
  BVUDIV("bvudiv", 2),
  BVUREM("bvurem", 2),
  BVSDIV("bvsdiv", 2),
  BVSREM("bvsrem", 2),
  BVSMOD("bvsmod", 2),
  CONCAT("concat", 2),
  /* interpreted predicates */
  LT("<", 2),
  GT(">", 2),
  LE("<=", 2),
  GE(">=", 2),
  EQ("=", 2),
  DISTINCT("distinct", -1),
  /* interpreted functions */
  PLUS("+", 2),
  UNMINUS("~","-", 1),
  BINMINUS("-", 2),
  MUL("*", 2),
  DIV("/", 2),
  /* array operators */
  SELECT("select", 2),
  STORE("store", 3),
  /* if-then-else on terms */
  ITE("ite", 3),
  UFUNC("extrafun", -1),
  UPRED("extrapred", -1);

  protected String smtlib1_name;
  protected String smtlib2_name;

  protected int arity; /* -1 is used to indicate n-ary operators */


  SMTNodeKind (String string, int arity){
    this.smtlib1_name = string;
    this.smtlib2_name = string;
    this.arity = arity;
  }

  SMTNodeKind (String smtlib1_name, String smtlib2_name, int arity){
	    this.smtlib1_name = smtlib1_name;
	    this.smtlib2_name = smtlib2_name;
	    this.arity = arity;
	  }


   public String getString(boolean smtlib1){
	   if (smtlib1)
		   return this.smtlib1_name;
	   else
		   return this.smtlib2_name;
	  }
 

  public int getArity() {
    return this.arity;
  }

}
