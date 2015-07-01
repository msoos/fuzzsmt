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

import java.util.*;
import java.math.*;

public class FuzzSMT {

	static boolean smtlib1; // if true output in smtlib1 format.
	static String bulkPrefix =""; // Prepend to bulk output. 	
	static java.io.PrintStream output; // where output is written to.
		

/*----------------------------------------------------------------------------*/
/* Auxillary                                                                  */
/*----------------------------------------------------------------------------*/

  private enum BVDivMode {
    OFF,
    GUARD,
    FULL;
  }

  private enum RelCompMode {
    OFF,
    EQ,
    FULL;
  }

  private static int selectRandValRange (Random r, int min, int max){
    int result;
    assert (r != null);
    assert (min >= 0);
    assert (max >= 0);
    assert (max >= min);
    result = r.nextInt(max - min + 1) + min;
    assert (result >= min);
    assert (result <= max);
    return result;
  }

  private static void updateStringRefs (HashMap<String, Integer> map, 
                                        String string, int minRefs){
    Integer refs;

    assert (map != null);
    assert (string != null);
    assert (minRefs > 0);

    refs = map.get(string);
    if (refs != null) {
      refs = new Integer (refs.intValue() + 1);
      if (refs.intValue() >= minRefs)
        map.remove(string);
      else
        map.put (string, refs);
    }
  }


  private static void updateNodeRefs (HashMap<SMTNode, Integer> map, 
                                      SMTNode node, int minRefs){
    Integer refs;

    assert (map != null);
    assert (node != null);
    assert (minRefs > 0);

    refs = map.get(node);
    if (refs != null) {
      refs = new Integer (refs.intValue() + 1);
      if (refs.intValue() >= minRefs)
        map.remove(node);
      else
        map.put (node, refs);
    }
  }

  private static void updateFuncRefs (HashMap<UFunc, Integer> map, 
                                      UFunc uFunc, int minRefs){
    Integer refs;

    assert (map != null);
    assert (uFunc != null);
    assert (minRefs > 0);

    refs = map.get(uFunc);
    if (refs != null) {
      refs = new Integer (refs.intValue() + 1);
      if (refs.intValue() >= minRefs)
        map.remove(uFunc);
      else
        map.put (uFunc, refs);
    }
  }

  private static void updatePredRefs (HashMap<UPred, Integer> map, 
                                      UPred uPred, int minRefs){
    Integer refs;

    assert (map != null);
    assert (uPred != null);
    assert (minRefs > 0);

    refs = map.get(uPred);
    if (refs != null) {
      refs = new Integer (refs.intValue() + 1);
      if (refs.intValue() >= minRefs)
        map.remove(uPred);
      else
        map.put (uPred, refs);
    }
  }

  private static String wrapEqualBW (Random r, SMTNode n1, SMTNode n2){
    int n1bw;
    int n2bw;
    int ext;
    StringBuilder builder;

    assert (n1 != null);
    assert (n2 != null);
    assert (n1.getType() instanceof BVType);
    assert (n2.getType() instanceof BVType);

    n1bw = (((BVType) n1.getType()).width);
    n2bw = (((BVType) n2.getType()).width);
    builder = new StringBuilder();
    if (n1bw == n2bw) {
      builder.append (n1.getName());
      builder.append (" ");
      builder.append (n2.getName());
    } else if (n1bw < n2bw){
      ext = n2bw - n1bw;
	if (smtlib1)
		builder.append("(");
	else
		builder.append("((_ ");

      if (r.nextBoolean())
        builder.append ("zero_extend");
      else
        builder.append ("sign_extend");
      
      if (smtlib1)
      {
    	  builder.append ("[");
    	  builder.append (ext);
    	  builder.append ("] ");
      }
      else
      {
    	  builder.append (" ");
    	  builder.append (ext);
    	  builder.append (") ");
      }
      
      builder.append (n1.getName());
      builder.append (") ");
      builder.append (n2.getName());
    } else {
      assert (n2bw < n1bw);
      ext = n1bw - n2bw;
      builder.append (n1.getName());
      builder.append (" ");
  	if (smtlib1)
		builder.append("(");
	else
		builder.append("((_ ");

      if (r.nextBoolean())
        builder.append ("zero_extend");
      else
        builder.append ("sign_extend");
      
      if (smtlib1)
      {
    	  builder.append ("[");
    	  builder.append (ext);
    	  builder.append ("] ");
      }
      else
      {
    	  builder.append (" ");
    	  builder.append (ext);
    	  builder.append (") ");
      }
      
      builder.append (n2.getName());
      builder.append (")"); 
    }
    return builder.toString();
  }

  private static String adaptBW (Random r, SMTNode n, int bw){
    BVType type;
    int diff, upper, lower;
    StringBuilder builder;

    assert (r != null);
    assert (n != null);
    assert (n.getType() instanceof BVType);
    assert (bw > 0);

    type = (BVType) n.getType();
    builder = new StringBuilder();
    if (type.width == bw){
      builder.append (n.getName());
    } else if (type.width < bw) {
      diff = bw - type.width;
    	if (smtlib1)
    		builder.append("(");
    	else
    		builder.append("((_ ");

          if (r.nextBoolean())
            builder.append ("zero_extend");
          else
            builder.append ("sign_extend");
          
          if (smtlib1)
          {
        	  builder.append ("[");
        	  builder.append (diff);
        	  builder.append ("] ");
          }
          else
          {
        	  builder.append (" ");
        	  builder.append (diff);
        	  builder.append (") ");
          }
      builder.append (n.getName());
      builder.append (")");
    } else {
      assert (type.width > bw);
      diff = type.width - bw;
      lower = r.nextInt(diff + 1);
      upper = lower + bw - 1;
      assert (upper - lower + 1 == bw);
      assert (upper >= 0);
      assert (upper >= lower);
      assert (upper < type.width);
      if (smtlib1)
      {
	      builder.append ("(extract[");
	      builder.append (upper);
	      builder.append (":");
	      builder.append (lower);
	      builder.append ("] ");
	      builder.append (n.getName());
	      builder.append (")");
      }
      else
      {
	      builder.append ("((_ extract ");
	      builder.append (upper);
	      builder.append (" ");
	      builder.append (lower);
	      builder.append (") ");
	      builder.append (n.getName());
	      builder.append (")");
      }
      
    }
    return builder.toString();
  }

/*----------------------------------------------------------------------------*/
/* Input Layer                                                                */
/*----------------------------------------------------------------------------*/

  private static int generateVarsOfOneType (List<SMTNode> nodes, int numVars, 
                                            SMTType type){
    String name;
    StringBuilder builder;

    assert (nodes != null);
    assert (type != null);
    assert (numVars >= 0);

    builder = new StringBuilder();
    for (int i = 0; i < numVars; i++) {
      name = "v" + SMTNode.getNodeCtr();
      if (smtlib1)
      {
	      builder.append (":extrafuns ((");
	      builder.append (name);
	      builder.append (" ");
	      builder.append (type.toString(smtlib1));
	      builder.append ("))\n");
      }
      else
      {
	      builder.append ("(declare-fun ");
	      builder.append (name);
	      builder.append (" () ");
	      builder.append (type.toString(smtlib1));
	      builder.append (")\n");
      }
      
      nodes.add (new SMTNode (type, name));
    }
    output.print (builder.toString());
    return numVars;
  }


  private static int generateBVVars (Random r, List<SMTNode> nodes, int numVars,
                                     int minBW, int maxBW) {
    int bw;
    String name;
    SMTNode node;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (numVars >= 0);
    assert (minBW > 0);
    assert (maxBW > 0);
    assert (maxBW >= minBW);

    builder = new StringBuilder();
    for (int i = 0; i < numVars; i++) {
      bw = selectRandValRange (r, minBW, maxBW);
      assert (bw >= minBW && bw <= maxBW);
      name = "v" + SMTNode.getNodeCtr();
      if (smtlib1)
      {
	      builder.append (":extrafuns ((");
	      builder.append (name);
	      builder.append (" BitVec[");
	      builder.append (bw);
	      builder.append ("]))\n");
      }
      else
      {
	      builder.append ("(declare-fun ");
	      builder.append (name);
	      builder.append (" () (_ BitVec ");
	      builder.append (bw);
	      builder.append ("))\n");
      }
      node = new SMTNode (new BVType (bw), name);
      nodes.add (node);
    }
    output.print (builder.toString());

    return numVars;
  }

  private static int generateBVConsts (Random r, List<SMTNode> nodes,
                                       int numConsts, int minBW, int maxBW) {
    int bw;
    int size;
    String name;
    SMTNode node;
    BigInteger bi;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (numConsts >= 0);
    assert (minBW > 0);
    assert (maxBW > 0);
    assert (maxBW >= minBW);

    builder = new StringBuilder();
    size = nodes.size();
    for (int i = 0; i < numConsts; i++) {
      bw = selectRandValRange (r, minBW, maxBW);
      assert (bw >= minBW && bw <= maxBW);
      name = letName();
      bi = new BigInteger(bw, r);
      builder.append(letStart());
      builder.append (name);
      if (smtlib1)
      {
	      builder.append (" bv");
	      builder.append (bi.toString());
	      builder.append ("[");
	      builder.append (bw);
	      builder.append ("]");
      }
      else
      {
    	  builder.append (" (_ bv"  );
    	  builder.append (bi.toString());
    	  builder.append (" "  );
    	  builder.append (bw);
    	  builder.append (")"  );
      }
      
      builder.append (letClose());
      node = new SMTNode (new BVType (bw), name);
      nodes.add (node);
    }
    output.print (builder.toString());

    return numConsts;
  }

  private static String letStart()
  {
	  if (smtlib1)
		  return "(let (";
	  else
		  return "(let ((";
  }

  private static String uMinus()
  {
	  return SMTNodeKind.UNMINUS.getString(smtlib1);
  }

  
  private static String letClose()
  {
	  if (smtlib1)
		  return ")\n";
	  else
		  return "))\n";
  }
  
  private static String letName()
  {
	  if (smtlib1)
		  return "?e" + SMTNode.getNodeCtr();
	  else
		  return "e" + SMTNode.getNodeCtr();
  }

  private static String oneBit()
  {
	  //bv1[1] bv0[1]");
	  if (smtlib1)
		  return "bv1[1]";
	  else
		  //return "#b1";
		  return "(_ bv1 1)";
		  		
  }
  
  private static String zeroBit()
  {
	  if (smtlib1)
		  return "bv0[1]";
	  else
		  //return "#b0";
		  return "(_ bv0 1)";
  }
  
  
  private static String fletName()
  {
	  if (smtlib1)
		  return "$e" + SMTNode.getNodeCtr();
	  else
		  return "e" + SMTNode.getNodeCtr();
  }

  
  private static String fletStart()
  {
	  if (smtlib1)
		  return "(flet (";
	  else
		  return "(let ((";
  }

  
  private static int generateBVArrayVars (Random r, List<SMTNode> nodes,
                                          int numArrays, int minBW, int maxBW) {
    int indexWidth, valWidth;
    String name;
    SMTNode node;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (numArrays > 0);
    assert (minBW > 0);
    assert (maxBW > 0);
    assert (maxBW >= minBW);

    builder = new StringBuilder();
    for (int i = 0; i < numArrays; i++) {
      indexWidth = selectRandValRange (r, minBW, maxBW); 
      assert (indexWidth >= minBW && indexWidth <= maxBW);
      valWidth = selectRandValRange (r, minBW, maxBW); 
      assert (valWidth >= minBW && valWidth <= maxBW);
      name = "a" + SMTNode.getNodeCtr();
      if (smtlib1)
      {
	      builder.append (":extrafuns ((");
	      builder.append (name);
	      builder.append (" Array[");
	      builder.append (indexWidth);
	      builder.append (":");
	      builder.append (valWidth);
	      builder.append ("]))\n");
      }
      else
      {
			builder.append("(declare-fun ");
			builder.append(name);
			builder.append(" () (Array (_ BitVec ");
			builder.append(indexWidth);
			builder.append(") (_ BitVec ");
			builder.append(valWidth);
			builder.append(")))\n");
      }
      
      node = new SMTNode (new BVArrayType (indexWidth, valWidth), name);
      nodes.add (node);
    }
    output.print (builder.toString());

    return numArrays;
  }

  private static int generateIntVars (List<SMTNode> nodes, int numVars){
    assert (nodes != null);
    assert (numVars >= 0);
    return generateVarsOfOneType (nodes, numVars, IntType.intType); 
  }

  private static int generateIntConsts (Random r, List<SMTNode> nodes,
                                        int numConsts, int maxBW){
    String name;
    BigInteger bi;
    int bw;
    StringBuilder builder;

    assert (nodes != null);
    assert (r != null);
    assert (nodes != null);
    assert (numConsts >= 0);
    assert (maxBW > 0);

    builder = new StringBuilder();
    for (int i = 0; i < numConsts; i++) {
      name = letName();
      bw = r.nextInt (maxBW) + 1;
      bi = new BigInteger(bw, r);
      builder.append (letStart());
      builder.append (name);
      builder.append (" ");
      builder.append (bi.toString());
      builder.append (letClose());
      nodes.add (new SMTNode (IntType.intType, name));
    }
    output.print (builder.toString());

    return numConsts;
  }

  private static int generateRealVars (List<SMTNode> nodes, int numVars){
    assert (nodes != null);
    assert (numVars >= 0);
    return generateVarsOfOneType (nodes, numVars, RealType.realType);
  }

  /* generates non empty list of int constants.
   * at least one constant is not mapped to zero */
  private static int generateIntConstsNotFilledZero (Random r,  
                                                     List<SMTNode> nodes,
                                                     Set<SMTNode> zeroConsts, 
                                                     int numConsts, int maxBW){
    String name;
    BigInteger bi;
    int bw;
    SMTNode node;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (zeroConsts != null);
    assert (numConsts > 0);
    assert (maxBW > 0);
    
    do {
      bw = r.nextInt (maxBW) + 1;
      bi = new BigInteger(bw, r);
    } while (bi.equals(BigInteger.ZERO));

    builder = new StringBuilder();
    for (int i = 0; i < numConsts; i++) {
      name = letName();
      builder.append (letStart());
      builder.append (name);
      builder.append (" ");
      builder.append (bi.toString());
      builder.append (letClose());
      node = new SMTNode (IntType.intType, name);
      nodes.add (node);
      if (bi.equals(BigInteger.ZERO))
        zeroConsts.add(node);
      bw = r.nextInt (maxBW) + 1;
      bi = new BigInteger(bw, r);
    }
    output.print (builder.toString());

    return numConsts;
  }

  /* generates non empty list of real constants.
   * at least one constant is not mapped to zero */
  private static int generateRealConstsNotFilledZero (Random r,  
                                                      List<SMTNode> nodes,
                                                      Set<SMTNode> zeroConsts, 
                                                      int numConsts, int maxBW,
                                                      boolean printAsReal){
    String name;
    BigInteger bi;
    int bw;
    SMTNode node;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (zeroConsts != null);
    assert (numConsts > 0);
    assert (maxBW > 0);
    
    do {
      bw = r.nextInt (maxBW) + 1;
      bi = new BigInteger(bw, r);
    } while (bi.equals(BigInteger.ZERO));

    builder = new StringBuilder();
    for (int i = 0; i < numConsts; i++) {
      name = letName();
      builder.append (letStart());
      builder.append (name);
      builder.append (" ");
      builder.append (bi.toString());
      if (printAsReal)
        builder.append (".0");
      builder.append (letClose());
      node = new SMTNode (RealType.realType, name);
      nodes.add (node);
      if (bi.equals(BigInteger.ZERO))
        zeroConsts.add(node);
      bw = r.nextInt (maxBW) + 1;
      bi = new BigInteger(bw, r);
    }
    output.print (builder.toString());

    return numConsts;
  }

  private static int generateUTypes (List<SMTType> types, int numUTypes){
    String name;
    StringBuilder builder;

    assert (types != null);
    assert (numUTypes > 0);

    builder = new StringBuilder();
    for (int i = 0; i < numUTypes; i++) {
      name = "S" + i;
      types.add (new UType (name));

      if (smtlib1)
      {
	      builder.append (":extrasorts (");
	      builder.append (name);
	      builder.append (")\n");
      }
      else
      {
          builder.append ("(declare-sort ");
          builder.append (name);
          builder.append (" 0 )\n");
      }
      
    }
    output.print (builder.toString());
    return numUTypes;
  }

  private static int generateUVars (List<SMTType> sorts, List<SMTNode> nodes,
                                    int numVars) {
    int generated = 0;
    int sizeSorts;

    assert (sorts != null);
    assert (sorts.size() > 0);
    assert (nodes != null);

    sizeSorts = sorts.size();
    for (int i = 0; i < sizeSorts; i++)
      generated += generateVarsOfOneType (nodes, numVars, sorts.get(i));

    assert (generated == sizeSorts * numVars);
    return generated;
  }

  private static int generateUFuncs (Random r, List<SMTType> sorts, 
                                     List<UFunc> funcs, int minNumFuncs, 
                                     int minArgs, int maxArgs) {
    int generated = 0;
    int numArgs, sizeSorts;
    Signature sig;
    ArrayList<SMTType> operandTypes;
    SMTType resultType, cur;
    HashSet<SMTType> todoResult, todoArg;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (sorts != null);
    assert (sorts.size() > 0);
    assert (funcs != null);
    assert (minNumFuncs > 0);
    assert (minArgs >= 1);
    assert (maxArgs >= minArgs);

    sizeSorts = sorts.size();
    /* each sort must be used as return type at least once */
    todoResult = new HashSet<SMTType>();
    for (int i = 0; i < sizeSorts; i++)
      todoResult.add (sorts.get(i));

    /* each sort must be used as argument type at least once */
    todoArg = new HashSet<SMTType>();
    for (int i = 0; i < sizeSorts; i++)
      todoArg.add (sorts.get(i));
    
    builder = new StringBuilder();
    while (!todoResult.isEmpty() || !todoArg.isEmpty() ||
           generated < minNumFuncs){
      name = "f" + UFunc.getFuncsCtr();
      numArgs = selectRandValRange (r, minArgs, maxArgs); 
      assert (numArgs >= minArgs);
      assert (numArgs <= maxArgs);
      operandTypes = new ArrayList<SMTType>(numArgs);
      for (int i = 0; i < numArgs; i++) {
        cur = sorts.get(r.nextInt(sizeSorts));
        operandTypes.add (cur);
        if (todoArg.contains (cur))
          todoArg.remove(cur);
      }
      resultType = sorts.get(r.nextInt(sizeSorts));
      if (todoResult.contains (resultType))
        todoResult.remove (resultType);
      sig = new Signature (operandTypes, resultType);
      funcs.add (new UFunc (name, sig));

      if (smtlib1)
      {
    	  builder.append (":extrafuns ((");
	      builder.append (name);
	      for (int i = 0; i < numArgs; i++) {
	        builder.append (" ");
	        builder.append (operandTypes.get(i).toString(smtlib1));
	      }
	      builder.append (" ");
	      builder.append (resultType.toString(smtlib1));
	      builder.append ("))\n");
      }
      else
      {
    	  // (declare-fun x_0 () Int)
    	  builder.append ("(declare-fun ");
	      builder.append (name);
	      builder.append (" (");

	      for (int i = 0; i < numArgs; i++) {
	        builder.append (operandTypes.get(i).toString(smtlib1)+" " );
	      }
          builder.append (")");
	      builder.append (" ");
	      builder.append (resultType.toString(smtlib1));
	      builder.append (")\n");
      }
   
      
      generated++;
    }
    output.print (builder.toString());
    assert (generated > 0);
    return generated;
  }

  private static int generateUPreds (Random r, List<SMTType> sorts, 
                                     List<UPred> preds, int minNumPreds, 
                                     int minArgs, int maxArgs) {
    int generated = 0;
    int numArgs, sizeSorts;
    Signature sig;
    ArrayList<SMTType> operandTypes;
    SMTType cur;
    HashSet<SMTType> todo;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (sorts != null);
    assert (sorts.size() > 0);
    assert (preds != null);
    assert (minNumPreds > 0);
    assert (minArgs >= 1);
    assert (maxArgs >= minArgs);

    /* each sort must be used as argument type at least once */
    sizeSorts = sorts.size();
    todo = new HashSet<SMTType>();
    for (int i = 0; i < sizeSorts; i++)
      todo.add (sorts.get(i));
    
    builder = new StringBuilder();
    while (!todo.isEmpty() || generated < minNumPreds){
      name = "p" + UPred.getPredsCtr();
      numArgs = selectRandValRange (r, minArgs, maxArgs);
      assert (numArgs >= minArgs);
      assert (numArgs <= maxArgs);
      operandTypes = new ArrayList<SMTType>(numArgs);
      for (int i = 0; i < numArgs; i++) {
        cur = sorts.get(r.nextInt(sizeSorts));
        if (todo.contains (cur))
          todo.remove (cur);
        operandTypes.add (cur);
      }
      sig = new Signature (operandTypes, BoolType.boolType);
      preds.add (new UPred (name, sig));
      
      if (smtlib1)
      {
	      builder.append (":extrapreds ((");
	      builder.append (name);
	      for (int i = 0; i < numArgs; i++) {
	        builder.append (" ");
	        builder.append (operandTypes.get(i).toString(smtlib1));
	      }
	      builder.append ("))\n");
      }
      else
      {
	      builder.append ("(declare-fun ");
	      builder.append (name);
	      builder.append (" (");
	      for (int i = 0; i < numArgs; i++) {
	    	  builder.append (operandTypes.get(i).toString(smtlib1) + " ");
	      }
	      builder.append (" )");
	      builder.append (" Bool )\n");
      }
      
      generated++;
    }
    output.print (builder.toString());
    assert (generated > 0);
    return generated;
  }

  private static int generateUFuncsBV (Random r, List<UFunc> funcs, 
                                       int numFuncs, int minArgs, int maxArgs,
                                       int minBW, int maxBW) {
    int numArgs, bw;
    Signature sig;
    ArrayList<SMTType> operandTypes;
    SMTType resultType;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (funcs != null);
    assert (numFuncs >= 0);
    assert (minArgs >= 1);
    assert (maxArgs >= minArgs);
    assert (minBW > 0);
    assert (maxBW >= minBW);

    builder = new StringBuilder();
    for (int i = 0; i < numFuncs; i++) {
      name = "f" + UFunc.getFuncsCtr();
      numArgs = selectRandValRange (r, minArgs, maxArgs);
      assert (numArgs >= minArgs);
      assert (numArgs <= maxArgs);
      operandTypes = new ArrayList<SMTType>(numArgs);
      for (int j = 0; j < numArgs; j++) {
        bw = selectRandValRange (r, minBW, maxBW);
        assert (bw >= minBW);
        assert (bw <= maxBW);
        operandTypes.add (new BVType (bw));
      }
      bw = selectRandValRange (r, minBW, maxBW);
      assert (bw >= minBW);
      assert (bw <= maxBW);
      resultType = new BVType (bw);
      sig = new Signature (operandTypes, resultType);
      funcs.add (new UFunc (name, sig));

      if (smtlib1)
      {
	      builder.append (":extrafuns ((");
	      builder.append (name);
	      for (int j = 0; j < numArgs; j++) {
	        builder.append (" ");
	        builder.append (operandTypes.get(j).toString(smtlib1));
	      }
	      builder.append (" ");
	      builder.append (resultType.toString(smtlib1));
	      builder.append ("))\n");
      }
      else
      {
          builder.append ("(declare-fun ");
          builder.append (name);
          builder.append (" (");
          for (int j = 0; j < numArgs; j++) {
            builder.append (" ");
            builder.append (operandTypes.get(j).toString(smtlib1));
          }
          builder.append (") ");
          builder.append (resultType.toString(smtlib1));
          builder.append (")\n");
          }
    	  
      
    }
    output.print (builder.toString());
    return numFuncs;
  }

  private static int generateUPredsBV (Random r, List<UPred> preds, 
                                       int numPreds, int minArgs, int maxArgs,
                                       int minBW, int maxBW) {
    int numArgs, bw;
    Signature sig;
    ArrayList<SMTType> operandTypes;
    HashSet<SMTType> todo;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (preds != null);
    assert (numPreds >= 0);
    assert (minArgs >= 1);
    assert (maxArgs >= minArgs);
    assert (minBW > 0);
    assert (maxBW >= minBW);

    builder = new StringBuilder();
    for (int i = 0; i < numPreds; i++){
      name = "p" + UPred.getPredsCtr();
      numArgs = selectRandValRange (r, minArgs, maxArgs);
      assert (numArgs >= minArgs);
      assert (numArgs <= maxArgs);
      operandTypes = new ArrayList<SMTType>(numArgs);
      for (int j = 0; j < numArgs; j++) {
        bw = selectRandValRange(r, minBW, maxBW);
        assert (bw >= minBW);
        assert (bw <= maxBW);
        operandTypes.add (new BVType(bw));
      }
      sig = new Signature (operandTypes, BoolType.boolType);
      preds.add (new UPred (name, sig));

      if (smtlib1)
      {
	      builder.append (":extrapreds ((");
	      builder.append (name);
	      for (int j = 0; j < numArgs; j++) {
	        builder.append (" ");
	        builder.append (operandTypes.get(j).toString(smtlib1));
	      }
	      builder.append ("))\n");
      }
      else
      {
	      builder.append ("(declare-fun ");
	      builder.append (name);
	      builder.append (" (");
	      for (int j = 0; j < numArgs; j++) {
	    	  builder.append (operandTypes.get(j).toString(smtlib1) + " ");
	      }
	      builder.append (" )");
	      builder.append (" Bool )\n");
      }

    }
    output.print (builder.toString());
    return numPreds;
  }

/*----------------------------------------------------------------------------*/
/* Main layer                                                                 */
/*----------------------------------------------------------------------------*/

  private static int generateBVLayer (Random r,  List<SMTNode> nodes,
                                      int minRefs, int minBW, int maxBW,
                                      BVDivMode divMode,
                                      HashMap<SMTNode, SMTNodeKind> guards,
                                      boolean noBlowup, List<UFunc> uFuncs,
                                      List<UPred> uPreds){
    int oldSize, upper, lower, maxRep, rep, ext, rotate, pos, tmp;
    int sizeOpTypes, n1BW, n2BW, n3BW, resBW = 0;
    int sizeUFuncs, sizeUPreds;
    SMTNodeKind kind;
    EnumSet<SMTNodeKind> kindSet;
    SMTNodeKind []kinds;
    SMTNode []todoNodesArray;
    UFunc []todoUFuncsArray;
    UPred []todoUPredsArray;
    String name;
    UFunc uFunc;
    UPred uPred;
    Signature sig;
    HashMap<SMTNode, Integer> todoNodes; 
    HashMap<UFunc, Integer> todoUFuncs; 
    HashMap<UPred, Integer> todoUPreds; 
    SMTNode n1, n2, n3, tmpNode;
    BVType curType;
    List<SMTType> operandTypes;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (minRefs > 0);
    assert (!nodes.isEmpty());
    assert (minBW > 0);
    assert (maxBW > 0);
    assert (maxBW >= minBW);
    assert (divMode != BVDivMode.GUARD || (guards != null));
    assert (uFuncs != null);
    assert (uPreds != null);
    assert (SMTNodeKind.BVNOT.ordinal() < SMTNodeKind.CONCAT.ordinal());

    kindSet = EnumSet.range (SMTNodeKind.BVNOT, SMTNodeKind.CONCAT);
    kindSet.add (SMTNodeKind.EQ);
    kindSet.add (SMTNodeKind.DISTINCT);
    kindSet.add (SMTNodeKind.ITE);
    if (divMode == BVDivMode.OFF) {
      kindSet.remove (SMTNodeKind.BVUDIV);
      kindSet.remove (SMTNodeKind.BVSDIV);
      kindSet.remove (SMTNodeKind.BVUREM);
      kindSet.remove (SMTNodeKind.BVSREM);
      kindSet.remove (SMTNodeKind.BVSMOD);
    }
    if (!uFuncs.isEmpty())
      kindSet.add (SMTNodeKind.UFUNC);
    if (!uPreds.isEmpty())
      kindSet.add (SMTNodeKind.UPRED);
    kinds = kindSet.toArray(new SMTNodeKind[0]);

    oldSize = nodes.size();
    todoNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < oldSize; i++)
      todoNodes.put (nodes.get(i), new Integer(0));

    todoUFuncs = new HashMap<UFunc, Integer>();
    sizeUFuncs = uFuncs.size();
    for (int i = 0; i < sizeUFuncs; i++)
      todoUFuncs.put (uFuncs.get(i), new Integer(0));

    todoUPreds = new HashMap<UPred, Integer>();
    sizeUPreds = uPreds.size();
    for (int i = 0; i < sizeUPreds; i++)
      todoUPreds.put (uPreds.get(i), new Integer(0));

    builder = new StringBuilder();
    while (!todoNodes.isEmpty() || !todoUFuncs.isEmpty() ||
           !todoUPreds.isEmpty()){
      name = letName();
      builder.append (letStart());
      builder.append (name);
      builder.append (" (");

      /* increase probability that ufunc or upred is selected
       * if todo list is not empty */
      if (!todoUFuncs.isEmpty() && r.nextBoolean())
        kind = SMTNodeKind.UFUNC;
      else if (!todoUPreds.isEmpty() && r.nextBoolean())
        kind = SMTNodeKind.UPRED;
      else
        kind = kinds[r.nextInt (kinds.length)];

      if (noBlowup && r.nextBoolean() && !todoNodes.isEmpty()) { 
        todoNodesArray = todoNodes.keySet().toArray(new SMTNode[0]);
        n1 = todoNodesArray[r.nextInt(todoNodesArray.length)];
      } else {
        n1 = nodes.get(r.nextInt(nodes.size()));
      }
      assert (n1.getType() instanceof BVType);
      n1BW = ((BVType) n1.getType()).width;
      switch (kind.arity) {
        case 1:
          builder.append (kind.getString(smtlib1));
          switch (kind) {
            case BVNOT:
            case BVNEG:
              builder.append (" ");
              resBW = n1BW;
              break;
            case EXTRACT:
              upper = r.nextInt(n1BW);
              lower = r.nextInt (upper + 1);

              if (smtlib1)
              {
	              builder.append ("[");
	              builder.append (upper);
	              builder.append (":");
	              builder.append (lower);
	              builder.append ("] ");
              }
              else
              {
            	  builder.append (" ");
	              builder.append (upper);
	              builder.append (" ");
	              builder.append (lower);
	              builder.append (") ");
              }
              
              resBW = upper - lower + 1;
              break;
            case ROTATE_LEFT:
            case ROTATE_RIGHT:
              // smtlib2 states explicitly that the rotate is performed modulo the bit-width.
              if (smtlib1)
            	  rotate = r.nextInt(n1BW);
              else
            	  rotate = r.nextInt(n1BW+2);
              if (smtlib1)
              {
	              builder.append ("[");
	              builder.append (rotate);
	              builder.append ("] ");
              }
              else
              {
                  builder.append (" ");
                  builder.append (rotate);
                  builder.append (") ");
              }
              resBW = n1BW;
              break;
            case ZERO_EXTEND:
            case SIGN_EXTEND:
              ext = r.nextInt(maxBW - n1BW + 1);
              if (smtlib1)
              {
	              builder.append ("[");
	              builder.append (ext);
	              builder.append ("] ");
              }
              else
              {
	              builder.append (" ");
	              builder.append (ext);
	              builder.append (") ");
              }
              resBW = n1BW + ext;
              break;
            default:
              assert (kind == SMTNodeKind.REPEAT);
              maxRep = maxBW / n1BW;
              rep = r.nextInt(maxRep) + 1;
              
              if (smtlib1)
              {
	              builder.append ("[");
	              builder.append (rep);
	              builder.append ("] ");
              }
              else
              {
	              builder.append (" ");
	              builder.append (rep);
	              builder.append (") ");
              }
              
              resBW = n1BW * rep;
              break;
          }
          builder.append (n1.getName());
          updateNodeRefs (todoNodes, n1, minRefs);
          break;
        case 2:
          n2 = nodes.get(r.nextInt(nodes.size()));
          assert (n2.getType() instanceof BVType);
          n2BW = ((BVType) n2.getType()).width;

          /* choose another binary operator if concat
           * exceeds maximum bit-width */
          if (kind == SMTNodeKind.CONCAT && n1BW + n2BW > maxBW) {
            do {
              kind = kinds[r.nextInt (kinds.length)];
            } while (kind.arity != 2 || kind == SMTNodeKind.CONCAT);
          }

          switch (kind) {
            case BVULT:
            case BVULE:
            case BVUGT:
            case BVUGE:
            case BVSLT:
            case BVSLE:
            case BVSGT:
            case BVSGE:
            case EQ:
              /* encode boolean results into bit-vector */
              builder.append ("ite (");
              builder.append (kind.getString(smtlib1));
              builder.append (" ");
              builder.append (wrapEqualBW (r, n1, n2));
           	  builder.append (")"+oneBit() +" " +zeroBit());
              resBW = 1;
              break;
            case CONCAT:
              builder.append (kind.getString(smtlib1));
              builder.append (" ");
              builder.append (n1.getName());
              builder.append (" ");
              builder.append (n2.getName());
              resBW = n1BW + n2BW;
              break;
            case BVUDIV:
            case BVSDIV:
            case BVUREM:
            case BVSREM:
            case BVSMOD:
              if (divMode == BVDivMode.GUARD) {
                /* assumption 
                 * wrapEqualBW tries to extend the first node before
                 * it tries to extend the second node
                 */

               /* we swap the nodes if the seond node would be extended  */
                if (n1BW > n2BW) {
                  tmp = n1BW;
                  n1BW = n2BW;
                  n2BW = tmp;
                  tmpNode = n1;
                  n1 = n2;
                  n2 = tmpNode;
                }
                /* update guards if necessary */
                if (!guards.containsKey(n2) || 
                    guards.get(n2) == SMTNodeKind.BVUDIV ||
                    guards.get(n2) == SMTNodeKind.BVUREM)
                  guards.put(n2, kind);
                /* fall through by intention */
              }
            default:
              builder.append (kind.getString(smtlib1));
              builder.append (" ");
              builder.append (wrapEqualBW (r, n1, n2));
              if (kind == SMTNodeKind.BVCOMP) {
                resBW = 1;
              } else  {
                if (n1BW < n2BW)
                  resBW = n2BW;
                else
                  resBW = n1BW;
              }
              break;
          }
          updateNodeRefs (todoNodes, n1, minRefs);
          updateNodeRefs (todoNodes, n2, minRefs);
          break;
        case 3:
          assert (kind == SMTNodeKind.ITE);
          n2 = nodes.get(r.nextInt(nodes.size()));
          assert (n2.getType() instanceof BVType);
          n2BW = ((BVType) n2.getType()).width;
          n3 = nodes.get(r.nextInt(nodes.size()));
          assert (n3.getType() instanceof BVType);
          n3BW = ((BVType) n3.getType()).width;
          pos = r.nextInt(n1BW);
          builder.append (kind.getString(smtlib1));
          /* ite condition: is bit at random bit position set to 1? */
          if (smtlib1)
          {
	          builder.append (" (= "+oneBit()+" (extract[");
	          builder.append (pos);
	          builder.append (":");
	          builder.append (pos);
	          builder.append ("] ");
	          builder.append (n1.getName());
	          builder.append (")) ");
          }
          else
          {
	          builder.append (" (= "+oneBit()+" ((_ extract ");
	          builder.append (pos);
	          builder.append (" ");
	          builder.append (pos);
	          builder.append (") ");
	          builder.append (n1.getName());
	          builder.append (")) ");
         }
          
          builder.append (wrapEqualBW(r, n2, n3));
          if (n2BW < n3BW)
            resBW = n3BW;
          else  
            resBW = n2BW;
          updateNodeRefs (todoNodes, n1, minRefs);
          updateNodeRefs (todoNodes, n2, minRefs);
          updateNodeRefs (todoNodes, n3, minRefs);
          break;
        default:
          assert (kind.arity == -1);
          switch (kind){
            case UFUNC:
              if (!todoUFuncs.isEmpty() && r.nextBoolean()) {
                todoUFuncsArray = todoUFuncs.keySet().toArray (new UFunc[0]);
                uFunc = todoUFuncsArray[r.nextInt(todoUFuncsArray.length)];
              } else {
                uFunc = uFuncs.get(r.nextInt(sizeUFuncs));
              }
              updateFuncRefs (todoUFuncs, uFunc, minRefs);
              builder.append (uFunc.getName());
              sig = uFunc.getSignature();
              operandTypes = sig.getOperandTypes();
              sizeOpTypes = operandTypes.size();
              assert (sizeOpTypes > 0);
              curType = (BVType) operandTypes.get(0);
              builder.append (" ");
              builder.append (adaptBW (r, n1, curType.getWidth()));
              updateNodeRefs (todoNodes, n1, minRefs);
              for (int i = 1; i < sizeOpTypes; i++) {
                n2 = nodes.get(r.nextInt(nodes.size()));
                assert (n2.getType() instanceof BVType);
                assert (operandTypes.get(i) instanceof BVType);
                curType = (BVType) operandTypes.get(i);
                builder.append (" ");
                builder.append (adaptBW (r, n2, curType.getWidth()));
                updateNodeRefs (todoNodes, n2, minRefs);
              }
              assert (sig.getResultType() instanceof BVType);
              curType = (BVType) sig.getResultType();
              resBW = curType.getWidth();
              break;
            case UPRED:
              if (!todoUPreds.isEmpty() && r.nextBoolean()) {
                todoUPredsArray = todoUPreds.keySet().toArray (new UPred[0]);
                uPred = todoUPredsArray[r.nextInt(todoUPredsArray.length)];
              } else {
                uPred = uPreds.get(r.nextInt(sizeUPreds));
              }
              updatePredRefs (todoUPreds, uPred, minRefs);
              builder.append ("ite (");
              builder.append (uPred.getName());
              sig = uPred.getSignature();
              operandTypes = sig.getOperandTypes();
              sizeOpTypes = operandTypes.size();
              assert (sizeOpTypes > 0);
              curType = (BVType) operandTypes.get(0);
              builder.append (" ");
              builder.append (adaptBW (r, n1, curType.getWidth()));
              updateNodeRefs (todoNodes, n1, minRefs);
              for (int i = 1; i < sizeOpTypes; i++) {
                n2 = nodes.get(r.nextInt(nodes.size()));
                assert (n2.getType() instanceof BVType);
                assert (operandTypes.get(i) instanceof BVType);
                curType = (BVType) operandTypes.get(i);
                builder.append (" ");
                builder.append (adaptBW (r, n2, curType.getWidth()));
                updateNodeRefs (todoNodes, n2, minRefs);
              }
              builder.append (")"+oneBit() +" " +zeroBit());
            	  
              
              assert (sig.getResultType() == BoolType.boolType);
              resBW = 1;
              break;
            default:
              assert (kind == SMTNodeKind.DISTINCT);
              n2 = nodes.get(r.nextInt(nodes.size()));
              assert (n2.getType() instanceof BVType);
              n2BW = ((BVType) n2.getType()).width;
              builder.append ("ite (");
              builder.append (kind.getString(smtlib1));
              builder.append (" ");
              builder.append (wrapEqualBW (r, n1, n2));
              builder.append (")"+oneBit() +" " +zeroBit());
              resBW = 1;
              updateNodeRefs (todoNodes, n1, minRefs);
              updateNodeRefs (todoNodes, n2, minRefs);
              break;
          }
          break;
      }

      builder.append (")");
      builder.append (letClose());
      assert (resBW <= maxBW);
      nodes.add (new SMTNode (new BVType (resBW), name));

    }
    output.print (builder.toString());
    assert (nodes.size() - oldSize > 0);
    return nodes.size() - oldSize;
  }

  private static int generateBVWriteLayer (Random r, List<SMTNode> arrays, 
                                           List<SMTNode> bvs, int numWrites){

    int aIndexWidth, aValWidth, indexWidth, valWidth;
    SMTNode array, index, val;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (arrays != null);
    assert (!arrays.isEmpty());
    assert (bvs != null);
    assert (!bvs.isEmpty());
    assert (numWrites >= 0);

    builder = new StringBuilder();
    for (int i = 0; i < numWrites; i++) {
      name = letName();
      array = arrays.get(r.nextInt(arrays.size()));
      assert (array.getType() instanceof BVArrayType);
      aIndexWidth = ((BVArrayType) array.getType()).indexWidth;
      aValWidth = ((BVArrayType) array.getType()).valWidth;
      builder.append (letStart());
      builder.append (name);
      builder.append (" (store ");
      builder.append (array.getName());
      builder.append (" ");

      index = bvs.get(r.nextInt(bvs.size()));
      assert (index.getType() instanceof BVType);
      indexWidth = ((BVType) index.getType()).width;
      val = bvs.get(r.nextInt(bvs.size()));
      assert (val.getType() instanceof BVType);
      valWidth = ((BVType) val.getType()).width;

      builder.append (adaptBW (r, index, aIndexWidth));
      builder.append (" ");
      builder.append (adaptBW (r, val, aValWidth));
      builder.append (")");
      builder.append (letClose());
      arrays.add (new SMTNode (new BVArrayType (aIndexWidth, aValWidth), name));
    }
    output.print (builder.toString());
    return numWrites;
  }

  private static int generateBVReadLayer (Random r, List<SMTNode> arrays, 
                                          List<SMTNode> bvs, int numReads){

    int aIndexWidth, aValWidth, indexWidth, sizeArrays;
    SMTNode array, index;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (arrays != null);
    assert (!arrays.isEmpty());
    assert (bvs != null);
    assert (!bvs.isEmpty());
    assert (numReads >= 0);

    builder = new StringBuilder();
    sizeArrays = arrays.size();
    for (int i = 0; i < numReads; i++) {
      name = letName();
      array = arrays.get(r.nextInt(sizeArrays));
      assert (array.getType() instanceof BVArrayType);
      aIndexWidth = ((BVArrayType) array.getType()).indexWidth;
      aValWidth = ((BVArrayType) array.getType()).valWidth;
      builder.append (letStart());
      builder.append (name);
      builder.append (" (select ");
      builder.append (array.getName());
      builder.append (" ");

      index = bvs.get(r.nextInt(bvs.size()));
      assert (index.getType() instanceof BVType);
      indexWidth = ((BVType) index.getType()).width;

      builder.append (adaptBW (r, index, aIndexWidth));
      builder.append (")");
      builder.append (letClose());
      bvs.add (new SMTNode (new BVType (aValWidth), name));
    }
    output.print (builder.toString());
    return numReads;
  }

  private static int generateBVArrayExtBVLayer (Random r, List<SMTNode> arrays, 
                                                List<SMTNode> bvs, int numExt) {

    SMTNode a1, a2;
    int oldSize, sizeArrays;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (arrays != null);
    assert (!arrays.isEmpty());
    assert (bvs != null);
    assert (numExt >= 0);

    builder = new StringBuilder();
    oldSize = bvs.size();
    sizeArrays = arrays.size();
    for (int i = 0; i < numExt; i++) {
      name = letName();
      do {
        a1 = arrays.get(r.nextInt(sizeArrays));
        a2 = arrays.get(r.nextInt(sizeArrays));
        assert (a1.getType() instanceof BVArrayType);
        assert (a2.getType() instanceof BVArrayType);
      } while (!a1.getType().equals(a2.getType()));
      builder.append (letStart());
      builder.append (name);
      builder.append (" (ite (= ");
      builder.append (a1.getName());
      builder.append (" ");
      builder.append (a2.getName());
      builder.append (")"+oneBit() +" " +zeroBit());
      builder.append (letClose());
      bvs.add (new SMTNode (new BVType (1), name));
    }
    output.print (builder.toString());
    assert (bvs.size() - oldSize >= 0);
    return bvs.size() - oldSize;
  }

  private static int generateWriteLayer (Random r, List<SMTNode> arrays, 
                                         List<SMTNode> indices, 
                                         List<SMTNode> elements, 
                                         SMTType resultType,
                                         int numWrites) {

    int oldSize, sizeIndices, sizeElements; 
    SMTNode array, index, element;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (arrays != null);
    assert (!arrays.isEmpty());
    assert (indices != null);
    assert (!indices.isEmpty());
    assert (elements != null);
    assert (!elements.isEmpty());
    assert (resultType != null);
    assert (numWrites >= 0);

    builder = new StringBuilder();
    sizeIndices = indices.size();
    sizeElements = elements.size();
    for (int i = 0; i < numWrites; i++) {
      name = letName();
      array = arrays.get(r.nextInt(arrays.size()));
      assert (array.getType() instanceof ArrayType);
      builder.append (letStart());
      builder.append (name);
      builder.append (" (store ");
      builder.append (array.getName());
      builder.append (" ");
      index = indices.get(r.nextInt(sizeIndices));
      element = elements.get(r.nextInt(sizeElements));
      builder.append (index.getName());
      builder.append (" ");
      builder.append (element.getName());
      builder.append (")");
      builder.append (letClose());
      arrays.add (new SMTNode (resultType, name));
    }
    output.print (builder.toString());
    return numWrites;
  }

  private static int generateReadLayer (Random r, List<SMTNode> arrays, 
                                        List<SMTNode> indices,
                                        List<SMTNode> elements,
                                        SMTType resultType,
                                        int numReads){

    int sizeArrays, sizeIndices;
    SMTNode array, index;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (arrays != null);
    assert (!arrays.isEmpty());
    assert (indices != null);
    assert (!indices.isEmpty());
    assert (elements != null);
    assert (resultType != null);
    assert (numReads >= 0);

    builder = new StringBuilder();
    sizeArrays = arrays.size();
    sizeIndices = indices.size();
    for (int i = 0; i < numReads; i++) {
      name = letName();
      array = arrays.get(r.nextInt(sizeArrays));
      assert (array.getType() instanceof ArrayType);
      builder.append (letStart());
      builder.append (name);
      builder.append (" (select ");
      builder.append (array.getName());
      builder.append (" ");
      index = indices.get(r.nextInt(sizeIndices));
      builder.append (index.getName());
      builder.append (")");
      builder.append (letClose());
      elements.add (new SMTNode (resultType, name));
    }
    output.print (builder.toString());
    return numReads;
  }

  private static int generateIntLayer (Random r, List<SMTNode> intNodes,
                                       List<SMTNode> intConsts, 
                                       List<UFunc> uFuncs, List<UPred> uPreds,
                                       boolean linear, int minRefs, 
                                       boolean noBlowup){ 
    HashMap<SMTNode, Integer> todoIntNodes; 
    HashMap<SMTNode, Integer> todoIntConsts; 
    HashMap<UFunc, Integer> todoUFuncs; 
    HashMap<UPred, Integer> todoUPreds; 
    int oldSize, sizeIntConsts, sizeOpTypes, sizeUFuncs, sizeUPreds;
    String name;
    SMTNode n1, n2;
    SMTNode []todoArray;
    EnumSet<SMTNodeKind> kindSet;
    SMTNodeKind [] kinds;
    SMTNodeKind kind;
    UFunc []todoUFuncsArray;
    UPred []todoUPredsArray;
    UFunc uFunc;
    UPred uPred;
    Signature sig;
    List<SMTType> operandTypes;
    StringBuilder builder;

    assert (r != null);
    assert (intNodes != null);
    assert (!intNodes.isEmpty());
    assert (intConsts != null);
    assert (!intConsts.isEmpty());
    assert (uFuncs != null);
    assert (uPreds != null);
    assert (minRefs > 0);

    kindSet = EnumSet.range (SMTNodeKind.PLUS, SMTNodeKind.MUL);
    if (!uFuncs.isEmpty())
      kindSet.add (SMTNodeKind.UFUNC);
    if (!uPreds.isEmpty())
      kindSet.add (SMTNodeKind.UPRED);
    kinds = kindSet.toArray(new SMTNodeKind[0]);

    todoIntNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < intNodes.size(); i++)
      todoIntNodes.put (intNodes.get(i), new Integer(0));

    todoIntConsts = new HashMap<SMTNode, Integer>();
    sizeIntConsts = intConsts.size();
    for (int i = 0; i < sizeIntConsts; i++)
      todoIntConsts.put (intConsts.get(i), new Integer(0));

    todoUFuncs = new HashMap<UFunc, Integer>();
    sizeUFuncs = uFuncs.size();
    for (int i = 0; i < sizeUFuncs; i++)
      todoUFuncs.put (uFuncs.get(i), new Integer(0));

    todoUPreds = new HashMap<UPred, Integer>();
    sizeUPreds = uPreds.size();
    for (int i = 0; i < sizeUPreds; i++)
      todoUPreds.put (uPreds.get(i), new Integer(0));

    builder = new StringBuilder();
    oldSize = intNodes.size();
    while (!todoIntNodes.isEmpty() || !todoIntConsts.isEmpty() ||
           !todoUFuncs.isEmpty() || !todoUPreds.isEmpty()) {
      name = letName();
      kind = kinds[r.nextInt(kinds.length)];
      builder.append (letStart());
      builder.append (name);
      builder.append (" (");
      if (noBlowup && r.nextBoolean() && !todoIntNodes.isEmpty()) {
        todoArray = todoIntNodes.keySet().toArray (new SMTNode[0]);
        n1 = todoArray[r.nextInt(todoArray.length)];
      } else {
        n1 = intNodes.get(r.nextInt(intNodes.size()));
      }
      assert (n1.getType() == IntType.intType);
      switch (kind) {
        case PLUS:
        case BINMINUS:
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          n2 = intNodes.get(r.nextInt(intNodes.size()));
          assert (n2.getType() == IntType.intType);
          builder.append (n1.getName());
          builder.append (" ");
          builder.append (n2.getName());
          updateNodeRefs (todoIntNodes, n1, minRefs);
          updateNodeRefs (todoIntNodes, n2, minRefs);
          break;
        case MUL:
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          if (linear || r.nextBoolean()) {
            n2 = intConsts.get(r.nextInt(sizeIntConsts));
            assert (n2.getType() == IntType.intType);
            switch (r.nextInt(4)) {
              case 0:
                builder.append (n1.getName());
                builder.append (" ");
                builder.append (n2.getName());
                break;
              case 1:
                builder.append (n2.getName());
                builder.append (" ");
                builder.append (n1.getName());
                break;
              case 2:
                builder.append (n1.getName());
                builder.append (" ("+uMinus()+" ");
                builder.append (n2.getName());
                builder.append (")");
                break;
              case 3:
                builder.append ("("+uMinus()+" ");
                builder.append (n2.getName());
                builder.append (") ");
                builder.append (n1.getName());
                break;
            }
            updateNodeRefs (todoIntConsts, n2, minRefs);
          } else {
            n2 = intNodes.get(r.nextInt(intNodes.size()));
            assert (n2.getType() == IntType.intType);
            builder.append (n1.getName());
            builder.append (" ");
            builder.append (n2.getName());
            updateNodeRefs (todoIntNodes, n2, minRefs);
          }
          updateNodeRefs (todoIntNodes, n1, minRefs);
          break;
        case UNMINUS:
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          builder.append (n1.getName());
          updateNodeRefs (todoIntNodes, n1, minRefs);
          break;
        case UFUNC:
          if (!todoUFuncs.isEmpty() && r.nextBoolean()) {
            todoUFuncsArray = todoUFuncs.keySet().toArray (new UFunc[0]);
            uFunc = todoUFuncsArray[r.nextInt(todoUFuncsArray.length)];
          } else {
            uFunc = uFuncs.get(r.nextInt(sizeUFuncs));
          }
          updateFuncRefs (todoUFuncs, uFunc, minRefs);
          builder.append (uFunc.getName());
          sig = uFunc.getSignature();
          operandTypes = sig.getOperandTypes();
          sizeOpTypes = operandTypes.size();
          assert (sizeOpTypes > 0);
          assert (operandTypes.get(0) == IntType.intType);
          builder.append (" ");
          builder.append (n1.getName());
          updateNodeRefs (todoIntNodes, n1, minRefs);
          for (int i = 1; i < sizeOpTypes; i++) {
            n2 = intNodes.get(r.nextInt(intNodes.size()));
            assert (n2.getType() == IntType.intType);
            assert (operandTypes.get(i) == IntType.intType);
            builder.append (" ");
            builder.append (n2.getName());
            updateNodeRefs (todoIntNodes, n2, minRefs);
          }
          assert (sig.getResultType() == IntType.intType);
          break;
        case UPRED:
          if (!todoUPreds.isEmpty() && r.nextBoolean()) {
            todoUPredsArray = todoUPreds.keySet().toArray (new UPred[0]);
            uPred = todoUPredsArray[r.nextInt(todoUPredsArray.length)];
          } else {
            uPred = uPreds.get(r.nextInt(sizeUPreds));
          }
          updatePredRefs (todoUPreds, uPred, minRefs);
          builder.append ("ite (");
          builder.append (uPred.getName());
          sig = uPred.getSignature();
          operandTypes = sig.getOperandTypes();
          sizeOpTypes = operandTypes.size();
          assert (sizeOpTypes > 0);
          assert (operandTypes.get(0) == IntType.intType);
          builder.append (" ");
          builder.append (n1.getName());
          updateNodeRefs (todoIntNodes, n1, minRefs);
          for (int i = 1; i < sizeOpTypes; i++) {
            n2 = intNodes.get(r.nextInt(intNodes.size()));
            assert (n2.getType() == IntType.intType);
            assert (operandTypes.get(i) == IntType.intType);
            builder.append (" ");
            builder.append (n2.getName());
            updateNodeRefs (todoIntNodes, n2, minRefs);
          }
          builder.append (") 1 0");
          assert (sig.getResultType() == BoolType.boolType);
          break;
      }
      builder.append (")");
      builder.append (letClose());
        
      intNodes.add (new SMTNode (IntType.intType, name));
    }
    output.print (builder.toString());
    assert (intNodes.size() - oldSize > 0);
    return intNodes.size() - oldSize;
  }

  private static int generateRealLayer (Random r, List<SMTNode> realNodes,
                                        List<SMTNode> intConstsAsReal, 
                                        Set<SMTNode> zeroConsts, 
                                        List<UFunc> uFuncs, List<UPred> uPreds,
                                        boolean linear, 
                                        boolean printConstsAsReal,
                                        int minRefs, boolean noBlowup){ 
    HashMap<SMTNode, Integer> todoRealNodes; 
    HashMap<SMTNode, Integer> todoIntConsts; 
    HashMap<UFunc, Integer> todoUFuncs; 
    HashMap<UPred, Integer> todoUPreds; 
    int oldSize, sizeIntConsts, sizeUFuncs, sizeUPreds, sizeOpTypes;
    String name;
    SMTNode []todoArray;
    SMTNode n2, c1, c2, n1 = null;
    EnumSet<SMTNodeKind> kindSet;
    SMTNodeKind [] kinds;
    SMTNodeKind kind;
    UFunc []todoUFuncsArray;
    UPred []todoUPredsArray;
    UFunc uFunc;
    UPred uPred;
    Signature sig;
    List<SMTType> operandTypes;
    StringBuilder builder;

    assert (r != null);
    assert (realNodes != null);
    assert (!realNodes.isEmpty());
    assert (intConstsAsReal != null);
    assert (!intConstsAsReal.isEmpty());
    assert (zeroConsts != null);
    assert (zeroConsts.size() < intConstsAsReal.size());
    assert (uFuncs != null); 
    assert (uPreds != null); 
    assert (minRefs > 0);

    kindSet = EnumSet.range (SMTNodeKind.PLUS, SMTNodeKind.DIV);
    if (!uFuncs.isEmpty())
      kindSet.add (SMTNodeKind.UFUNC);
    if (!uPreds.isEmpty())
      kindSet.add (SMTNodeKind.UPRED);
    kinds = kindSet.toArray(new SMTNodeKind[0]);

    todoRealNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < realNodes.size(); i++)
      todoRealNodes.put (realNodes.get(i), new Integer(0));

    todoIntConsts = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < intConstsAsReal.size(); i++)
      todoIntConsts.put (intConstsAsReal.get(i), new Integer(0));

    todoUFuncs = new HashMap<UFunc, Integer>();
    sizeUFuncs = uFuncs.size();
    for (int i = 0; i < sizeUFuncs; i++)
      todoUFuncs.put (uFuncs.get(i), new Integer(0));

    todoUPreds = new HashMap<UPred, Integer>();
    sizeUPreds = uPreds.size();
    for (int i = 0; i < sizeUPreds; i++)
      todoUPreds.put (uPreds.get(i), new Integer(0));

    builder = new StringBuilder();
    oldSize = realNodes.size();
    sizeIntConsts = intConstsAsReal.size();
    while (!todoRealNodes.isEmpty() || !todoIntConsts.isEmpty() ||
           !todoUFuncs.isEmpty() || !todoUPreds.isEmpty()){
      name = letName();
      kind = kinds[r.nextInt(kinds.length)];
      builder.append (letStart());
      builder.append (name);
      builder.append (" (");
      if (kind != SMTNodeKind.DIV) {
        if (noBlowup && r.nextBoolean() && !todoRealNodes.isEmpty()) {
          todoArray = todoRealNodes.keySet().toArray (new SMTNode[0]);
          n1 = todoArray[r.nextInt(todoArray.length)];
        } else {
          n1 = realNodes.get(r.nextInt(realNodes.size()));
        }
      }
      switch (kind) {
        case PLUS:
        case BINMINUS:
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          n2 = realNodes.get(r.nextInt(realNodes.size()));
          assert (n2.getType() == RealType.realType);
          builder.append (n1.getName());
          builder.append (" ");
          builder.append (n2.getName());
          updateNodeRefs (todoRealNodes, n1, minRefs);
          updateNodeRefs (todoRealNodes, n2, minRefs);
          break;
        case MUL:
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          if (linear || r.nextBoolean()) {
            n2 = intConstsAsReal.get(r.nextInt(sizeIntConsts));
            assert (n2.getType() == RealType.realType);
            switch (r.nextInt(4)) {
              case 0:
                builder.append (n1.getName());
                builder.append (" ");
                builder.append (n2.getName());
                break;
              case 1:
                builder.append (n2.getName());
                builder.append (" ");
                builder.append (n1.getName());
                break;
              case 2:
                builder.append (n1.getName());
                builder.append (" ("+uMinus()+" ");
                builder.append (n2.getName());
                builder.append (")");
                break;
              case 3:
                builder.append ("("+uMinus()+" ");
                builder.append (n2.getName());
                builder.append (") ");
                builder.append (n1.getName());
                break;
            }
            updateNodeRefs (todoIntConsts, n2, minRefs);
          } else {
            n2 = realNodes.get(r.nextInt(realNodes.size()));
            assert (n2.getType() == RealType.realType);
            builder.append (n1.getName());
            builder.append (" ");
            builder.append (n2.getName());
            updateNodeRefs (todoRealNodes, n2, minRefs);
          }
          updateNodeRefs (todoRealNodes, n1, minRefs);
          break;
        case UNMINUS:
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          builder.append (n1.getName());
          updateNodeRefs (todoRealNodes, n1, minRefs);
          break;
        case DIV:
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          if (noBlowup && r.nextBoolean() && !todoIntConsts.isEmpty()){
            todoArray = todoIntConsts.keySet().toArray (new SMTNode[0]);
            c1 = todoArray[r.nextInt(todoArray.length)];
          } else {
            c1 = intConstsAsReal.get(r.nextInt(sizeIntConsts));
          }
          do {
            c2 = intConstsAsReal.get(r.nextInt(sizeIntConsts));
          } while (zeroConsts.contains(c2));
          builder.append (c1.getName());
          builder.append (" ");
          if (r.nextBoolean()) {
            builder.append (c2.getName());
          } else {
            builder.append ("("+uMinus()+" ");
            builder.append (c2.getName());
            builder.append (")");
          }
          updateNodeRefs (todoIntConsts, c1, minRefs);
          updateNodeRefs (todoIntConsts, c2, minRefs);
          break;
       case UFUNC:
          if (!todoUFuncs.isEmpty() && r.nextBoolean()) {
            todoUFuncsArray = todoUFuncs.keySet().toArray (new UFunc[0]);
            uFunc = todoUFuncsArray[r.nextInt(todoUFuncsArray.length)];
          } else {
            uFunc = uFuncs.get(r.nextInt(sizeUFuncs));
          }
          updateFuncRefs (todoUFuncs, uFunc, minRefs);
          builder.append (uFunc.getName());
          sig = uFunc.getSignature();
          operandTypes = sig.getOperandTypes();
          sizeOpTypes = operandTypes.size();
          assert (sizeOpTypes > 0);
          assert (operandTypes.get(0) == RealType.realType);
          builder.append (" ");
          builder.append (n1.getName());
          updateNodeRefs (todoRealNodes, n1, minRefs);
          for (int i = 1; i < sizeOpTypes; i++) {
            n2 = realNodes.get(r.nextInt(realNodes.size()));
            assert (n2.getType() == RealType.realType);
            assert (operandTypes.get(i) == RealType.realType);
            builder.append (" ");
            builder.append (n2.getName());
            updateNodeRefs (todoRealNodes, n2, minRefs);
          }
          assert (sig.getResultType() == RealType.realType);
          break;
        case UPRED:
          if (!todoUPreds.isEmpty() && r.nextBoolean()) {
            todoUPredsArray = todoUPreds.keySet().toArray (new UPred[0]);
            uPred = todoUPredsArray[r.nextInt(todoUPredsArray.length)];
          } else {
            uPred = uPreds.get(r.nextInt(sizeUPreds));
          }
          updatePredRefs (todoUPreds, uPred, minRefs);
          builder.append ("ite (");
          builder.append (uPred.getName());
          sig = uPred.getSignature();
          operandTypes = sig.getOperandTypes();
          sizeOpTypes = operandTypes.size();
          assert (sizeOpTypes > 0);
          assert (operandTypes.get(0) == RealType.realType);
          builder.append (" ");
          builder.append (n1.getName());
          updateNodeRefs (todoRealNodes, n1, minRefs);
          for (int i = 1; i < sizeOpTypes; i++) {
            n2 = realNodes.get(r.nextInt(realNodes.size()));
            assert (n2.getType() == RealType.realType);
            assert (operandTypes.get(i) == RealType.realType);
            builder.append (" ");
            builder.append (n2.getName());
            updateNodeRefs (todoRealNodes, n2, minRefs);
          }
          builder.append (") ");
          if (printConstsAsReal) 
            builder.append ("1.0 0.0");
          else
            builder.append ("1 0");
          assert (sig.getResultType() == BoolType.boolType);
          break;
      }
      builder.append (")");
      builder.append(letClose());
        
      realNodes.add (new SMTNode (RealType.realType, name));
    }
    output.print (builder.toString());
    assert (realNodes.size() - oldSize > 0);
    return realNodes.size() - oldSize;
  }

  private static int generateUTermLayer (Random r, List<SMTType> sorts, 
                                         List<SMTNode> nodes, 
                                         List<UFunc> funcs, int minRefs) {

    int oldSize, sizeFuncs, sizeSorts, sizeOperandTypes;
    String name;
    HashMap<SMTNode, Integer> todoNodes; 
    HashMap<SMTType, ArrayList<UFunc>> opTypeToUFuncs; 
    HashSet<UFunc> todoFuncs; 
    ArrayList<UFunc> typeMappings;
    UFunc func;
    Signature sig;
    List<SMTType> operandTypes;
    SMTType curType, resultType, selectedType;
    StringBuilder builder;
    SMTNode node, selectedNode;
    SMTNode []todoNodesArray;

    assert (r != null);
    assert (nodes != null);
    assert (nodes.size() > 0);
    assert (funcs != null);
    assert (funcs.size() > 0);
    assert (minRefs > 0);

    oldSize = nodes.size();
    sizeFuncs = funcs.size();
    sizeSorts = sorts.size();

    /* map UType to list of functions that use this
     * type at least once as argument type */
    opTypeToUFuncs = new HashMap<SMTType, ArrayList<UFunc>>();
    for (int i = 0; i < sizeSorts; i++) {
      curType = sorts.get(i);
      typeMappings = new ArrayList<UFunc>();
      for (int j = 0; j < sizeFuncs; j++) {
        func = funcs.get(j);
        sig = func.getSignature();
        operandTypes = sig.getOperandTypes();
        sizeOperandTypes = operandTypes.size();
        for (int k = 0; k < sizeOperandTypes; k++) {
          if (curType == operandTypes.get(k)) {
            typeMappings.add (func);
            break;
          }
        }
      }
      assert (!typeMappings.isEmpty());
      opTypeToUFuncs.put (curType, typeMappings);
    }

    /* each function should be used at least once */
    todoFuncs = new HashSet<UFunc>();
    for (int i = 0; i < sizeFuncs; i++)
      todoFuncs.add (funcs.get(i));

    todoNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < nodes.size(); i++)
      todoNodes.put (nodes.get(i), new Integer(0));

    builder = new StringBuilder();
    while (!todoNodes.isEmpty() || !todoFuncs.isEmpty()){
      name = letName();
      builder.append (letStart());
      builder.append (name);
      builder.append (" (");
      /* either select function or at least one 
       * node from the todo list to prevent
       * blowup because of incompatible types */
      if (r.nextBoolean() || todoNodes.isEmpty()) {
        func = funcs.get (r.nextInt(sizeFuncs));
        if (todoFuncs.contains (func))
          todoFuncs.remove (func);
        builder.append (func.getName());
        sig = func.getSignature();
        operandTypes = sig.getOperandTypes();
        resultType = sig.getResultType();
        sizeOperandTypes = operandTypes.size();
        for (int i = 0; i < sizeOperandTypes; i++){
          builder.append (" ");
          curType = operandTypes.get(i);
          do {
            node = nodes.get(r.nextInt(nodes.size()));
          } while (node.getType() != curType);
          updateNodeRefs (todoNodes, node, minRefs);
          builder.append (node.getName());
        }
      } else {
        /* select node from todo list and appropriate function */
        todoNodesArray = todoNodes.keySet().toArray (new SMTNode[0]);
        selectedNode = todoNodesArray[r.nextInt(todoNodesArray.length)];
        selectedType = selectedNode.getType();
        typeMappings = opTypeToUFuncs.get(selectedType);
        func = typeMappings.get(r.nextInt(typeMappings.size()));
        if (todoFuncs.contains (func))
          todoFuncs.remove (func);
        builder.append (func.getName());
        sig = func.getSignature();
        operandTypes = sig.getOperandTypes();
        resultType = sig.getResultType();
        sizeOperandTypes = operandTypes.size();
        for (int i = 0; i < sizeOperandTypes; i++){
          builder.append (" ");
          curType = operandTypes.get(i);
          if (curType == selectedType && selectedNode != null) {
            node = selectedNode;
            if (r.nextBoolean())
              selectedNode = null;
          } else {
            do {
              node = nodes.get(r.nextInt(nodes.size()));
            } while (node.getType() != curType);
          }
          updateNodeRefs (todoNodes, node, minRefs);
          builder.append (node.getName());
        }
      }
      builder.append (")");
      builder.append (letClose());
      nodes.add (new SMTNode (resultType, name));
    }
    output.print (builder.toString());
    assert (nodes.size() - oldSize > 0);
    return nodes.size() - oldSize;
  }

  private static int generateITELayer (Random r, List<SMTNode> nodes,
                                       List<SMTNode> boolNodes, int minRefs){
    int generated = 0;
    int sizeBoolNodes;
    HashMap<SMTNode, Integer> todoNodes;
    HashMap<SMTNode, Integer> todoBoolNodes;
    SMTNode []nArray;
    SMTNode n1, n2, f;
    StringBuilder builder;
    String name;
    SMTType curType;

    assert (r != null);
    assert (nodes != null);
    assert (nodes.size() > 0);
    assert (boolNodes != null);
    assert (boolNodes.size() > 0);
    assert (minRefs > 0);

    todoNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < nodes.size(); i++)
      todoNodes.put (nodes.get(i), new Integer(0));

    todoBoolNodes = new HashMap<SMTNode, Integer>();
    sizeBoolNodes = boolNodes.size();
    for (int i = 0; i < sizeBoolNodes; i++)
      todoBoolNodes.put (boolNodes.get(i), new Integer(0));

    builder = new StringBuilder();
    while (!todoNodes.isEmpty() || !todoBoolNodes.isEmpty()){
      name = letName();
      builder.append (letStart());
      builder.append (name);
      builder.append (" (ite ");
      /* either choose a random formula or one of the todo list 
       * to prevent blowup */
      if (r.nextBoolean() || todoBoolNodes.isEmpty()){
        f = boolNodes.get(r.nextInt(sizeBoolNodes));
      } else { 
        nArray = todoBoolNodes.keySet().toArray(new SMTNode[0]);
        f = nArray[r.nextInt(nArray.length)];
      }
      assert (f.getType() == BoolType.boolType);
      builder.append (f.getName());
      /* either choose a random term or one of the todo list 
       * to prevent blowup because of incomatible types */
      if (r.nextBoolean() || todoNodes.isEmpty()) {
        n1 = nodes.get(r.nextInt(nodes.size()));
      } else {
        nArray = todoNodes.keySet().toArray(new SMTNode[0]);
        n1 = nArray[r.nextInt(nArray.length)];
      }
      curType = n1.getType();
      assert (curType != BoolType.boolType);
      do {
        n2 = nodes.get(r.nextInt(nodes.size()));
      } while (curType != n2.getType());
      builder.append (" ");
      builder.append (n1.getName());
      builder.append (" ");
      builder.append (n2.getName());
      builder.append (")");
      builder.append (letClose());
      updateNodeRefs (todoBoolNodes, f, minRefs);
      updateNodeRefs (todoNodes, n1, minRefs);
      updateNodeRefs (todoNodes, n2, minRefs);
      nodes.add (new SMTNode (curType, name));
      generated++;
    }
    output.print (builder.toString());
    assert (generated > 0);
    return generated;
  }

/*----------------------------------------------------------------------------*/
/* Predicate Layer                                                            */
/*----------------------------------------------------------------------------*/

  private static int generateBVPredicateLayer (Random r, 
                                               List<SMTNode> bvNodes,
                                               List<SMTNode> boolNodes,
                                               int minRefs, 
                                               List<UPred> uPreds) {
    SMTNodeKind kind;
    EnumSet<SMTNodeKind> kindSet;
    SMTNodeKind [] kinds;
    String name;
    HashMap<SMTNode, Integer> todoNodes; 
    HashMap<UPred, Integer> todoUPreds; 
    UPred []todoUPredsArray;
    UPred uPred;
    SMTNode n1, n2;
    int oldSize, sizeBVNodes, sizeOpTypes, sizeUPreds;
    Signature sig;
    StringBuilder builder;
    List<SMTType> operandTypes;
    BVType curType;

    assert (bvNodes != null);
    assert (!bvNodes.isEmpty());
    assert (boolNodes != null);
    assert (minRefs > 0);
    assert (SMTNodeKind.BVULT.ordinal() < SMTNodeKind.BVSGE.ordinal());

    kindSet = EnumSet.range (SMTNodeKind.BVULT, SMTNodeKind.BVSGE);
    kindSet.add (SMTNodeKind.EQ);
    kindSet.add (SMTNodeKind.DISTINCT);
    if (!uPreds.isEmpty())
      kindSet.add(SMTNodeKind.UPRED);
    kinds = kindSet.toArray(new SMTNodeKind[0]);

    todoNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < bvNodes.size(); i++)
      todoNodes.put (bvNodes.get(i), new Integer(0));

    todoUPreds = new HashMap<UPred, Integer>();
    sizeUPreds = uPreds.size();
    for (int i = 0; i < sizeUPreds; i++)
      todoUPreds.put (uPreds.get(i), new Integer(0));

    builder = new StringBuilder();
    oldSize = boolNodes.size();
    sizeBVNodes = bvNodes.size();
    while (!todoNodes.isEmpty() || !todoUPreds.isEmpty()){
         name = fletName();
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (");
      /* increase probability to select upred
       * if todo list ist not empty */
      if (!todoUPreds.isEmpty() && r.nextBoolean())
        kind = SMTNodeKind.UPRED;
      else 
        kind = kinds[r.nextInt (kinds.length)];
      assert (kind.arity == 2 || kind.arity == -1);
      if (kind == SMTNodeKind.UPRED) {
        if (!todoUPreds.isEmpty() && r.nextBoolean()) {
          todoUPredsArray = todoUPreds.keySet().toArray (new UPred[0]);
          uPred = todoUPredsArray[r.nextInt(todoUPredsArray.length)];
        } else {
          uPred = uPreds.get(r.nextInt(sizeUPreds));
        }
        updatePredRefs (todoUPreds, uPred, minRefs);
        builder.append (uPred.getName());
        sig = uPred.getSignature();
        operandTypes = sig.getOperandTypes();
        sizeOpTypes = operandTypes.size();
        assert (sizeOpTypes > 0);
        for (int i = 0; i < sizeOpTypes; i++) {
          n1 = bvNodes.get(r.nextInt(sizeBVNodes));
          assert (n1.getType() instanceof BVType);
          assert (operandTypes.get(i) instanceof BVType);
          curType = (BVType) operandTypes.get(i);
          builder.append (" ");
          builder.append (adaptBW (r, n1, curType.getWidth()));
          updateNodeRefs (todoNodes, n1, minRefs);
        }
        assert (sig.getResultType() == BoolType.boolType);
      } else {
        n1 = bvNodes.get(r.nextInt(sizeBVNodes));
        assert (n1.getType() instanceof BVType);
        n2 = bvNodes.get(r.nextInt(sizeBVNodes));
        assert (n2.getType() instanceof BVType);
        builder.append (kind.getString(smtlib1));
        builder.append (" ");
        builder.append (wrapEqualBW (r, n1, n2));
        updateNodeRefs (todoNodes, n1, minRefs);
        updateNodeRefs (todoNodes, n2, minRefs);
      }
      builder.append (")");
      builder.append (letClose());
      boolNodes.add (new SMTNode (BoolType.boolType, name));
    }
    output.print (builder.toString());
    assert (boolNodes.size() - oldSize > 0);
    return boolNodes.size() - oldSize;
  }

  private static int generateIDLLayer (Random r, List<SMTNode> intVars,
                                       List<SMTNode> intConsts,
                                       List<SMTNode> boolNodes, int minRefs){

    int oldSize, sizeIntConsts, sizeIntVars;
    EnumSet<SMTNodeKind> kindSet;
    SMTNodeKind [] kinds;
    SMTNodeKind kind;
    String name;
    HashMap<SMTNode, Integer> todo; 
    SMTNode v1, v2, c;
    StringBuilder builder;

    assert (r != null);
    assert (intVars != null);
    assert (!intVars.isEmpty());
    assert (intConsts != null);
    assert (!intConsts.isEmpty());
    assert (boolNodes != null);
    assert (minRefs > 0);

    kindSet = EnumSet.range (SMTNodeKind.LT, SMTNodeKind.DISTINCT);
    kinds = kindSet.toArray(new SMTNodeKind[0]);

    todo = new HashMap<SMTNode, Integer>();
    sizeIntVars = intVars.size();
    for (int i = 0; i < sizeIntVars; i++)
      todo.put (intVars.get(i), new Integer(0));
    sizeIntConsts = intConsts.size();
    for (int i = 0; i < sizeIntConsts; i++)
      todo.put (intConsts.get(i), new Integer(0));

    builder = new StringBuilder();
    oldSize = boolNodes.size();
    while (!todo.isEmpty()){
      name = fletName();
      kind = kinds[r.nextInt (kinds.length)];
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (");
      builder.append (kind.getString(smtlib1));
      builder.append (" ");
      v1 = intVars.get(r.nextInt(sizeIntVars));
      v2 = intVars.get(r.nextInt(sizeIntVars));
      c = intConsts.get(r.nextInt(sizeIntConsts));
      assert (v1.getType() == IntType.intType);
      assert (v2.getType() == IntType.intType);
      assert (c.getType() == IntType.intType);
      if (r.nextBoolean()){
        builder.append ("(- ");
        builder.append (v1.getName());
        builder.append (" ");
        builder.append (v2.getName());
        builder.append (") ");
        if (r.nextBoolean()) {
          builder.append ("("+uMinus()+" ");
          builder.append (c.getName());
          builder.append (")");
        } else {
          builder.append (c.getName());
        }
      } else {
        builder.append (v1.getName());
        builder.append (" ");
        builder.append (v2.getName());
      }
      builder.append (")");
      builder.append (letClose());
      boolNodes.add (new SMTNode (BoolType.boolType, name));
      updateNodeRefs (todo, v1, minRefs);
      updateNodeRefs (todo, v2, minRefs);
      updateNodeRefs (todo, c, minRefs);
    }
    output.print (builder.toString());
    assert (boolNodes.size() - oldSize > 0);
    return boolNodes.size() - oldSize;
  }

  private static int generateRDLLayer (Random r, List<SMTNode> realVars,
                                       List<SMTNode> intConsts, 
                                       Set<SMTNode> zeroConsts,
                                       List<SMTNode> boolNodes, int minRefs, 
                                       int maxBW){

    int oldSize, sizeRealVars, sizeIntConsts;
    EnumSet<SMTNodeKind> kindSet;
    SMTNodeKind [] kinds;
    SMTNodeKind kind;
    String name;
    HashMap<SMTNode, Integer> todo; 
    SMTNode v1, v2, c1, c2;
    BigInteger n; 
    StringBuilder builder;

    assert (r != null);
    assert (realVars != null);
    assert (!realVars.isEmpty());
    assert (intConsts != null);
    assert (!intConsts.isEmpty());
    assert (zeroConsts != null);
    assert (zeroConsts.size() < intConsts.size());
    assert (boolNodes != null);
    assert (minRefs > 0);
    assert (maxBW > 0);

    kindSet = EnumSet.range (SMTNodeKind.LT, SMTNodeKind.DISTINCT);
    kinds = kindSet.toArray(new SMTNodeKind[0]);

    todo = new HashMap<SMTNode, Integer>();
    sizeRealVars = realVars.size();
    for (int i = 0; i < sizeRealVars; i++)
      todo.put (realVars.get(i), new Integer(0));
    sizeIntConsts = intConsts.size();
    for (int i = 0; i < sizeIntConsts; i++)
      todo.put (intConsts.get(i), new Integer(0));

    builder = new StringBuilder();
    oldSize = boolNodes.size();
    while (!todo.isEmpty()){
      name = fletName();
      kind = kinds[r.nextInt (kinds.length)];
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (");
      builder.append (kind.getString(smtlib1));
      builder.append (" ");
      v1 = realVars.get(r.nextInt(sizeRealVars));
      v2 = realVars.get(r.nextInt(sizeRealVars));
      c1 = intConsts.get(r.nextInt(sizeIntConsts));
      assert (v1.getType() == RealType.realType);
      assert (v2.getType() == RealType.realType);
      assert (c1.getType() == IntType.intType);
      if (r.nextBoolean()){
        if (r.nextBoolean()){
          builder.append ("(- ");
          builder.append (v1.getName());
          builder.append (" ");
          builder.append (v2.getName());
          builder.append (") ");
          if (r.nextBoolean()) {
            if (r.nextBoolean()) {
              builder.append ("("+uMinus()+" ");
              builder.append (c1.getName());
              builder.append (")");
            } else {
              builder.append (c1.getName());
            }
          } else {
            do {
              c2 = intConsts.get(r.nextInt(intConsts.size())); 
            } while (zeroConsts.contains(c2));
            builder.append ("(/ ");
            builder.append (c1.getName());
            builder.append (" ");
            if (r.nextBoolean()) {
              builder.append (c2.getName());
            } else {
              builder.append ("("+uMinus()+" ");
              builder.append (c2.getName());
              builder.append (")");
            }
            builder.append (")");
            updateNodeRefs (todo, c2, minRefs);
          }
        } else {
          builder.append (v1.getName());
          builder.append (" ");
          builder.append (v2.getName());
        }
      } else {
        n = new BigInteger (maxBW, r);
        builder.append ("(- (+ ");
        builder.append (v1.getName());
        builder.append (" " + v1.getName());
        for (BigInteger i = BigInteger.ZERO; i.compareTo(n) == - 1; 
             i = i.add(BigInteger.ONE)) {
          builder.append (" ");
          builder.append (v1.getName());
        }

        builder.append (") (+ ");
        builder.append (v2.getName());
        builder.append (" " + v1.getName());
        for (BigInteger i = BigInteger.ZERO; i.compareTo(n) == - 1; 
             i = i.add(BigInteger.ONE)) {
          builder.append (" ");
          builder.append (v2.getName());
        }

        builder.append (")) ");
        if (r.nextBoolean()) {
          builder.append ("("+uMinus()+" ");
          builder.append (c1.getName());
          builder.append (")");
        } else {
          builder.append (c1.getName());
        }
      }
      builder.append (")");
      builder.append (letClose());
      boolNodes.add (new SMTNode (BoolType.boolType, name));
      updateNodeRefs (todo, v1, minRefs);
      updateNodeRefs (todo, v2, minRefs);
      updateNodeRefs (todo, c1, minRefs);
    }
    output.print (builder.toString());
    assert (boolNodes.size() - oldSize > 0);
    return boolNodes.size() - oldSize;
  }

  private static int generateComparisonLayer (Random r, List<SMTNode> nodes,
                                              List<SMTNode> boolNodes, 
                                              List<UPred> uPreds,
                                              int minRefs, RelCompMode compMode,
                                              boolean noBlowup) {

    int oldSize, sizeNodes, sizeOpTypes, sizeUPreds = 0;
    EnumSet<SMTNodeKind> kindSet = null;
    SMTNodeKind []kinds;
    SMTNodeKind kind;
    SMTNode []todoNodesArray;
    UPred []todoUPredsArray;
    String name;
    HashMap<SMTNode, Integer> todoNodes; 
    HashMap<UPred, Integer> todoUPreds; 
    SMTNode n1, n2;
    StringBuilder builder;
    UPred uPred;
    Signature sig;
    List<SMTType> operandTypes;

    assert (r != null);
    assert (nodes != null);
    assert (!nodes.isEmpty());
    assert (boolNodes != null);
    assert (minRefs > 0);
    
    switch (compMode) {
      case OFF:
        assert (uPreds.size() > 0);
        kindSet = EnumSet.noneOf (SMTNodeKind.class);
        break;
      case EQ:
        kindSet = EnumSet.range (SMTNodeKind.EQ, SMTNodeKind.DISTINCT);
        break;
      case FULL:
        kindSet = EnumSet.range (SMTNodeKind.LT, SMTNodeKind.DISTINCT);
        break;
      default:
        assert (false);
    }

    todoUPreds = new HashMap<UPred, Integer>();
    if (uPreds != null && !uPreds.isEmpty()) {
      sizeUPreds = uPreds.size();
      kindSet.add (SMTNodeKind.UPRED);
      for (int i = 0; i < sizeUPreds; i++)
        todoUPreds.put (uPreds.get(i), new Integer(0));
    }

    kinds = kindSet.toArray(new SMTNodeKind[0]);

    todoNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < nodes.size(); i++)
      todoNodes.put (nodes.get(i), new Integer(0));

    builder = new StringBuilder();
    sizeNodes = nodes.size();
    oldSize = boolNodes.size();
    while (!todoNodes.isEmpty() || !todoUPreds.isEmpty()){
      name = fletName();
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (");
      if (noBlowup && r.nextBoolean() && !todoNodes.isEmpty()) {
        todoNodesArray = todoNodes.keySet().toArray(new SMTNode[0]);
        n1 = todoNodesArray[r.nextInt(todoNodesArray.length)];
      } else {
        n1 = nodes.get(r.nextInt(sizeNodes));
      }
      kind = kinds[r.nextInt (kinds.length)];
      if (kind == SMTNodeKind.UPRED) {
        if (!todoUPreds.isEmpty() && r.nextBoolean()) {
          todoUPredsArray = todoUPreds.keySet().toArray (new UPred[0]);
          uPred = todoUPredsArray[r.nextInt(todoUPredsArray.length)];
        } else {
          uPred = uPreds.get(r.nextInt(sizeUPreds));
        }
        updatePredRefs (todoUPreds, uPred, minRefs);
        builder.append (uPred.getName());
        sig = uPred.getSignature();
        operandTypes = sig.getOperandTypes();
        sizeOpTypes = operandTypes.size();
        assert (sizeOpTypes > 0);
        builder.append (" ");
        builder.append (n1.getName());
        updateNodeRefs (todoNodes, n1, minRefs);
        for (int i = 1; i < sizeOpTypes; i++) {
          n2 = nodes.get(r.nextInt(nodes.size()));
          builder.append (" ");
          builder.append (n2.getName());
          updateNodeRefs (todoNodes, n2, minRefs);
        }
      } else {
        builder.append (kind.getString(smtlib1));
        builder.append (" ");
        n2 = nodes.get(r.nextInt(sizeNodes));
        assert (n1.getType() == n2.getType());
        builder.append (n1.getName());
        builder.append (" ");
        builder.append (n2.getName());
        updateNodeRefs (todoNodes, n1, minRefs);
        updateNodeRefs (todoNodes, n2, minRefs);
      }
      builder.append (")");
      builder.append (letClose());
      boolNodes.add (new SMTNode (BoolType.boolType, name));
    }
    output.print (builder.toString());
    assert (boolNodes.size() - oldSize > 0);
    return boolNodes.size() - oldSize;
  }

  private static int generateUPredLayer (Random r, List<SMTNode> nodes, 
                                         List<SMTNode> boolNodes, 
                                         List<UPred> preds, int minRefs) {

    int oldSize, sizePreds, sizeOperandTypes;
    String name;
    HashMap<SMTNode, Integer> todoNodes; 
    SMTNode []todoNodesArray;
    HashSet<UPred> todoPreds; 
    UPred pred;
    Signature sig;
    List<SMTType> operandTypes;
    SMTType curType;
    StringBuilder builder;
    SMTNode n1, n2;

    assert (r != null);
    assert (nodes != null);
    assert (nodes.size() > 0);
    assert (boolNodes != null);
    assert (preds != null);
    assert (preds.size() > 0);
    assert (minRefs > 0);

    oldSize = boolNodes.size();
    sizePreds = preds.size();
    /* each predicate should be used at least once */
    todoPreds = new HashSet<UPred>();
    for (int i = 0; i < sizePreds; i++)
      todoPreds.add (preds.get(i));

    todoNodes = new HashMap<SMTNode, Integer>();
    for (int i = 0; i < nodes.size(); i++)
      todoNodes.put (nodes.get(i), new Integer(0));

    builder = new StringBuilder();
    while (!todoNodes.isEmpty() || !todoPreds.isEmpty()){
      name = fletName();
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (");
      if (r.nextBoolean() || todoNodes.isEmpty()) {
        pred = preds.get (r.nextInt(sizePreds));
        if (todoPreds.contains (pred))
          todoPreds.remove (pred);
        builder.append (pred.getName());
        sig = pred.getSignature();
        operandTypes = sig.getOperandTypes();
        assert (sig.getResultType() == BoolType.boolType);
        sizeOperandTypes = operandTypes.size();
        for (int i = 0; i < sizeOperandTypes; i++){
          builder.append (" ");
          curType = operandTypes.get(i);
          do {
            n1 = nodes.get(r.nextInt(nodes.size()));
          } while (n1.getType() != curType);
          updateNodeRefs (todoNodes, n1, minRefs);
          builder.append (n1.getName());
        }
      } else {
        if (r.nextBoolean())
          builder.append (SMTNodeKind.EQ.getString(smtlib1));
        else
          builder.append (SMTNodeKind.DISTINCT.getString(smtlib1));
        builder.append (" ");
        /* select at least one of the todo nodes,
         * to prevent blowup because of type incompatibility */
        todoNodesArray = todoNodes.keySet().toArray (new SMTNode[0]);
        n1 = todoNodesArray[r.nextInt(todoNodesArray.length)];
        curType = n1.getType();
        do {
          n2 = nodes.get(r.nextInt(nodes.size()));
        } while (curType != n2.getType());
        builder.append (n1.getName());
        builder.append (" ");
        builder.append (n2.getName());
        updateNodeRefs (todoNodes, n1, minRefs);
        updateNodeRefs (todoNodes, n2, minRefs);
      }
      builder.append (")");
      builder.append (letClose());
      boolNodes.add (new SMTNode (BoolType.boolType, name));
    }
    output.print (builder.toString());
    assert (boolNodes.size() - oldSize > 0);
    return boolNodes.size() - oldSize;
  }

/*----------------------------------------------------------------------------*/
/* Boolean Layer                                                              */
/*----------------------------------------------------------------------------*/

  private static int generateBooleanLayer (Random r, List<SMTNode> nodes){
    int generated = 0;
    SMTNode n1, n2, n3;
    SMTNodeKind [] kinds;
    SMTNodeKind [] kindsNoIfThenElse;
    SMTNodeKind kind;
    EnumSet<SMTNodeKind> kindSet;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (!nodes.isEmpty());

    kindSet = EnumSet.range (SMTNodeKind.AND, SMTNodeKind.IFF);
    kindSet.add (SMTNodeKind.NOT);
    kindsNoIfThenElse = kindSet.toArray(new SMTNodeKind[0]);
    kindSet.add (SMTNodeKind.IF_THEN_ELSE);
    kinds = kindSet.toArray(new SMTNodeKind[0]);

    builder = new StringBuilder();
    while (nodes.size() > 1){
      name = fletName();
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (");
      n1 = nodes.get(r.nextInt(nodes.size()));
      assert (n1.getType() == BoolType.boolType);

      n2 = n3 = null;
      if (nodes.size() >= 3)
        kind = kinds[r.nextInt(kinds.length)];
      else
        kind = kindsNoIfThenElse[r.nextInt(kindsNoIfThenElse.length)];
      switch (kind) {
        case NOT:
          builder.append (SMTNodeKind.NOT.getString(smtlib1));
          builder.append (" ");
          builder.append (n1.getName());
          break;
        case IF_THEN_ELSE:
          assert (nodes.size() >= 3);
          n2 = nodes.get(r.nextInt(nodes.size()));
          assert (n2.getType() == BoolType.boolType);
          n3 = nodes.get(r.nextInt(nodes.size()));
          assert (n3.getType() == BoolType.boolType);
          builder.append (SMTNodeKind.IF_THEN_ELSE.getString(smtlib1));
          builder.append (" ");
          builder.append (n1.getName());
          builder.append (" ");
          builder.append (n2.getName());
          builder.append (" ");
          builder.append (n3.getName());
          break;
      default:
        /* binary operators */
        n2 = nodes.get(r.nextInt(nodes.size()));
        assert (n2.getType() == BoolType.boolType);
        builder.append (kind.getString(smtlib1));
        builder.append (" ");
        builder.append (n1.getName());
        builder.append (" ");
        builder.append (n2.getName());
        break;
      }
      builder.append (")");
      builder.append (letClose());
      generated++;
      nodes.add (new SMTNode (BoolType.boolType, name));
      nodes.remove (n1);
      if (n2 != null)
        nodes.remove (n2);
      if (n3 != null)
        nodes.remove (n3);
    }
    output.print (builder.toString());

    return generated;
  }

  protected static int generateBooleanTopOp (List<SMTNode> nodes, String op){

    SMTNode cur;
    String name;
    StringBuilder builder;

    assert (nodes != null);
    assert (!nodes.isEmpty());
    assert (op != null);

    if (nodes.size() == 1)
      return 0;

    name = fletName();
    builder = new StringBuilder(); 
    builder.append (fletStart());
    builder.append (name);
    builder.append (" \n");
    builder.append ("(");
    builder.append (op);
    builder.append ("\n");
    for (int i = 0; i < nodes.size(); i++){
      cur = nodes.get(i);
      assert (cur.getType() == BoolType.boolType);
      builder.append (" ");
      builder.append (cur.getName());
      builder.append ("\n");
    }
    nodes.clear();
    nodes.add (new SMTNode (BoolType.boolType, name));
    builder.append (")");
    builder.append (letClose());
    output.print (builder.toString());
    return 1;
  }

  private static int generateBooleanTopAnd (List<SMTNode> nodes){

    assert (nodes != null);
    assert (!nodes.isEmpty());
    return generateBooleanTopOp (nodes, SMTNodeKind.AND.getString(smtlib1));
  }

  private static int generateBooleanTopOr (List<SMTNode> nodes){

    assert (nodes != null);
    assert (!nodes.isEmpty());
    return generateBooleanTopOp (nodes, SMTNodeKind.OR.getString(smtlib1));
  }


  private static int generateBooleanCNF (Random r, List<SMTNode> nodes, 
                                         double factor){
    SMTNode cur;
    String name;
    int numClauses;
    StringBuilder builder;

    assert (r != null);
    assert (nodes != null);
    assert (!nodes.isEmpty());
    assert (factor >= 0.0);

    if (nodes.size() == 1)
      return 0;

    numClauses = (int) (nodes.size() * factor);
    if (numClauses <= 1)
      numClauses = 2;

    name = fletName();
    builder = new StringBuilder();
    builder.append (fletStart());
    builder.append (name);
    builder.append (" \n(and\n");
    for (int i = 0; i < numClauses; i++){
      builder.append (" (or");
      for (int j = 0; j < 3; j++) {
        cur = nodes.get(r.nextInt(nodes.size()));
        assert (cur.getType() == BoolType.boolType);
        builder.append (" ");
        if (r.nextBoolean()) {
          builder.append (cur.getName());
        } else {
          builder.append ("(not ");
          builder.append (cur.getName());
          builder.append (")");
        }
      }
      builder.append (")\n");
    }
    builder.append ("))\n");
    nodes.clear();
    nodes.add (new SMTNode (BoolType.boolType, name));
    output.print (builder.toString());
    return 1;
  }

  private static int addBVDivGuards (List<SMTNode> root, 
                                     HashMap<SMTNode, SMTNodeKind> guardsMap){
    int generated = 0;
    int bw;
    String name;
    SMTNode []guards;
    SMTNode cur, guard;
    SMTNodeKind kind;
    StringBuilder builder;

    assert (root != null);
    assert (root.size() == 1);
    assert (guardsMap != null);

    builder = new StringBuilder();
    guards = guardsMap.keySet().toArray (new SMTNode[0]);
    cur = root.get(0);
    assert (cur.getType() == BoolType.boolType);
    for (int i = 0; i < guards.length; i++) {
      guard = guards[i];
      assert (guard.getType() instanceof BVType);
      bw = ((BVType) guard.getType()).width;
      name = fletName();
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (and ");
      builder.append (cur.getName());
      builder.append (" (not (= ");
      builder.append (guard.getName());
      if (smtlib1)
      {
	      builder.append (" bv0[");
	      builder.append (bw);
	      builder.append ("]");
      }
      else
      {
	      builder.append (" (_ bv0 ");
	      builder.append (bw);
	      builder.append (")");
      }
      builder.append (")))");
      builder.append(letClose());
      cur = new SMTNode (BoolType.boolType, name);
      generated++;
      kind = guardsMap.get(guard);
      assert (kind != null);
      /* also rule out division by -1 */
      if (kind == SMTNodeKind.BVSDIV || kind == SMTNodeKind.BVSREM ||
          kind == SMTNodeKind.BVSMOD) {
        name = fletName();
        builder.append (fletStart());
        builder.append (name);
        builder.append (" (and ");
        builder.append (cur.getName());
        builder.append (" (not (= ");
        builder.append (guard.getName());
        builder.append (" (bvnot");
        if (smtlib1)
        {
        	builder.append (" bv0[");
        	builder.append (bw);
        	builder.append ("]");
        }
        else
        {
  	      builder.append (" (_ bv0 ");
	      builder.append (bw);
	      builder.append (")");
        }
        
        builder.append ("))))");
        builder.append(letClose());
        cur = new SMTNode (BoolType.boolType, name);
        generated++;
      }
    } 
    output.print (builder.toString());

    root.clear();
    root.add(cur);

    return generated;
  }

  static int addArrayExt (Random r, List<SMTNode> arrays, 
                          List<SMTNode> boolNodes, int numExt){
    int oldSize, sizeArrays;
    SMTNode a1, a2;
    String name;
    StringBuilder builder;

    assert (r != null);
    assert (arrays != null);
    assert (!arrays.isEmpty());
    assert (boolNodes != null);
    assert (numExt >= 0);

    builder = new StringBuilder();
    oldSize = boolNodes.size();
    sizeArrays = arrays.size();
    for (int i = 0; i < numExt; i++) {
      name = fletName();
      do {
        a1 = arrays.get(r.nextInt(sizeArrays));
        a2 = arrays.get(r.nextInt(sizeArrays));
        assert (a1.getType() instanceof ArrayType);
        assert (a2.getType() instanceof ArrayType);
      } while (!a1.getType().equals(a2.getType()));
      builder.append (fletStart());
      builder.append (name);
      builder.append (" (= ");
      builder.append (a1.getName());
      builder.append (" ");
      builder.append (a2.getName());
      builder.append (")");
      builder.append (letClose());
      boolNodes.add (new SMTNode (BoolType.boolType, name));
    }
    output.print (builder.toString());

    assert (boolNodes.size() - oldSize >= 0);
    return boolNodes.size() - oldSize;
  }

  private static void generateQFormulasUF (Random r, SMTType type, 
                                           List<UFunc> uFuncs, 
                                           List<UPred> uPreds, 
                                           int numQFormulas, int minQVars, 
                                           int maxQVars, int minQNestings, 
                                           int maxQNestings, boolean onlyEqComp,
                                           int minRefs) {

    int qVarCounter = 0;
    int nodeCounter = 0;
    int numQNestings, numQVars;
    EnumSet<SMTNodeKind> kindSetComp;
    EnumSet<SMTNodeKind> kindSetBool;
    SMTNodeKind []kindsBool;
    SMTNodeKind []kindsComp;
    SMTNodeKind []kindsBoolNoIfThenElse;
    SMTNodeKind kind;
    String name, s1, s2, s3;
    String []qVarNamesArray;
    String []boolNamesArray;
    HashMap<String, Integer> todoQVarNames; 
    UFunc uFunc;
    UPred uPred;
    UFunc [] uFuncsArray = null;
    UPred [] uPredsArray = null;
    HashSet<String> boolNames;
    StringBuilder builder;
    Signature sig;
    List<SMTType> operandTypes;
    int sizeOpTypes, pars;

    assert (r != null);
    assert (type != null);
    assert (uFuncs != null);
    assert (uPreds != null);
    assert (uFuncs.size() > 0 || uPreds.size() > 0);
    assert (numQFormulas >= 0);
    assert (minQNestings >= 0);
    assert (maxQNestings >= minQNestings);
    assert (minQVars > 0);
    assert (maxQVars >= minQVars);
    assert (minRefs > 0);

    todoQVarNames = new HashMap<String, Integer>();
    boolNames = new HashSet<String>();

    if (onlyEqComp)
      kindSetComp = EnumSet.range (SMTNodeKind.EQ, SMTNodeKind.DISTINCT);
    else
      kindSetComp = EnumSet.range (SMTNodeKind.LT, SMTNodeKind.DISTINCT);
    kindsComp = kindSetComp.toArray(new SMTNodeKind[0]);

    kindSetBool = EnumSet.range (SMTNodeKind.AND, SMTNodeKind.IFF);
    kindSetBool.add (SMTNodeKind.NOT);
    kindsBoolNoIfThenElse = kindSetBool.toArray(new SMTNodeKind[0]);
    kindSetBool.add (SMTNodeKind.IF_THEN_ELSE);
    kindsBool = kindSetBool.toArray(new SMTNodeKind[0]);

    if (!uFuncs.isEmpty())
      uFuncsArray = uFuncs.toArray (new UFunc[0]);
    if (!uPreds.isEmpty())
      uPredsArray = uPreds.toArray (new UPred[0]);

    builder = new StringBuilder();
    for (int i = 0; i < numQFormulas; i++) {
      assert (todoQVarNames.isEmpty());
      assert (boolNames.isEmpty());
      numQNestings = selectRandValRange (r, minQNestings, maxQNestings); 
      if (smtlib1)
    	  builder.append (":assumption\n");
      else
    	  builder.append ("(assert\n");
      pars = 0;
      for (int j = 0; j <= numQNestings; j++) {
        pars++;
        numQVars = selectRandValRange (r, minQVars, maxQVars); 
        if (r.nextBoolean())
          builder.append ("(forall ");
        else
          builder.append ("(exists ");

        if (!smtlib1)
        	builder.append ("(");
        
        for (int k = 0; k < numQVars; k++) {
          name = "?qvar" + qVarCounter++;
          todoQVarNames.put (name, new Integer (minRefs));
          builder.append ("(");
          builder.append (name);
          builder.append (" ");
          builder.append (type.toString(smtlib1));
          builder.append ( ") ");
        }

        if (!smtlib1)
        	builder.append (")");

        builder.append ("\n");
      }
      qVarNamesArray = todoQVarNames.keySet().toArray(new String[0]);
      while (!todoQVarNames.isEmpty()){
        name = "$qf" + nodeCounter++;
        builder.append (fletStart());
        builder.append (name);
        builder.append (" (");
        pars++;
        if ((!uFuncs.isEmpty() && r.nextBoolean()) || uPreds.isEmpty()) {
          assert (!uFuncs.isEmpty());
          kind = kindsComp[r.nextInt(kindsComp.length)];
          builder.append (kind.getString(smtlib1));
          for (int j = 0; j < 2; j++) {
            uFunc = uFuncsArray[r.nextInt(uFuncsArray.length)];
            sig = uFunc.getSignature();
            operandTypes = sig.getOperandTypes();
            assert (sig.getResultType() == type);
            sizeOpTypes = operandTypes.size();
            assert (sizeOpTypes > 0);
            builder.append (" (");
            builder.append (uFunc.getName());
            for (int k = 0; k < sizeOpTypes; k++){
              s1 = qVarNamesArray[r.nextInt(qVarNamesArray.length)];
              assert (operandTypes.get(k) == type);
              builder.append (" ");
              builder.append (s1);
              updateStringRefs (todoQVarNames, s1, minRefs);
            }
            builder.append (")");
          }
        } else {
          assert (!uPreds.isEmpty());
          uPred = uPredsArray[r.nextInt(uPredsArray.length)];
          sig = uPred.getSignature();
          operandTypes = sig.getOperandTypes();
          assert (sig.getResultType() == BoolType.boolType);
          sizeOpTypes = operandTypes.size();
          assert (sizeOpTypes > 0);
          builder.append (uPred.getName());
          for (int j = 0; j < sizeOpTypes; j++){
            s1 = qVarNamesArray[r.nextInt(qVarNamesArray.length)];
            assert (operandTypes.get(j) == type);
            builder.append (" ");
            builder.append (s1);
            updateStringRefs (todoQVarNames, s1, minRefs);
          }
        }
        builder.append (")");
        builder.append (letClose());
        
        boolNames.add (name);
      }
      assert (boolNames.size() > 0);
      while (boolNames.size() > 1) {
        boolNamesArray = boolNames.toArray(new String[0]);
        name = "$qf" + nodeCounter++;
        builder.append (fletStart());
        builder.append (name);
        builder.append (" (");
        s1 = boolNamesArray[r.nextInt(boolNamesArray.length)];
        s2 = s3 = null;
        if (boolNames.size() >= 3)
          kind = kindsBool[r.nextInt(kindsBool.length)];
        else
          kind = kindsBoolNoIfThenElse[r.nextInt(kindsBoolNoIfThenElse.length)];
        switch (kind) {
          case NOT:
            builder.append (SMTNodeKind.NOT.getString(smtlib1));
            builder.append (" ");
            builder.append (s1);
            break;
          case IF_THEN_ELSE:
            assert (boolNames.size() >= 3);
            s2 = boolNamesArray[r.nextInt(boolNamesArray.length)];
            s3 = boolNamesArray[r.nextInt(boolNamesArray.length)];
            builder.append (SMTNodeKind.IF_THEN_ELSE.getString(smtlib1));
            builder.append (" ");
            builder.append (s1);
            builder.append (" ");
            builder.append (s2);
            builder.append (" ");
            builder.append (s3);
            break;
        default:
          /* binary operators */
          s2 = boolNamesArray[r.nextInt(boolNamesArray.length)];
          builder.append (kind.getString(smtlib1));
          builder.append (" ");
          builder.append (s1);
          builder.append (" ");
          builder.append (s2);
          break;
        }
        builder.append (")");
        builder.append (letClose());

        boolNames.add (name);
        boolNames.remove (s1);
        if (s2 != null)
          boolNames.remove (s2);
        if (s3 != null)
          boolNames.remove (s3);
        pars++;
      }
      assert (boolNames.size() == 1);
      builder.append (boolNames.toArray(new String[0])[0]);
      builder.append ("\n");
      boolNames.clear();
      for (int j = 0; j < pars; j++)
        builder.append (")");
      if (!smtlib1)
    	  builder.append (")");
      builder.append ("\n");
    }
    output.print (builder.toString());
  }


/*----------------------------------------------------------------------------*/
/* Main method                                                                */
/*----------------------------------------------------------------------------*/

  private enum BooleanLayerKind {
    AND,
    OR,
    CNF,
    RANDOM;
  }

  private static void printErrAndExit (String string) {
    assert (string != null);
    System.err.println (string);
    System.exit (1);
  }

  private static void checkMinMax (int min, int max, String str){
    assert (min >= 0);
    assert (max >= 0);
    assert (str != null);
    if (max < min)
      printErrAndExit ("minimum number of " + str + " must be <= maximum");
  }

  private static void printHelpAndExit () {
    output.println (usage);
    System.exit (0);
  }

  private static void printVersionAndExit () {
    output.println (version);
    System.exit (0);
  }

  private static int parseIntOption (String []args, int pos, int minVal, 
                                     String errorMsg) {
    int result = 0;

    assert (args != null);
    assert (pos >= 0);
    assert (pos < args.length);
    assert (errorMsg != null);
    if (pos == args.length - 1)
      printErrAndExit ("option argument missing");
    try {
      result = Integer.valueOf(args[pos + 1]).intValue();
    } catch (NumberFormatException nfe) {
      printErrAndExit (errorMsg);
    }
    if (result < minVal)
      printErrAndExit (errorMsg);
    return result;
  }

  private static long parseLongOption (String []args, int pos, long minVal, 
                                       String errorMsg) {
    long result = 0l;

    assert (args != null);
    assert (pos >= 0);
    assert (pos < args.length);
    assert (errorMsg != null);
    if (pos == args.length - 1)
      printErrAndExit ("option argument missing");
    try {
      result = Long.valueOf(args[pos + 1]).longValue();
    } catch (NumberFormatException nfe) {
      printErrAndExit (errorMsg);
    }
    if (result < minVal)
      printErrAndExit (errorMsg);
    return result;
  }

  
  private static String startFormula()
  {
	  if (smtlib1)
		  return ":formula";
	  else
	  	return "(assert";
  }
  
  
  private static double parseDoubleOption (String []args, int pos, double minVal, 
                                           String errorMsg) {
    double result = 0.0;

    assert (args != null);
    assert (pos >= 0);
    assert (pos < args.length);
    assert (errorMsg != null);
    if (pos == args.length - 1)
      printErrAndExit ("option argument missing");
    try {
      result = Double.valueOf(args[pos + 1]).doubleValue();
    } catch (NumberFormatException nfe) {
      printErrAndExit (errorMsg);
    }
    if (result < minVal)
      printErrAndExit (errorMsg);
    return result;
  }



  private static final String version = "0.3";

  private static final String usage = 
"********************************************************************************\n" +
"*              FuzzSMT " + version + "                                                     *\n"  +
"*              Fuzzing Tool for SMT-LIB 2.0 & SMT-LIB 1.2 Benchmarks           *\n" +
"*              written by Robert Daniel Brummayer, 2009                        *\n" + 
"********************************************************************************\n" +
"\n" +
"usage: fuzzsmt <logic> [option...]\n\n" +
"  <logic> is one of the following:\n" + 
"  QF_A, QF_ABV, QF_AUFBV, QF_AUFLIA, QF_AX, QF_BV, QF_IDL, QF_LIA, QF_LRA,\n" + 
"  QF_NIA, QF_NRA, QF_RDL, QF_UF, QF_UFBV, QF_UFIDL, QF_UFLIA, QF_UFLRA,\n" +
"  QF_UFNIA, QF_UFNRA, QF_UFRDL, AUFLIA, AUFLIRA, AUFNIRA and LRA.\n" + 
"\n" +
"  for details about SMT see: www.smtlib.org\n" +
"\n" +
"  general options:\n\n" + 
"  -h                   print usage information and exit\n" +
"  -V                   print version and exit\n" +
"  -smtlib1             output smtlib1 format instead of smtlib2\n"+
"  -seed <seed>         initialize random number generator with <seed>\n" +
"  -bulk-export <num>   create <num> instances in the current directory\n"+
"\n" +
"  -bulk-prefix <string> prepend the string prefix to the file names created\n"+
"  -bool-random         generate a random boolean layer (default)\n" +
"  -bool-and            use an n-ary AND for the boolean layer\n" +
"  -bool-or             use an n-ary OR for the boolean layer\n" +
"  -bool-cnf <f>        generate a boolean CNF layer\n" +
"                       with <f> * <literals> clauses\n" +
"\n" +
"QF_A and QF_AX options:\n" +
"  -mar <arrays>        use min <arrays> array variables       (default  1)\n" +
"  -Mar <arrays>        use max <arrays> array variables       (default  3)\n" +
"  -mi <indices>        use min <indices> index variables      (default  1)\n" +
"  -Mi <indices>        use max <indices> index variables      (default  5)\n" +
"  -me <elements>       use min <elements> element variables   (default  1)\n" +
"  -Me <elements>       use max <elements> element variables   (default  5)\n" +
"  -mr <reads>          use min <reads> reads                  (default  1)\n" +
"  -Mr <reads>          use max <reads> reads                  (default 10)\n" +
"  -mw <writes>         use min <writes> writes                (default  0)\n" +
"  -Mw <writes>         use max <writes> writes                (default 10)\n" +
"  -ref <refs>          set min number of references for terms\n" +
"                       in input and main layer to <refs>      (default  1)\n" +
"\n" +
"QF_AUFBV options:\n" +
"  -mv <vars>           use min <vars> bit-vector variables    (default  1)\n" +
"  -Mv <vars>           use max <vars> bit-vector variables    (default  5)\n" +
"  -mc <consts>         use min <const> bit-vector constants   (default  1)\n" +
"  -Mc <consts>         use max <const> bit-vector constants   (default  2)\n" +
"  -mar <arrays>        use min <arrays> array variables       (default  1)\n" +
"  -Mar <arrays>        use max <arrays> array variables       (default  3)\n" +
"  -mr <reads>          use min <reads> reads                  (default  1)\n" +
"  -Mr <reads>          use max <reads> reads                  (default  5)\n" +
"  -mw <writes>         use min <writes> writes                (default  0)\n" +
"  -Mw <writes>         use max <writes> writes                (default  5)\n" +
"  -mxn <n>             compare min <n> arrays for equality    (default  0)\n" +
"  -Mxn <n>             compare max <n> arrays for equality    (default  0)\n" +
"  -mbw <bw>            set min bit-width to <bw>              (default  1)\n" +
"  -Mbw <bw>            set max bit-width to <bw>              (default 16)\n" +
"  -mf <funcs>          use min <funcs> uninterpreted BV funcs (default  0)\n" +
"  -Mf <funcs>          use max <funcs> uninterpreted BV funcs (default  2)\n" +
"  -mp <preds>          use min <preds> uninterpreted BV preds (default  0)\n" +
"  -Mp <preds>          use max <preds> uninterpreted BV preds (default  2)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"  -g                   do not guard BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n"+
"  -n                   do not use BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n" +
"  -ref <refs>          set min number of references for terms\n" + 
"                       in input and main layer to <refs>      (default  1)\n" +
"\n" +
"QF_ABV options:\n" +
"  -mv <vars>           use min <vars> bit-vector variables    (default  1)\n" +
"  -Mv <vars>           use max <vars> bit-vector variables    (default  5)\n" +
"  -mc <consts>         use min <const> bit-vector constants   (default  1)\n" +
"  -Mc <consts>         use max <const> bit-vector constants   (default  2)\n" +
"  -mar <arrays>        use min <arrays> array variables       (default  1)\n" +
"  -Mar <arrays>        use max <arrays> array variables       (default  3)\n" +
"  -mr <reads>          use min <reads> reads                  (default  1)\n" +
"  -Mr <reads>          use max <reads> reads                  (default  5)\n" +
"  -mw <writes>         use min <writes> writes                (default  0)\n" +
"  -Mw <writes>         use max <writes> writes                (default  5)\n" +
"  -mxn <n>             compare min <n> arrays for equality    (default  0)\n" +
"  -Mxn <n>             compare max <n> arrays for equality    (default  0)\n" +
"  -mbw <bw>            set min bit-width to <bw>              (default  1)\n" +
"  -Mbw <bw>            set max bit-width to <bw>              (default 16)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"  -g                   do not guard BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n"+
"  -n                   do not use BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n" +
"  -ref <refs>          set min number of references for terms\n" + 
"                       in input and main layer to <refs>      (default  1)\n" +
"\n" +
"QF_AUFLIA and AUFLIA options:\n" +
"  -mv <vars>           use min <vars> integer variables       (default  1)\n" +
"  -Mv <vars>           use max <vars> integer variables       (default  3)\n" +
"  -mc <consts>         use min <const> integer constants      (default  1)\n" +
"  -Mc <consts>         use max <const> integer constants      (default  3)\n" +
"  -mar <arrays>        use min <arrays> array variables       (default  1)\n" +
"  -Mar <arrays>        use max <arrays> array variables       (default  3)\n" +
"  -mr <reads>          use min <reads> reads                  (default  1)\n" +
"  -Mr <reads>          use max <reads> reads                  (default  5)\n" +
"  -mw <writes>         use min <writes> writes                (default  0)\n" +
"  -Mw <writes>         use max <writes> writes                (default  5)\n" +
"  -x                   compare arrays for equality            (default no)\n" +
"  -mfi <f>             use min <f> uninterpreted int funcs    (default  1)\n" +
"  -Mfi <f>             use max <f> uninterpreted int funcs    (default  1)\n" +
"  -mfar <f>            use min <f> uninterpreted array funcs  (default  1)\n" +
"  -Mfar <f>            use max <f> uninterpreted array funcs  (default  1)\n" +
"  -mpi <p>             use min <p> uninterpreted int preds    (default  1)\n" +
"  -Mpi <p>             use max <p> uninterpreted int preds    (default  1)\n" +
"  -mpar <p>            use min <p> uninterpreted array preds  (default  1)\n" +
"  -Mpar <p>            use max <p> uninterpreted array preds  (default  1)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
"                       bit-width is used to\n" +
"                       restrict the constants\n" +
"  -ref <refs>          set min number of references for terms\n" + 
"                       in input and main layer to <refs>      (default  1)\n" +
"  AUFLIA only:\n" +
"  -mqfi <qf>           use min <qf> quantified formulas over\n" +
"                       integer function and predicates        (default  1)\n" +
"  -Mqfi <qf>           use max <qf> quantified formulas over\n" +
"                       integer function and predicates        (default  1)\n" +
"  -mqfar <qf>          use min <qf> quantified formulas over\n" +
"                       array function and predicates          (default  0)\n" +
"  -Mqfar <qf>          use max <qf> quantified formulas over\n" +
"                       array function and predicates          (default  0)\n" +
"  -mqv <qv>            set min number of quantified\n" +
"                       variables per quantifier to <qn>       (default  1)\n" +
"  -Mqv <qv>            set max number of quantified\n" +
"                       variables per quantifier to <qn>       (default  3)\n" +
"  -mqn <qn>            set min quantifier nesting\n" +
"                       level to <qn>                          (default  0)\n" +
"  -Mqn <qn>            set max quantifier nesting\n" +
"                       level to <qn>                          (default  1)\n" +
"\n" +
"AUFLIRA and AUFNIRA options:\n" +
"  -mvi <vars>          use min <vars> integer variables       (default  1)\n" +
"  -Mvi <vars>          use max <vars> integer variables       (default  2)\n" +
"  -mvr <vars>          use min <vars> real variables          (default  1)\n" +
"  -Mvr <vars>          use max <vars> real variables          (default  2)\n" +
"  -mci <consts>        use min <const> integer constants      (default  1)\n" +
"  -Mci <consts>        use max <const> integer constants      (default  3)\n" +
"  -mcr <consts>        use min <const> real constants         (default  1)\n" +
"  -Mcr <consts>        use max <const> real constants         (default  3)\n" +
"  -mar1 <arrays>       use min <arrays> array1 variables      (default  1)\n" +
"  -Mar1 <arrays>       use max <arrays> array1 variables      (default  2)\n" +
"  -mar2 <arrays>       use min <arrays> array2 variables      (default  1)\n" +
"  -Mar2 <arrays>       use max <arrays> array2 variables      (default  2)\n" +
"  -mr1 <reads>         use min <reads> reads on array1 terms  (default  1)\n" +
"  -Mr1 <reads>         use max <reads> reads on array1 terms  (default  4)\n" +
"  -mr2 <reads>         use min <reads> reads on array2 terms  (default  1)\n" +
"  -Mr2 <reads>         use max <reads> reads on array2 terms  (default  4)\n" +
"  -mw1 <writes>        use min <writes> writes on array1 terms(default  0)\n" +
"  -Mw1 <writes>        use max <writes> writes on array1 terms(default  3)\n" +
"  -mw2 <writes>        use min <writes> writes on array2 terms(default  0)\n" +
"  -Mw2 <writes>        use max <writes> writes on array2 terms(default  3)\n" +
"  -x1                  compare array1 terms for equality      (default no)\n" +
"  -x2                  compare array2 terms for equality      (default no)\n" +
"  -mfi <f>             use min <f> uninterpreted int funcs    (default  1)\n" +
"  -Mfi <f>             use max <f> uninterpreted int funcs    (default  1)\n" +
"  -mfr <f>             use min <f> uninterpreted real funcs   (default  1)\n" +
"  -Mfr <f>             use max <f> uninterpreted real funcs   (default  1)\n" +
"  -mfar1 <f>           use min <f> uninterpreted array1 funcs (default  1)\n" +
"  -Mfar1 <f>           use max <f> uninterpreted array1 funcs (default  1)\n" +
"  -mfar2 <f>           use min <f> uninterpreted array2 funcs (default  1)\n" +
"  -Mfar2 <f>           use max <f> uninterpreted array2 funcs (default  1)\n" +
"  -mpi <p>             use min <p> uninterpreted int preds    (default  1)\n" +
"  -Mpi <p>             use max <p> uninterpreted int preds    (default  1)\n" +
"  -mpr <p>             use min <p> uninterpreted real preds   (default  1)\n" +
"  -Mpr <p>             use max <p> uninterpreted real preds   (default  1)\n" +
"  -mpar1 <p>           use min <p> uninterpreted array1 preds (default  1)\n" +
"  -Mpar1 <p>           use max <p> uninterpreted array1 preds (default  1)\n" +
"  -mpar2 <p>           use min <p> uninterpreted array2 preds (default  1)\n" +
"  -Mpar2 <p>           use max <p> uninterpreted array2 preds (default  1)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
"                       bit-width is used to\n" +
"                       restrict the constants\n" +
"  -mqfi <qf>           use min <qf> quantified formulas over\n" +
"                       integer function and predicates        (default  1)\n" +
"  -Mqfi <qf>           use max <qf> quantified formulas over\n" +
"                       integer function and predicates        (default  1)\n" +
"  -mqfr <qf>           use min <qf> quantified formulas over\n" +
"                       real function and predicates           (default  1)\n" +
"  -Mqfr <qf>           use max <qf> quantified formulas over\n" +
"                       real function and predicates           (default  1)\n" +
"  -mqfar1 <qf>         use min <qf> quantified formulas over\n" +
"                       array1 function and predicates         (default  0)\n" +
"  -Mqfar1 <qf>         use max <qf> quantified formulas over\n" +
"                       array1 function and predicates         (default  0)\n" +
"  -mqfar2 <qf>         use min <qf> quantified formulas over\n" +
"                       array2 function and predicates         (default  0)\n" +
"  -Mqfar2 <qf>         use max <qf> quantified formulas over\n" +
"                       array2 function and predicates         (default  0)\n" +
"  -mqv <qv>            set minimum number of quantified\n" +
"                       variables per quantifier to <qn>       (default  1)\n" +
"  -Mqv <qv>            set maximum number of quantified\n" +
"                       variables per quantifier to <qn>       (default  3)\n" +
"  -mqn <qn>            set minimum quantifier nesting\n" +
"                       level to <qn>                          (default  0)\n" +
"  -Mqn <qn>            set maximum quantifier nesting\n" +
"                       level to <qn>                          (default  1)\n" +
"  -ref <refs>          set min number of references for terms\n" + 
"                       in input and main layer to <refs>      (default  1)\n" +
"\n" +
"QF_BV and QF_UFBV options:\n" +
"  -mv <vars>           use min <vars> bit-vector variables    (default  1)\n" +
"  -Mv <vars>           use max <vars> bit-vector variables    (default  5)\n" +
"  -mc <consts>         use min <const> bit-vector constants   (default  1)\n" +
"  -Mc <consts>         use max <const> bit-vector constants   (default  2)\n" +
"  -mbw <bw>            set min bit-width to <bw>              (default  1)\n" +
"  -Mbw <bw>            set max bit-width to <bw>              (default 16)\n" +
"  -g                   do not guard BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n"+
"  -n                   do not use BVUDIV BVSDIV BVUREM BVSREM BVSMOD\n" +
"  -ref <refs>          set min number of references for terms\n" +
"                       in input and main layer to <refs>      (default  1)\n" +
"  QF_UFBV only:\n" +
"  -mf <funcs>          use min <funcs> uninterpreted funcs    (default  1)\n" +
"  -Mf <funcs>          use max <funcs> uninterpreted funcs    (default  2)\n" +
"  -mp <preds>          use min <preds> uninterpreted preds    (default  1)\n" +
"  -Mp <preds>          use max <preds> uninterpreted preds    (default  2)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"\n" +
"QF_IDL, QF_UFIDL, QF_RDL and QF_UFRDL options:\n" +
"  -mv <vars>           use min <vars> variables               (default  1)\n" +
"  -Mv <vars>           use max <vars> variables               (default  8)\n" +
"  -mc <consts>         use min <const> integer constants      (default  1)\n" +
"  -Mc <consts>         use max <const> integer constants      (default  6)\n" +
"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
"                       bit-width is used to\n" +
"                       restrict the constants\n" +
"  -ref <refs>          set minimum number of references\n" +  
"                       for vars and consts to <refs>          (default  5)\n"+
"   QF_UFIDL and QF_UFRDL only:\n" +
"  -mf <funcs>          use min <funcs> uninterpreted funcs    (default  1)\n" +
"  -Mf <funcs>          use max <funcs> uninterpreted funcs    (default  2)\n" +
"  -mp <preds>          use min <preds> uninterpreted preds    (default  1)\n" +
"  -Mp <preds>          use max <preds> uninterpreted preds    (default  2)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"\n" +
"QF_LIA, QF_UFLIA, QF_NIA, QF_UFNIA, QF_LRA,\n" +  
"QF_UFLRA, QF_NRA, QF_UFNRA and LRA options:\n" +
"  -mv <vars>           use min <vars> variables               (default  1)\n" +
"  -Mv <vars>           use max <vars> variables               (default  3)\n" +
"  -mc <consts>         use min <const> integer constants      (default  1)\n" +
"  -Mc <consts>         use max <const> integer constants      (default  3)\n" +
"                       in the real context, integer constants\n" +
"                       are used, amongst others, to generate\n" +
"                       real constants of the form (c1 / c2)\n" +
"  -Mbw <bw>            set max bit-width to <bw>              (default  4)\n" +
"                       bit-width is used to\n" +
"                       restrict the constants\n" +
"  -ref <refs>          set minimum number of references\n" +  
"                       for vars and consts to <refs>          (default  1)\n" +
"  QF_UFLIA, QF_UFNIA, QF_UFLRA and QF_UFNRA only:\n" +
"  -mf <funcs>          use min <funcs> uninterpreted funcs    (default  1)\n" +
"  -Mf <funcs>          use max <funcs> uninterpreted funcs    (default  2)\n" +
"  -mp <preds>          use min <preds> uninterpreted preds    (default  1)\n" +
"  -Mp <preds>          use max <preds> uninterpreted preds    (default  2)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"\n" +
"QF_UF options:\n" +
"  -ms <sorts>          use min <sorts> sorts                  (default  1)\n" +
"  -Ms <sorts>          use max <sorts> sorts                  (default  3)\n" +
"  -mv <vars>           use min <vars> variables for each sort (default  1)\n" +
"  -Mv <vars>           use max <vars> variables for each sort (default  3)\n" +
"  -mf <funcs>          use at least <funcs> functions         (default  5)\n" +
"  -mp <preds>          use at least <preds> predicates        (default  5)\n" +
"  -ma <args>           set min number of arguments to <args>  (default  1)\n" +
"  -Ma <args>           set max number of arguments to <args>  (default  3)\n" +
"  -ref <refs>          set min number of references for terms\n" + 
"                       in input and main layer to <refs>      (default  1)\n" +
"\n";

  public static void main (String args[]) {
    smtlib1 =false;
	SMTLogic logic = null;
    Random r = null;
    int pars = 1;
    int minRefs = 1;
    int minNumConsts = 1;
    int maxNumConsts = 1;
    int numConsts = 0;
    int minNumConstsInt = 1;
    int maxNumConstsInt = 1;
    int numConstsInt = 0;
    int minNumConstsIntAsReal = 1;
    int maxNumConstsIntAsReal = 1;
    int numConstsIntAsReal = 0;
    int minNumVars = 1;
    int maxNumVars = 1;
    int numVars = 0;
    int minNumVarsInt = 1;
    int maxNumVarsInt = 1;
    int numVarsInt = 0;
    int minNumVarsReal = 1;
    int maxNumVarsReal = 1;
    int numVarsReal = 0;
    int minNumArrays = 1;
    int maxNumArrays = 1;
    int numArrays = 0;
    int minNumArrays1 = 0;
    int maxNumArrays1 = 0;
    int numArrays1 = 0;
    int minNumArrays2 = 0;
    int maxNumArrays2 = 0;
    int numArrays2 = 0;
    int minNumReads = 1;
    int maxNumReads = 1;
    int numReads = 0;
    int minNumReadsArray1 = 1;
    int maxNumReadsArray1 = 1;
    int numReadsArray1 = 0;
    int minNumReadsArray2 = 1;
    int maxNumReadsArray2 = 1;
    int numReadsArray2 = 0;
    int minNumWrites = 0;
    int maxNumWrites = 0;
    int numWrites = 0;
    int minNumWritesArray1 = 0;
    int maxNumWritesArray1 = 0;
    int numWritesArray1 = 0;
    int minNumWritesArray2 = 0;
    int maxNumWritesArray2 = 0;
    int numWritesArray2 = 0;
    int minBW = 0;
    int maxBW = 0;
    int minNumExtBool = 0;
    int maxNumExtBool = 0;
    int numExtBool = 0;
    int minNumSorts = 1;
    int maxNumSorts = 1;
    int numSorts = 0;
    int minNumUFuncs = 0;
    int maxNumUFuncs = 0;
    int numUFuncs = 0;
    int minNumUPreds = 0;
    int maxNumUPreds = 0;
    int numUPreds = 0;
    int minArgs = 1;
    int maxArgs = 3;
    int minNumIndices = 1;
    int maxNumIndices = 1;
    int numIndices = 0;
    int minNumElements = 1;
    int maxNumElements = 1;
    int numElements = 0;
    int minNumQFormulasInt = 0;
    int maxNumQFormulasInt = 0;
    int numQFormulasInt = 0;
    int minNumQFormulasReal = 0;
    int maxNumQFormulasReal = 0;
    int numQFormulasReal = 0;
    int minNumQFormulasArray = 0;
    int maxNumQFormulasArray = 0;
    int numQFormulasArray = 0;
    int minNumQFormulasArray1 = 0;
    int maxNumQFormulasArray1 = 0;
    int numQFormulasArray1 = 0;
    int minNumQFormulasArray2 = 0;
    int maxNumQFormulasArray2 = 0;
    int numQFormulasArray2 = 0;
    int minQVars = 0;
    int maxQVars = 0;
    int minQNestings = 0;
    int maxQNestings = 0;
    int minNumUFuncsInt = 0;
    int maxNumUFuncsInt = 0;
    int numUFuncsInt = 0;
    int minNumUFuncsReal = 0;
    int maxNumUFuncsReal = 0;
    int numUFuncsReal = 0;
    int minNumUFuncsArray = 0;
    int maxNumUFuncsArray = 0;
    int numUFuncsArray = 0;
    int minNumUFuncsArray1 = 0;
    int maxNumUFuncsArray1 = 0;
    int numUFuncsArray1 = 0;
    int minNumUFuncsArray2 = 0;
    int maxNumUFuncsArray2 = 0;
    int numUFuncsArray2 = 0;
    int minNumUPredsInt = 0;
    int maxNumUPredsInt = 0;
    int numUPredsInt = 0;
    int minNumUPredsReal = 0;
    int maxNumUPredsReal = 0;
    int numUPredsReal = 0;
    int minNumUPredsArray = 0;
    int maxNumUPredsArray = 0;
    int numUPredsArray = 0;
    int minNumUPredsArray1 = 0;
    int maxNumUPredsArray1 = 0;
    int numUPredsArray1 = 0;
    int minNumUPredsArray2 = 0;
    int maxNumUPredsArray2 = 0;
    int numUPredsArray2 = 0;
    boolean linear = true;
    double factor = 1.0;
    int bulkExport = 0;
    
    output = System.out;
    
    RelCompMode compModeArray = RelCompMode.OFF;
    RelCompMode compModeArray1 = RelCompMode.OFF;
    RelCompMode compModeArray2 = RelCompMode.OFF;
    BVDivMode bvDivMode = BVDivMode.GUARD;
    
    StringBuilder builder;
    ArrayList<SMTNode> boolNodes = null;
    HashMap<SMTNode, SMTNodeKind> BVDivGuards = null;
    BooleanLayerKind booleanLayerKind = BooleanLayerKind.RANDOM;

    if (args.length == 0) {
      output.println (usage);
      System.exit (0);
    }

    if (args[0].equals ("-V"))
      printVersionAndExit ();
    
    if (args[0].equals ("-h"))
      printHelpAndExit ();

    logic = SMTLogic.stringToLogic.get(args[0]);
    if (logic == null)
      printHelpAndExit ();

    switch (logic) {
      case QF_A:
      case QF_AX:
        minNumArrays = 1;
        maxNumArrays = 3;
        minNumIndices = 1;
        maxNumIndices = 5;
        minNumElements = 1;
        maxNumElements = 5;
        minNumReads = 1;
        maxNumReads = 10;
        minNumWrites = 0;
        maxNumWrites = 10;
        break;
      case QF_AUFBV:
        minNumVars = 1;
        maxNumVars = 5;
        minNumConsts = 1;
        maxNumConsts = 2;
        minNumArrays = 1;
        maxNumArrays = 3;
        minNumReads = 1;
        maxNumReads = 5;
        minNumWrites = 0;
        maxNumWrites = 5;
        minNumExtBool = 0;
        maxNumExtBool = 0;
        minBW = 1;
        maxBW = 16;
        minNumUFuncs = 0;
        maxNumUFuncs = 2;
        minNumUPreds = 0;
        maxNumUPreds = 2;
        minArgs = 1;
        maxArgs = 3;
        bvDivMode = BVDivMode.GUARD;
        break;
      case QF_ABV:
          minNumVars = 1;
          maxNumVars = 5;
          minNumConsts = 1;
          maxNumConsts = 2;
          minNumArrays = 1;
          maxNumArrays = 3;
          minNumReads = 1;
          maxNumReads = 5;
          minNumWrites = 0;
          maxNumWrites = 5;
          minNumExtBool = 0;
          maxNumExtBool = 0;
          minBW = 1;
          maxBW = 16;
          minNumUFuncs = 0;
          maxNumUFuncs = 0;
          minNumUPreds = 0;
          maxNumUPreds = 0;
          minArgs = 1;
          maxArgs = 3;
          bvDivMode = BVDivMode.GUARD;
          break;
      case AUFLIA:
        minNumQFormulasInt = 1;
        maxNumQFormulasInt = 1;
        minNumQFormulasArray = 0;
        maxNumQFormulasArray = 0;
        minQVars = 1;
        maxQVars = 3;
        minQNestings = 0;
        maxQNestings = 1;
        /* fall through by intention */
      case QF_AUFLIA:
        minNumVars = 1;
        maxNumVars = 3;
        minNumConsts = 1;
        maxNumConsts = 3;
        minNumArrays = 1;
        maxNumArrays = 3;
        minNumReads = 1;
        maxNumReads = 5;
        minNumWrites = 0;
        maxNumWrites = 5;
        compModeArray = RelCompMode.OFF;
        minNumUFuncsInt = 1;
        maxNumUFuncsInt = 1;
        minNumUFuncsArray = 1;
        maxNumUFuncsArray = 1;
        minNumUPredsInt = 1;
        maxNumUPredsInt = 1;
        minNumUPredsArray = 1;
        maxNumUPredsArray = 1;
        minArgs = 1;
        maxArgs = 3;
        maxBW = 4;
        break;
      case AUFNIRA:
        linear = false;
        /* fall through by intention */
      case AUFLIRA:
        minNumVarsInt = 1;
        maxNumVarsInt = 2;
        minNumVarsReal = 1;
        maxNumVarsReal = 2;
        minNumConstsInt = 1;
        maxNumConstsInt = 3;
        minNumConstsIntAsReal = 1;
        maxNumConstsIntAsReal = 3;
        minNumArrays1 = 1;
        maxNumArrays1 = 2;
        minNumArrays2 = 1;
        maxNumArrays2 = 2;
        minNumReadsArray1 = 1;
        maxNumReadsArray1 = 4;
        minNumReadsArray2 = 1;
        maxNumReadsArray2 = 4;
        minNumWritesArray1 = 0;
        maxNumWritesArray1 = 3;
        minNumWritesArray2 = 0;
        maxNumWritesArray2 = 3;
        compModeArray1 = RelCompMode.OFF;
        compModeArray2 = RelCompMode.OFF;
        minNumUFuncsInt = 1;
        maxNumUFuncsInt = 1;
        minNumUFuncsReal = 1;
        maxNumUFuncsReal = 1;
        minNumUFuncsArray1 = 1;
        maxNumUFuncsArray1 = 1;
        minNumUFuncsArray2 = 1;
        maxNumUFuncsArray2 = 1;
        minNumUPredsInt = 1;
        maxNumUPredsInt = 1;
        minNumUPredsReal = 1;
        maxNumUPredsReal = 1;
        minNumUPredsArray1 = 1;
        maxNumUPredsArray1 = 1;
        minNumUPredsArray2 = 1;
        maxNumUPredsArray2 = 1;
        minArgs = 1;
        maxArgs = 3;
        maxBW = 4;
        minNumQFormulasInt = 1;
        maxNumQFormulasInt = 1;
        minNumQFormulasReal = 1;
        maxNumQFormulasReal = 1;
        minNumQFormulasArray1 = 0;
        maxNumQFormulasArray1 = 0;
        minNumQFormulasArray2 = 0;
        maxNumQFormulasArray2 = 0;
        minQVars = 1;
        maxQVars = 3;
        minQNestings = 0;
        maxQNestings = 1;
        break;
      case QF_UFBV:
        minNumUFuncs = 1;
        maxNumUFuncs = 2;
        minNumUPreds = 1;
        maxNumUPreds = 2;
        minArgs = 1;
        maxArgs = 3;
        /* fall through by intenion */
      case QF_BV:
        minNumVars = 1;
        maxNumVars = 5;
        minNumConsts = 1;
        maxNumConsts = 2;
        minBW = 1;
        maxBW = 16;
        bvDivMode = BVDivMode.GUARD;
        break;
      case QF_UFIDL:
      case QF_UFRDL:
        minNumUFuncs = 1;
        maxNumUFuncs = 2;
        minNumUPreds = 1;
        maxNumUPreds = 2;
        minArgs = 1;
        maxArgs = 3;
        /* fall through by intention */
      case QF_IDL:
      case QF_RDL:
        minNumVars = 1;
        maxNumVars = 8;
        minNumConsts = 1;
        maxNumConsts = 6;
        maxBW = 4;
        minRefs = 5;
        break;
      case QF_UFNIA:
      case QF_UFNRA:
      case QF_UFLIA:
      case QF_UFLRA:
        minNumUFuncs = 1;
        maxNumUFuncs = 2;
        minNumUPreds = 1;
        maxNumUPreds = 2;
        minArgs = 1;
        maxArgs = 3;
        /* fall through by intenion */
      case QF_LIA:
      case QF_NIA:
      case QF_LRA:
      case LRA:
      case QF_NRA:
        minNumVars = 1;
        maxNumVars = 3;
        minNumConsts = 1;
        maxNumConsts = 3;
        maxBW = 4;
        switch (logic) {
          case QF_NIA:
          case QF_NRA:
          case QF_UFNIA:
          case QF_UFNRA:
            linear = false;
            break;
          default:
            break;
        }
        break;
      case QF_UF:
        minNumVars = 1;
        maxNumVars = 3;
        minNumSorts = 1;
        maxNumSorts = 3;
        minNumUFuncs = 5;
        minNumUPreds = 5;
        minArgs = 1;
        maxArgs = 3;
        break;
      default:
        assert (false);
    }

    for (int i = 1; i < args.length; i++) {
      String arg = args[i];
      if (arg.charAt(0) == '-') {
        if (arg.equals ("-h")) {
          printHelpAndExit ();
        } else if (arg.equals("-V")) {
          printVersionAndExit ();
        } else if (arg.equals("-g")) {
          bvDivMode = BVDivMode.FULL;
        } else if (arg.equals("-n")) {
          bvDivMode = BVDivMode.OFF;
        } else if (arg.equals("-x")) {
          compModeArray = RelCompMode.EQ;
        } else if (arg.equals("-x1")) {
          compModeArray1 = RelCompMode.EQ;
        } else if (arg.equals("-x2")) {
          compModeArray2 = RelCompMode.EQ;
        } else if (arg.equals("-bool-random")) {
          booleanLayerKind = BooleanLayerKind.RANDOM;
        } else if (arg.equals("-bool-and")) {
          booleanLayerKind = BooleanLayerKind.AND;
        } else if (arg.equals("-bool-or")) {
          booleanLayerKind = BooleanLayerKind.OR;
        } else if (arg.equals("-seed")) {
          r = new Random (parseLongOption (args, i++, 0l, "invalid seed"));
        } else if (arg.equals("-bool-cnf")) {
          factor = parseDoubleOption (args, i++, 0.0, "invalid CNF factor");
          booleanLayerKind = BooleanLayerKind.CNF;
        } else if (arg.equals("-ref")) {
          minRefs = parseIntOption (args, i++, 1, "invalid minimum number of references");
        } else if (arg.equals("-mv")) {
          minNumVars = parseIntOption (args, i++, 1, "invalid minimum number of variables");
        } else if (arg.equals("-Mv")) {
          maxNumVars = parseIntOption (args, i++, 1, "invalid maximum number of variables");
        } else if (arg.equals("-mvi")) {
          minNumVarsInt = parseIntOption (args, i++, 1, "invalid minimum number of variables of type integer");
        } else if (arg.equals("-Mvi")) {
          maxNumVarsInt = parseIntOption (args, i++, 1, "invalid maximum number of variables of type integer");
        } else if (arg.equals("-mvr")) {
          minNumVarsReal = parseIntOption (args, i++, 1, "invalid minimum number of variables of type real");
        } else if (arg.equals("-Mvr")) {
          maxNumVarsReal = parseIntOption (args, i++, 1, "invalid maximum number of variables of type real");
        } else if (arg.equals("-mc")) {
          minNumConsts = parseIntOption (args, i++, 1, "invalid minimum number of constants");
        } else if (arg.equals("-Mc")) {
          maxNumConsts = parseIntOption (args, i++, 1, "invalid maximum number of constants");
        } else if (arg.equals("-mci")) {
          minNumConstsInt = parseIntOption (args, i++, 1, "invalid minimum number of integer constants");
        } else if (arg.equals("-Mci")) {
          maxNumConstsInt = parseIntOption (args, i++, 1, "invalid maximum number of integer constants");
        } else if (arg.equals("-mcr")) {
          minNumConstsIntAsReal = parseIntOption (args, i++, 1, "invalid minimum number of integer constants in real context");
        } else if (arg.equals("-Mcr")) {
          maxNumConstsIntAsReal = parseIntOption (args, i++, 1, "invalid maximum number of integer constants in real context");
        } else if (arg.equals("-ms")) {
          minNumSorts = parseIntOption (args, i++, 1, "invalid minimum number of sorts");
        } else if (arg.equals("-Ms")) {
          maxNumSorts = parseIntOption (args, i++, 1, "invalid maximum number of sorts");
        } else if (arg.equals("-mf")) {
          minNumUFuncs = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted functions");
        } else if (arg.equals("-Mf")) {
          maxNumUFuncs = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted functions");
        } else if (arg.equals("-mfi")) {
          minNumUFuncsInt = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted integer functions");
        } else if (arg.equals("-Mfi")) {
          maxNumUFuncsInt = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted integer functions");
        } else if (arg.equals("-mfr")) {
          minNumUFuncsReal = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted real functions");
        } else if (arg.equals("-Mfr")) {
          maxNumUFuncsReal = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted real functions");
        } else if (arg.equals("-mfar")) {
          minNumUFuncsArray = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array functions");
        } else if (arg.equals("-Mfar")) {
          maxNumUFuncsArray = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array functions");
        } else if (arg.equals("-mfar1")) {
          minNumUFuncsArray1 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array1 functions");
        } else if (arg.equals("-Mfar1")) {
          maxNumUFuncsArray1 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array1 functions");
        } else if (arg.equals("-mfar2")) {
          minNumUFuncsArray2 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array2 functions");
        } else if (arg.equals("-Mfar2")) {
          maxNumUFuncsArray2 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array2 functions");
        } else if (arg.equals("-mp")) {
          minNumUPreds = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted predicates");
        } else if (arg.equals("-Mp")) {
          maxNumUPreds = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted predicates");
        } else if (arg.equals("-mpi")) {
          minNumUPredsInt = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted integer predicates");
        } else if (arg.equals("-Mpi")) {
          maxNumUPredsInt = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted integer predicates");
        } else if (arg.equals("-mpr")) {
          minNumUPredsReal = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted real predicates");
        } else if (arg.equals("-Mpr")) {
          maxNumUPredsReal = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted real predicates");
        } else if (arg.equals("-mpar")) {
          minNumUPredsArray = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array predicates");
        } else if (arg.equals("-Mpar")) {
          maxNumUPredsArray = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array predicates");
        } else if (arg.equals("-mpar1")) {
          minNumUPredsArray1 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array1 predicates");
        } else if (arg.equals("-Mpar1")) {
          maxNumUPredsArray1 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array1 predicates");
        } else if (arg.equals("-mpar2")) {
          minNumUPredsArray2 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array2 predicates");
        } else if (arg.equals("-Mpar2")) {
          maxNumUPredsArray2 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array2 predicates");
        } else if (arg.equals("-ma")) {
          minArgs = parseIntOption (args, i++, 1, "invalid minimum number of arguments");
        } else if (arg.equals("-Ma")) {
          maxArgs = parseIntOption (args, i++, 1, "invalid maximum number of arguments");
        } else if (arg.equals("-mqfi")) {
          minNumQFormulasInt = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over integers");
        } else if (arg.equals("-Mqfi")) {
          maxNumQFormulasInt = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over integers");
        } else if (arg.equals("-mqfr")) {
          minNumQFormulasReal = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over reals");
        } else if (arg.equals("-Mqfr")) {
          maxNumQFormulasReal = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over reals");
        } else if (arg.equals("-mqfar")) {
          minNumQFormulasArray = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over arrays");
        } else if (arg.equals("-Mqfar")) {
          maxNumQFormulasArray = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over arrays");
        } else if (arg.equals("-mqfar1")) {
          minNumQFormulasArray1 = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over arrays of type array1");
        } else if (arg.equals("-Mqfar1")) {
          maxNumQFormulasArray1 = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over arrays of type array1");
        } else if (arg.equals("-mqfar2")) {
          minNumQFormulasArray2 = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over arrays of type array2");
        } else if (arg.equals("-Mqfar2")) {
          maxNumQFormulasArray2 = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over arrays of type array2");
        } else if (arg.equals("-mqv")) {
          minQVars = parseIntOption (args, i++, 1, "invalid minimum number of quantified variables");
        } else if (arg.equals("-Mqv")) {
          maxQVars = parseIntOption (args, i++, 1, "invalid maximum number of quantified variables");
        } else if (arg.equals("-mqn")) {
          minQNestings = parseIntOption (args, i++, 0, "invalid minimum number of quantifier nestings");
        } else if (arg.equals("-Mqn")) {
          maxQNestings = parseIntOption (args, i++, 0, "invalid maximum number of quantifier nestings");
        } else if (arg.equals("-mar")) {
          minNumArrays = parseIntOption (args, i++, 1, "invalid minimum number of arrays");
        } else if (arg.equals("-Mar")) {
          maxNumArrays = parseIntOption (args, i++, 1, "invalid maximum number of arrays");
        } else if (arg.equals("-mar1")) {
          minNumArrays1 = parseIntOption (args, i++, 1, "invalid minimum number of arrays of type array1");
        } else if (arg.equals("-Mar1")) {
          maxNumArrays1 = parseIntOption (args, i++, 1, "invalid maximum number of arrays of type array1");
        } else if (arg.equals("-mar2")) {
          minNumArrays2 = parseIntOption (args, i++, 1, "invalid minimum number of arrays of type array2");
        } else if (arg.equals("-Mar2")) {
          maxNumArrays2 = parseIntOption (args, i++, 1, "invalid maximum number of arrays of type array2");
        } else if (arg.equals("-mi")) {
          minNumIndices = parseIntOption (args, i++, 1, "invalid minimum number of indices");
        } else if (arg.equals("-Mi")) {
          maxNumIndices = parseIntOption (args, i++, 1, "invalid maximum number of indices");
        } else if (arg.equals("-me")) {
          minNumElements = parseIntOption (args, i++, 1, "invalid minimum number of elements");
        } else if (arg.equals("-Me")) {
          maxNumElements = parseIntOption (args, i++, 1, "invalid maximum number of elements");
        } else if (arg.equals("-mr")) {
          minNumReads = parseIntOption (args, i++, 1, "invalid minimum number of reads");
        } else if (arg.equals("-Mr")) {
          maxNumReads = parseIntOption (args, i++, 1, "invalid maximum number of reads");
        } else if (arg.equals("-mr1")) {
          minNumReadsArray1 = parseIntOption (args, i++, 1, "invalid minimum number of reads on arrays of type array1");
        } else if (arg.equals("-Mr1")) {
          maxNumReadsArray1 = parseIntOption (args, i++, 1, "invalid maximum number of reads on arrays of type array1");
        } else if (arg.equals("-mr2")) {
          minNumReadsArray2 = parseIntOption (args, i++, 1, "invalid minimum number of reads on arrays of type array2");
        } else if (arg.equals("-Mr2")) {
          maxNumReadsArray2 = parseIntOption (args, i++, 1, "invalid maximum number of reads on arrays of type array2");
        } else if (arg.equals("-mw")) {
          minNumWrites = parseIntOption (args, i++, 0, "invalid minimum number of writes");
        } else if (arg.equals("-Mw")) {
          maxNumWrites = parseIntOption (args, i++, 0, "invalid maximum number of writes");
        } else if (arg.equals("-mw1")) {
          minNumWritesArray1 = parseIntOption (args, i++, 0, "invalid minimum number of writes on arrays of type array1");
        } else if (arg.equals("-Mw1")) {
          maxNumWritesArray1 = parseIntOption (args, i++, 0, "invalid maximum number of writes on arrays of type array1");
        } else if (arg.equals("-mw2")) {
          minNumWritesArray2 = parseIntOption (args, i++, 0, "invalid minimum number of writes on arrays of type array2");
        } else if (arg.equals("-Mw2")) {
          maxNumWritesArray2 = parseIntOption (args, i++, 0, "invalid maximum number of writes on arrays of type array2");
        } else if (arg.equals("-mxn")) {
          minNumExtBool = parseIntOption (args, i++, 0, "invalid minimum number of array equalities");
        } else if (arg.equals("-Mxn")) {
          maxNumExtBool = parseIntOption (args, i++, 0, "invalid maximum number of array equalities");
        } else if (arg.equals("-mbw")) {
          minBW = parseIntOption (args, i++, 1, "invalid minimum bit-width");
        } else if (arg.equals("-Mbw")) {
          maxBW = parseIntOption (args, i++, 1, "invalid maximum bit-width");
        } else if (arg.equals("-smtlib1")) {
        	smtlib1 = true;
        } else if (arg.equals("-bulk-export")) {
        	bulkExport = parseIntOption (args, i++, 1, "invalid bulk export amount");
        } else if (arg.equals("-bulk-prefix")) {
		if (i+1 == args.length - 1)
      			printErrAndExit ("option argument missing");
        	bulkPrefix = args[++i];
        }

        else { 
          printErrAndExit ("invalid option: " + arg);
        }
      } else {
        printHelpAndExit();
      }
    }

    if (r == null) /* seed has not been set */
	      r = new Random();
    
    for (int fileId =0; fileId < Math.max(bulkExport,1);fileId++)
    {
	    if (bulkExport ==0)
	    	output = System.out;
	    else
	    {
	        try
	        {
	        	if (fileId > 0)
	        		{
	        	    boolNodes = null;
	        	    BVDivGuards = null;
	        	    pars = 1;
	        		output.close();
	        		}
	        	
	        	java.io.FileOutputStream out = new java.io.FileOutputStream(bulkPrefix + "_file_" + fileId + (smtlib1?".smt":".smt2"));
	        	output = new java.io.PrintStream(out);
	        } catch (Exception e)
	        {
	        	throw new Error(e);
	        }
	    }
	
	    assert (numVars >= 0);
	    assert (numConsts >= 0);
	    assert (minRefs >= 1);
	    switch (logic) {
	      case AUFLIRA:
	      case AUFNIRA:
	        assert (linear || logic != SMTLogic.AUFLIRA);
	        assert (!linear || logic != SMTLogic.AUFNIRA);
	        assert (minNumVarsInt > 0);
	        assert (maxNumVarsInt > 0);
	        assert (minNumVarsReal > 0);
	        assert (maxNumVarsReal > 0);
	        assert (minNumConstsInt > 0);
	        assert (maxNumConstsInt > 0);
	        assert (minNumConstsIntAsReal > 0);
	        assert (maxNumConstsIntAsReal > 0);
	        assert (minNumArrays1 > 0);
	        assert (maxNumArrays1 > 0);
	        assert (minNumArrays2 > 0);
	        assert (maxNumArrays2 > 0);
	        assert (minNumReadsArray1 > 0);
	        assert (maxNumReadsArray1 > 0);
	        assert (minNumReadsArray2 > 0);
	        assert (maxNumReadsArray2 > 0);
	        assert (minNumWritesArray1 >= 0);
	        assert (maxNumWritesArray1 >= 0);
	        assert (minNumWritesArray2 >= 0);
	        assert (maxNumWritesArray2 >= 0);
	        assert (minNumUFuncsInt >= 0);
	        assert (maxNumUFuncsInt >= 0);
	        assert (minNumUFuncsReal >= 0);
	        assert (maxNumUFuncsReal >= 0);
	        assert (minNumUFuncsArray1 >= 0);
	        assert (maxNumUFuncsArray1 >= 0);
	        assert (minNumUFuncsArray2 >= 0);
	        assert (maxNumUFuncsArray2 >= 0);
	        assert (minNumUPredsInt >= 0);
	        assert (maxNumUPredsInt >= 0);
	        assert (minNumUPredsReal >= 0);
	        assert (maxNumUPredsReal >= 0);
	        assert (minNumUPredsArray1 >= 0);
	        assert (maxNumUPredsArray1 >= 0);
	        assert (minNumUPredsArray2 >= 0);
	        assert (maxNumUPredsArray2 >= 0);
	        assert (minArgs > 0);
	        assert (maxArgs > 0);
	        assert (maxBW > 0);
	        assert (minNumQFormulasInt >= 0);
	        assert (maxNumQFormulasInt >= 0);
	        assert (minNumQFormulasReal >= 0);
	        assert (maxNumQFormulasReal >= 0);
	        assert (minNumQFormulasArray1 >= 0);
	        assert (maxNumQFormulasArray1 >= 0);
	        assert (minNumQFormulasArray2 >= 0);
	        assert (maxNumQFormulasArray2 >= 0);
	        assert (minQVars > 0);
	        assert (maxQVars > 0);
	        assert (minQNestings >= 0);
	        assert (maxQNestings >= 0);
	        checkMinMax (minNumVarsInt, maxNumVarsInt, "integer variables");
	        checkMinMax (minNumVarsReal, maxNumVarsReal, "real variables");
	        checkMinMax (minNumConstsInt, maxNumConstsInt, "integer constants");
	        checkMinMax (minNumConstsIntAsReal, maxNumConstsIntAsReal, 
	                     "integer constants in real context");
	        checkMinMax (minNumArrays1, maxNumArrays1, "arrays of type array1");
	        checkMinMax (minNumArrays2, maxNumArrays2, "arrays of type array2");
	        checkMinMax (minNumReadsArray1, maxNumReadsArray1, 
	                     "reads on arrays of type array1");
	        checkMinMax (minNumReadsArray2, maxNumReadsArray2,
	                     "reads on arrays of type array2");
	        checkMinMax (minNumWritesArray1, maxNumWritesArray1, 
	                     "writes on arrays of type array1");
	        checkMinMax (minNumWritesArray2, maxNumWritesArray2, 
	                     "writes on arrays of type array2");
	        checkMinMax (minNumUFuncsInt, maxNumUFuncsInt, 
	                     "uninterpreted integer functions");
	        checkMinMax (minNumUFuncsReal, maxNumUFuncsReal, 
	                     "uninterpreted real functions");
	        checkMinMax (minNumUFuncsArray1, maxNumUFuncsArray1, 
	                     "uninterpreted array1 functions");
	        checkMinMax (minNumUFuncsArray2, maxNumUFuncsArray2, 
	                     "uninterpreted array2 functions");
	        checkMinMax (minNumUPredsInt, maxNumUPredsInt, 
	                     "uninterpreted integer predicates");
	        checkMinMax (minNumUPredsReal, maxNumUPredsReal, 
	                     "uninterpreted real predicates");
	        checkMinMax (minNumUPredsArray1, maxNumUPredsArray1, 
	                     "uninterpreted array1 predicates");
	        checkMinMax (minNumUPredsArray2, maxNumUPredsArray2, 
	                     "uninterpreted array2 predicates");
	        checkMinMax (minArgs, maxArgs, "arguments");
	        checkMinMax (minNumQFormulasInt, maxNumQFormulasInt,
	                     "quantified formulas over integers");
	        checkMinMax (minNumQFormulasReal, maxNumQFormulasReal,
	                     "quantified formulas over reals");
	        checkMinMax (minNumQFormulasArray1, maxNumQFormulasArray1,
	                     "quantified formulas over arrays of type array1");
	        checkMinMax (minNumQFormulasArray2, maxNumQFormulasArray2,
	                     "quantified formulas over arrays of type array2");
	        numVarsInt = selectRandValRange (r, minNumVarsInt, maxNumVarsInt);
	        numVarsReal = selectRandValRange (r, minNumVarsReal, maxNumVarsReal);
	        numConstsInt = selectRandValRange (r, minNumConstsInt, maxNumConstsInt);
	        numConstsIntAsReal = selectRandValRange (r, minNumConstsIntAsReal, 
	                                                 maxNumConstsIntAsReal);
	        numArrays1 = selectRandValRange (r, minNumArrays1, maxNumArrays1);
	        numArrays2 = selectRandValRange (r, minNumArrays2, maxNumArrays2);
	        numReadsArray1 = selectRandValRange (r, minNumReadsArray1, 
	                                             maxNumReadsArray1);
	        numReadsArray2 = selectRandValRange (r, minNumReadsArray2, 
	                                             maxNumReadsArray2);
	        numWritesArray1 = selectRandValRange (r, minNumWritesArray1, 
	                                              maxNumWritesArray1);
	        numWritesArray2 = selectRandValRange (r, minNumWritesArray2, 
	                                              maxNumWritesArray2);
	        numUFuncsInt = selectRandValRange (r, minNumUFuncsInt, maxNumUFuncsInt);
	        numUFuncsReal = selectRandValRange (r, minNumUFuncsReal, 
	                                            maxNumUFuncsReal);
	        numUFuncsArray1 = selectRandValRange (r, minNumUFuncsArray1, 
	                                              maxNumUFuncsArray1);
	        numUFuncsArray2 = selectRandValRange (r, minNumUFuncsArray2, 
	                                              maxNumUFuncsArray2);
	        numUPredsInt = selectRandValRange (r, minNumUPredsInt, maxNumUPredsInt);
	        numUPredsReal = selectRandValRange (r, minNumUPredsReal, 
	                                            maxNumUPredsReal);
	        numUPredsArray1 = selectRandValRange (r, minNumUPredsArray1, 
	                                              maxNumUPredsArray1);
	        numUPredsArray2 = selectRandValRange (r, minNumUPredsArray2, 
	                                              maxNumUPredsArray2);
	        numQFormulasInt = selectRandValRange (r, minNumQFormulasInt,
	                                              maxNumQFormulasInt);
	        numQFormulasReal = selectRandValRange (r, minNumQFormulasReal,
	                                               maxNumQFormulasReal);
	        numQFormulasArray1 = selectRandValRange (r, minNumQFormulasArray1,
	                                                 maxNumQFormulasArray1);
	        numQFormulasArray2 = selectRandValRange (r, minNumQFormulasArray2,
	                                                 maxNumQFormulasArray2);
	        break;
	      case QF_ABV:
	      case QF_AUFBV:
	        assert (minNumVars > 0);
	        assert (maxNumVars > 0);
	        assert (minNumConsts > 0);
	        assert (maxNumConsts > 0);
	        assert (minNumArrays > 0);
	        assert (maxNumArrays > 0);
	        assert (minNumReads > 0);
	        assert (maxNumReads > 0);
	        assert (minNumWrites >= 0);
	        assert (maxNumWrites >= 0);
	        assert (minNumExtBool >= 0);
	        assert (maxNumExtBool >= 0);
	        assert (minBW > 0);
	        assert (maxBW > 0);
	        assert (minNumUFuncs >= 0);
	        assert (maxNumUFuncs >= 0);
	        assert (minNumUPreds >= 0);
	        assert (maxNumUPreds >= 0);
	        assert (minArgs > 0);
	        assert (maxArgs > 0);
	        checkMinMax (minNumVars, maxNumVars, "variables");
	        checkMinMax (minNumConsts, maxNumConsts, "constants");
	        checkMinMax (minNumArrays, maxNumArrays, "arrays");
	        checkMinMax (minNumReads, maxNumReads, "reads");
	        checkMinMax (minNumWrites, maxNumWrites, "writes");
	        checkMinMax (minNumExtBool, maxNumExtBool, "array equalities");
	        checkMinMax (minBW, maxBW, "bits");
	        checkMinMax (minNumUFuncs, maxNumUFuncs, "uninterpreted functions");
	        checkMinMax (minNumUPreds, maxNumUPreds, "uninterpreted predicates");
	        checkMinMax (minArgs, maxArgs, "arguments");
	        numVars = selectRandValRange (r, minNumVars, maxNumVars);
	        numConsts = selectRandValRange (r, minNumConsts, maxNumConsts);
	        numArrays = selectRandValRange (r, minNumArrays, maxNumArrays);
	        numReads = selectRandValRange (r, minNumReads, maxNumReads);
	        numWrites = selectRandValRange (r, minNumWrites, maxNumWrites);
	        numExtBool = selectRandValRange (r, minNumExtBool, maxNumExtBool);
	        numUFuncs = selectRandValRange (r, minNumUFuncs, maxNumUFuncs);
	        numUPreds = selectRandValRange (r, minNumUPreds, maxNumUPreds);
	        break;
	      case QF_UFBV:
	        assert (minNumUFuncs >= 0);
	        assert (maxNumUFuncs >= 0);
	        assert (minNumUPreds >= 0);
	        assert (maxNumUPreds >= 0);
	        assert (minArgs > 0);
	        assert (maxArgs > 0);
	        checkMinMax (minNumUFuncs, maxNumUFuncs, "uninterpreted functions");
	        checkMinMax (minNumUPreds, maxNumUPreds, "uninterpreted predicates");
	        checkMinMax (minArgs, maxArgs, "arguments");
	        numUFuncs = selectRandValRange (r, minNumUFuncs, maxNumUFuncs);
	        numUPreds = selectRandValRange (r, minNumUPreds, maxNumUPreds);
	        /* fall through by intention */
	      case QF_BV:
	        assert (minNumVars > 0);
	        assert (maxNumVars > 0);
	        assert (minNumConsts > 0);
	        assert (maxNumConsts > 0);
	        assert (minBW > 0);
	        assert (maxBW > 0);
	        checkMinMax (minNumVars, maxNumVars, "variables");
	        checkMinMax (minNumConsts, maxNumConsts, "constants");
	        numVars = selectRandValRange (r, minNumVars, maxNumVars);
	        numConsts = selectRandValRange (r, minNumConsts, maxNumConsts);
	        break;
	      case QF_LIA:
	      case QF_NIA:
	      case QF_UFLIA:
	      case QF_UFNIA:
	      case QF_LRA:
	      case LRA:
	      case QF_NRA:
	      case QF_UFLRA:
	      case QF_UFNRA:
	        assert (linear || logic != SMTLogic.QF_LIA);
	        assert (linear || logic != SMTLogic.QF_UFLIA);
	        assert (linear || logic != SMTLogic.QF_LRA);
	        assert (linear || logic != SMTLogic.QF_UFLRA);
	        assert (!linear || logic != SMTLogic.QF_NIA);
	        assert (!linear || logic != SMTLogic.QF_UFNIA);
	        assert (!linear || logic != SMTLogic.QF_NRA);
	        assert (!linear || logic != SMTLogic.QF_UFNRA);
	        /* fall through by intention */
	      case QF_IDL:
	      case QF_UFIDL:
	      case QF_RDL:
	      case QF_UFRDL:
	        assert (minNumVars > 0);
	        assert (maxNumVars > 0);
	        assert (minNumConsts > 0);
	        assert (maxNumConsts > 0);
	        assert (maxBW > 0);
	        checkMinMax (minNumVars, maxNumVars, "variables");
	        checkMinMax (minNumConsts, maxNumConsts, "constants");
	        numVars = selectRandValRange (r, minNumVars, maxNumVars);
	        numConsts = selectRandValRange (r, minNumConsts, maxNumConsts);
	        if (logic == SMTLogic.QF_UFIDL || logic == SMTLogic.QF_UFRDL ||
	            logic == SMTLogic.QF_UFLIA || logic == SMTLogic.QF_UFLRA ||
	            logic == SMTLogic.QF_UFNIA || logic == SMTLogic.QF_UFNRA) {
	          assert (minNumUFuncs >= 0);
	          assert (maxNumUFuncs >= 0);
	          assert (minNumUPreds >= 0);
	          assert (maxNumUPreds >= 0);
	          checkMinMax (minNumUFuncs, maxNumUFuncs, "uninterpreted functions");
	          checkMinMax (minNumUPreds, maxNumUPreds, "uninterpreted predicates");
	          checkMinMax (minArgs, maxArgs, "arguments");
	          numUFuncs = selectRandValRange (r, minNumUFuncs, maxNumUFuncs);
	          numUPreds = selectRandValRange (r, minNumUPreds, maxNumUPreds);
	        }
	        break;
	      case QF_UF:
	        assert (minNumVars > 0);
	        assert (maxNumVars > 0);
	        assert (minNumSorts > 0);
	        assert (maxNumSorts > 0);
	        assert (minNumUFuncs >= 0);
	        assert (minNumUPreds >= 0);
	        checkMinMax (minNumVars, maxNumVars, "variables");
	        checkMinMax (minNumSorts, maxNumSorts, "sorts");
	        checkMinMax (minArgs, maxArgs, "arguments");
	        numVars = selectRandValRange (r, minNumVars, maxNumVars);
	        numSorts = selectRandValRange (r, minNumSorts, maxNumSorts);
	        if (minNumUFuncs == 0)
	          printErrAndExit ("number of uninterpreted functions must be > 0");
	        if (minNumUPreds == 0)
	          printErrAndExit ("number of uninterpreted predicates must be > 0");
	        break;
	      case QF_A:
	      case QF_AX:
	        assert (minNumArrays > 0);
	        assert (maxNumArrays > 0);
	        assert (minNumIndices > 0);
	        assert (maxNumIndices > 0);
	        assert (minNumElements > 0);
	        assert (maxNumElements > 0);
	        assert (minNumReads > 0);
	        assert (maxNumReads > 0);
	        assert (minNumWrites >= 0);
	        assert (maxNumWrites >= 0);
	        checkMinMax (minNumArrays, maxNumArrays, "arrays");
	        checkMinMax (minNumIndices, maxNumIndices, "indices");
	        checkMinMax (minNumElements, maxNumElements, "elements");
	        checkMinMax (minNumReads, maxNumReads, "reads");
	        checkMinMax (minNumWrites, maxNumWrites, "writes");
	        numArrays = selectRandValRange (r, minNumArrays, maxNumArrays);
	        numIndices = selectRandValRange (r, minNumIndices, maxNumIndices);
	        numElements = selectRandValRange (r, minNumElements, maxNumElements);
	        numReads = selectRandValRange (r, minNumReads, maxNumReads);
	        numWrites = selectRandValRange (r, minNumWrites, maxNumWrites);
	        break;
	      case AUFLIA:
	        assert (minNumQFormulasInt >= 0);
	        assert (maxNumQFormulasInt >= 0);
	        assert (minNumQFormulasArray >= 0);
	        assert (maxNumQFormulasArray >= 0);
	        assert (minQVars > 0);
	        assert (maxQVars > 0);
	        assert (minQNestings >= 0);
	        assert (maxQNestings >= 0);
	        checkMinMax (minNumQFormulasInt, maxNumQFormulasInt,
	                     "quantified formulas over integers");
	        checkMinMax (minNumQFormulasArray, maxNumQFormulasArray,
	                     "quantified formulas over arrays");
	        numQFormulasInt = selectRandValRange (r, minNumQFormulasInt,
	                                              maxNumQFormulasInt);
	        numQFormulasArray = selectRandValRange (r, minNumQFormulasArray,
	                                                maxNumQFormulasArray);
	        /* fall through by intention */
	      case QF_AUFLIA:
	        assert (minNumVars > 0);
	        assert (maxNumVars > 0);
	        assert (minNumConsts > 0);
	        assert (maxNumConsts > 0);
	        assert (minNumArrays > 0);
	        assert (maxNumArrays > 0);
	        assert (minNumReads > 0);
	        assert (maxNumReads > 0);
	        assert (minNumWrites >= 0);
	        assert (maxNumWrites >= 0);
	        assert (minNumUFuncsInt >= 0);
	        assert (maxNumUFuncsInt >= 0);
	        assert (minNumUFuncsArray >= 0);
	        assert (maxNumUFuncsArray >= 0);
	        assert (minNumUPredsInt >= 0);
	        assert (maxNumUPredsInt >= 0);
	        assert (minNumUPredsArray >= 0);
	        assert (maxNumUPredsArray >= 0);
	        assert (minArgs > 0);
	        assert (maxArgs > 0);
	        assert (maxBW > 0);
	        assert (linear);
	        checkMinMax (minNumVars, maxNumVars, "variables");
	        checkMinMax (minNumConsts, maxNumConsts, "constants");
	        checkMinMax (minNumArrays, maxNumArrays, "arrays");
	        checkMinMax (minNumReads, maxNumReads, "reads");
	        checkMinMax (minNumWrites, maxNumWrites, "writes");
	        checkMinMax (minNumUFuncsInt, maxNumUFuncsInt, 
	                     "uninterpreted int functions");
	        checkMinMax (minNumUFuncsArray, maxNumUFuncsArray, 
	                     "uninterpreted array functions");
	        checkMinMax (minNumUPredsInt, maxNumUPredsInt, 
	                     "uninterpreted int predicates");
	        checkMinMax (minNumUPredsArray, maxNumUPredsArray, 
	                     "uninterpreted array predicates");
	        checkMinMax (minArgs, maxArgs, "arguments");
	        numVars = selectRandValRange (r, minNumVars, maxNumVars);
	        numConsts = selectRandValRange (r, minNumConsts, maxNumConsts);
	        numArrays = selectRandValRange (r, minNumArrays, maxNumArrays);
	        numReads = selectRandValRange (r, minNumReads, maxNumReads);
	        numWrites = selectRandValRange (r, minNumWrites, maxNumWrites);
	        numUFuncsInt = selectRandValRange (r, minNumUFuncsInt, maxNumUFuncsInt);
	        numUFuncsArray = selectRandValRange (r, minNumUFuncsArray, 
	                                             maxNumUFuncsArray);
	        numUPredsInt = selectRandValRange (r, minNumUPredsInt, maxNumUPredsInt);
	        numUPredsArray = selectRandValRange (r, minNumUPredsArray, 
	                                             maxNumUPredsArray);
	        break;
	    }
	    
	
	    boolNodes = new ArrayList<SMTNode>();
	    assert (r != null);
	    assert (logic != null);
	    if (smtlib1)
	    {
	    	output.println ("(benchmark fuzzsmt" + version);
	    	output.println (":logic " + logic.toString());
	    	output.println (":status unknown");
	    }
	    else
	    {
			output.println("(set-info :source | fuzzsmt "+ version +" |)");
			output.println("(set-logic  " + logic.toString() + ")");
			output.println("(set-info :status unknown)");
	    }
	    switch (logic) {
	      case QF_BV:
	      case QF_UFBV:{
	        ArrayList<SMTNode> bvNodes = new ArrayList<SMTNode>();
	        ArrayList<UFunc> uFuncs = new ArrayList<UFunc>();
	        ArrayList<UPred> uPreds = new ArrayList<UPred>();
	        BVDivGuards = new HashMap<SMTNode, SMTNodeKind>();
	        generateUFuncsBV (r, uFuncs, numUFuncs, minArgs, maxArgs, minBW, maxBW);
	        generateUPredsBV (r, uPreds, numUPreds, minArgs, maxArgs, minBW, maxBW);
	        generateBVVars (r, bvNodes, numVars, minBW, maxBW);
	       	output.println (startFormula());
	        
	        pars += generateBVConsts (r, bvNodes, numConsts, minBW, maxBW); 
	        pars += generateBVLayer (r, bvNodes, minRefs, minBW, maxBW, bvDivMode,
	                                 BVDivGuards, false, uFuncs, uPreds);
	        pars += generateBVPredicateLayer (r, bvNodes, boolNodes, minRefs,
	                                          uPreds);
	      }
	      break;
	      case QF_ABV:
	      case QF_AUFBV: {
	        int numExtBV = 0;
	        ArrayList<SMTNode> sorts = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> bvNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> arrayNodes = new ArrayList<SMTNode>();
	        ArrayList<UFunc> uFuncs = new ArrayList<UFunc>();
	        ArrayList<UPred> uPreds = new ArrayList<UPred>();
	        BVDivGuards = new HashMap<SMTNode, SMTNodeKind>();
	        generateUFuncsBV (r, uFuncs, numUFuncs, minArgs, maxArgs, minBW, maxBW);
	        generateUPredsBV (r, uPreds, numUPreds, minArgs, maxArgs, minBW, maxBW);
	        generateBVVars (r, bvNodes, numVars, minBW, maxBW);
	        generateBVArrayVars (r, arrayNodes, numArrays, minBW, maxBW);
	        output.println(startFormula());
	
	        /* half of extensional array equalities are encoded intot bit-vector, 
	         * the other half into the boolean part */
	        if (numExtBool > 0) {
	          numExtBV = (numExtBool >>> 1) + (numExtBool & 1);
	          numExtBool >>>= 1;
	        }
	
	        pars += generateBVConsts (r, bvNodes, numConsts, minBW, maxBW); 
	        pars += generateBVLayer (r, bvNodes, minRefs, minBW, maxBW, bvDivMode,
	                                 BVDivGuards, true, uFuncs, uPreds);
	        /* interleave creation of layers to ensure that
	         * numReads are also used as read indices, numWrites indices 
	         * and write values.
	         * Moreover, equalities between numArrays are encoded as bit-vectors
	         * and integrated into the bit-vector layer. Therefore, they
	         * may also contribute to read indices, write indices and write values.
	         */
	        while (numWrites > 0 || numReads > 0 || numExtBV > 0) {
	          pars += generateBVWriteLayer (r, arrayNodes, bvNodes, 
	                                        (numWrites >>> 1) + (numWrites & 1));
	          pars += generateBVArrayExtBVLayer (r, arrayNodes, bvNodes, 
	                                             (numExtBV >>> 1) + (numExtBV & 1));
	          pars += generateBVReadLayer (r, arrayNodes, bvNodes, 
	                                       (numReads >>> 1) + (numReads & 1));
	          numWrites >>>= 1;
	          numExtBV >>>= 1;
	          numReads >>>= 1;
	        }
	        assert (numWrites == 0);
	        assert (numReads == 0);
	        assert (numExtBV == 0);
	        /* create additional bit-vector layer on top to ensure
	         * that numReads and equalities between numArrays are also used as
	         * inputs for bit-vector operations.
	         */
	        pars += generateBVLayer (r, bvNodes, minRefs, minBW, maxBW, bvDivMode,
	                                 BVDivGuards, true, uFuncs, uPreds);
	        pars += generateBVPredicateLayer (r, bvNodes, boolNodes, minRefs,
	                                          uPreds);
	        pars += addArrayExt (r, arrayNodes, boolNodes, numExtBool);
	      }
	      break;
	      case QF_A: 
	      case QF_AX: {
	        int numWritesH, numReadsH;
	        SMTType indexType = new UType ("Index");
	        SMTType elementType = new UType ("Element");
	        SMTType arrayType = new ArrayTypeFromTo(indexType,elementType);
	        if (!smtlib1)
	        {
	        	output.println("(declare-sort Index 0)");
	        	output.println("(declare-sort Element 0)");
	        }
	        
	        ArrayList<SMTNode> arrays = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> indices = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> elements = new ArrayList<SMTNode>();
	        generateVarsOfOneType (arrays, numArrays, arrayType);
	        generateVarsOfOneType (indices, numIndices, indexType);
	        generateVarsOfOneType (elements, numElements, elementType);
	        output.println (startFormula());
	        numWritesH = (numWrites >>> 1) + (numWrites & 1);
	        numReadsH = (numReads >>> 1) + (numReads & 1);
	        numWrites >>>= 1;
	        numReads >>>= 1;
	        while (numWrites > 0 || numReads > 0) {
	          pars += generateWriteLayer (r, arrays, indices, elements, arrayType,
	                                      (numWrites >>> 1) + (numWrites & 1));
	          pars += generateReadLayer (r, arrays, indices, elements, elementType,
	                                     (numReads >>> 1) + (numReads & 1));
	          numWrites >>>= 1;
	          numReads >>>= 1;
	        }
	        if (logic == SMTLogic.QF_AX)
	          pars += generateComparisonLayer (r, arrays, boolNodes, null, minRefs,
	                                           RelCompMode.EQ, false);
	        pars += generateComparisonLayer (r, indices, boolNodes, null, minRefs, 
	                                         RelCompMode.EQ, false);
	        pars += generateComparisonLayer (r, elements, boolNodes, null, minRefs, 
	                                         RelCompMode.EQ, false);
	        /* generate ITE Layer */
	        pars += generateITELayer (r, arrays, boolNodes, minRefs);
	        pars += generateITELayer (r, indices, boolNodes, minRefs);
	        pars += generateITELayer (r, elements, boolNodes, minRefs);
	        /* generate second write and read layer */
	        while (numWritesH > 0 || numReadsH > 0) {
	          pars += generateWriteLayer (r, arrays, indices, elements, arrayType, 
	                                      (numWritesH >>> 1) + (numWritesH & 1));
	          pars += generateReadLayer (r, arrays, indices, elements, elementType,
	                                     (numReadsH >>> 1) + (numReadsH & 1));
	          numWritesH >>>= 1;
	          numReadsH >>>= 1;
	        }
	        if (logic == SMTLogic.QF_AX)
	          pars += generateComparisonLayer (r, arrays, boolNodes, null, minRefs, 
	                                           RelCompMode.EQ, false);
	        pars += generateComparisonLayer (r, indices, boolNodes, null, minRefs, 
	                                         RelCompMode.EQ, false);
	        pars += generateComparisonLayer (r, elements, boolNodes, null, minRefs, 
	                                         RelCompMode.EQ, false);
	      }
	      break;
	      case AUFLIA: 
	      case QF_AUFLIA: {
	        int numWritesH, numReadsH;
	        ArrayList<SMTType> sortsInt = new ArrayList<SMTType>();
	        ArrayList<SMTType> sortsArray = new ArrayList<SMTType>();
	        ArrayList<SMTNode> intNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConsts = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> arrays = new ArrayList<SMTNode>();
	        ArrayList<UFunc> uFuncsInt = new ArrayList<UFunc>();
	        ArrayList<UPred> uPredsInt = new ArrayList<UPred>();
	        ArrayList<UFunc> uFuncsArray = new ArrayList<UFunc>();
	        ArrayList<UPred> uPredsArray = new ArrayList<UPred>();
	
	        
	        SMTType arrayType = new ArrayTypeFromTo(IntType.intType, IntType.intType);
	        sortsInt.add (IntType.intType);
	        sortsArray.add (arrayType);
	
	        if (numUFuncsInt > 0)
	          generateUFuncs (r, sortsInt, uFuncsInt, numUFuncsInt, 
	                          minArgs, maxArgs);
	        if (numUFuncsArray > 0)
	          generateUFuncs (r, sortsArray, uFuncsArray, numUFuncsArray, 
	                          minArgs, maxArgs);
	 
	        if (numUPredsInt > 0)
	          generateUPreds (r, sortsInt, uPredsInt, numUPredsInt, 
	                          minArgs, maxArgs);
	        if (numUPredsArray > 0)
	          generateUPreds (r, sortsArray, uPredsArray, numUPredsArray, 
	                          minArgs, maxArgs);
	
	        generateIntVars (intNodes, numVars);
	        generateVarsOfOneType (arrays, numArrays, arrayType);
	        if (numQFormulasInt > 0 && (numUFuncsInt > 0 || numUPredsInt > 0))
	          generateQFormulasUF (r, IntType.intType, uFuncsInt, uPredsInt,
	                               numQFormulasInt, minQVars, maxQVars, 
	                               minQNestings, maxQNestings, false, minRefs);
	        if (numQFormulasArray > 0 && (numUFuncsArray > 0 || numUPredsArray > 0))
	          generateQFormulasUF (r, arrayType, uFuncsArray, 
	                               uPredsArray, numQFormulasArray, minQVars, 
	                               maxQVars, minQNestings, maxQNestings, true, 
	                               minRefs);
	        output.println (startFormula());
	
	        pars += generateIntConsts (r, intConsts, numConsts, maxBW);
	        numWritesH = (numWrites >>> 1) + (numWrites & 1);
	        numReadsH = (numReads >>> 1) + (numReads & 1);
	        numWrites >>>= 1;
	        numReads >>>= 1;
	        pars += generateIntLayer (r, intNodes, intConsts, uFuncsInt, uPredsInt,
	                                  true, minRefs, true);
	        while (numWrites > 0 | numReads > 0){
	          pars += generateWriteLayer (r, arrays, intNodes, intNodes, 
	                                      arrayType, 
	                                      (numWrites >>> 1) + (numWrites & 1));
	          pars += generateReadLayer (r, arrays, intNodes, intNodes,
	                                     IntType.intType, 
	                                     (numReads >>> 1) + (numReads & 1));
	          numWrites >>>= 1;
	          numReads >>>= 1;
	        }
	
	        if (numUFuncsArray > 0)
	          pars += generateUTermLayer (r, sortsArray, arrays, uFuncsArray, 
	                                      minRefs);
	        if (compModeArray == RelCompMode.EQ || numUPredsArray > 0)
	          pars += generateComparisonLayer (r, arrays, boolNodes, uPredsArray, 
	                                           minRefs, compModeArray, true);
	        pars += generateComparisonLayer (r, intNodes, boolNodes, uPredsInt, 
	                                         minRefs, RelCompMode.FULL, true);
	        pars += generateITELayer (r, arrays, boolNodes, minRefs);
	        pars += generateITELayer (r, intNodes, boolNodes, minRefs);
	        /* generate second write and read layer */
	        while (numWritesH > 0 || numReadsH > 0) {
	          pars += generateWriteLayer (r, arrays, intNodes, intNodes,
	        		  						arrayType, 
	                                      (numWritesH >>> 1) + (numWritesH & 1));
	          pars += generateReadLayer (r, arrays, intNodes, intNodes,
	                                     IntType.intType, 
	                                     (numReadsH >>> 1) + (numReadsH & 1));
	          numWritesH >>>= 1;
	          numReadsH >>>= 1;
	        }
	
	        if (numUFuncsArray > 0)
	          pars += generateUTermLayer (r, sortsArray, arrays, uFuncsArray, 
	                                      minRefs);
	        pars += generateIntLayer (r, intNodes, intConsts, uFuncsInt, uPredsInt,
	                                  true, minRefs, true);
	        if (compModeArray == RelCompMode.EQ || numUPredsArray > 0)
	          pars += generateComparisonLayer (r, arrays, boolNodes, uPredsArray, 
	                                           minRefs, compModeArray, true);
	        pars += generateComparisonLayer (r, intNodes, boolNodes, uPredsInt, 
	                                         minRefs, RelCompMode.FULL, true);
	      }
	      break;
	      case AUFLIRA:
	      case AUFNIRA: {
	        int numWritesArray1H, numWritesArray2H; 
	        int numReadsArray1H, numReadsArray2H;
	        HashSet<SMTNode> zeroConsts = new HashSet<SMTNode>();
	        ArrayList<SMTType> sortsInt = new ArrayList<SMTType>();
	        ArrayList<SMTType> sortsReal = new ArrayList<SMTType>();
	        ArrayList<SMTType> sortsArray1 = new ArrayList<SMTType>();
	        ArrayList<SMTType> sortsArray2 = new ArrayList<SMTType>();
	        ArrayList<SMTNode> intNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> realNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConsts = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConstsAsReal = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> arrays1 = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> arrays2 = new ArrayList<SMTNode>();
	        ArrayList<UFunc> uFuncsInt = new ArrayList<UFunc>();
	        ArrayList<UPred> uPredsInt = new ArrayList<UPred>();
	        ArrayList<UFunc> uFuncsReal = new ArrayList<UFunc>();
	        ArrayList<UPred> uPredsReal = new ArrayList<UPred>();
	        ArrayList<UFunc> uFuncsArray1 = new ArrayList<UFunc>();
	        ArrayList<UPred> uPredsArray1 = new ArrayList<UPred>();
	        ArrayList<UFunc> uFuncsArray2 = new ArrayList<UFunc>();
	        ArrayList<UPred> uPredsArray2 = new ArrayList<UPred>();
	
	        sortsInt.add (IntType.intType);
	        sortsReal.add (RealType.realType);
	        sortsArray1.add (Array1Type.array1Type);
	        sortsArray2.add (Array2Type.array2Type);
	
	        if (numUFuncsInt > 0)
	          generateUFuncs (r, sortsInt, uFuncsInt, numUFuncsInt, 
	                          minArgs, maxArgs);
	        if (numUFuncsReal > 0)
	          generateUFuncs (r, sortsReal, uFuncsReal, numUFuncsReal, 
	                          minArgs, maxArgs);
	        if (numUFuncsArray1 > 0)
	          generateUFuncs (r, sortsArray1, uFuncsArray1, numUFuncsArray1, 
	                          minArgs, maxArgs);
	        if (numUFuncsArray2 > 0)
	          generateUFuncs (r, sortsArray2, uFuncsArray2, numUFuncsArray2, 
	                          minArgs, maxArgs);
	 
	        if (numUPredsInt > 0)
	          generateUPreds (r, sortsInt, uPredsInt, numUPredsInt, 
	                          minArgs, maxArgs);
	        if (numUPredsReal > 0)
	          generateUPreds (r, sortsReal, uPredsReal, numUPredsReal, 
	                          minArgs, maxArgs);
	        if (numUPredsArray1 > 0)
	          generateUPreds (r, sortsArray1, uPredsArray1, numUPredsArray1, 
	                          minArgs, maxArgs);
	        if (numUPredsArray2 > 0)
	          generateUPreds (r, sortsArray2, uPredsArray2, numUPredsArray2, 
	                          minArgs, maxArgs);
	
	        generateIntVars (intNodes, numVarsInt);
	        generateRealVars (realNodes, numVarsReal);
	        generateVarsOfOneType (arrays1, numArrays1, Array1Type.array1Type);
	        generateVarsOfOneType (arrays2, numArrays2, Array2Type.array2Type);
	
	        if (numQFormulasInt > 0 && (numUFuncsInt > 0 || numUPredsInt > 0))
	          generateQFormulasUF (r, IntType.intType, uFuncsInt, uPredsInt,
	                               numQFormulasInt, minQVars, maxQVars, 
	                               minQNestings, maxQNestings, false, minRefs);
	        if (numQFormulasReal > 0 && (numUFuncsReal > 0 || numUPredsReal > 0))
	          generateQFormulasUF (r, RealType.realType, uFuncsReal, uPredsReal,
	                               numQFormulasReal, minQVars, maxQVars, 
	                               minQNestings, maxQNestings, false, minRefs);
	        if (numQFormulasArray1 > 0 
	            && (numUFuncsArray1 > 0 || numUPredsArray1 > 0))
	          generateQFormulasUF (r, Array1Type.array1Type, uFuncsArray1, 
	                               uPredsArray1, numQFormulasArray1, minQVars, 
	                               maxQVars, minQNestings, maxQNestings, true, 
	                               minRefs);
	        if (numQFormulasArray2 > 0 
	            && (numUFuncsArray2 > 0 || numUPredsArray2 > 0))
	          generateQFormulasUF (r, Array2Type.array2Type, uFuncsArray2, 
	                               uPredsArray2, numQFormulasArray2, minQVars, 
	                               maxQVars, minQNestings, maxQNestings, true, 
	                               minRefs);
	        output.println (startFormula());
	
	        pars += generateIntConsts (r, intConsts, numConstsInt, maxBW);
	        pars += generateRealConstsNotFilledZero (r, intConstsAsReal, zeroConsts,
	                                                 numConstsIntAsReal, maxBW, 
	                                                 true);
	        pars += generateIntLayer (r, intNodes, intConsts, uFuncsInt, uPredsInt,
	                                  true, minRefs, true);
	        pars += generateRealLayer (r, realNodes, intConstsAsReal, zeroConsts, 
	                                   uFuncsReal, uPredsReal, linear, true, 
	                                   minRefs, false);
	
	        numWritesArray1H = (numWritesArray1 >>> 1) + (numWritesArray1 & 1);
	        numReadsArray1H = (numReadsArray1 >>> 1) + (numReadsArray1 & 1);
	        numWritesArray1 >>>= 1;
	        numReadsArray1 >>>= 1;
	        numWritesArray2H = (numWritesArray2 >>> 1) + (numWritesArray2 & 1);
	        numReadsArray2H = (numReadsArray2 >>> 1) + (numReadsArray2 & 1);
	        numWritesArray2 >>>= 1;
	        numReadsArray2 >>>= 1;
	        /* interleave both array phases */
	        while (numWritesArray1 > 0 || numReadsArray1 > 0 ||
	               numWritesArray2 > 0 || numReadsArray2 > 0){
	          pars += generateWriteLayer (r, arrays1, intNodes, realNodes, 
	                                      Array1Type.array1Type, 
	                                      (numWritesArray1 >>> 1) + 
	                                      (numWritesArray1 & 1));
	          pars += generateReadLayer (r, arrays1, intNodes, realNodes,
	                                     RealType.realType, 
	                                     (numReadsArray1 >>> 1) + 
	                                     (numReadsArray1 & 1));
	          pars += generateWriteLayer (r, arrays2, intNodes, arrays1, 
	                                      Array2Type.array2Type, 
	                                      (numWritesArray2 >>> 1) + 
	                                      (numWritesArray2 & 1));
	          pars += generateReadLayer (r, arrays2, intNodes, arrays1,
	                                     Array1Type.array1Type,
	                                     (numReadsArray2 >>> 1) + 
	                                     (numReadsArray2 & 1));
	          numWritesArray1 >>>= 1;
	          numReadsArray1 >>>= 1;
	          numWritesArray2 >>>= 1;
	          numReadsArray2 >>>= 1;
	
	        }
	
	        if (numUFuncsArray1 > 0)
	          pars += generateUTermLayer (r, sortsArray1, arrays1, uFuncsArray1, 
	                                      minRefs);
	        if (numUFuncsArray2 > 0)
	          pars += generateUTermLayer (r, sortsArray2, arrays2, uFuncsArray2, 
	                                      minRefs);
	        if (compModeArray1 == RelCompMode.EQ || numUPredsArray1 > 0)
	          pars += generateComparisonLayer (r, arrays1, boolNodes, uPredsArray1, 
	                                           minRefs, compModeArray1, true);
	        if (compModeArray2 == RelCompMode.EQ || numUPredsArray2 > 0)
	          pars += generateComparisonLayer (r, arrays2, boolNodes, uPredsArray2, 
	                                           minRefs, compModeArray2, true);
	        pars += generateComparisonLayer (r, intNodes, boolNodes, uPredsInt, 
	                                         minRefs, RelCompMode.FULL, true);
	        pars += generateComparisonLayer (r, realNodes, boolNodes, uPredsReal, 
	                                         minRefs, RelCompMode.FULL, true);
	        pars += generateITELayer (r, arrays1, boolNodes, minRefs);
	        pars += generateITELayer (r, arrays2, boolNodes, minRefs);
	        
	        pars += generateITELayer (r, intNodes, boolNodes, minRefs);
	        pars += generateITELayer (r, realNodes, boolNodes, minRefs);
	        /* generate second write and read phase */
	        while (numWritesArray1H > 0 || numReadsArray1H > 0 ||
	               numWritesArray2H > 0 || numReadsArray2H > 0) {
	          pars += generateWriteLayer (r, arrays1, intNodes, realNodes,
	                                      Array1Type.array1Type, 
	                                      (numWritesArray1H >>> 1) + 
	                                      (numWritesArray1H & 1));
	          pars += generateReadLayer (r, arrays1, intNodes, realNodes,
	                                     RealType.realType, 
	                                     (numReadsArray1H >>> 1) + 
	                                     (numReadsArray1H & 1));
	          pars += generateWriteLayer (r, arrays2, intNodes, arrays1,
	                                      Array2Type.array2Type, 
	                                      (numWritesArray2H >>> 1) + 
	                                      (numWritesArray2H & 1));
	          pars += generateReadLayer (r, arrays2, intNodes, arrays1,
	                                     Array1Type.array1Type, 
	                                     (numReadsArray2H >>> 1) + 
	                                     (numReadsArray2H & 1));
	          numWritesArray1H >>>= 1;
	          numReadsArray1H >>>= 1;
	          numWritesArray2H >>>= 1;
	          numReadsArray2H >>>= 1;
	        }
	
	        if (numUFuncsArray1 > 0)
	          pars += generateUTermLayer (r, sortsArray1, arrays1, uFuncsArray1, 
	                                      minRefs);
	        if (numUFuncsArray2 > 0)
	          pars += generateUTermLayer (r, sortsArray2, arrays2, uFuncsArray2, 
	                                      minRefs);
	        pars += generateIntLayer (r, intNodes, intConsts, uFuncsInt, uPredsInt,
	                                  true, minRefs, true);
	        if (compModeArray1 == RelCompMode.EQ || numUPredsArray1 > 0)
	          pars += generateComparisonLayer (r, arrays1, boolNodes, uPredsArray1, 
	                                           minRefs, compModeArray1, true);
	        if (compModeArray2 == RelCompMode.EQ || numUPredsArray2 > 0)
	          pars += generateComparisonLayer (r, arrays2, boolNodes, uPredsArray2, 
	                                           minRefs, compModeArray2, true);
	        pars += generateComparisonLayer (r, intNodes, boolNodes, uPredsInt, 
	                                         minRefs, RelCompMode.FULL, true);
	        pars += generateComparisonLayer (r, realNodes, boolNodes, uPredsReal, 
	                                         minRefs, RelCompMode.FULL, true);
	      }
	      break;
	
	      case QF_IDL: {
	        ArrayList<SMTNode> intNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConsts = new ArrayList<SMTNode>();
	        generateIntVars (intNodes, numVars);
	        output.println (startFormula());
	        pars += generateIntConsts (r, intConsts, numConsts, maxBW);
	        pars += generateIDLLayer (r, intNodes, intConsts, boolNodes, minRefs);
	      }
	      break;
	      case QF_UFIDL: {
	        ArrayList<SMTType> sortsInt = new ArrayList<SMTType>();
	        ArrayList<SMTNode> intNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConsts = new ArrayList<SMTNode>();
	        ArrayList<UFunc> uFuncs = new ArrayList<UFunc>();
	        ArrayList<UPred> uPreds = new ArrayList<UPred>();
	
	        sortsInt.add (IntType.intType);
	
	        generateIntVars (intNodes, numVars);
	        if (numUFuncs > 0)
	          generateUFuncs (r, sortsInt, uFuncs, numUFuncs, minArgs, maxArgs);
	        if (numUPreds > 0)
	          generateUPreds (r, sortsInt, uPreds, numUPreds, minArgs, maxArgs);
	        output.println (startFormula());
	        pars += generateIntConsts (r, intConsts, numConsts, maxBW);
	        pars += generateIDLLayer (r, intNodes, intConsts, boolNodes, minRefs);
	        if (numUFuncs > 0)
	          pars += generateUTermLayer (r, sortsInt, intNodes, uFuncs, minRefs);
	        if (numUPreds > 0) 
	          pars += generateUPredLayer (r, intNodes, boolNodes, uPreds, minRefs);
	        pars += generateComparisonLayer (r, intNodes, boolNodes, uPreds, 
	                                         minRefs, RelCompMode.FULL, true);
	      }
	      break;
	      case QF_RDL: {
	        ArrayList<SMTNode> realVars = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConsts = new ArrayList<SMTNode>();
	        HashSet<SMTNode> zeroConsts = new HashSet<SMTNode>();
	        generateRealVars (realVars, numVars);
	        output.println (startFormula());
	        pars += generateIntConstsNotFilledZero (r, intConsts, zeroConsts, 
	                                                numConsts, maxBW);
	        pars += generateRDLLayer (r, realVars, intConsts, zeroConsts, 
	                                  boolNodes, minRefs, maxBW);
	      }
	      break;
	      case QF_UFRDL: {
	        ArrayList<SMTType> sortsReal = new ArrayList<SMTType>();
	        ArrayList<SMTNode> realNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConsts = new ArrayList<SMTNode>();
	        HashSet<SMTNode> zeroConsts = new HashSet<SMTNode>();
	        ArrayList<UFunc> uFuncs = new ArrayList<UFunc>();
	        ArrayList<UPred> uPreds = new ArrayList<UPred>();
	
	        sortsReal.add (RealType.realType);
	
	        generateRealVars (realNodes, numVars);
	        if (numUFuncs > 0)
	          generateUFuncs (r, sortsReal, uFuncs, numUFuncs, minArgs, maxArgs);
	        if (numUPreds > 0)
	          generateUPreds (r, sortsReal, uPreds, numUPreds, minArgs, maxArgs);
	        output.println (startFormula());
	        pars += generateIntConstsNotFilledZero (r, intConsts, zeroConsts, 
	                                                numConsts, maxBW);
	        pars += generateRDLLayer (r, realNodes, intConsts, zeroConsts, 
	                                  boolNodes, minRefs, maxBW);
	        if (numUFuncs > 0)
	          pars += generateUTermLayer (r, sortsReal, realNodes, uFuncs, minRefs);
	        if (numUPreds > 0) 
	          pars += generateUPredLayer (r, realNodes, boolNodes, uPreds, minRefs);
	        pars += generateComparisonLayer (r, realNodes, boolNodes, uPreds, 
	                                         minRefs, RelCompMode.FULL, true);
	      }
	      break;
	      case QF_LIA:
	      case QF_NIA:
	      case QF_UFLIA:
	      case QF_UFNIA: {
	        ArrayList<SMTType> sorts = new ArrayList<SMTType>();
	        ArrayList<SMTNode> intNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConsts = new ArrayList<SMTNode>();
	        ArrayList<UFunc> uFuncs = new ArrayList<UFunc>();
	        ArrayList<UPred> uPreds = new ArrayList<UPred>();
	
	        sorts.add (IntType.intType);
	
	        if (numUFuncs > 0)
	          generateUFuncs (r, sorts, uFuncs, numUFuncs, minArgs, maxArgs);
	        if (numUPreds > 0)
	          generateUPreds (r, sorts, uPreds, numUPreds, minArgs, maxArgs);
	
	        generateIntVars (intNodes, numVars);
	        output.println (startFormula());
	        pars += generateIntConsts (r, intConsts, numConsts, maxBW);
	        pars += generateIntLayer (r, intNodes, intConsts, uFuncs, uPreds,
	                                  linear, minRefs, false);
	        pars += generateComparisonLayer (r, intNodes, boolNodes, uPreds, 
	                                         minRefs, RelCompMode.FULL, false);
	        pars += generateITELayer (r, intNodes, boolNodes, minRefs);
	        pars += generateComparisonLayer (r, intNodes, boolNodes, uPreds, 
	                                         minRefs, RelCompMode.FULL, false);
	      }
	      break;
	
	
	      case LRA:
	      case QF_LRA:
	      case QF_NRA:
	      case QF_UFLRA:
	      case QF_UFNRA: {
	        ArrayList<SMTType> sorts = new ArrayList<SMTType>();
	        ArrayList<SMTNode> realNodes = new ArrayList<SMTNode>();
	        ArrayList<SMTNode> intConstsAsReal = new ArrayList<SMTNode>();
	        HashSet<SMTNode> zeroConsts = new HashSet<SMTNode>();
	        ArrayList<UFunc> uFuncs = new ArrayList<UFunc>();
	        ArrayList<UPred> uPreds = new ArrayList<UPred>();
	
	        sorts.add (RealType.realType);
	
	        if (numUFuncs > 0)
	          generateUFuncs (r, sorts, uFuncs, numUFuncs, minArgs, maxArgs);
	        if (numUPreds > 0)
	          generateUPreds (r, sorts, uPreds, numUPreds, minArgs, maxArgs);
	
	        generateRealVars (realNodes, numVars);
	        output.println (startFormula());
	        pars += generateRealConstsNotFilledZero (r, intConstsAsReal, zeroConsts,
	                                                 numConsts, maxBW, false);
	        pars += generateRealLayer (r, realNodes, intConstsAsReal, zeroConsts, 
	                                   uFuncs, uPreds, linear, false, minRefs, 
	                                   false);
	        pars += generateComparisonLayer (r, realNodes, boolNodes, uPreds,
	                                         minRefs, RelCompMode.FULL, false);
	        pars += generateITELayer (r, realNodes, boolNodes, minRefs);
	        pars += generateComparisonLayer (r, realNodes, boolNodes, uPreds, 
	                                         minRefs, RelCompMode.FULL, false);
	      }
	      break;
	      case QF_UF: {
	        ArrayList<SMTType> sorts = new ArrayList<SMTType>();
	        ArrayList<UFunc> uFuncs = new ArrayList<UFunc>();
	        ArrayList<UPred> uPreds = new ArrayList<UPred>();
	        ArrayList<SMTNode> nodes = new ArrayList<SMTNode>();
	        generateUTypes (sorts, numSorts);
	        generateUVars  (sorts, nodes, numVars);
	        generateUFuncs (r, sorts, uFuncs, minNumUFuncs, minArgs, maxArgs);
	        generateUPreds (r, sorts, uPreds, minNumUPreds, minArgs, maxArgs);
	        output.println (startFormula());
	        pars += generateUTermLayer (r, sorts, nodes, uFuncs, minRefs);
	        pars += generateUPredLayer (r, nodes, boolNodes, uPreds, minRefs);
	        pars += generateITELayer (r, nodes, boolNodes, 1); 
	        pars += generateUPredLayer (r, nodes, boolNodes, uPreds, minRefs);
	      }
	      break;
	    }
	
	    /* generate boolean layer */
	    assert (boolNodes.size() > 0);
	    switch (booleanLayerKind) {
	      case RANDOM:
	        pars += generateBooleanLayer (r, boolNodes);
	        break;
	      case AND:
	        pars += generateBooleanTopAnd (boolNodes);
	        break;
	      case OR:
	        pars += generateBooleanTopOr (boolNodes);
	        break;
	      case CNF:
	        pars += generateBooleanCNF (r, boolNodes, factor);
	        break;
	    }
	    assert (boolNodes.size() == 1);
	    assert (boolNodes.get(0).getType() == BoolType.boolType);
	    if (bvDivMode == BVDivMode.GUARD && 
	        (logic == SMTLogic.QF_ABV || logic == SMTLogic.QF_BV || logic == SMTLogic.QF_AUFBV)){
	      assert (BVDivGuards != null);
	      pars += addBVDivGuards (boolNodes, BVDivGuards);
	      assert (boolNodes.size() == 1);
	      assert (boolNodes.get(0).getType() == BoolType.boolType);
	    }
	    output.println (boolNodes.get(0).getName());
	   
	    builder = new StringBuilder (pars);
	    for (int i = 0; i < pars; i++)
	      builder.append (")");
	    builder.append ("\n");
	    output.print(builder.toString());
	    if (smtlib1)
	    	output.println("");
	    else
	    	output.println("(check-sat)");
	 
    }
    output.close();
    System.exit (0);
    }

}

