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

public class BVArrayType extends ArrayType 
{

  protected String smtlib1_name;
  protected String smtlib2_name;
  
  protected int indexWidth;

  protected int valWidth;

  public BVArrayType (int indexWidth, int valWidth){
    StringBuilder builder;

    assert (indexWidth > 0);
    assert (valWidth > 0);

    this.indexWidth = indexWidth;
    this.valWidth = valWidth;
    builder = new StringBuilder();
    builder.append ("Array[");
    builder.append (indexWidth);
    builder.append (":");
    builder.append (valWidth);
    builder.append ("]");
    this.smtlib1_name = builder.toString();
    
    builder.setLength(0);
    builder.append("(_ BitVec "+ indexWidth +" ) (_ BitVec " + valWidth + " )");
    this.smtlib2_name = builder.toString();
  }

  public String toString (boolean smtlib1){
	  if (smtlib1)
		  return this.smtlib1_name;
	  else
		  return this.smtlib2_name;
  }

  public int getIndexWidth(){
    return this.indexWidth;
  }

  public int getValWidth(){
    return this.valWidth;
  }

  public boolean equals (Object o){
    BVArrayType type;
    assert (o != null);

    if (! (o instanceof BVArrayType))
      return false;

    type = (BVArrayType) o;

    return this.indexWidth == type.indexWidth &&
           this.valWidth == type.valWidth;
  }

}
