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

public class BVType extends SMTType 
{

  protected String smtlib1_name;
  protected String smtlib2_name;

  protected int width;

  public BVType (int width){
    assert (width > 0);
    this.width = width;
    this.smtlib1_name = "BitVec["+ width + "]";
    this.smtlib2_name = "(_ BitVec "+ width + ")";
  }

  public String toString (boolean smtlib1){
    if (smtlib1)
	  return this.smtlib1_name;
    else
    	return this.smtlib2_name;
  }

  public int getWidth(){
    return this.width;
  }

  public boolean equals (Object o){
    assert (o != null);

    if (! (o instanceof BVType))
      return false;

    return this.width == ((BVType) o).width;
  }

}
