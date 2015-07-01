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

public class SMTNode
{

  protected static int nodeCtr = 0;


  protected SMTType type;

  protected String name; 


  public SMTNode (SMTType type, String name){
    assert (type != null);
    assert (name != null);

    this.type = type;
    this.name = name;
    nodeCtr++;
  }

  public SMTType getType(){
    return this.type;
  }

  public String getName (){
    return this.name;
  }

  public static int getNodeCtr (){
    return nodeCtr;
  }

}
