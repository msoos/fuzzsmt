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

public class UPred {

  protected static int predsCtr = 0;

  protected String name;

  protected Signature sig;


  public UPred (String name, Signature sig){
    assert (name != null);
    assert (sig != null);
    assert (sig.getResultType() == BoolType.boolType);
    this.name = name;
    this.sig = sig;
    predsCtr++;
  }

  public String getName() {
    return this.name;
  }

  public Signature getSignature() {
    return this.sig;
  }

  public static int getPredsCtr() {
    return predsCtr;
  }

}
