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

public enum SMTLogic
{
  QF_A,
  QF_AX,
  QF_BV,
  QF_ABV,
  QF_AUFBV,
  QF_AUFLIA,
  QF_IDL,
  QF_LIA,
  QF_LRA,
  QF_NIA,
  QF_NRA,
  QF_RDL,
  QF_UF,
  QF_UFBV,
  QF_UFIDL,
  QF_UFLIA,
  QF_UFLRA,
  QF_UFNIA,
  QF_UFNRA,
  QF_UFRDL,
  AUFLIA,
  AUFLIRA,
  LRA,
  AUFNIRA;
  
  public final static HashMap<String, SMTLogic> stringToLogic;

  static {
    EnumSet<SMTLogic> set = EnumSet.range (QF_A, AUFNIRA);
    stringToLogic = new HashMap<String, SMTLogic>(AUFNIRA.ordinal());
    for (SMTLogic logic : set)
      stringToLogic.put (logic.toString(), logic);
  }

}
