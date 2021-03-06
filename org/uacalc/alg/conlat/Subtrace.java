/* Subtrace.java 2001/06/04 Ralph Freese */

package org.uacalc.alg.conlat;

import org.uacalc.util.IntArray;


import java.util.*;

/**
 * A class to hold a subtrace {a, b} and its TCT type.
 *
 * @author Ralph Freese
 * @version $Id$
 */
public class Subtrace {

  private int a;
  private int b;
  private int type = -1;
  private boolean hasInvolution;
  
  /**
   * This is the subuniverse of A^2
   * generated by the diagonal and a single pair (a,b), 
   * where {a,b} is a trace.
   */
  private List<IntArray> subtraceUniverse;
  
  /**
   * This is part of the subuniverse of A^4
   * generated by the diagonal and two 4-tuples,
   * (a,a,b,b) and (a,b,a,b), 
   * where {a,b} is a trace. Only if the type is 1, 2, or 5 
   * is this guaranteed to be the whole subuniverse. 
   */
  private List<IntArray> matrixUniverse;
  
  

  Subtrace(int a, int b, boolean inv) {
    this.a = a;
    this.b = b;
    hasInvolution = inv;
  }

  Subtrace(int a, int b, boolean inv, int type) {
    this.a = a;
    this.b = b;
    hasInvolution = inv;
    this.type = type;
  }

  public int first() { return a; }
  public int second() { return b; }
  public int type() { return type; }
  public boolean hasInvolution() { return hasInvolution; }
  
  public List<IntArray> getSubtraceUniverse() { return subtraceUniverse; }
  public void setSubtraceUniverse(List<IntArray> univ) { subtraceUniverse = univ; }
  
  /**
   * This is part of the subuniverse of A^4
   * generated by the diagonal and two 4-tuples,
   * (a,a,b,b) and (a,b,a,b), 
   * where {a,b} is a trace. Only if the type is 1, 2, or 5 
   * is this guaranteed to be the whole subuniverse. 
   */
  public List<IntArray> getMatrixUniverse() { return matrixUniverse; }
  public void setMatrixUniverse(List<IntArray> univ) { matrixUniverse = univ; }

  public void setType(int t) { this.type = t; }
  
  public String toString(boolean brief) {
    if (!brief) return toString();
    return "[" + a + ", " + b + "]";
  }

  public String toString() {
    return "subtrace [" + a + ", " + b + "] typ = " + type 
                      + " inv: " + hasInvolution;
  }


}

