/* Algebras.java 2001/09/02  */

package org.uacalc.alg;

import java.util.*;
import org.uacalc.util.*;
import org.uacalc.alg.op.Operation;
import org.uacalc.alg.op.OperationSymbol;
import org.uacalc.alg.op.Operations;
import org.uacalc.alg.op.SimilarityType;
import org.uacalc.terms.*;
import org.uacalc.alg.conlat.*;
//import org.apache.log4j.*;
import java.util.logging.*;

/**
 * A class with static methods for algebras.
 *
 *
 *
 */
public class Algebras {

  static Logger logger = Logger.getLogger("org.uacalc.alg.Algebras");
  static {
    logger.setLevel(Level.FINER);
    //BasicConfigurator.configure();
  }

  // make sure the class cannot be instantiated.
  private Algebras() {}

  /**
   * WARNING: this is not complete. Make an algebra from the unary operations respecting a list pars
   * of partitions.
   * 
   * @param pars      a list of partitions
   * @param decomp    a sublist whose meet is 0
   * @return          the algebra
   */
  public static SmallAlgebra unaryCloneAlgFromPartitions(List<Partition> pars, List<Partition> decomp) {
    final int size = pars.get(0).universeSize();
    final int k = decomp.size();
    final int[] sizes = new int[k];
    int index = 0;
    for (Partition par : decomp) {
      sizes[index++] = par.representatives().length;
    }
    Map<Integer,IntArray> int2vec = new TreeMap<Integer,IntArray>();
    Map<IntArray,Integer> vec2int = new TreeMap<IntArray,Integer>();
    for (int i = 0; i < size; i++) {
      final int[] vec = new int[k];
      for (int j = 0; j < k; j++) {
        vec[j] = decomp.get(j).representative(i);
      }
      final IntArray ia = new IntArray(vec);
      int2vec.put(i, ia);
      vec2int.put(ia, i);
    }
    // here
    return null;
  }
  
  /**
   * Make the unary algebra whose operations are the clone of unary
   * operation respecting every partition in pars and also eta0 and
   * eta1, which meet and join to 0 and 1 and permute. 
   *  
   * @param pars
   * @param eta0
   * @param eta1
   * @return
   */
  public static SmallAlgebra unaryCloneAlgFromPartitions(List<Partition> pars, Partition eta0, Partition eta1) {
    final int size = pars.get(0).universeSize();
    Map<Integer,IntArray> int2vec = new TreeMap<Integer,IntArray>();
    Map<IntArray,Integer> vec2int = new TreeMap<IntArray,Integer>();
    for (int i = 0; i < size; i++) {
      final int[] vec = new int[2];
      vec[0] = eta0.representative(i);
      vec[1] = eta1.representative(i);
      final IntArray ia = new IntArray(vec);
      int2vec.put(i, ia);
      vec2int.put(ia, i);
    }
    return null;
  }
  
  public static List<IntArray> unaryClone(final List<Partition> pars, 
                                                   final Partition eta0, final Partition eta1) {
    final int size = pars.get(0).universeSize();
    Map<Integer,IntArray> int2vec = new TreeMap<Integer,IntArray>();
    Map<IntArray,Integer> vec2int = new TreeMap<IntArray,Integer>();
    for (int i = 0; i < size; i++) {
      final int[] vec = new int[2];
      vec[0] = eta0.representative(i);
      vec[1] = eta1.representative(i);
      final IntArray ia = new IntArray(vec);
      int2vec.put(i, ia);
      vec2int.put(ia, i);
    }
    final int size0 = eta0.numberOfBlocks();
    final int size1 = eta1.numberOfBlocks();
    final IntArray f0 = new IntArray(size0);
    final IntArray f1 = new IntArray(size1);
    final int n = eta0.universeSize();
    final List<IntArray> ans = new ArrayList<IntArray>();
    unaryCloneAux(f0, f1, size0, size1, 0, 0, n, true, ans, int2vec, vec2int, pars);
    return ans;
  }
  
  private static void unaryCloneAux(final IntArray f0, final IntArray f1,
                                                  final int size0, final int size1,
                                                  final int k0, final int k1, final int n,
                                                  final boolean zeroFirst,
                                                  //IntArray partialFn,
                                                  final List<IntArray> ans,
                                                  final Map<Integer,IntArray> int2vec,
                                                  final Map<IntArray,Integer> vec2int,
                                                  final List<Partition> pars) {
    //if (partialFn == null) {
    //  partialFn = new IntArray(n);
    //  for (int i = 0; i < n; i++) {
    //    partialFn.set(i, -1);
    //  }
    //}
    if (k0 * k1 == n) {
      IntArray copy = new IntArray(n);
      final IntArray scratch = new IntArray(2);
      for (int i = 0; i < n; i++) {
        final IntArray argv = int2vec.get(i);
        scratch.set(0, f0.get(argv.get(0)));
        scratch.set(1, f1.get(argv.get(1)));
        copy.set(i, vec2int.get(scratch));
      }
      ans.add(copy);
      //System.out.println(copy);
      return;
    }
    
    final int size = zeroFirst ? size0 : size1;
    //final int k = zeroFirst ? k0 : k1;
    //final int otherK = zeroFirst ? k1 : k0;
    for (int value = 0; value < size; value++) {
      if (respects(value, f0, f1, size0, size1, k0, k1, n, zeroFirst, int2vec, vec2int, pars)) {
        if (zeroFirst) f0.set(k0, value);
        else f1.set(k1, value);
        unaryCloneAux(f0, f1, size0, size1, k0, k1, n, !zeroFirst, ans, int2vec, vec2int, pars);
      }
      //if (respects(partialFunct, k, value, pars)) {
        //arr.set(k, value);
        //unaryCloneAux(arr, k + 1, n, ans, pars);
      //}
    }
    
    return;
  }
  
  private static boolean respects(final int value,
                                  final IntArray f0, final IntArray f1,
                                  final int size0, final int size1,
                                  final int k0, final int k1, final int n,
                                  final boolean zeroFirst,
                                  final Map<Integer,IntArray> int2vec,
                                  final Map<IntArray,Integer> vec2int,
                                  final List<Partition> pars) {
    final IntArray scratch = new IntArray(2);
    if (zeroFirst) {
      for (int j = 0; j < k1; j++) {
        final int m = getScratchValue(scratch, k0, j, vec2int);
        final int image = getScratchValue(scratch, value, f1.get(j), vec2int);
        for (int u = 0; u < k0; u++) {
          for (int v = 0; v < k1; v++) {
            final int uv = getScratchValue(scratch, u, v, vec2int);
            int uvImg = -1;
            for (Partition par : pars) {
              final int r = par.representative(m);
              if (r == par.representative(uv)) {
                if (uvImg == -1) uvImg = getScratchValue(scratch, f0.get(u), f1.get(v), vec2int);
                if (!par.isRelated(image, uvImg)) return false;
              }
            }
          }
        } 
      }
    }
    else {
      for (int i = 0; i < k1; i++) {
        final int m = getScratchValue(scratch, i, k1, vec2int);
        final int image = getScratchValue(scratch, f0.get(i), value, vec2int);
        for (int u = 0; u < k0; u++) {
          for (int v = 0; v < k1; v++) {
            final int uv = getScratchValue(scratch, u, v, vec2int);
            int uvImg = -1;
            for (Partition par : pars) {
              final int r = par.representative(m);
              if (r == par.representative(uv)) {
                if (uvImg == -1) uvImg = getScratchValue(scratch, f0.get(u), f1.get(v), vec2int);
                if (!par.isRelated(image, uvImg)) return false;
              }
            }
          }
        }
      }
    }
    return true;
  }

  private static int getScratchValue(final IntArray scratch, final int i, final int j, 
                                     final Map<IntArray,Integer> vec2int) {
    scratch.set(0, i);
    scratch.set(1, j);
    return vec2int.get(scratch);
  }
  
  
  /**
   * This will find a near unamimity term of the given arity
   * if one exits; otherwise it return <tt>null</tt>.
   */
  public static Term findNUF(SmallAlgebra alg, int arity) {
    return Malcev.findNUF(alg, arity);
  }

  /**
   * This returns a list of Jonsson terms witnessing or null if 
   * the algebra does generate a congruence distributive variety.
   * It is guarenteed to be the least number of terms possible.
   */
  public static List jonssonTerms(SmallAlgebra alg) {
    return Malcev.jonssonTerms(alg);
  }

  /**
   * If this algebra generates a distributive variety, this returns
   * the minimal number of Jonsson terms; otherwise it returns -1,
   * but it is probably better to <tt>jonssonTerms</tt> and get
   * get the actual terms.
   * So congruence distributivity can be tested by seeing if this 
   * this is positive. If the algebra has only one element, it returns 2.
   * For a lattice it returns 3. For Miklos Marioti's 5-ary near unanimity
   * operation on a 4 element set, it returns 7 (the maximum possible).
   */
  public static int jonssonLevel(SmallAlgebra alg) {
    return Malcev.jonssonLevel(alg);
  }

  public static boolean isEndomorphism(Operation endo, SmallAlgebra alg) {
    for (Iterator it = alg.operations().iterator(); it.hasNext(); ) {
      Operation op = (Operation)it.next();
      if (! Operations.commutes(endo, op)) {
        logger.finer(op + " failed to commute with " + endo);
        return false;
      }
    }
    return true;
  }
  
  public static boolean isHomomorphism(final int[] map, 
                                       final SmallAlgebra alg0, 
                                       final SmallAlgebra alg1) {
    for (Iterator it = alg0.operations().iterator(); it.hasNext(); ) {
      Operation op0 = (Operation)it.next();
      Operation op1 = alg1.getOperation(op0.symbol());
      if (! Operations.commutes(map, op0, op1)) {
        logger.finer(op0 + " failed to commute with " + map);
        return false;
      }
    }
    return true;
  }
  
  /**
   * The matrix power algebra as defined in Hobby-McKenzie.
   * 
   * @param alg
   * @param k
   * @return
   */
  public static SmallAlgebra matrixPower(final SmallAlgebra alg, final int k) {
    PowerAlgebra pow = new PowerAlgebra(alg, k);
    List<Operation> ops = pow.operations();
    ops.add(Operations.makeLeftShift(k, alg.cardinality()));
    ops.add(Operations.makeMatrixDiagonalOp(k, alg.cardinality()));
    return new BasicAlgebra("matrixPower", Operations.power(alg.cardinality(), k), ops);
  }
  
  public static SmallAlgebra fullTransformationSemigroup(final int n, boolean includeConstants, boolean includeId) {
    if (n > 9) throw new IllegalArgumentException("n can be at most 9");
    
    //System.out.println(Horner.horner(new int[] {1,0,0}, 3));
    
    int pow = n;
    for (int i = 1; i < n; i++) {
      pow = pow * n;
    }
    List<Operation> ops = new ArrayList<Operation>(4);
    ops.add(Operations.makeCompositionOp(n, pow));
    if (includeConstants) {
      for (int i = 0; i < n; i++) {
        final int[] ci = new int[n];
        for (int j = 0; j < n; j++) {
          ci[j] = i;
        }
        final int c = Horner.horner(ci, n);
        ops.add(Operations.makeConstantIntOperation(pow, c));
      }
    }
    if (includeId) {
      final int[] id = new int[n];
      for (int i = 0; i < n; i++) {
        id[i] = i;
      }
      final int idx = Horner.horner(id, n);
      ops.add(Operations.makeConstantIntOperation(pow, idx));
    }
    return new BasicAlgebra("Trans" + n, pow, ops);
  }

  /**
   * Make a random algebra of a given similarity type.
   */
  public static SmallAlgebra makeRandomAlgebra(int n, SimilarityType simType) {
    return makeRandomAlgebra(n, simType, -1);
  }

  /**
   * Make a random algebra of a given similarity type, optionally 
   * supplying a seed to the random number generator (in case
   * regenerating the same algebra is important.
   */
  public static SmallAlgebra makeRandomAlgebra(int n, 
                                      SimilarityType simType, long seed) {
    List ops = Operations.makeRandomOperations(n, simType, seed);
    // the second argument is the size of the algebra.
    return new BasicAlgebra("RAlg" + n, n, ops);
  }

  /**
   * Make a random algebra of a given the arities of the operations.
   */
  public static SmallAlgebra makeRandomAlgebra(int n, int[] arities) {
    return makeRandomAlgebra(n, arities, -1);
  }

  /**
   * Make a random algebra of a given the arities of the operations, 
   * optionally supplying a seed to the random number generator (in case
   * regenerating the same algebra is important.
   */
  public static SmallAlgebra makeRandomAlgebra(int n, 
                                               int[] arities, long seed) {
    final int len = arities.length;
    List<OperationSymbol> syms = new ArrayList<OperationSymbol>(len);
    for (int i = 0; i < len; i++) {
      syms.add(new OperationSymbol("r" + i, arities[i]));
    }
    return makeRandomAlgebra(n, new SimilarityType(syms), seed);
  }


  public static void main(String[] args) throws Exception {
    SmallAlgebra alg0 = fullTransformationSemigroup(3, true, true);
    List<Operation> ops = alg0.operations();
    //int[] inv = new int[] {2,1,0};
    int[] inv = new int[] {1,2,0};
    final int invx = Horner.horner(inv, 3);
    //ops.add(Operations.makeConstantIntOperation(alg0.cardinality(), invx));
    org.uacalc.io.AlgebraIO.writeAlgebraFile(alg0, "/home/ralph/Java/Algebra/algebras/trans3.ua");
    for (int i = 0; i < 27; i++) {
      System.out.println("" + i + ": " + ArrayString.toString(Horner.hornerInv(i, 3, 3)));
    }
    org.uacalc.alg.sublat.SubalgebraLattice sub = alg0.sub();
    Set univ = sub.universe();
    List<org.uacalc.alg.sublat.BasicSet> univList = new ArrayList<org.uacalc.alg.sublat.BasicSet>(univ);
    Collections.sort(univList);
    System.out.println("number of subs with constants: " + univ.size());
    for (int i = 0; i < univList.size(); i++) {
      org.uacalc.alg.sublat.BasicSet s = (org.uacalc.alg.sublat.BasicSet)univList.get(i);
      System.out.println(i + ": " + s);
    }
    
    if (args.length == 0) return;
    int arity = 3;
    try {
      alg0 = (SmallAlgebra)org.uacalc.io.AlgebraIO.readAlgebraFile(args[0]);
      if (args.length > 1) {
        arity = Integer.parseInt(args[1]);
      }
    }
    catch (Exception e) {}
    //int level = Algebras.jonssonLevel(alg0);
    //System.out.println("level is " + level);
    Term t = findNUF(alg0, arity);
    if (t == null) System.out.println("there is no NUF with arity " + arity);
    else System.out.println("the alg has a NUF of arity " + arity + ": " + t);
  }



}







