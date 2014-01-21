package org.uacalc.alg.parallel;

import java.util.concurrent.*;
import java.util.*;

import org.uacalc.util.*;
import org.uacalc.alg.op.*;
import org.uacalc.terms.*;

// Notes:
// The map below should be either a ConcurrentHashMap or a
// ConcurrentSkipListMap. The latter uses the natural order
// of the keys, IntArray in our case, for lookups, and so
// may be faster. 
//
// In either case we should use putIfAbsent(key, value). This will 
// return null if the entry is new. 
//
// The univList should have a Collections.unmodifiable wrapper.
//
// The individual threads should all modify the map but keep the
// new elements found on a private list that should be returned
// and the fork part should concatenate these list of new elements
// serially.
//
// Note the univList may have already started this pass with another
// operation and so may be larger than the "max" in the incrementor
// but that doesn't matter: we don't have to worry about that.
//

// this version, based on 
//    oracle.com/technetwork/articles/java/fork-join-422606.html
// just did each task serially. Don't know why.
// Figured it out: it was call join on each task in the *opposite* order
// of the forks. Also did one with a direct call to compute as 
// suggested by Grossman.
// The times for this just about equal the times for ParallelClose2.

// compile (use java 7) with 
//
// % javac ParallelClose3.java
//
// and run with
//
// % java ParallelClose3 k
//
// for k processes. k is optional, defaulting to 4.

// Some good ideas at
// http://homes.cs.washington.edu/~djg/teachingMaterials/spac/grossmanSPAC_forkJoinFramework.html

//               Times for ParallelClose2
// 
// timing with a = b = 1: 2 threads was the fastest, a liitle over 10 secs
//                          and 1 thread was over 19. 4 threads was slightly
//                          slower than 1
//
// with a = 43, b = 571: with 1  thread  64.8 seconds,
//                       with 2  threads 32.5 seconds,
//                       with 4  threads 20.6 seconds,
//                       with 8  threads 19.1 seconds,
//                       with 16 threads 18.3 seconds,
//                       with 32 threads 23.5 seconds,
//                       with 64 threads 34.6 seconds,

class SingleCloseSerial extends RecursiveTask<List<IntArray>> {
  
  final ConcurrentMap<IntArray,Term> map;
  final List<IntArray> univList;
  final Operation op;
  
  final int[] argIndeces;
  
  /**
   * An incrementor associated with argIndeces.
   */
  final ArrayIncrementor incrementor;
  
  final int arity;
  
  final List<IntArray> newElts = new ArrayList<>();
  
  SingleCloseSerial(List<IntArray> univList, ConcurrentMap<IntArray,Term> map, 
                    Operation op, int[] argIndeces, ArrayIncrementor incrementor) {
    this.univList = univList;
    this.map = map;
    this.op = op;
    this.argIndeces = argIndeces;
    this.incrementor = incrementor;
    this.arity = op.arity();
  }
  
  @Override
  protected List<IntArray> compute() {
    final int[][] arg = new int[arity][];
    while (true) {
      for (int i = 0; i < arity; i++) {
        arg[i] = univList.get(argIndeces[i]).getArray();
      }
      int[] vRaw = op.valueAt(arg);
      IntArray v = new IntArray(vRaw);
      // this is subtle: we don't want to build the term
      // if this element has already been found. But 
      // because of threading it may get added just after
      // this so we need to check again and only add v to
      // newElts if it was not added.
      if (!map.containsKey(v)) {
        List<Term> children = new ArrayList<Term>(arity);
        for (int j = 0; j < arity; j++) {
          children.add(map.get(univList.get(argIndeces[j])));
        }
        Term term = map.putIfAbsent(v, new NonVariableTerm(op.symbol(), children));
        if (term == null) newElts.add(v);
      }
      
      if (!incrementor.increment()) return newElts;
    }
    
    
  }
  
}

/**
 * This will will do one pass partial closure with a single 
 * Operation using a parallel algorithm. Note the term map
 * map e different on different runs with the same data.  
 * 
 * 
 * @author ralph
 *
 */
public class SingleClose extends RecursiveTask<List<IntArray>> {
  
  final int increment;  // this is also the number of processes that will be used
  // it will also serve as id
  final Map<IntArray,Integer> map;
  final Operation op;
  //final int closedMark;
  final int min;
  final int max;
  final List<int[]> arrays;
  
  public SingleClose(Map<IntArray,Integer> map, Operation op, int min) {
    this(map, op, min, -1);
  }
  
  public SingleClose(Map<IntArray,Integer> map, Operation op, int min, int inc) {
    this.increment = inc > 0 ? inc : calculateInc();
    this.map = map;
    this.op = op;
    this.min = min;
    this.max = map.size() - 1;
    this.arrays = new ArrayList<>(increment);
    setArrays();
  }
  
  private int calculateInc() {
    return 4;
  }
  
  private void setArrays() {
    final int k = op.arity();
    int[] a = new int[k];
    a[k-1] = min;
    ArrayIncrementor inc = SequenceGenerator.sequenceIncrementor(a, max, min, increment);
    for (int i = 0; i < increment; i++) {
      final int[] b = Arrays.copyOf(a, a.length);
      arrays.set(i, b);
      inc.increment();
    }
  }
  
  
  @Override
  protected List<IntArray> compute() {
    return null;
  }
  

  /**
   * @param args
   */
  public static void main(String[] args) {
    //SingleClose foo = new SingleClose()
    
  }

}
