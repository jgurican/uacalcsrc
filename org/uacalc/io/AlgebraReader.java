
package org.uacalc.io;

import java.io.*;
import java.util.*;

import org.uacalc.lat.BasicLattice;
import org.xml.sax.*;
import org.xml.sax.helpers.DefaultHandler;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;

import org.uacalc.alg.*;
import org.uacalc.alg.conlat.*;
import org.uacalc.alg.op.Operation;
import org.uacalc.alg.op.OperationSymbol;
import org.uacalc.alg.op.Operations;
import org.uacalc.alg.op.Operations;
import org.uacalc.util.*;
import org.latdraw.orderedset.*;

/**
 * XML reading. Eventually we will have "project" files with multiple
 * algebras. For now we will have just single algebras.
 *
 * @author Ralph Freese
 * @version $Id$
 */
public final class AlgebraReader extends DefaultHandler {


  // maybe these should be in SmallAlgebra
  public static final int BASIC = 0;
  public static final int PRODUCT = 1;
  public static final int QUOTIENT = 2;
  public static final int SUBALGEBRA = 3;
  public static final int POWER = 4;
  public static final String EMPTY_STRING = "";

  private String algNameString = EMPTY_STRING;
  private String opNameString = EMPTY_STRING;
  private String descString = EMPTY_STRING;
  private String cardinalityString = EMPTY_STRING;
  private String arityString = EMPTY_STRING;
  private String powerString = EMPTY_STRING;
  private String powersString = EMPTY_STRING;
  private String rowString = EMPTY_STRING;
  private String labelsString = EMPTY_STRING;
  private String covString = EMPTY_STRING;
  private String intArrayString = EMPTY_STRING;
  private String productElemString = EMPTY_STRING;

  private File file;
  private InputStream inputStream;
  private SmallAlgebra algebra;
  private List<SmallAlgebra> algebraList;
  private int algType;
  private SimpleList tagStack = SimpleList.EMPTY_LIST;
  private String algName;
  private String opName;
  private String desc;
  private int cardinality;
  private int arity;
  private int power;
  private int[] powers;
  //private OperationSymbol opSym;
  //private Operation op;
  private List<Operation> ops = new ArrayList<Operation>();
  private OrderedSet underlyingPoset;
  private List labels = new ArrayList();
  private List upperCovers = new ArrayList();
  private int[] intArray;
  private int intArrayIndex;
  private List<IntArray> universe = new ArrayList<IntArray>();
  private List<SmallAlgebra> factors = new ArrayList<SmallAlgebra>();
  private List<IntArray> generators = new ArrayList<IntArray>();
  private SmallAlgebra superAlgebra;
  private SmallAlgebra rootAlgebra;
  private Algebra bigAlgebra;
  private Partition congruence;
  private int[] subUniverse;
  private Map<String,String> nameDescMap = new HashMap<String,String>();
  //private Deque<String> descStack = new LinkedList<String>();
  private Deque<String> algNameStack = new LinkedList<String>();

  public AlgebraReader(File file) throws IOException {
    this.file = file;
  }

  public AlgebraReader(String file) throws IOException {
    this(new File(file));
  }

  public AlgebraReader(InputStream is) throws IOException {
    this.inputStream = is;
  }

  public SmallAlgebra readAlgebraFile() throws IOException, SAXException,
                                               ParserConfigurationException {
    //  Use an instance of ourselves as the SAX event handler
    DefaultHandler handler = this;
    //  Use the default (non-validating) parser
    SAXParserFactory factory = SAXParserFactory.newInstance();
    SAXParser saxParser = factory.newSAXParser();
    saxParser.parse(file, handler);
    return algebra;
  }

  public SmallAlgebra readAlgebraFromStream() throws IOException, SAXException,
                                               ParserConfigurationException {
    // Use an instance of ourselves as the SAX event handler
    DefaultHandler handler = this;
    // Use the default (non-validating) parser
    SAXParserFactory factory = SAXParserFactory.newInstance();
    SAXParser saxParser = factory.newSAXParser();
    saxParser.parse(inputStream, handler);
    return algebra;
  }

  public List<SmallAlgebra> readAlgebraListFile() throws IOException, SAXException,
                                               ParserConfigurationException {
    //  Use an instance of ourselves as the SAX event handler
    DefaultHandler handler = this;
    //  Use the default (non-validating) parser
    SAXParserFactory factory = SAXParserFactory.newInstance();
    SAXParser saxParser = factory.newSAXParser();
    saxParser.parse(file, handler);
    return algebraList;
  }

  public List<SmallAlgebra> readAlgebraListFromStream() throws IOException, SAXException,
                                                           ParserConfigurationException {
    //  Use an instance of ourselves as the SAX event handler
    DefaultHandler handler = this;
    //  Use the default (non-validating) parser
    SAXParserFactory factory = SAXParserFactory.newInstance();
    SAXParser saxParser = factory.newSAXParser();
    saxParser.parse(inputStream, handler);
    return algebraList;
  }

  private void clearStrings() {
    algNameString = EMPTY_STRING;
    opNameString = EMPTY_STRING;
    descString = EMPTY_STRING;
    cardinalityString = EMPTY_STRING;
    arityString = EMPTY_STRING;
    powerString = EMPTY_STRING;
    powersString = EMPTY_STRING;
    rowString = EMPTY_STRING;
    labelsString = EMPTY_STRING;
    covString = EMPTY_STRING;
    intArrayString = EMPTY_STRING;
    productElemString = EMPTY_STRING;
  }

  private String currentTag() {
    return (String)tagStack.first();
  }

  private String parentTag() {
    if (tagStack.rest().isEmpty()) return null;
    return (String)tagStack.rest().first();
  }


  private void intRow(final String str) {
    String[] strArr = str.split(",\\s*");
    final int n = strArr.length;
    for (int i = 0; i < n; i++) {
      intArray[intArrayIndex + i] = Integer.parseInt(strArr[i]);
    }
    intArrayIndex = intArrayIndex + n;
  }

  private int[] rawIntArray(String str) {
    String[] strArr = str.split(",\\s*");
    final int n = strArr.length;
    int[] ans = new int[n];
    for (int i = 0; i < n; i++) {
      ans[i] = Integer.parseInt(strArr[i]);
    }
    return ans;
  }

  private List rawList(String str) {
    String[] strArr = str.split(",\\s*");
    final int n = strArr.length;
    List ans = new ArrayList(n);
    if (str.isEmpty()) {
      return ans;
    }
    for (int i = 0; i < n; i++) {
      ans.add(strArr[i]);
    }
    return ans;
  }

  private IntArray intArray(String str) {
    return new IntArray(rawIntArray(str));
  }

  public void startElement(String namespaceURI,
                             String lName, // local name
                             String qName, // qualified name
                             Attributes attrs) throws SAXException {
    String elemName = lName; // element name
    if ("".equals(elemName)) elemName = qName; // namespaceAware = false
    //System.out.println("elem is " + elemName);
    tagStack = tagStack.cons(elemName);

    if ("algName".equals(elemName)) algNameString = EMPTY_STRING;
    if ("opName".equals(elemName)) opNameString = EMPTY_STRING;
    if ("desc".equals(elemName)) descString = EMPTY_STRING;
    if ("cardinality".equals(elemName)) cardinalityString = EMPTY_STRING;
    if ("arity".equals(elemName)) arityString = EMPTY_STRING;
    if ("power".equals(elemName)) powerString = EMPTY_STRING;
    if ("powers".equals(elemName)) powersString = EMPTY_STRING;
    if ("row".equals(elemName)) rowString = EMPTY_STRING;
    if ("cov".equals(elemName)) covString = EMPTY_STRING;
    if ("productElem".equals(elemName)) productElemString = EMPTY_STRING;
    if ("intArray".equals(elemName)) intArrayString = EMPTY_STRING;

    if ("basicAlgebra".equals(elemName)) algType = BASIC;
    if ("powerAlgebra".equals(elemName)) algType = POWER;
    if ("productAlgebra".equals(elemName)) algType = PRODUCT;
    if ("quotientAlgebra".equals(elemName)) algType = QUOTIENT;
    if ("subAlgebra".equals(elemName)) algType = SUBALGEBRA;
    if ("basicLattice".equals(elemName)) algType = BASIC;
    if ("pAlgebra".equals(elemName)) algType = BASIC;
    if ("brouwerianAlgebra".equals(elemName)) algType = BASIC;
    if ("heytingAlgebra".equals(elemName)) algType = BASIC;
    if ("opTable".equals(elemName)) {
      int h = 1;
      for (int i = 0; i < arity; i++ ) {
        h = h * cardinality;
      }
      intArray = new int[h];
      intArrayIndex = 0;
    }
    if ("congruence".equals(elemName)) {
      intArray = new int[cardinality];
      intArrayIndex = 0;
    }
    // 6/1/2012
    if ("subUniverse".equals(elemName)) {
      intArray = new int[cardinality];
      intArrayIndex = 0;
    }
  }

  /**
   * Since this is allowed to chunk the string in any way, we have to
   * append the strings until we get to the end tag.
   */
  public void characters(char buf[], int offset, int len) throws SAXException {
    //System.out.println("calling characters with tagStack = " + tagStack);

    String s = new String(buf, offset, len);
    if ("algName".equals(currentTag())) algNameString += s;
    if ("opName".equals(currentTag())) opNameString += s;
    if ("desc".equals(currentTag())) descString += s;
    if ("cardinality".equals(currentTag())) cardinalityString += s;
    if ("arity".equals(currentTag())) arityString += s;
    if ("power".equals(currentTag())) powerString += s;
    if ("row".equals(currentTag())) rowString += s;
    if ("labels".equals(currentTag())) labelsString += s;
    if ("cov".equals(currentTag())) covString += s;
    if ("intArray".equals(currentTag())) {
      if ("congruence".equals(parentTag()) && s.length() > 0) {
        intArrayString += s;
      }
      // 6/1/2012
      else if ("subUniverse".equals(parentTag()) &&  s.length() > 0) {
        intArrayString += s;
      }
      else if ("powers".equals(parentTag()) && s.length() > 0) {
        powersString += s;
      }
    }

    if ("productElem".equals(currentTag())) productElemString += s;
  }

  public void endElement(String namespaceURI, String lName, String qName)
                                                       throws SAXException {
    //System.out.println("calling endElement with tagstack = " + tagStack + " \nand poping");
    String parent = parentTag();
    tagStack = tagStack.rest();
    String elemName = lName; // element name
    if ("".equals(elemName)) elemName = qName; // namespaceAware = false
    //System.out.println("and elemName = " + elemName);

    if ("algebra".equals(elemName)) {
      if (algebraList == null) algebraList = new ArrayList<SmallAlgebra>();
      algebraList.add(algebra);
      clearStrings();
    }
    if ("algName".equals(elemName)) {
      algName = algNameString.trim();
      algNameStack.push(algName);
      nameDescMap.put(algName, null);
    }
    if ("opName".equals(elemName)) opName = opNameString.trim();
    if ("desc".equals(elemName)) {
      desc = descString.trim();
      // note for this to work desc, if it exists, should come after algName
      nameDescMap.put(algName, desc);
      descString = EMPTY_STRING;
    }
    if ("cardinality".equals(elemName))
            cardinality = Integer.parseInt(cardinalityString.trim());
    if ("arity".equals(elemName)) arity = Integer.parseInt(arityString.trim());
    if ("power".equals(elemName)) power = Integer.parseInt(powerString.trim());
    if ("powers".equals(elemName)) powers = rawIntArray(powersString.trim());
    if ("row".equals(elemName)) intRow(rowString.trim());
    if ("labels".equals(elemName)) labels = rawList(labelsString.trim());
    if ("cov".equals(elemName)) upperCovers.add(rawList(covString.trim()));
    if ("intArray".equals(elemName) && "congruence".equals(parent)) {
      intArrayString = intArrayString.trim();
      if (intArrayString.length() > 0) intArray = rawIntArray(intArrayString);
    }
    if ("intArray".equals(elemName) && "subUniverse".equals(parent)) {
      intArrayString = intArrayString.trim();
      if (intArrayString.length() > 0) intArray = rawIntArray(intArrayString);
    }
    if ("productElem".equals(elemName)) {
      productElemString = productElemString.trim();
      if ("generators".equals(parent)) generators.add(intArray(productElemString));
      else if ("universe".equals(parent)) universe.add(intArray(productElemString));
    }

    if ("op".equals(elemName)) {
      ops.add(Operations.makeIntOperation(opName, arity, cardinality,
                   Horner.leftRightReverse(intArray, cardinality, arity)));
    }
    if ("subUniverse".equals(elemName)) {
      subUniverse = intArray;
    }
    if ("congruence".equals(elemName)) {
      congruence = new BasicPartition(intArray);
    }

    if ("basicAlgebra".equals(elemName)) {
      // need to see if universe exists
      String tmp = algNameStack.peekFirst();
      algebra = new BasicAlgebra(tmp, cardinality, ops);
      addDescription();
      ops = new ArrayList<Operation>();
    }

    if ("basicLattice".equals(elemName)) {
      String tmp = algNameStack.peekFirst();
      try {
        underlyingPoset = new OrderedSet(tmp,labels,upperCovers);

        BasicLattice algebra = new BasicLattice(tmp, underlyingPoset);

        addMeetAndJoinOperations(algebra);

        this.algebra = (SmallAlgebra) algebra;
        addDescription();
      } catch (NonOrderedSetException e) {
          System.out.println(e.getMessage());
          return;
      }
    }


    if ("pAlgebra".equals(elemName)) {
      String tmp = algNameStack.peekFirst();
      try {
        underlyingPoset = new OrderedSet(tmp,labels,upperCovers);
        BasicLattice algebra = new BasicLattice(tmp, underlyingPoset);

        addMeetAndJoinOperations(algebra);
        addPseudoComplementOperation(algebra);
        addConstantOperation(algebra, "zero");


        this.algebra = (SmallAlgebra) algebra;
        addDescription();
      } catch (NonOrderedSetException e) {
        System.out.println(e.getMessage());
        return;
      }
    }

    if ("heytingAlgebra".equals(elemName)) {
      String tmp = algNameStack.peekFirst();
      try {
        underlyingPoset = new OrderedSet(tmp,labels,upperCovers);
        BasicLattice algebra = new BasicLattice(tmp, underlyingPoset);

        addMeetAndJoinOperations(algebra);
        addRelativeComplements(algebra);
        // This is a little overkill, we can do it via ipm(x,0)
        addPseudoComplementOperation(algebra);
        addConstantOperation(algebra, "zero");
        addConstantOperation(algebra, "one");

        this.algebra = (SmallAlgebra) algebra;
        addDescription();
      } catch (NonOrderedSetException e) {
        System.out.println(e.getMessage());
        return;
      }
    }

    if ("brouwerianAlgebra".equals(elemName)) {
      String tmp = algNameStack.peekFirst();
      try {
        underlyingPoset = new OrderedSet(tmp,labels,upperCovers);

        BasicLattice algebra = new BasicLattice(tmp, underlyingPoset);

        addMeetAndJoinOperations(algebra);
        addRelativeComplements(algebra);

        // preparing implication operation
/*
        int s = algebra.cardinality();
        int[] imp_table = new int[s*s];
        for (int i = 0; i< s; i++) {
          for (int j = 0; j < s; j++) {
            POElem a = (POElem) algebra.getElement(i);
            POElem b = (POElem) algebra.getElement(j);
            if ( algebra.leq(a,b) ) {
              imp_table[i*s+j] = s-1;
            } else if ( algebra.leq(b,a) && !a.equals(b)) {
              imp_table[i*s+j] = j;
            } else {
              // do real thing
            }

          }
        }
        algebra.operations().add(Operations.makeIntOperation("impl", 2, s,
                Horner.leftRightReverse(imp_table, s, 2)));
*/
        //one as a nullary operation
        addConstantOperation(algebra,"one");

        this.algebra = (SmallAlgebra) algebra;
        addDescription();
      } catch (NonOrderedSetException e) {
        System.out.println(e.getMessage());
        return;
      }
    }


    if ("factor".equals(elemName)) {
      factors.add(algebra);
    }
    if ("root".equals(elemName)) {
      rootAlgebra = algebra;
    }
    if ("superAlgebra".equals(elemName)) {
      superAlgebra = algebra;
    }
    if ("powerAlgebra".equals(elemName)) {
      String tmp = algNameStack.peekFirst();
      if (tmp == null) {
        algebra = new PowerAlgebra(rootAlgebra, power);
      }
      else algebra = new PowerAlgebra(tmp, rootAlgebra, power);
      addDescription();
    }

    if ("productAlgebra".equals(elemName)) {
      String tmp = algNameStack.peekFirst();
      if (tmp != null) algebra = new ProductAlgebra(tmp, factors);
      else  algebra = new ProductAlgebra(factors);
      addDescription();
      factors = new ArrayList<SmallAlgebra>();
    }
    if ("bigProductAlgebra".equals(elemName)) {
      String tmp = algNameStack.peekFirst();
      if (tmp != null) bigAlgebra = new BigProductAlgebra(tmp,
                                               (List<SmallAlgebra>)factors, powers);
      else  bigAlgebra = new BigProductAlgebra((List<SmallAlgebra>)factors, powers);
      addDescription();
      factors = new ArrayList<SmallAlgebra>();
    }
    if ("subProductAlgebra".equals(elemName)) {
      // we hack around the super tag by just skipping it since
      // the BigProductAlgebra cannot be cast into a SmallAlgebra.
      String tmp = algNameStack.peekFirst();

      algebra = new SubProductAlgebra(tmp, (BigProductAlgebra)bigAlgebra,
                           (List<IntArray>)generators, (List<IntArray>)universe);
      addDescription();
    }
    if ("subAlgebra".equals(elemName)) {
      //System.out.println("superAlgebra size = " + superAlgebra.cardinality());
      //System.out.println("subUniv size = " + subUniverse.length);
      //System.out.println("subUniv = " + Arrays.toString(subUniverse));
      String tmp = algNameStack.peekFirst();
      if (tmp == null) {
        algebra = new Subalgebra(superAlgebra, subUniverse);
      }
      else algebra = new Subalgebra(tmp, superAlgebra, subUniverse);
      System.out.println("algebra size = " + algebra.cardinality());
      addDescription();
    }
    if ("quotientAlgebra".equals(elemName)) {
      System.out.println("|" + algName + "|");
      String tmp = algNameStack.peekFirst();
      if (tmp == null) {
        algebra = new QuotientAlgebra(superAlgebra, congruence);
      }
      else algebra = new QuotientAlgebra(tmp, superAlgebra, congruence);
      addDescription();
    }
    //if (algebra != null && !EMPTY_STRING.equals(descString)) {
    //  algebra.setDescription(descString);
    //  descString = EMPTY_STRING;
    //}
  }

  /**
   * This also does some clean up:
   * pop'ing the algNameStack and setting algName to null.
   */
  private void addDescription() {
    //System.out.println(nameDescMap);
    if (algebra != null) {
      String tmp = nameDescMap.get(algebra.getName());
      //System.out.println(algebra.getName());
      //System.out.println("tmp: " + tmp);
      if (tmp != null) algebra.setDescription(tmp);
      // pop if a name was given
      // this is not a perfect solution: if some but not all algebras in a
      // product are missing names, the names may go in the wrong places.
      if (!algNameStack.isEmpty()) algNameStack.pop();
      algName = null;
    }
    //if (algebra != null && !EMPTY_STRING.equals(descString)) {
    //  algebra.setDescription(descString);
    //  descString = EMPTY_STRING;
    //}
  }

  void addMeetAndJoinOperations(BasicLattice lattice) {

    int s = lattice.cardinality();
    int[] join_table = new int[s*s];
    int[] meet_table = new int[s*s];

    // prepare/fill in tables for join and meet
    for (int i = 0; i< s; i++) {
      for (int j = i; j < s; j++) {
        List args = new ArrayList(2);
        args.add((POElem) lattice.getElement(i));
        args.add((POElem) lattice.getElement(j));
        int join = lattice.elementIndex(lattice.join(args));
        int meet = lattice.elementIndex(lattice.meet(args));

        join_table[i*s+j] = join;
        join_table[j*s+i] = join;
        meet_table[i*s+j] = meet;
        meet_table[j*s+i] = meet;
      }
    }

    lattice.operations().remove(1);
    lattice.operations().remove(0);

    lattice.operations().add(Operations.makeIntOperation("join", 2, s,
            Horner.leftRightReverse(join_table, s, 2)));
    lattice.operations().add(Operations.makeIntOperation("meet", 2, s,
            Horner.leftRightReverse(meet_table, s, 2)));
  }

  void addPseudoComplementOperation(BasicLattice lattice) {
    // prepare the table for pseudocomplenet
    POElem zero = lattice.zero();
    int s = lattice.cardinality();
    int[] pc_table = new int[s];
    for (int i = 0; i < s; i++) {
      POElem pc = zero;
      for (int j = 0; j < s; j++) {
        POElem candidate = (POElem) lattice.getElement(j);
        POElem meet_result = (POElem) lattice.meet((POElem) lattice.getElement(i), candidate);
        boolean OKmeet0 = zero.equals(meet_result);
        if (zero.equals(meet_result) && lattice.leq(pc, candidate) && !pc.equals(candidate)) pc = candidate;
      }
      pc_table[i] = lattice.elementIndex(pc);
    }
    // add the operation
    lattice.operations().add(Operations.makeIntOperation("pc", 1, s,
            Horner.leftRightReverse(pc_table, s, 1)));
  }

  void addRelativeComplements(BasicLattice lattice) {
    // preparing implication operation
    int s = lattice.cardinality();
    int[] imp_table = new int[s * s];
    for (int i = 0; i < s; i++) {
      for (int j = 0; j < s; j++) {
        POElem a = (POElem) lattice.getElement(i);
        POElem b = (POElem) lattice.getElement(j);
        if (lattice.leq(a, b)) {
          imp_table[i * s + j] = s - 1;
        } else {
          // do real thing
          // get a meet
          POElem meet_result = (POElem) lattice.meet(a, b);
          POElem candidate = meet_result;
          for (int k = lattice.elementIndex(meet_result); k < s ;k++) {
            POElem test = (POElem) lattice.getElement(k);
            // the second test is probably not necessary, but we want to be sure
            if (lattice.leq(lattice.meet(a,test),b) && lattice.leq(candidate,test)) candidate = test;
          }
          imp_table[i * s + j] = lattice.elementIndex(candidate);
        }

      }
    }
    lattice.operations().add(Operations.makeIntOperation("impl", 2, s,
            Horner.leftRightReverse(imp_table, s, 2)));
  }

  void addConstantOperation(BasicLattice lattice, String constant) {
    POElem nullary = lattice.zero();
    if ("zero".equalsIgnoreCase(constant)) {
      nullary = lattice.zero();
    } else if ("one".equalsIgnoreCase(constant)) {
      nullary =lattice.one();
    }

    int s = lattice.cardinality();
    int[] const_table = new int[1];
    const_table[0] = lattice.elementIndex(nullary);
    lattice.operations().add(Operations.makeIntOperation(constant, 0, s,
            Horner.leftRightReverse(const_table, s, 0)));
  }

  public static void main(String[] args) throws ParserConfigurationException,
                          SAXException, IOException, BadAlgebraFileException {
    //if (args.length == 0) return;
    //System.out.println("reading " + args[0]);
    //AlgebraReader r = new AlgebraReader("/tmp/lyndonQuot.ua");
    //AlgebraReader r = new AlgebraReader("/tmp/testalg.ua");
    AlgebraReader r = new AlgebraReader("/tmp/5HM3alt1sub.ua");
    //SmallAlgebra alg = r.readAlgebraFile();
    for (SmallAlgebra algx : r.readAlgebraListFile()) {
      System.out.println("alg: " + algx + ", card: " + algx.cardinality());
    }
    System.out.println("");
    //System.out.println("alg has size " + alg.cardinality());
    //System.out.println("alg.con jis " + alg.con().joinIrreducibles().size());
    //AlgebraWriter xmlWriter = new AlgebraWriter(alg, "/tmp/hoo.xml");
    //xmlWriter.writeAlgebraXML();
    //System.out.println("/tmp/hoo.xml written");
  }

}

