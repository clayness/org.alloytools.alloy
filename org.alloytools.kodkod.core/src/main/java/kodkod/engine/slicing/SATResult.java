package kodkod.engine.slicing;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import kodkod.engine.satlab.SATSolver;

/**
 * Created by guolongzheng on 2/12/17.
 */
//what needed to know
//(1) each solver to each normalized boolean formula
//(2) each boolean formula to each label map
//(3) each normalized boolean formula to each result
public class SATResult {

    private static final class Inner {

        private int                                   numOfrun                  = 0;

        //the total number of independent clauses
        private int                                   totalClauses;
        private int                                   repeatedClauses;
        private int                                   currentRepeatedClauses;


        //record normalized and solved boolean formula, hash code is used to check equivalence, integer is the hashcode
        private Map<ExtendBooleanFormula,Boolean>     solvedBooleanFormulaSet   = new HashMap<>();

        private Set<ExtendBooleanFormula>             unsolvedBooleanFormulaSet = new HashSet<>();
        //record solution for each normalized boolean formula, using their hashcode as key
        private Map<Integer,HashMap<Integer,Boolean>> booleanFormulaToResult    = new HashMap<>();

        //map sat solver to extend boolean formula so that we can retrieve boolean formula information later
        private Map<SATSolver,ExtendBooleanFormula>   solverTobooleanFormula    = new HashMap<>();

        //this is shared in the whole process for current Alloy model
        private Map<Integer,Boolean>                  labelToResult             = new HashMap<>();

        //initialize some glabal variables, but keep the solution, visited boolean formulas and their mapping
        private Inner() {
            totalClauses = 0;
            repeatedClauses = 0;
            currentRepeatedClauses = 0;
            labelToResult.clear();
            solverTobooleanFormula.clear();
            unsolvedBooleanFormulaSet.clear();
        }

        private String results() {
            return null;
        }

        // For all solutions
        public HashMap<Integer,BitSet[]> allSolution = new HashMap<>();

        public long                      solveTime;

        public int                       numClauses;

        public int                       numPrimary;

        public int                       numVars;

        public long                      transTime;
    }

    private static Inner INSTANCE = new Inner();

    //search the solved boolean formula set to find whether this formula has beeen solved or not
    public static boolean contains(ExtendBooleanFormula booleanFormula) {
        return INSTANCE.solvedBooleanFormulaSet.containsKey(booleanFormula);
    }

    //put new boolean formula to visited set
    public static void putBooleanFormula(ExtendBooleanFormula bf, boolean isSat) {
        INSTANCE.solvedBooleanFormulaSet.put(bf, isSat);
        INSTANCE.unsolvedBooleanFormulaSet.remove(bf);
    }

    //read the result from previous solution for current boolean formula
    public static void readResult(ExtendBooleanFormula bf) {
        HashMap<Integer,Boolean> preSolution = INSTANCE.booleanFormulaToResult.get(bf.hashCode);
        if (preSolution == null) {
            //null means that previous solution for this boolean formula is unsatisfiable
            INSTANCE.labelToResult.put(0, false);
        } else {
            for (int i = 1; i <= bf.numPrimiryVariables; i++) {
                int label = bf.getOriginalLabel(i);
                INSTANCE.labelToResult.put(label, preSolution.get(i));
            }
        }
    }


    public void storeResult(int key, BitSet[] result) {
        INSTANCE.allSolution.put(key, result);
    }

    public static void nextSol() {

    }

    public static Output getOutput() {
        return new Output();
    }

    public static void addUnsolvedFormula(ExtendBooleanFormula extendBooleanFormula) {
        INSTANCE.unsolvedBooleanFormulaSet.add(extendBooleanFormula);
    }

    public static void currentRepeat() {
        INSTANCE.currentRepeatedClauses++;
    }

    public static void globalRepeat() {
        INSTANCE.repeatedClauses++;
    }

    public static Set<ExtendBooleanFormula> getUnsolvedFormulas() {
        return INSTANCE.unsolvedBooleanFormulaSet;
    }

    public static void run() {
        ++INSTANCE.numOfrun;
    }

    public static ExtendBooleanFormula getSolverFormula(SATSolver cnf) {
        return INSTANCE.solverTobooleanFormula.get(cnf);
    }

    public static void setSolverFormula(SATSolver solver, ExtendBooleanFormula independentBooleanFormula) {
        INSTANCE.solverTobooleanFormula.put(solver, independentBooleanFormula);
    }

    public static boolean getBooleanFormulaResult(ExtendBooleanFormula bf) {
        return INSTANCE.solvedBooleanFormulaSet.get(bf);
    }

    public static class Output {

        public final long solveTime;
        public final int  numClauses;
        public final int  numVars;
        public final int  numPrimary;
        public final long transTime;

        private Output() {
            this.solveTime = INSTANCE.solveTime;
            this.transTime = INSTANCE.transTime;
            this.numClauses = INSTANCE.numClauses;
            this.numVars = INSTANCE.numVars;
            this.numPrimary = INSTANCE.numPrimary;

            INSTANCE.solveTime = 0;
            INSTANCE.transTime = 0;
            INSTANCE.numClauses = 0;
            INSTANCE.numVars = 0;
            INSTANCE.numPrimary = 0;
        }
    }

    public static void solveTime(long l) {
        INSTANCE.solveTime = l;
    }

    public static void addClauses(int numberOfClauses) {
        INSTANCE.numClauses += numberOfClauses;
    }

    public static void addVars(int numberOfVariables) {
        INSTANCE.numVars += numberOfVariables;
    }

    public static void addPrimary(int numPrimaryVariables) {
        INSTANCE.numPrimary += numPrimaryVariables;
    }

    public static void translate(long translTime) {
        INSTANCE.transTime = translTime;
    }


}


