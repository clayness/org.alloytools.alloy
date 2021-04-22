package kodkod.engine.slicing;

import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import kodkod.engine.bool.BooleanAccumulator;
import kodkod.engine.bool.BooleanFactory;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.bool.BooleanVariable;
import kodkod.engine.bool.BooleanVisitor;
import kodkod.engine.bool.ITEGate;
import kodkod.engine.bool.MultiGate;
import kodkod.engine.bool.NotGate;
import kodkod.engine.bool.Operator;
import kodkod.engine.config.Options;

/**
 * The class to slice a boolean formula to independent parts
 *
 * @author guolongzheng
 */
public class Canonicalizer {

    BooleanFactory                         buildFactory;
    BooleanFormula[]                       sortedBf;
    final private HashMap<Integer,Integer> reverseLabelMap = new HashMap<>();    //map the normalized label to original label

    public void canonize(List<BooleanFormula> booleanFormulaSet) {

        Set<BooleanVariable> variableSet = new HashSet<>();
        for (BooleanFormula bf : booleanFormulaSet) {
            //System.out.print(bf.toString() + " ");
            new BooleanFormulaCounter(bf, bf.varSet).explore();
            variableSet.addAll(bf.varSet);
        }

        final BooleanVariable[] sortedVars = variableSet.toArray(new BooleanVariable[variableSet.size()]);
        Arrays.parallelSort(sortedVars, new Comparator<BooleanVariable>() {

            @Override
            public int compare(BooleanVariable o1, BooleanVariable o2) {
                return o1.weight - o2.weight;
            }
        });

        final int numVars = sortedVars.length;
        final int numClauses = booleanFormulaSet.size();
        for (int i = 0; i < numVars; i++) {
            reverseLabelMap.put(i + 1, sortedVars[i].label());
            sortedVars[i].setLabel(i + 1);

        }

        sortedBf = booleanFormulaSet.toArray(new BooleanFormula[booleanFormulaSet.size()]);
        Arrays.parallelSort(sortedBf, new Comparator<BooleanFormula>() {

            @Override
            public int compare(BooleanFormula o1, BooleanFormula o2) {
                return o1.weight - o2.weight;
            }
        });

        int base = numVars;
        for (int i = 0; i < sortedBf.length; i++) {
            base = new CircuitLabelRenamer().explore(sortedBf[i], base);
        }

        buildFactory = BooleanFactory.factory(numVars, new Options());
        BooleanFormula independentFormula;
        buildFactory.setLabel(base + 1);
        buildFactory.setComparisonDepth(1);
        BooleanAccumulator acc = BooleanAccumulator.treeGate(Operator.AND);
        for (BooleanFormula bf : sortedBf)
            acc.add(bf);
        independentFormula = (BooleanFormula) buildFactory.accumulate(acc);

        // independentFormula = combine(0,sortedBf.length-1);
        /*
         * for (int i = 1; i < sortedBf.length; i++) { // independentFormula =
         * (BooleanFormula) buildFactory.uncheckedAnd(independentFormula, sortedBf[i]);
         * independentFormula = (BooleanFormula)
         * buildFactory.uncheckedAnd(independentFormula, sortedBf[i]); }
         */
        ExtendBooleanFormula extendBooleanFormula = new ExtendBooleanFormula(independentFormula, numVars, numClauses, reverseLabelMap);
        if (SATResult.contains(extendBooleanFormula)) {//if have visited this formula, read the solution from SATResult
            SATResult.globalRepeat();
            SATResult.readResult(extendBooleanFormula);
            return;
        } else {
            for (ExtendBooleanFormula bf : SATResult.getUnsolvedFormulas()) {
                if (bf.equals(extendBooleanFormula)) {
                    SATResult.currentRepeat();
                    for (int l : reverseLabelMap.keySet()) {
                        bf.reverseLabelMapSet.get(l).add(reverseLabelMap.get(l));
                    }
                    return;
                }
            }
            for (int l : reverseLabelMap.keySet()) {
                int newLabel = reverseLabelMap.get(l);
                LinkedList<Integer> labels = new LinkedList();
                labels.add(newLabel);
                extendBooleanFormula.reverseLabelMapSet.put(l, labels);
            }
            SATResult.addUnsolvedFormula(extendBooleanFormula);
        }
        return;
    }



    BooleanFormula combine(int l, int h) {
        if ((h - l) < 3) {
            BooleanFormula bf = sortedBf[l];
            for (int i = l + 1; i <= h; i++)
                bf = (BooleanFormula) buildFactory.and(bf, sortedBf[i]);
            return bf;
        } else {
            return (BooleanFormula) buildFactory.and(combine(l, (l + h) / 2), combine((l + h) / 2 + 1, h));
        }
    }

    /* rename the circuit label to the new sorted order */
    private class CircuitLabelRenamer implements BooleanVisitor<Object,Object> {

        private int circuitLabel;

        public int explore(BooleanFormula bf, int base) {
            circuitLabel = base;
            for (BooleanFormula input : bf) {
                input.accept(this, circuitLabel);
            }
            if (bf instanceof MultiGate) {
                //if haven't visited this gate yeah
                if (!bf.isVisited) {
                    ((MultiGate) bf).setLabel(++circuitLabel);
                    bf.isVisited = true;
                }
            } else if (bf instanceof ITEGate) {
                if (!bf.isVisited) {
                    ((ITEGate) bf).setLabel(++circuitLabel);
                    bf.isVisited = true;
                }
            }
            return circuitLabel;
        }

        @Override
        public Object visit(MultiGate multigate, Object arg) {
            for (BooleanFormula input : multigate) {
                input.accept(this, null);
            }
            if (!multigate.isVisited) {
                multigate.setLabel(++circuitLabel);
                multigate.isVisited = true;
            }
            return null;
        }

        @Override
        public Object visit(ITEGate ite, Object arg) {
            ite.input(0).accept(this, null);
            ite.input(1).accept(this, null);
            ite.input(2).accept(this, null);
            if (!ite.isVisited) {
                ite.setLabel(++circuitLabel);
                ite.isVisited = true;
            }
            return null;
        }

        @Override
        public Object visit(NotGate negation, Object arg) {
            if (!negation.visited) {
                negation.input(0).accept(this, null);
                negation.visited = true;
            }
            return null;
        }

        @Override
        public Object visit(BooleanVariable variable, Object arg) {
            return null;
        }
    }


    //count number of operators and variables for each boolean formula
    //and count number of operators and formulas for each variable
    private class BooleanFormulaCounter implements BooleanVisitor<Object,Object> {

        BooleanFormula       bf;
        Set<BooleanVariable> varSet;

        public BooleanFormulaCounter(BooleanFormula bf, Set<BooleanVariable> varSet) {
            this.bf = bf;
            this.varSet = varSet;
        }

        public void explore() {
            bf.accept(this, null);
            return;
        }

        @Override
        public Object visit(MultiGate multigate, Object arg) {
            for (BooleanFormula input : multigate) {
                bf.weight++;
                input.accept(this, null);
            }
            return null;
        }

        @Override
        public Object visit(ITEGate ite, Object arg) {
            int pre = (arg == null) ? 0 : (int) arg;
            bf.weight++;
            ite.input(0).accept(this, pre + 1);
            ite.input(1).accept(this, pre + 1);
            ite.input(2).accept(this, pre + 1);
            return null;
        }

        @Override
        public Object visit(NotGate negation, Object arg) {
            int pre = (arg == null) ? 0 : (int) arg;
            bf.weight++;
            negation.input(0).accept(this, pre + 1);
            return null;
        }

        @Override
        public Object visit(BooleanVariable variable, Object arg) {
            int pre = (arg == null) ? 0 : (int) arg;
            bf.weight += 10;
            if (!variable.isVisited) {
                variable.weight += variable.label();
                varSet.add(variable);
                variable.isVisited = true;
            } else
                variable.weight += pre * 1000;
            return null;
        }
    }


}


