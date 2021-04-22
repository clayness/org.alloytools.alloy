package kodkod.engine.slicing;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.bool.BooleanVariable;
import kodkod.engine.bool.BooleanVisitor;
import kodkod.engine.bool.ITEGate;
import kodkod.engine.bool.MultiGate;
import kodkod.engine.bool.NotGate;
import kodkod.engine.bool.Operator;


/**
 * Created by guolongzheng on 3/31/17.
 */
public class Decomposer implements BooleanVisitor {

    private int[]                        parents;
    private int[]                        ranks;
    private LinkedList<BooleanFormula>[] represent2IndependentSet;

    public Decomposer(int numPrimaryVars) {
        ranks = new int[numPrimaryVars];
        parents = new int[numPrimaryVars];
        for (int i = 1; i < numPrimaryVars; i++) {
            parents[i] = i;
            ranks[i] = 1;
        }
        represent2IndependentSet = new LinkedList[numPrimaryVars];
    }

    public List<List<BooleanFormula>> decompose(BooleanFormula root) {
        //System.out.println(root.toString());
        root.accept(this, null);
        return Arrays.stream(represent2IndependentSet).filter(x -> x != null).collect(Collectors.toList());
    }

    @Override
    public Object visit(MultiGate multigate, Object arg) {
        if (multigate.op() == Operator.AND) {
            for (BooleanFormula input : multigate) {
                input.accept(this, null);
            }
        } else {
            if (!multigate.sliced) {
                new AtomCircuitVisitor(multigate).execute();
                multigate.sliced = true;
            }
        }
        return null;
    }

    @Override
    public Object visit(ITEGate ite, Object arg) {
        if (!ite.sliced) {
            new AtomCircuitVisitor(ite).execute();
            ite.sliced = true;
        }
        return null;
    }

    @Override
    public Object visit(NotGate negation, Object arg) {
        if (!negation.sliced)
            new AtomCircuitVisitor(negation).execute();
        return null;
    }

    @Override
    public Object visit(BooleanVariable variable, Object arg) {
        if (!variable.visited)
            new AtomCircuitVisitor(variable).execute();
        return null;
    }

    private class AtomCircuitVisitor implements BooleanVisitor, UnionFind {

        private final BooleanFormula bf;    // current circuit
        private boolean              meetVisited; // indicate whether or not has encountered a visited variable
        private int                  represent; // the root lable for current circuit

        public AtomCircuitVisitor(BooleanFormula bf) {
            this.bf = bf;
            bf.varSet = new HashSet<>();
            this.meetVisited = false;
            represent = -1;
        }

        public void execute() {
            bf.accept(this, null);
            bf.sliced = true;
            if (!meetVisited) {
                LinkedList<BooleanFormula> newFormula = new LinkedList<>();
                newFormula.add(bf);
                represent2IndependentSet[represent] = newFormula;
                meetVisited = true;
            }
            return;
        }

        @Override
        public Object visit(MultiGate multigate, Object arg) {
            for (BooleanFormula input : multigate) {
                input.accept(this, null);
            }
            return null;
        }

        @Override
        public Object visit(ITEGate ite, Object arg) {
            ite.input(0).accept(this, null);
            ite.input(1).accept(this, null);
            ite.input(2).accept(this, null);
            return null;
        }

        @Override
        public Object visit(NotGate negation, Object arg) {
            negation.input(0).accept(this, null);
            return null;
        }

        @Override
        public Object visit(BooleanVariable variable, Object arg) {
            int root = root(variable.label());
            // if meet a variable that has been visited, means this circuit has dependence with another one
            if (!meetVisited) {
                if (variable.visited) {
                    if (represent == root)
                        return null;
                    if (represent != -1) {
                        represent2IndependentSet[represent] = null;
                        parents[represent] = root;
                    }
                    represent = root;
                    if (represent2IndependentSet[represent] == null)
                        represent2IndependentSet[represent] = new LinkedList<>();
                    represent2IndependentSet[represent].add(bf);
                    meetVisited = true;
                } else {
                    if (represent == -1) {   // the first unvisited variable
                        represent = root;
                        if (represent2IndependentSet[represent] == null)
                            represent2IndependentSet[represent] = new LinkedList<>();
                        represent2IndependentSet[represent].add(bf);
                    } else {      // union two variables
                        simpleUnion(represent, root);
                    }
                }
            } else {      //if already meet a visited variable
                if (variable.visited) {
                    if (represent == root)
                        return null;
                    union(represent, root, represent2IndependentSet[represent], represent2IndependentSet[root]);
                } else {
                    simpleUnion(represent, root);
                }
            }
            //if(!variable.visited) {
            bf.varSet.add(variable);
            variable.visited = true;
            //}
            return null;
        }

        @Override
        public int root(int i) {
            while (i != parents[i]) {
                i = parents[i];
                parents[i] = parents[parents[i]];
            }
            return i;
        }

        @Override
        public boolean find(int p, int q) {
            return root(p) == root(q);
        }

        @Override
        public void union(int p, int q, List<BooleanFormula> independentSetP, List<BooleanFormula> independentSetQ) {
            int i = root(p);
            int j = root(q);
            if (ranks[i] < ranks[j]) {
                independentSetQ.addAll(independentSetP);
                represent2IndependentSet[p] = null;
                represent = j;
                parents[i] = j;
                ranks[j] += ranks[i];
            } else {
                independentSetP.addAll(independentSetQ);
                represent2IndependentSet[q] = null;
                represent = i;
                parents[j] = i;
                ranks[i] += ranks[j];
            }
        }

        @Override
        public void simpleUnion(int p, int q) {
            parents[q] = p;
            ranks[p]++;
        }
    }
}
