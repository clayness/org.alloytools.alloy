package kodkod.engine.slicing;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;
import java.util.stream.Collectors;

import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.bool.BooleanValue;
import kodkod.engine.bool.BooleanVariable;
import kodkod.engine.bool.BooleanVisitor;
import kodkod.engine.bool.ITEGate;
import kodkod.engine.bool.MultiGate;
import kodkod.engine.bool.NotGate;
import kodkod.engine.bool.Operator;


/**
 * Created by guolongzheng on 3/31/17.
 */
public class Decomposer implements BooleanVisitor<Object,Map<BooleanValue,Set<BooleanVariable>>> {

    private final int[]                      parents;
    private final int[]                      ranks;
    private final List<List<BooleanFormula>> represent2IndependentSet;
    private final Set<BooleanValue>          sliced = new HashSet<>();

    @SuppressWarnings("serial" )
    public Decomposer(int maxPrimaryVar) {
        ranks = new int[maxPrimaryVar + 1];
        parents = new int[maxPrimaryVar + 1];
        for (int i = 1; i <= maxPrimaryVar; i++) {
            parents[i] = i;
            ranks[i] = 1;
        }
        represent2IndependentSet = new Vector<List<BooleanFormula>>() {

            {
                setSize(maxPrimaryVar + 1);
            }
        };
    }

    public List<List<BooleanFormula>> decompose(BooleanFormula root, Map<BooleanValue,Set<BooleanVariable>> varset) {
        //System.out.println(root.toString());
        root.accept(this, varset);
        return represent2IndependentSet.stream().filter(x -> x != null).collect(Collectors.toList());
    }

    @Override
    public Object visit(MultiGate multigate, Map<BooleanValue,Set<BooleanVariable>> arg) {
        if (multigate.op() == Operator.AND) {
            for (BooleanFormula input : multigate) {
                input.accept(this, arg);
            }
        } else {
            if (sliced.add(multigate)) {
                new AtomCircuitVisitor(multigate, arg).execute();
            }
        }
        return null;
    }

    @Override
    public Object visit(ITEGate ite, Map<BooleanValue,Set<BooleanVariable>> arg) {
        if (sliced.add(ite)) {
            new AtomCircuitVisitor(ite, arg).execute();
        }
        return null;
    }

    @Override
    public Object visit(NotGate negation, Map<BooleanValue,Set<BooleanVariable>> arg) {
        if (sliced.add(negation)) {
            new AtomCircuitVisitor(negation, arg).execute();
        }
        return null;
    }

    @Override
    public Object visit(BooleanVariable variable, Map<BooleanValue,Set<BooleanVariable>> arg) {
        if (!sliced.contains(variable)) {
            new AtomCircuitVisitor(variable, arg).execute();
        }
        return null;
    }

    private class AtomCircuitVisitor implements BooleanVisitor<Object,Object>, UnionFind {

        private final BooleanFormula                         bf;    // current circuit
        private final Map<BooleanValue,Set<BooleanVariable>> varset;

        private boolean                                      meetVisited; // indicate whether or not has encountered a visited variable
        private int                                          represent; // the root lable for current circuit

        public AtomCircuitVisitor(BooleanFormula bf, Map<BooleanValue,Set<BooleanVariable>> varset) {
            this.bf = bf;
            this.varset = varset;
            varset.put(bf, new HashSet<>());
            this.meetVisited = false;
            represent = -1;
        }

        public void execute() {
            bf.accept(this, null);
            assert sliced.contains(bf);
            if (!meetVisited) {
                LinkedList<BooleanFormula> newFormula = new LinkedList<>();
                newFormula.add(bf);
                represent2IndependentSet.set(represent, newFormula);
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
                if (sliced.contains(variable)) {
                    if (represent == root)
                        return null;
                    if (represent != -1) {
                        represent2IndependentSet.set(represent, null);
                        parents[represent] = root;
                    }
                    represent = root;
                    if (represent2IndependentSet.get(represent) == null)
                        represent2IndependentSet.set(represent, new LinkedList<>());
                    represent2IndependentSet.get(represent).add(bf);
                    meetVisited = true;
                } else {
                    if (represent == -1) {   // the first unvisited variable
                        represent = root;
                        if (represent2IndependentSet.get(represent) == null)
                            represent2IndependentSet.set(represent, new LinkedList<>());
                        represent2IndependentSet.get(represent).add(bf);
                    } else {      // union two variables
                        simpleUnion(represent, root);
                    }
                }
            } else {      //if already meet a visited variable
                if (sliced.contains(variable)) {
                    if (represent == root)
                        return null;
                    union(represent, root, represent2IndependentSet.get(represent), represent2IndependentSet.get(root));
                } else {
                    simpleUnion(represent, root);
                }
            }
            //if(!variable.visited) {
            varset.get(bf).add(variable);
            sliced.add(variable);
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
                represent2IndependentSet.set(p, null);
                represent = j;
                parents[i] = j;
                ranks[j] += ranks[i];
            } else {
                independentSetP.addAll(independentSetQ);
                represent2IndependentSet.set(q, null);
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
