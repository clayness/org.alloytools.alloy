package edu.mit.csail.sdg.alloy4whole;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.Statistics;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.util.ints.IntSet;

public final class ExampleChenxi {


    /**
     * Converts the passed Alloy options into Kodkod options
     *
     * @param opt
     * @return options
     */
    public static Options convert(A4Solution frame, A4Options opt) {
        Options retval = new Options();
        if (frame.getBitwidth() > 0)
            retval.setBitwidth(frame.getBitwidth());
        retval.setCoreGranularity(opt.coreGranularity);
        retval.setNoOverflow(opt.noOverflow);
        retval.setSkolemDepth(opt.skolemDepth);
        retval.setSymmetryBreaking(opt.symmetry);
        if (opt.solver == A4Options.SatSolver.GlucoseJNI) {
            retval.setSolver(SATFactory.Glucose);
        } else if (opt.solver == A4Options.SatSolver.Glucose41JNI) {
            retval.setSolver(SATFactory.Glucose41);
        } else if (opt.solver == A4Options.SatSolver.MiniSatJNI) {
            retval.setSolver(SATFactory.MiniSat);
        } else if (opt.solver == A4Options.SatSolver.MiniSatProverJNI) {
            retval.setSolver(SATFactory.MiniSatProver);
        } else if (opt.solver == A4Options.SatSolver.CryptoMiniSatJNI) {
            retval.setSolver(SATFactory.CryptoMiniSat);
        } else {
            retval.setSolver(SATFactory.DefaultSAT4J);
        }
        return retval;
    }

    public static void main(String[] args) throws Exception {


        String filename = "/Users/cstevens/Research/chenxi-code/testing/1m.als";
        // Parse+typecheck the model
        System.out.println("=========== Parsing+Typechecking " + filename + " =============");
        Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);

        // Choose some default options for how you want to execute the
        // commands
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.SAT4J;

        ArrayList<A4Solution> sols = new ArrayList<A4Solution>();
        ArrayList<Integer> positive = new ArrayList<Integer>();

        Translation.Whole firstTranslation;
        Bounds firstBounds;

        HashMap<Relation,IntSet> reMap = new HashMap<Relation,IntSet>();
        Set<Relation> used = null;

        long startSolve = System.currentTimeMillis();

        //first run
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Command " + command + ": ============");
            System.out.println("1111111");
            System.out.println("22222222");

            Translation.Whole translation;
            long translTime;

            TranslateAlloyToKodkod tatk = new TranslateAlloyToKodkod(A4Reporter.NOP, options, world.getAllReachableSigs(), command);
            tatk.makeFacts(command.formula.and(world.getAllReachableFacts()));
            A4Solution frame = tatk.getFrame();

            Formula f = Formula.and(frame.getFormulas());
            Bounds b = frame.getBounds();
            Set<Relation> relations = b.relations();

            firstBounds = b;
            used = b.relations();
            Options o = convert(frame, options);

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;
            firstTranslation = translation;

            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;
            ArrayList<Solution> solutionCollection = new ArrayList<Solution>();

            System.out.println("first solving time is" + translTime);

            HashMap<Relation,int[]> map = new HashMap<Relation,int[]>();
            HashMap<Relation,int[]> ref = new HashMap<Relation,int[]>();

            int[] notModel = new int[primaryVars];
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();
            int[] track = new int[primaryVars];
            double inf = Double.POSITIVE_INFINITY;
            double min = inf;

            for (Relation re : b.relations()) {
                if (re.toString().contains(".")) {
                    final IntSet i = translation.primaryVariables(re);
                    map.put(re, i.toArray());
                    ref.put(re, i.toArray());
                    reMap.put(re, i);
                    if (min > i.min()) {
                        min = i.min();
                    }
                }
            }

            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                solutionCollection.add(sol);
                System.out.println(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                    int cur = notModel[i - 1];
                    int abs = Math.abs(cur);
                    if (abs >= min) {
                        if (!notModelHelp.contains(cur) && !notModelHelp.contains(-cur)) {
                            notModelHelp.add(cur);
                        }
                        if (notModelHelp.contains(abs) && cur < 0) {
                            int index = notModelHelp.indexOf(abs);
                            notModelHelp.set(index, cur);
                        }
                    }
                }
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
            }
            sol = Solver.unsat(translation, stats);
            translation = null;


            for (int i : notModelHelp) {
                if (i > 0) {
                    positive.add(i);
                }
            }

            for (Map.Entry<Relation,int[]> m : map.entrySet()) {
                ArrayList<Integer> temp = new ArrayList<Integer>();
                for (int i : positive) {
                    int[] b1 = m.getValue();
                    for (int i1 : b1) {
                        if (i1 == i) {
                            temp.add(i);
                        }
                    }
                }
                int[] a = new int[temp.size()];
                for (int i = 0; i < a.length; i++) {
                    a[i] = temp.get(i);
                }
                m.setValue(a);
            }

            // If satisfiable...
            System.out.println("end of the loop");
        }

        String filenames = "/Users/cstevens/Research/chenxi-code/testing/1.als";
        world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filenames);

        // pre-process before running second time

        //second run
        System.out.println("start second run");
        startSolve = System.currentTimeMillis();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Run Second Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            TranslateAlloyToKodkod tatk = new TranslateAlloyToKodkod(A4Reporter.NOP, options, world.getAllReachableSigs(), command);
            tatk.makeFacts(command.formula.and(world.getAllReachableFacts()));
            A4Solution frame = tatk.getFrame();
            Formula f = Formula.and(frame.getFormulas());
            Bounds b = frame.getBounds();
            Options o = convert(frame, options);

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;
            firstTranslation = translation;

            Set<Relation> relat = reMap.keySet();
            String s = relat.toString();

            int add = 0;
            for (Relation rs : b.relations()) {
                if (rs.toString().contains(".")) {
                    for (Relation sr : used) {
                        if (sr.name().equals(rs.name())) {
                            if (reMap.keySet().contains(sr)) {
                                IntSet first = reMap.get(sr);
                                int fMin = first.min();
                                int fMax = first.max();
                                int sMin = translation.primaryVariables(rs).min();
                                add = sMin - fMin;

                                for (int i = 0; i < positive.size(); i++) {
                                    if (positive.get(i) <= fMax && positive.get(i) >= fMin) {
                                        positive.set(i, (positive.get(i) + add));
                                    }
                                }
                            }
                        }
                    }
                }
            }

            ArrayList<Integer> less = new ArrayList<Integer>();
            if (b.relations().size() < used.size()) {
                for (Relation rs : b.relations()) {
                    if (rs.toString().contains(".")) {
                        for (Relation sr : used) {
                            if ((sr.name().equals(rs.name())) && (sr.name().contains("."))) {
                                int[] second = translation.primaryVariables(rs).toArray();
                                for (int i = 0; i < second.length; i++) {
                                    if (positive.contains(second[i])) {
                                        if (second[i] == translation.primaryVariables(rs).min()) {
                                            less.add(translation.primaryVariables(rs).max());
                                        } else {
                                            less.add(second[i]);
                                        }

                                    }
                                }
                            }
                        }
                    }
                }
            }
            if (b.relations().size() >= used.size()) {
                for (Relation rs : b.relations()) {
                    if (rs.toString().contains(".")) {
                        for (Relation sr : used) {
                            if ((!sr.name().equals(rs.name())) && (sr.name().contains("."))) {
                                int[] second = translation.primaryVariables(rs).toArray();
                                for (int i = 0; i < second.length; i++) {
                                    positive.add(second[i]);
                                }
                            }
                        }
                    }
                }
            }

            int[] solved;
            if (b.relations().size() > used.size()) {
                solved = new int[positive.size()];
                for (int q = 0; q < solved.length; q++) {
                    solved[q] = positive.get(q);
                }
            } else {
                solved = new int[less.size()];
                for (int q = 0; q < solved.length; q++) {
                    solved[q] = less.get(q);
                }
            }

            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            cnf.addClause(solved);

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;
            ArrayList<Solution> solutionCollection = new ArrayList<Solution>();

            System.out.println("second solving time is " + translTime);
            int[] notModel = new int[primaryVars];
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                solutionCollection.add(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                }
                System.out.println(sol);
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
            }

            int bbc = 0;
            sol = Solver.unsat(translation, stats);
            translation = null;
        }
    }

}
