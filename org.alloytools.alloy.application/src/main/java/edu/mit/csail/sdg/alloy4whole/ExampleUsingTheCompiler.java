/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A2KConverter;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.Statistics;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntSet;

/**
 * This class demonstrates how to access Alloy4 via the compiler methods.
 */

public final class ExampleUsingTheCompiler {

    /*
     * Execute every command in every file. This method parses every file, then
     * execute every command. If there are syntax or type errors, it may throw a
     * ErrorSyntax or ErrorType or ErrorAPI or ErrorFatal exception. You should
     * catch them and display them, and they may contain filename/line/column
     * information.
     */

    public static void main(String[] args) throws Exception {
        // The visualizer (We will initialize it to nonnull when we visualize an
        // Alloy solution)
        VizGUI viz = null;
        //        String filename, filenames;

        // Alloy4 sends diagnostic messages and progress reports to the
        // A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can
        // extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {

            // For example, here we choose to display each "warning" by printing
            // it to System.out
            @Override
            public void warning(ErrorWarning msg) {
                //                System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                System.out.flush();
            }
        };
        String filename = args[0];
        //        String filename = "/Users/yuchenxi/dsl/Project/Implementation/splmodel/Banking_Machine/b.als";
        //        String filename = "/Users/yuchenxi/Downloads/G-Play/ICC2.als";
        //        String filename = "/Users/yuchenxi/1.als";
        // Parse+typecheck the model
        //        System.out.println("=========== Parsing+Typechecking " + filename + " =============");
        Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

        // Choose some default options for how you want to execute the
        // commands
        A4Options options = new A4Options();

        options.solver = A4Options.SatSolver.SAT4J;

        ArrayList<A4Solution> sols = new ArrayList<A4Solution>();
        ArrayList<Integer> positive = new ArrayList<Integer>();
        ArrayList<Solution> solutionCollection = new ArrayList<Solution>();

        Translation.Whole firstTranslation;
        Bounds firstBounds;

        HashMap<Relation,IntSet> reMap = new HashMap<Relation,IntSet>();
        HashMap<String,Integer> map = new HashMap<String,Integer>();
        HashMap<Integer,String> tupleLow = new HashMap<Integer,String>();
        HashMap<Relation,int[]> ref = new HashMap<Relation,int[]>();

        Set<Relation> used = null;
        ArrayList<String> uAtoms = new ArrayList<String>();
        ArrayList<String> unary = new ArrayList<String>();
        ArrayList<String> lAtoms = new ArrayList<String>();
        ArrayList<String> lunary = new ArrayList<String>();
        Formula formulaSet = null;

        long startSolve = System.currentTimeMillis();

        boolean empty = true;
        StringBuilder sb = new StringBuilder();
        FileWriter writer = new FileWriter("test.csv", true);

        BufferedReader br = new BufferedReader(new FileReader("test.csv"));
        if (br.readLine() != null) {
            empty = false;
        }
        if (empty) {
            String columnNamesList = "specification,Alloy 5 get first solution,Alloy 5 get entire solutions,Titanium adjust bounds,Titanium solving CNF,Titanium get first solution,Titanium get entire solution,Opt adjust bounds,Opt solving CNF,Opt get first solution,Opt get entire solution";
            sb.append(columnNamesList + "\n");
            sb.append("1" + ",");
        } else {
            sb.append("1" + ",");
        }
        //        String columnNamesList = "specification,Alloy 5 get first solution,Alloy 5 get entire solutions,Titanium adjust bounds,Titanium solving CNF,Titanium get first solution,Titanium get entire solution,Opt adjust bounds,Opt solving CNF,Opt get first solution,Opt get entire solution";
        //        sb.append(columnNamesList +"\n");
        //        sb.append("1"+",");

        //first run for Alloy 5
        for (Command command : world.getAllCommands()) {
            // Execute the command
            //            System.out.println("============ Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            A2KConverter a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            Set<Relation> relations = b.relations();
            firstBounds = b;
            used = b.relations();
            Options o = a2K.getOptions();

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;
            firstTranslation = translation;

            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();
            //            System.out.println("first solving time is" + (-startSolve+endSolve));
            //            sb.append(String.valueOf((-startSolve+endSolve))+",");

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;

            int[] notModel = new int[primaryVars];
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();
            int[] track = new int[primaryVars];
            double inf = Double.POSITIVE_INFINITY;
            double min = inf;

            int pos = 1;
            for (Relation re : b.relations()) {
                if (re.toString().contains("this")) {
                    TupleSet atoms = b.upperBound(re);
                    TupleSet lowerA = b.lowerBound(re);
                    for (Object i : atoms) {
                        if (!lowerA.contains(i)) {
                            String head = re.name();
                            String body = "#";
                            String key = head + body + i.toString();
                            map.put(key, pos);
                            tupleLow.put(pos, key);
                            pos++;
                        }
                    }
                }
                if (re.toString().contains(".")) {
                    final IntSet i = translation.primaryVariables(re);
                    reMap.put(re, i);
                    if (min > i.min()) {
                        min = i.min();
                    }
                }
            }
            System.out.println("111");
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
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
            //            System.out.println("set size is " + solutionCollection.size());
            //            sb.append(String.valueOf((-startSolve+endSolve))+",");

            for (int i : notModelHelp) {
                if (i > 0) {
                    positive.add(i);
                }
                for (Map.Entry<String,Integer> m : map.entrySet()) {
                    if (m.getValue() == -i && i < 0) {
                        String key = m.getKey();
                        map.put(key, i);
                    }
                }
            }
        }

        // first run for opt
        startSolve = System.currentTimeMillis();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            //            System.out.println("============ Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            A2KConverter a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            used = b.relations();
            Options o = a2K.getOptions();
            formulaSet = f;

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;

            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();
            //            System.out.println("first solving time is" + (-startSolve+endSolve));

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;

            int[] notModel = new int[primaryVars];
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();

            boolean firstSol = true;
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                solutionCollection.add(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                    int cur = notModel[i - 1];
                    int abs = Math.abs(cur);

                    if (!notModelHelp.contains(cur) && !notModelHelp.contains(-cur)) {
                        notModelHelp.add(cur);
                    }
                    if (notModelHelp.contains(abs) && cur < 0) {
                        int index = notModelHelp.indexOf(abs);
                        notModelHelp.set(index, cur);
                    }
                }
                ArrayList<Integer> help = new ArrayList<Integer>();
                for (int i = 0; i < notModelHelp.size(); i++) {
                    if (notModelHelp.get(i) > 0) {
                        help.add(notModelHelp.get(i));
                    }
                }
                int[] notModel1 = new int[help.size()];
                for (int i = 0; i < help.size(); i++) {
                    notModel1[i] = help.get(i);
                }
                cnf.addClause(notModel1);
                Instance instance = sol.instance();
                for (Relation r : b.relations()) {
                    boolean firstRel = true;
                    if (r.toString().contains("this/") && !r.toString().contains(".")) {
                        String s = instance.tuples(r).toString();
                        s.split(",");
                        String[] split = s.split("\\[+|\\]+");
                        for (String s1 : split) {
                            s1.toString();
                            if (s1.contains(r.toString().split("this/")[1])) {
                                if (!unary.contains(s1)) {
                                    unary.add(s1);
                                }
                            }
                        }
                    }
                    if (r.toString().contains("this/") && r.toString().contains(".")) {
                        String s = instance.tuples(r).toString();
                        String[] split = s.split("\\[+|\\]+");
                        for (String s1 : split) {
                            s1.toString();
                            if (!s1.equals(", ") && !s1.equals("") && instance.tuples(r).toString().contains(s1)) {
                                if (!uAtoms.contains(s1)) {
                                    uAtoms.add(s1);
                                }
                            }
                        }
                    }
                }

                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
                firstSol = false;
            }
            sol = Solver.unsat(translation, stats);
            translation = null;
            //            System.out.println("set size is " + solutionCollection.size());

            // get lower bounds

            for (int i = 1; i < primaryVars; i++) {
                long start = System.currentTimeMillis();
                a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
                f = a2K.getFormula();
                b = a2K.getBounds();
                o = a2K.getOptions();

                translTime = System.currentTimeMillis();
                translation = Translator.translate(f, b, o);
                translTime = System.currentTimeMillis() - translTime;
                startSolve = System.currentTimeMillis();
                cnf = translation.cnf();
                primaryVars = translation.numPrimaryVariables();
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                int[] ad = {
                            -i
                };
                cnf.addClause(ad);

                isSat = cnf.solve();
                if (!isSat) {
                    String s = tupleLow.get(i).split("#")[1];
                    String so = s.toString().split("\\[|\\]")[1];
                    lAtoms.add(so);
                }
            }
        }

        //        String filenames = "/Users/yuchenxi/dsl/Project/Implementation/splmodel/Banking_Machine/hh.als";
        String filenames = args[1];
        //        String filenames = "/Users/yuchenxi/1m.als";
        world = CompUtil.parseEverything_fromFile(rep, null, filenames);

        // pre-process before running second time
        long startsSolve = System.currentTimeMillis();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            A2KConverter a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            used = b.relations();
            Options o = a2K.getOptions();

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;

            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

            boolean isSat = cnf.solve();

            long endSolve = System.currentTimeMillis();
            //            System.out.println("first solving time is" + (-startsSolve+endSolve));
            sb.append(String.valueOf((-startSolve + endSolve)) + ",");
            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;

            int[] notModel = new int[primaryVars];
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();

            boolean e = true;
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                //                solutionCollection.add(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                }
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
            }
            sol = Solver.unsat(translation, stats);
            translation = null;
            //            System.out.println("set size is " + solutionCollection.size());
            sb.append(String.valueOf((-startSolve + System.currentTimeMillis())) + ",");
        }

        // titanium
        startSolve = System.currentTimeMillis();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            //            System.out.println("============ Run Second Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            //            long startSolve = System.currentTimeMillis();

            A2KConverter a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            Options o = a2K.getOptions();

            ArrayList<String> uAtom = new ArrayList<String>();
            ArrayList<String> unarys = new ArrayList<String>();

            long adjTime = System.currentTimeMillis();

            boolean firstSol = true;
            HashMap<String,List<String>> lowers = new HashMap<String,List<String>>();
            for (Solution s : solutionCollection) {
                Instance instance = s.instance();
                for (Relation r : b.relations()) {
                    ArrayList<String> mapTuple = new ArrayList<String>();
                    if (!used.toString().contains(r.name())) {
                        continue;
                    }
                    boolean firstRel = true;
                    ArrayList<String> tep = new ArrayList<String>();
                    ArrayList<String> btep = new ArrayList<String>();
                    if (r.toString().contains("this/") && !r.toString().contains(".")) {
                        String ss = instance.tuples(r.name()).toString();
                        String[] split = ss.split("\\[+|\\]+");
                        for (String s1 : split) {
                            s1.toString();
                            if (s1.contains(r.toString().split("this/")[1])) {
                                if (!unarys.contains(s1)) {
                                    unarys.add(s1);
                                }
                                if (firstSol) {
                                    mapTuple.add(s1);
                                }
                                if (!firstSol) {
                                    tep.add(s1);
                                }
                            }
                        }
                        if (firstSol) {
                            lowers.put(r.name(), mapTuple);
                        }
                        if (!firstSol) {
                            List<String> te = lowers.get(r.name());
                            te.retainAll(tep);
                            lowers.put(r.name(), te);
                        }
                    }
                    if (r.toString().contains("this/") && r.toString().contains(".")) {
                        String ss = instance.tuples(r.name()).toString();
                        String[] split = ss.split("\\[+|\\]+");
                        for (String s1 : split) {
                            s1.toString();
                            if (!s1.equals(", ") && !s1.equals("") && instance.tuples(r.name()).toString().contains(s1)) {
                                if (!uAtom.contains(s1)) {
                                    uAtom.add(s1);
                                }
                                if (firstSol) {
                                    mapTuple.add(s1);
                                }
                                if (!firstSol) {
                                    btep.add(s1);
                                }
                            }
                        }
                        if (firstSol) {
                            lowers.put(r.name(), mapTuple);
                        }
                        if (!firstSol) {
                            List<String> te = lowers.get(r.name());
                            te.retainAll(btep);
                            lowers.put(r.name(), te);
                        }
                    }
                }
                firstSol = false;
            }

            List<String> f2 = Arrays.asList(f.toString().split("\\&&+"));
            List<String> f1 = Arrays.asList(formulaSet.toString().split("\\&&+"));
            ArrayList<Relation> effected = new ArrayList<Relation>();
            ArrayList<Relation> notEffected = new ArrayList<Relation>();

            for (String sf : f2) {
                if (!f1.contains(sf)) {
                    for (Relation r : b.relations()) {
                        if (sf.contains(r.name()) && !effected.contains(r.name())) {
                            effected.add(r);
                        }
                    }
                }
            }
            for (Relation r : b.relations()) {
                if (!effected.contains(r) && r.toString().contains("this/")) {
                    notEffected.add(r);
                }
            }

            Map<Relation,TupleSet> ub = b.upperBoundsM();
            Map<Relation,TupleSet> lb = b.lowerBoundsM();
            if (b.relations().size() <= used.size()) {
                for (Relation r : notEffected) {
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[|\\]")[1];
                            if (unarys.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                    if (r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[+|\\]+")[1];
                            if (uAtom.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                }
            }

            if (b.relations().size() >= used.size()) {
                for (Relation r : notEffected) {
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[|\\]")[1];
                            List<String> atoms = lowers.get(r.name());
                            if (atoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                            //                            if (lunary.contains(split)){
                            //                                newB.add((Tuple) uo);
                            //                            }
                        }
                        lb.put(r, newB);
                    }
                    if (r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[+|\\]+")[1];
                            List<String> atoms = lowers.get(r.name());
                            if (atoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                            //                            if (lAtom.contains(split)){
                            //                                newB.add((Tuple) uo);
                            //                            }
                        }
                        lb.put(r, newB);
                    }
                }
            }

            long endAdj = System.currentTimeMillis();
            //            System.out.println("adjusting bounds time is " + (adjTime-startSolve));
            sb.append(String.valueOf((endAdj - startSolve)) + ",");

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;

            long cnfSolving = System.currentTimeMillis();

            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();
            //            System.out.println("time for getting first sol is "+(endSolve-startSolve));
            sb.append(String.valueOf((-cnfSolving + endSolve)) + ",");
            //            System.out.println("time for cnf solving is" + (endSolve-cnfSolving));
            sb.append(String.valueOf((-startSolve + endSolve)) + ",");

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;

            int[] notModel = new int[primaryVars];

            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                //                solutionCollection.add(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                }
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
            }

            endSolve = System.currentTimeMillis();
            //            System.out.println("time for getting all sol is " + (endSolve-startSolve));
            //            System.out.println(solutionCollection.size());
            sb.append(String.valueOf((-startSolve + endSolve)) + ",");
            sol = Solver.unsat(translation, stats);
            translation = null;
        }

        //second run
        //        System.out.println("start second run");
        startSolve = System.currentTimeMillis();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            //            System.out.println("============ Run Second Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            //            long startSolve = System.currentTimeMillis();

            A2KConverter a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            Options o = a2K.getOptions();

            List<String> f2 = Arrays.asList(f.toString().split("\\&&+"));
            List<String> f1 = Arrays.asList(formulaSet.toString().split("\\&&+"));
            ArrayList<Relation> effected = new ArrayList<Relation>();
            ArrayList<Relation> notEffected = new ArrayList<Relation>();

            for (String sf : f2) {
                if (!f1.contains(sf)) {
                    for (Relation r : b.relations()) {
                        if (sf.contains(r.name()) && !effected.contains(r.name())) {
                            effected.add(r);
                        }
                    }
                }
            }
            for (Relation r : b.relations()) {
                if (!effected.contains(r) && r.toString().contains("this/")) {
                    notEffected.add(r);
                }
            }

            Map<Relation,TupleSet> lb = b.lowerBoundsM();
            Map<Relation,TupleSet> ub = b.upperBoundsM();
            if (b.relations().size() <= used.size()) {
                for (Relation r : notEffected) {
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[|\\]")[1];
                            if (unary.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                    if (r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[+|\\]+")[1];
                            if (uAtoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                }
            }
            if (b.relations().size() >= used.size()) {
                for (Relation r : notEffected) {
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[|\\]")[1];
                            if (lAtoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        lb.put(r, newB);
                    }
                    if (r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        for (Object uo : t) {
                            String split = uo.toString().split("\\[+|\\]+")[1];
                            if (lAtoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        lb.put(r, newB);
                    }
                }
            }

            //            System.out.println("time for adjust bounds is " + (System.currentTimeMillis() - startSolve));
            sb.append(String.valueOf((-startSolve + System.currentTimeMillis())) + ",");

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;
            firstTranslation = translation;

            long cnfT = System.currentTimeMillis();
            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());


            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();
            //            System.out.println("time for get first solution is " + (endSolve-startSolve));
            sb.append(String.valueOf((-cnfT + endSolve)) + ",");
            //            System.out.println("time for cnf solving is " + (endSolve-cnfT));
            sb.append(String.valueOf((-startSolve + endSolve)) + ",");

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;

            int[] notModel = new int[primaryVars];
            Solution sool;
            //sool = Solution.satisfiable(stats, translation.interpret());

            while (isSat) {
                //sol = Solution.satisfiable(stats, translation.interpret());
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                }
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
            }
            //            System.out.println("time for get all solution is" + (System.currentTimeMillis() - startSolve));
            sb.append(String.valueOf((-startSolve + System.currentTimeMillis())));
            sb.append('\n');
            writer.write(sb.toString());
            writer.close();
            sol = Solver.unsat(translation, stats);
            translation = null;
        }
    }

}
