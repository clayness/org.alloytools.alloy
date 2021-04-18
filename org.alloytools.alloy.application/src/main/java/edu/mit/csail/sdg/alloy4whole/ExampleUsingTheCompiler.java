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
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

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
        //        String filename = "/Users/yuchenxi/dsl/Project/Implementation/splmodel/Banking_Machine/hh.als";
        //        String filename = "/Users/yuchenxi/Downloads/G-Play/ICC2.als";
        //        String filename = "/Users/yuchenxi/1m.als";
        // Parse+typecheck the model
        //        System.out.println("=========== Parsing+Typechecking " + filename + " =============");
        Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

        // Choose some default options for how you want to execute the
        // commands
        A4Options options = new A4Options();
        options.symmetry = 0;

        options.solver = A4Options.SatSolver.SAT4J;

        Translation.Whole firstTranslation;
        Bounds firstBounds;

        ArrayList<Solution> ori = new ArrayList<Solution>();
        ArrayList<Solution> revised = new ArrayList<Solution>();

        Set<Relation> used = null;
        ArrayList<String> uAtomsForOpt = new ArrayList<String>();
        ArrayList<String> unaryForOpt = new ArrayList<String>();
        HashMap<String,List<String>> lowerForOpt = new HashMap<String,List<String>>();

        ArrayList<Integer> ubForT = new ArrayList<Integer>();
        ArrayList<Integer> lbForT = new ArrayList<Integer>();


        ArrayList<String> uAtoms = new ArrayList<String>();
        ArrayList<String> unary = new ArrayList<String>();
        HashMap<String,List<String>> lowerForT = new HashMap<String,List<String>>();
        long overheadT = 0;
        Formula formulaSet = null;

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

        // prime the solver, just to make sure there's no startup costs in the time
        A2KConverter p = new A2KConverter(world, rep, world.getAllReachableSigs(), world.getAllCommands().get(0), options);
        Translation.Whole pt = Translator.translate(p.getFormula(), p.getBounds(), p.getOptions());
        pt.cnf().solve();
        pt.cnf().free();

        //first run for Alloy 5
        long startSolve = System.currentTimeMillis();
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


            boolean firstSol = true;
            long time = 0;
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                long tts = System.currentTimeMillis();
                ArrayList<Integer> notModelH = new ArrayList<Integer>();
                //                Instance instance = sol.instance();
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                    int cur = notModel[i - 1];
                    if (cur < 0 && !ubForT.contains(cur)) {
                        ubForT.add(cur);
                    }
                    if (cur < 0 && firstSol) {
                        lbForT.add(cur);
                    }
                    if (cur < 0 && !firstSol) {
                        notModelH.add(cur);
                    }
                }
                if (!firstSol) {
                    lbForT.retainAll(notModelH);
                }
                time = time + System.currentTimeMillis() - tts;
                //                for (Relation r:b.relations()){
                //                    ArrayList<String> mapTuple = new ArrayList<String>();
                //                    boolean firstRel = true;
                //                    ArrayList<String> tep = new ArrayList<String>();
                //                    ArrayList<String> btep = new ArrayList<String>();
                //
                //                    if (r.toString().contains("this/") && !r.toString().contains(".")){
                //                        TupleSet tuples = instance.tuples(r);
                //                        for (Object s1 : tuples){
                //                            String tu = s1.toString();
                //                            if (!unary.contains(tu)){
                //                                unary.add(tu);
                //                            }
                //                            if (firstSol){
                //                                mapTuple.add(tu);
                //                            }
                //                            if (!firstSol){
                //                                tep.add(tu);
                //                            }
                //                        }
                //                        if (firstSol){
                //                            lowerForT.put(r.name(),mapTuple);
                //                        }
                //                        if (!firstSol){
                //                            List<String> te = lowerForT.get(r.name());
                //                            te.retainAll(tep);
                //                            lowerForT.put(r.name(),te);
                //                        }
                //                    }
                //                    if (r.toString().contains("this/") && r.toString().contains(".")){
                //                        TupleSet tuples = instance.tuples(r);
                //                        for (Object s1 : tuples){
                //                            String tu = s1.toString();
                //                            if (!s1.equals(", ") && !s1.equals("") && instance.tuples(r).toString().contains(tu)){
                //                                if (!uAtoms.contains(tu)){
                //                                    uAtoms.add(tu);
                //                                }
                //                                if (firstSol){
                //                                    mapTuple.add(tu);
                //                                }
                //                                if (!firstSol){
                //                                    btep.add(tu);
                //                                }
                //                            }
                //                        }
                //                        if (firstSol){
                //                            lowerForT.put(r.name(),mapTuple);
                //                        }
                //                        if (!firstSol){
                //                            List<String> te = lowerForT.get(r.name());
                //                            te.retainAll(btep);
                //                            lowerForT.put(r.name(),te);
                //                        }
                //                    }
                //                }
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
                firstSol = false;
            }
            long tr = System.currentTimeMillis();
            int pos = 1;
            for (Relation r : b.relations()) {
                List<String> tup = new ArrayList<String>();
                if (r.name().contains("this") && b.upperBound(r).size() != b.lowerBound(r).size()) {
                    TupleSet lowerTuple = b.upperBound(r);
                    for (Object obj : lowerTuple) {
                        if (lbForT.contains(-pos)) {
                            tup.add(obj.toString());
                        }
                        if (ubForT.contains(-pos) && !obj.toString().contains(",")) {
                            unary.add(obj.toString());
                        }
                        if (ubForT.contains(-pos) && obj.toString().contains(",")) {
                            uAtoms.add(obj.toString());
                        }
                        pos++;
                    }
                    lowerForT.put(r.name(), tup);
                }
                if (r.name().contains("this") && b.upperBound(r).size() == b.lowerBound(r).size()) {
                    TupleSet lowerTuple = b.upperBound(r);
                    for (Object obj : lowerTuple) {
                        tup.add(obj.toString());
                        if (!obj.toString().contains(",")) {
                            unary.add(obj.toString());
                        }
                        if (obj.toString().contains(",")) {
                            uAtoms.add(obj.toString());
                        }
                    }
                    lowerForT.put(r.name(), tup);
                }
            }
            time = time + System.currentTimeMillis() - tr;

            overheadT = time;
            System.out.println("overheadT is " + overheadT);
            sol = Solver.unsat(translation, stats);
            translation = null;
            //            System.out.println("upper bounds(!unary) from Titanium "+unary.size());
            //            System.out.println("upper bounds from(unary) Titanium "+uAtoms.size());
            //            System.out.println("lower bounds from Titanium "+lowerForT.size());
            //            System.out.println("------------------------------------------");
            //            System.out.println("set size is " + solutionCollection.size());
            //            sb.append(String.valueOf((-startSolve+endSolve))+",");

        }

        // first run for opt
        ArrayList<Integer> ubForOpt = new ArrayList<Integer>();
        ArrayList<Integer> lbForOpt = new ArrayList<Integer>();
        startSolve = System.currentTimeMillis();
        long adT = System.currentTimeMillis();
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
            long time = 0;
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                long tts = System.currentTimeMillis();
                ArrayList<Integer> notModelH = new ArrayList<Integer>();
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
                    if (cur < 0 && !ubForT.contains(cur)) {
                        ubForOpt.add(cur);
                    }
                    if (cur < 0 && firstSol) {
                        lbForOpt.add(cur);
                    }
                    if (cur < 0 && !firstSol) {
                        notModelH.add(cur);
                    }
                }
                if (!firstSol) {
                    lbForOpt.retainAll(notModelH);
                }
                time = time + System.currentTimeMillis() - tts;
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
                //                Instance instance = sol.instance();
                //                for (Relation r : b.relations()){
                //                    ArrayList<String> mapTuple = new ArrayList<String>();
                //                    boolean firstRel = true;
                //                    ArrayList<String> tep = new ArrayList<String>();
                //                    ArrayList<String> btep = new ArrayList<String>();
                //
                //                    if (r.toString().contains("this/") && !r.toString().contains(".")){
                ////                        String s = instance.tuples(r).toString();
                ////                        s.split(",");
                ////                        String[] split = s.split("\\[+|\\]+");
                //                        TupleSet tuples = instance.tuples(r);
                //                        for (Object s1 : tuples){
                //                            String tu = s1.toString();
                //                            if (!unaryForOpt.contains(tu)){
                //                                unaryForOpt.add(tu);
                //                            }
                //                            if (firstSol){
                //                                mapTuple.add(tu);
                //                            }
                //                            if (!firstSol){
                //                                tep.add(tu);
                //                            }
                //                        }
                //                        if (firstSol){
                //                            lowerForOpt.put(r.name(),mapTuple);
                //                        }
                //                        if (!firstSol){
                //                            List<String> te = lowerForOpt.get(r.name());
                //                            te.retainAll(tep);
                //                            lowerForOpt.put(r.name(),te);
                //                        }
                //                    }
                //                    if (r.toString().contains("this/") && r.toString().contains(".")){
                ////                        String s = instance.tuples(r).toString();
                ////                        String[] split = s.split("\\[+|\\]+");
                //                        TupleSet tuples = instance.tuples(r);
                //                        for (Object s1 : tuples){
                //                            String tu = s1.toString();
                //                            if (!tu.equals(", ") && !tu.equals("") && instance.tuples(r).toString().contains(tu)){
                //                                if (!uAtomsForOpt.contains(tu)){
                //                                    uAtomsForOpt.add(tu);
                //                                }
                //                                if (firstSol){
                //                                    mapTuple.add(tu);
                //                                }
                //                                if (!firstSol){
                //                                    btep.add(tu);
                //                                }
                //                            }
                //                        }
                //                        if (firstSol){
                //                            lowerForOpt.put(r.name(),mapTuple);
                //                        }
                //                        if (!firstSol){
                //                            List<String> te = lowerForOpt.get(r.name());
                //                            te.retainAll(btep);
                //                            lowerForOpt.put(r.name(),te);
                //                        }
                //                    }
                //                }
                //                tts = System.currentTimeMillis()-tts;
                //                time = time + tts;
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
                firstSol = false;
            }
            long tr = System.currentTimeMillis();
            int pos = 1;
            for (Relation r : b.relations()) {
                List<String> tup = new ArrayList<String>();
                if (r.name().contains("this") && b.upperBound(r).size() != b.lowerBound(r).size()) {
                    TupleSet lowerTuple = b.upperBound(r);
                    for (Object obj : lowerTuple) {
                        if (lbForOpt.contains(-pos)) {
                            tup.add(obj.toString());
                        }
                        if (ubForOpt.contains(-pos) && !obj.toString().contains(",")) {
                            unaryForOpt.add(obj.toString());
                        }
                        if (ubForOpt.contains(-pos) && obj.toString().contains(",")) {
                            uAtomsForOpt.add(obj.toString());
                        }
                        pos++;
                    }
                    lowerForOpt.put(r.name(), tup);
                }
                if (r.name().contains("this") && b.upperBound(r).size() == b.lowerBound(r).size()) {
                    TupleSet lowerTuple = b.upperBound(r);
                    for (Object obj : lowerTuple) {
                        tup.add(obj.toString());
                        if (!obj.toString().contains(",")) {
                            unaryForOpt.add(obj.toString());
                        }
                        if (obj.toString().contains(",")) {
                            uAtomsForOpt.add(obj.toString());
                        }
                    }
                    lowerForOpt.put(r.name(), tup);
                }
            }
            time = time + System.currentTimeMillis() - tr;
            //            System.out.println("overhead for optimization is" + time);
            //            System.out.println("upper bounds(!unary) from Titanium "+unaryForOpt.size());
            //            System.out.println("upper bounds from(unary) Titanium "+uAtomsForOpt.size());
            //            System.out.println("lower bounds from Titanium "+lowerForOpt.size());
            adT = time;
            System.out.println("overhead for optimization is" + adT);
            sol = Solver.unsat(translation, stats);
            translation = null;

            //            System.out.println("set size is " + solutionCollection.size());

            // get lower bounds

            //            for (int i = 1; i < primaryVars; i++){
            //                long start = System.currentTimeMillis();
            //                a2K = new A2KConverter(world,rep,world.getAllReachableSigs(),command,options);
            //                f = a2K.getFormula();
            //                b = a2K.getBounds();
            //                o = a2K.getOptions();
            //
            //                translTime = System.currentTimeMillis();
            //                translation = Translator.translate(f,b,o);
            //                translTime = System.currentTimeMillis() - translTime;
            //                startSolve = System.currentTimeMillis();
            //                cnf = translation.cnf();
            //                primaryVars = translation.numPrimaryVariables();
            //                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
            //                int[] ad = {-i};
            //                cnf.addClause(ad);
            //
            //                isSat = cnf.solve();
            //                if (!isSat){
            //                    String s = tupleLow.get(i).split("#")[1];
            //                    String so = s.toString().split("\\[|\\]")[1];
            //                    lAtoms.add(so);
            //                }
            //            }
        }
        options.symmetry = 20;

        //        String filenames = "/Users/yuchenxi/dsl/Project/Implementation/splmodel/Banking_Machine/b.als";
        String filenames = args[1];
        //        String filenames = "/Users/yuchenxi/1m.als";
        world = CompUtil.parseEverything_fromFile(rep, null, filenames);

        // second time Alloy
        startSolve = System.currentTimeMillis();
        ArrayList<Solution> ss = new ArrayList<Solution>();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            A2KConverter a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            //used = b.relations();
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

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;
            sol = Solution.satisfiable(stats, translation.interpret());
            sb.append(String.valueOf((-startSolve + System.currentTimeMillis())) + ",");

            int[] notModel = new int[primaryVars];
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();

            boolean e = true;

            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                ss.add(sol);
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
            System.out.println("solution set size is " + ss.size());
            sb.append(String.valueOf((-startSolve + System.currentTimeMillis())) + ",");
        }

        // titanium
        startSolve = System.currentTimeMillis();
        //        options.symmetry=0;
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

            //            ArrayList<String> uAtom = new ArrayList<String>();
            //            ArrayList<String> unarys = new ArrayList<String>();

            long adjTime = System.currentTimeMillis();

            boolean firstSol = true;
            HashMap<String,List<String>> lowers = new HashMap<String,List<String>>();
            //            long time = System.currentTimeMillis();
            //            for (Solution s : solutionCollection){
            //                Instance instance = s.instance();
            //                for (Relation r : b.relations()){
            //                    ArrayList<String> mapTuple = new ArrayList<String>();
            //                    if (!used.toString().contains(r.name())){
            //                        continue;
            //                    }
            //                    boolean firstRel = true;
            //                    ArrayList<String> tep = new ArrayList<String>();
            //                    ArrayList<String> btep = new ArrayList<String>();
            //                    if (r.toString().contains("this/") && !r.toString().contains(".")){
            //                        String ss = instance.tuples(r.name()).toString();
            //                        String[] split = ss.split("\\[+|\\]+");
            //                        for (String s1 : split){
            //                            s1.toString();
            //                            if (s1.contains(r.toString().split("this/")[1])){
            //                                if (!unarys.contains(s1)){
            //                                    unarys.add(s1);
            //                                }
            //                                if (firstSol){
            //                                    mapTuple.add(s1);
            //                                }
            //                                if (!firstSol){
            //                                    tep.add(s1);
            //                                }
            //                            }
            //                        }
            //                        if (firstSol){
            //                            lowers.put(r.name(),mapTuple);
            //                        }
            //                        if (!firstSol){
            //                            List<String> te = lowers.get(r.name());
            //                            te.retainAll(tep);
            //                            lowers.put(r.name(),te);
            //                        }
            //                    }
            //                    if (r.toString().contains("this/") && r.toString().contains(".") ){
            //                        String ss = instance.tuples(r.name()).toString();
            //                        String[] split = ss.split("\\[+|\\]+");
            //                        for (String s1 : split){
            //                            s1.toString();
            //                            if (!s1.equals(", ") && !s1.equals("") && instance.tuples(r.name()).toString().contains(s1)){
            //                                if (!uAtom.contains(s1)){
            //                                    uAtom.add(s1);
            //                                }
            //                                if (firstSol){
            //                                    mapTuple.add(s1);
            //                                }
            //                                if (!firstSol){
            //                                    btep.add(s1);
            //                                }
            //                            }
            //                        }
            //                        if (firstSol){
            //                            lowers.put(r.name(),mapTuple);
            //                        }
            //                        if (!firstSol){
            //                            List<String> te = lowers.get(r.name());
            //                            te.retainAll(btep);
            //                            lowers.put(r.name(),te);
            //                        }
            //                    }
            //                }
            //                firstSol = false;
            //            }
            //            time = System.currentTimeMillis()-time;
            //            System.out.println("time is "+time);

            List<String> f2 = Arrays.asList(f.toString().split("\\&&+"));
            List<String> f1 = Arrays.asList(formulaSet.toString().split("\\&&+"));
            ArrayList<Relation> effected = new ArrayList<Relation>();
            ArrayList<Relation> notEffected = new ArrayList<Relation>();

            //            for (String sf : f2){
            //                if (!f1.contains(sf)){
            //                    for (Relation r : b.relations()){
            //                        if (sf.contains(r.name()) && !effected.contains(r.name())){
            //                            effected.add(r);
            //                        }
            //                    }
            //                }
            //            }
            //            for (Relation r : b.relations()){
            //                if (!effected.contains(r) && r.toString().contains("this/")){
            //                    notEffected.add(r);
            //                }
            //            }

            Map<Relation,TupleSet> ub = b.upperBoundsM();
            Map<Relation,TupleSet> lb = b.lowerBoundsM();
            if (b.relations().size() < used.size()) {

                for (String sf : f1) {
                    if (!f2.contains(sf)) {
                        for (Relation r : b.relations()) {
                            if (sf.contains(r.name()) && !effected.contains(r)) {
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

                for (Relation r : notEffected) {
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            //                            String split = uo.toString().split("\\[|\\]")[1];
                            String split = uo.toString();
                            if (unary.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                    if (r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        for (Object uo : t) {
                            //                            String split = uo.toString().split("\\[+|\\]+")[1];
                            String split = uo.toString();
                            if (uAtoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                }
            }

            if (b.relations().size() >= used.size()) {

                for (String sf : f2) {
                    if (!f1.contains(sf)) {
                        for (Relation r : b.relations()) {
                            if (sf.contains(r.name()) && !effected.contains(r)) {
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

                for (Relation r : notEffected) {
                    if (!lowerForT.keySet().contains(r.name())) {
                        continue;
                    }
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            //                            String split = uo.toString().split("\\[|\\]")[1];
                            String split = uo.toString();
                            List<String> atoms = lowerForT.get(r.name());
                            if (atoms.size() != 0 && atoms.contains(split)) {
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
                            //                            String split = uo.toString().split("\\[+|\\]+")[1];
                            String split = uo.toString();
                            List<String> atoms = lowerForT.get(r.name());
                            if (atoms.size() != 0 && atoms.contains(split)) {
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
            sb.append(String.valueOf((endAdj - startSolve + overheadT)) + ",");

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
            sb.append(String.valueOf(-cnfSolving + endSolve) + ",");
            //            System.out.println("time for cnf solving is" + (endSolve-cnfSolving));
            sb.append(String.valueOf((-startSolve + endSolve + overheadT)) + ",");

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;

            int[] notModel = new int[primaryVars];

            ArrayList<Solution> as = new ArrayList<Solution>();
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                as.add(sol);
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
            System.out.println("titanium solution sieze " + as.size());
            sb.append(String.valueOf(overheadT - startSolve + endSolve) + ",");
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

            //            for (String sf : f2){
            //                if (!f1.contains(sf)){
            //                    for (Relation r : b.relations()){
            //                        if (sf.contains(r.name()) && !effected.contains(r.name())){
            //                            effected.add(r);
            //                        }
            //                    }
            //                }
            //            }
            //            for (Relation r : b.relations()){
            //                if (!effected.contains(r) && r.toString().contains("this/")){
            //                    notEffected.add(r);
            //                }
            //            }

            Map<Relation,TupleSet> lb = b.lowerBoundsM();
            Map<Relation,TupleSet> ub = b.upperBoundsM();
            if (b.relations().size() < used.size()) {
                for (String sf : f1) {
                    if (!f2.contains(sf)) {
                        for (Relation r : b.relations()) {
                            if (sf.contains(r.name()) && !effected.contains(r)) {
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

                for (Relation r : notEffected) {
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            //                            String split = uo.toString().split("\\[|\\]")[1];
                            String split = uo.toString();
                            if (unaryForOpt.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                    if (r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        for (Object uo : t) {
                            //                            String split = uo.toString().split("\\[+|\\]+")[1];
                            String split = uo.toString();
                            if (uAtomsForOpt.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        ub.put(r, newB);
                    }
                }
            }
            if (b.relations().size() >= used.size()) {

                for (String sf : f2) {
                    if (!f1.contains(sf)) {
                        for (Relation r : b.relations()) {
                            if (sf.contains(r.name()) && !effected.contains(r)) {
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

                for (Relation r : notEffected) {
                    if (!lowerForOpt.keySet().contains(r.name())) {
                        continue;
                    }
                    TupleSet newB = new TupleSet(b.universe(), r.arity());
                    if (!r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        String relN = r.name().toString().split("this/")[1];
                        for (Object uo : t) {
                            //                            String split = uo.toString().split("\\[|\\]")[1];
                            String split = uo.toString();
                            List<String> atoms = lowerForOpt.get(r.name());
                            if (atoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        lb.put(r, newB);
                    }
                    if (r.name().toString().contains(".")) {
                        TupleSet t = ub.get(r);
                        for (Object uo : t) {
                            //                            String split = uo.toString().split("\\[+|\\]+")[1];
                            String split = uo.toString();
                            List<String> atoms = lowerForOpt.get(r.name());
                            if (atoms.contains(split)) {
                                newB.add((Tuple) uo);
                            }
                        }
                        lb.put(r, newB);
                    }
                }
            }

            //            System.out.println("time for adjust bounds is " + (System.currentTimeMillis() - startSolve));
            sb.append(String.valueOf(-startSolve + System.currentTimeMillis() + adT) + ",");

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
            sb.append(String.valueOf((-startSolve + endSolve + adT)) + ",");

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;

            int[] notModel = new int[primaryVars];
            Solution sool;
            //sool = Solution.satisfiable(stats, translation.interpret());

            ArrayList<Solution> as = new ArrayList<Solution>();
            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                as.add(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                }
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
            }
            //            System.out.println("time for get all solution is" + (System.currentTimeMillis() - startSolve));
            System.out.println("opt solution size is" + as.size());
            sb.append(String.valueOf(-startSolve + System.currentTimeMillis() + adT));
            sb.append('\n');
            writer.write(sb.toString());
            writer.close();
            sol = Solver.unsat(translation, stats);
            translation = null;
        }
    }

}
