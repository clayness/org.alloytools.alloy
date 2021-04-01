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

import java.util.ArrayList;
import java.util.HashMap;
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
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntSet;

//import org.alloytools.alloy.core.src.man.java.edu.mit.csail.sdg.alloy4.A4Reporter;

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
                System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                System.out.flush();
            }
        };
        String filename = args[1];
        //        String filename = "/Users/yuchenxi/Downloads/G-Play/ICC2.als";
        // Parse+typecheck the model
        System.out.println("=========== Parsing+Typechecking " + filename + " =============");
        Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

        // Choose some default options for how you want to execute the
        // commands
        A4Options options = new A4Options();

        options.solver = A4Options.SatSolver.SAT4J;

        ArrayList<A4Solution> sols = new ArrayList<A4Solution>();
        ArrayList<Integer> positive = new ArrayList<Integer>();

        Translation.Whole firstTranslation;
        Bounds firstBounds;

        HashMap<Relation,IntSet> reMap = new HashMap<Relation,IntSet>();
        HashMap<String,Integer> map = new HashMap<String,Integer>();
        HashMap<Relation,int[]> ref = new HashMap<Relation,int[]>();

        Set<Relation> used = null;
        ArrayList<String> lowb = new ArrayList<String>();

        long startSolve = System.currentTimeMillis();

        //first run
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Command " + command + ": ============");

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
            System.out.println("first solving time is" + (-startSolve + endSolve));

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;
            ArrayList<Solution> solutionCollection = new ArrayList<Solution>();

            System.out.println("first translation time is" + translTime);

            int[] notModel = new int[primaryVars];
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();
            int[] track = new int[primaryVars];
            double inf = Double.POSITIVE_INFINITY;
            double min = inf;

            int pos = 1;
            for (Relation re : b.relations()) {
                if (re.toString().contains("this") && b.lowerBound(re).size() != b.upperBound(re).size()) {
                    TupleSet atoms = b.upperBound(re);
                    for (Object i : atoms) {
                        lowb.add(i.toString());
                        map.put(i.toString(), pos);

                        Translation.Whole translationForlow;
                        translationForlow = Translator.translate(f, b, o);
                        SATSolver cnfForLow = translationForlow.cnf();
                        translationForlow.options().reporter().solvingCNF(primaryVars, cnfForLow.numberOfVariables(), cnfForLow.numberOfClauses());


                        int[] not = {
                                     -pos
                        };
                        cnfForLow.addClause(not);
                        translationForlow.options().reporter().solvingCNF(primaryVars, cnfForLow.numberOfVariables(), cnfForLow.numberOfClauses());
                        boolean sat = cnfForLow.solve();
                        if (sat) {
                            lowb.remove(i.toString());
                        }

                        pos++;
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

            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                solutionCollection.add(sol);
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
            System.out.println("set size is " + solutionCollection.size());


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


            // can delete
            //            for (Map.Entry<Relation,int[]> m : map.entrySet()){
            //                ArrayList<Integer> temp = new ArrayList<Integer>();
            //                for (int i : positive){
            //                    int[] b1 = m.getValue();
            ////                    if (Arrays.asList(b1).contains(i)){
            ////                        temp.add(i);
            ////                    }
            //                    for (int i1 : b1){
            //                        if (i1 == i){
            //                            temp.add(i);
            //                        }
            //                    }
            //                }
            //                int[] a = new int[temp.size()];
            //                for (int i = 0; i < a.length;i++){
            //                    a[i] = temp.get(i);
            //                }
            //                m.setValue(a);
            //            }
        }

        //String filenames = "/Users/yuchenxi/dsl/Project/Implementation/splmodel/Banking_Machine/b.als";
        String filenames = args[2];
        world = CompUtil.parseEverything_fromFile(rep, null, filenames);

        // pre-process before running second time


        //second run
        System.out.println("start second run");
        startSolve = System.currentTimeMillis();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Run Second Command " + command + ": ============");

            Translation.Whole translation;
            long translTime;

            //            long startSolve = System.currentTimeMillis();

            A2KConverter a2K = new A2KConverter(world, rep, world.getAllReachableSigs(), command, options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            Options o = a2K.getOptions();

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f, b, o);
            translTime = System.currentTimeMillis() - translTime;

            Set<Relation> relat = reMap.keySet();
            String s = relat.toString();

            long adjTime = System.currentTimeMillis();
            int add = 0;
            ArrayList<Integer> less = new ArrayList<Integer>();
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
            int pos1 = 1;
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();
            //            for (Relation rs : b.relations()){
            //                if (rs.toString().contains("this")){
            //                    TupleSet atoms = b.upperBound(rs);
            //                    for (Object i : atoms){
            //                        if (map.containsKey(i.toString()) && map.get(i.toString()) > 0  && i.toString().contains(",")){
            //                            notModelHelp.add(pos1);
            //                        }
            //                        if (!map.containsKey(i.toString()) && i.toString().contains(",")){
            //                            notModelHelp.add(pos1);
            //                        }
            //                        pos1++;
            //                    }
            //                }
            //            }

            Map<Relation,TupleSet> lb = b.lowerBounds();
            if (b.relations().size() >= used.size()) {
                for (Relation rs : b.relations()) {
                    TupleSet newB = new TupleSet(b.universe(), rs.arity());
                    if (rs.toString().contains("this") && b.lowerBound(rs).size() != b.upperBound(rs).size()) {
                        TupleSet atoms = b.upperBound(rs);
                        for (Object i : atoms) {
                            if (map.containsKey(i.toString()) && map.get(i.toString()) > 0 && i.toString().contains(",")) {
                                notModelHelp.add(pos1);
                            }
                            if (!map.containsKey(i.toString()) && i.toString().contains(",")) {
                                notModelHelp.add(pos1);
                            }
                            pos1++;
                            if (lowb.contains(i.toString())) {
                                newB.add((Tuple) i);
                            }
                        }
                    }
                    lb.put(rs, newB);
                }
            }

            int pos2 = 1;
            if (b.relations().size() < used.size()) {
                for (Relation rs : b.relations()) {
                    if (rs.toString().contains("this") && b.upperBound(rs).size() != b.lowerBound(rs).size()) {
                        TupleSet atoms = b.upperBound(rs);
                        for (Object i : atoms) {
                            if (map.containsKey(i.toString()) && map.get(i.toString()) > 0 && i.toString().contains(",")) {
                                notModelHelp.add(pos2);
                            }
                            if (!map.containsKey(i.toString()) && i.toString().contains(",")) {
                                notModelHelp.add(pos2);
                            }
                            pos2++;
                        }
                    }
                }
            }

            //            if (b.relations().size() < used.size()){
            //                for (Relation rs : b.relations()){
            //                    if (rs.toString().contains(".")){
            //                        for (Relation sr : used){
            //                            if (sr.name().equals(rs.name())){
            //                                if (reMap.keySet().contains(sr)){
            //                                    IntSet first = reMap.get(sr);
            //                                    int fMin = first.min();
            //                                    int fMax = first.max();
            //                                    int sMin = translation.primaryVariables(rs).min();
            //                                    add = sMin - fMin;
            //                                    if (positive.size()>0){
            //                                        for (int i = 0; i < positive.size();i++){
            //                                            if (positive.get(i) <= fMax && positive.get(i)  >= fMin){
            //                                                positive.set(i, (positive.get(i)+add));
            //                                            }
            //                                        }
            //                                    }
            //                                }
            //
            //                                int[] second = translation.primaryVariables(rs).toArray();
            //                                if (positive.size()>0){
            //                                    for (int i = 0; i < second.length; i++){
            //                                        if (positive.contains(second[i])){
            //                                            if (second[i] == translation.primaryVariables(rs).min()){
            //                                                less.add(translation.primaryVariables(rs).max());
            //                                            }else {
            //                                                less.add(second[i]);
            //                                            }
            //                                        }
            //                                    }
            //                                }
            //                            }
            //                        }
            //                    }
            //                }
            //            }

            //            if (b.relations().size() < used.size()){
            //                for (Relation rs : b.relations()){
            //                    if (rs.toString().contains(".")){
            //                        for (Relation sr : used){
            //                            if ((sr.name().equals(rs.name())) && (sr.name().contains("."))){
            //                                int[] second = translation.primaryVariables(rs).toArray();
            //                                for (int i = 0; i < second.length; i++){
            //                                    if (positive.contains(second[i])){
            //                                        if (second[i] == translation.primaryVariables(rs).min()){
            //                                            less.add(translation.primaryVariables(rs).min());
            //                                        }else {
            //                                            less.add(second[i]);
            //                                        }
            //
            //                                    }
            //                                }
            //                            }
            //                        }
            //                    }
            //                }
            //            }


            //            if (b.relations().size() >= used.size()){
            //                for (Relation rs : b.relations()){
            //                    if (rs.toString().contains(".")){
            //                        for (Relation sr : used){
            //                            if ((!sr.name().equals(rs.name())) && (sr.name().contains("."))){
            //                                int[] second = translation.primaryVariables(rs).toArray();
            //                                for (int i = 0; i < second.length; i++){
            //                                    positive.add(second[i]);
            //                                }
            //                            }
            //                        }
            //                    }
            //                }
            //            }


            //            if (b.relations().size() > used.size()){
            //                for (Relation rs : b.relations()){
            //                    if (rs.toString().contains(".")){
            //                        for (Relation sr : used){
            //                            if (sr.name().equals(rs.name())){
            //                                if (reMap.keySet().contains(sr)){
            //                                    IntSet first = reMap.get(sr);
            //                                    int fMin = first.min();
            //                                    int fMax = first.max();
            //                                    int sMin = translation.primaryVariables(rs).min();
            //                                    add = sMin - fMin;
            //
            //                                    for (int i = 0; i < positive.size();i++){
            //                                        if (positive.get(i) <= fMax && positive.get(i)  >= fMin){
            //                                            positive.set(i, (positive.get(i)+add));
            //                                        }
            //                                    }
            //                                }
            //                            }
            //                            if ((!sr.name().equals(rs.name())) && (sr.name().contains("."))){
            //                                int[] second = translation.primaryVariables(rs).toArray();
            //                                for (int i = 0; i < second.length; i++){
            //                                    positive.add(second[i]);
            //                                }
            //                            }
            //                        }
            //                    }
            //                }
            //            }

            //            int[] solved;
            //            if (b.relations().size() > used.size()){
            //                solved = new int[positive.size()];
            //                for (int q = 0; q < solved.length; q++){
            //                    solved[q] = positive.get(q);
            //                }
            //            }else{
            //                solved = new int[less.size()];
            //                for (int q = 0; q < solved.length; q++){
            //                    solved[q] = less.get(q);
            //                }
            //            }
            int[] solved = new int[notModelHelp.size()];
            for (int i = 0; i < notModelHelp.size(); i++) {
                solved[i] = notModelHelp.get(i);
            }

            long endAdj = System.currentTimeMillis();
            System.out.println("bounds adjustment time is " + (endAdj - adjTime));

            long cnfSolvingTime = System.currentTimeMillis();
            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            cnf.addClause(solved);

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());


            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();
            System.out.println("second solving time for getting first solution is" + (-startSolve + endSolve));
            System.out.println("cnf solving time is " + (endSolve - cnfSolvingTime));

            //            startSolve = System.currentTimeMillis();

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;
            ArrayList<Solution> solutionCollection = new ArrayList<Solution>();

            //            System.out.println("second translation time is" + translTime);
            //            System.out.println(stats);


            int[] notModel = new int[primaryVars];
            Solution sool;
            sool = Solution.satisfiable(stats, translation.interpret());

            while (isSat) {
                sol = Solution.satisfiable(stats, translation.interpret());
                solutionCollection.add(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                }
                cnf.addClause(notModel);
                //solve next one
                translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
                isSat = cnf.solve();
            }
            //            System.out.println("instance sets is " + solutionCollection.size());
            endSolve = System.currentTimeMillis();
            System.out.println("time for getting all solution is " + (endSolve - startSolve));
            sol = Solver.unsat(translation, stats);
            translation = null;
            //            System.out.println(solutionCollection);



            //            A4Solution ans = TranslateAlloyToKodkod.execute_second_command(rep, world.getAllReachableSigs(), command, options,sols);
            //            System.out.println(ans);
            //            while (ans.next().satisfiable() && ans.satisfiable()){
            //                ans = ans.next();
            ////                instances.add(ans.eval.instance());
            //                //System.out.println(ans);
            //            }

            // If satisfiable...
            //            if (ans.satisfiable()) {
            //                // You can query "ans" to find out the values of each set or
            //                // type.
            //                // This can be useful for debugging.
            //                //
            //                // You can also write the outcome to an XML file
            //                ans.writeXML("alloy_example_output.xml");
            //                //
            //                // You can then visualize the XML file by calling this:
            //                if (viz == null) {
            //                    viz = new VizGUI(false, "alloy_example_output.xml", null);
            //                } else {
            //                    viz.loadXML("alloy_example_output.xml", true);
            //                }
            //            }
        }
    }

}
