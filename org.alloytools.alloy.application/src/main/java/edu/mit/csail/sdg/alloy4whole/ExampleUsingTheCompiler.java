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
import kodkod.util.ints.IntSet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

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
        String filename = "/Users/yuchenxi/1m.als";
//        String filename = "/Users/yuchenxi/Downloads/G-Play/co_vine_android.als";
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

        HashMap<Relation,IntSet> reMap = new HashMap<Relation, IntSet>();
        Set<Relation> used = null;

        long startSolve = System.currentTimeMillis();

        //first run
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Command " + command + ": ============");
            //A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
            //sols.add(ans);
//            ans = ans.next();
//            sols.add(ans);
            System.out.println("1111111");
            //System.out.println(ans);
            //ans = ans.next();
            System.out.println("22222222");
            //System.out.println(ans);

            Translation.Whole translation;
            long              translTime;

            A2KConverter a2K = new A2KConverter(rep,world.getAllReachableSigs(),command,options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            Set<Relation> relations = b.relations();
            firstBounds = b;
            used = b.relations();
            Options o = a2K.getOptions();

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f,b,o);
            translTime = System.currentTimeMillis() - translTime;
            firstTranslation = translation;

//            translation.numPrimaryVariables();

            SATSolver cnf = translation.cnf();
            int primaryVars = translation.numPrimaryVariables();

            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());


//            long startSolve = System.currentTimeMillis();
            boolean isSat = cnf.solve();
            long endSolve = System.currentTimeMillis();

            Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            Solution sol;
            ArrayList<Solution> solutionCollection = new ArrayList<Solution>();

            System.out.println("first solving time is" + translTime);

            HashMap<Relation,int[]> map = new HashMap<Relation, int[]>();
            HashMap<Relation,int[]> ref = new HashMap<Relation, int[]>();

            int[] notModel = new int[primaryVars];
            ArrayList<Integer> notModelHelp = new ArrayList<Integer>();
            int[] track = new int[primaryVars];
            double inf = Double.POSITIVE_INFINITY;
            double min = inf;


            for (Relation re : b.relations()) {
                if (re.toString().contains(".")){
                    final IntSet i = translation.primaryVariables(re);
                    map.put(re,i.toArray());
                    ref.put(re,i.toArray());
                    reMap.put(re,i);
                    if (min > i.min()){
                        min = i.min();
                    }
                }
            }

            while (isSat){
                sol = Solution.satisfiable(stats, translation.interpret());
                solutionCollection.add(sol);
                System.out.println(sol);
                for (int i = 1; i <= primaryVars; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                    int cur = notModel[i-1];
                    int abs = Math.abs(cur);
                    if (abs >= min ){
                        if (!notModelHelp.contains(cur) && !notModelHelp.contains(-cur)){
                            notModelHelp.add(cur);
                        }
                        if (notModelHelp.contains(abs) && cur < 0){
                            int index = notModelHelp.indexOf(abs);
                            notModelHelp.set(index,cur);
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


            for (int i : notModelHelp){
                if (i > 0){
                    positive.add(i);
                }
            }

            for (Map.Entry<Relation,int[]> m : map.entrySet()){
                ArrayList<Integer> temp = new ArrayList<Integer>();
                for (int i : positive){
                    int[] b1 = m.getValue();
//                    if (Arrays.asList(b1).contains(i)){
//                        temp.add(i);
//                    }
                    for (int i1 : b1){
                        if (i1 == i){
                            temp.add(i);
                        }
                    }
                }
                int[] a = new int[temp.size()];
                for (int i = 0; i < a.length;i++){
                    a[i] = temp.get(i);
                }
                m.setValue(a);
            }

            int abc = 0;

//            translation.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
//            isSat = cnf.solve();
//            stats = new Statistics(translation, translTime, endSolve - startSolve);
//            sol = Solution.satisfiable(stats, translation.interpret());

//            while (ans.next().satisfiable() && ans.satisfiable()){
//                ans = ans.next();
////                sols.add(ans);
////                System.out.println(ans);
////                System.out.println("2222222222222222222222");
////                System.out.println(ans.bounds.uppers.toString());
////                System.out.println("lower bounds: " + ans.bounds.lowers.toString());
////                System.out.println("-----------------------------------------------------------------------------");
////                System.out.println("atom is " +ans.getAllAtoms().toString() );
//                System.out.println(ans);
//            }

            // If satisfiable...
            System.out.println("end of the loop");
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

        String filenames = "/Users/yuchenxi/1.als";
        world = CompUtil.parseEverything_fromFile(rep, null, filenames);

        // pre-process before running second time


        //second run
        System.out.println("start second run");
        startSolve = System.currentTimeMillis();
        for (Command command : world.getAllCommands()) {
            // Execute the command
            System.out.println("============ Run Second Command " + command + ": ============");

            Translation.Whole translation;
            long              translTime;

//            long startSolve = System.currentTimeMillis();

            A2KConverter a2K = new A2KConverter(rep,world.getAllReachableSigs(),command,options);
            Formula f = a2K.getFormula();
            Bounds b = a2K.getBounds();
            Options o = a2K.getOptions();

            translTime = System.currentTimeMillis();
            translation = Translator.translate(f,b,o);
            translTime = System.currentTimeMillis() - translTime;
            firstTranslation = translation;

            Set<Relation> relat = reMap.keySet();
            String s = relat.toString();

//            for (Relation rs : used){
//
//                if (rs.toString().contains(".") && s.contains(rs.name())){
//                    IntSet first = reMap.get(rs);
//                    int fMin = first.min();
//                    int fMax = first.max();
//                    int sMin = translation.primaryVariables(rs).min();
//                    int add = sMin - fMin;
//
//                    for (int i = 0; i < positive.size();i++){
//                        if (positive.get(i) <= fMax && positive.get(i)  >= fMin){
//                            positive.set(i, (positive.get(i)+add));
//                        }
//                    }
//                }
//            }
            int add = 0;
            for (Relation rs : b.relations()){
                if (rs.toString().contains(".")){
                    for (Relation sr : used){
                        if (sr.name().equals(rs.name())){
                            if (reMap.keySet().contains(sr)){
                                IntSet first = reMap.get(sr);
                                int fMin = first.min();
                                int fMax = first.max();
                                int sMin = translation.primaryVariables(rs).min();
                                add = sMin - fMin;

                                for (int i = 0; i < positive.size();i++){
                                    if (positive.get(i) <= fMax && positive.get(i)  >= fMin){
                                        positive.set(i, (positive.get(i)+add));
                                    }
                                }

                            }
                        }
                    }
                }
            }

            ArrayList<Integer> less = new ArrayList<Integer>();
            if (b.relations().size() < used.size()){
                for (Relation rs : b.relations()){
                    if (rs.toString().contains(".")){
                        for (Relation sr : used){
                            if ((sr.name().equals(rs.name())) && (sr.name().contains("."))){
                                int[] second = translation.primaryVariables(rs).toArray();
                                for (int i = 0; i < second.length; i++){
                                    if (positive.contains(second[i])){
                                        if (second[i] == translation.primaryVariables(rs).min()){
                                            less.add(translation.primaryVariables(rs).max());
                                        }else {
                                            less.add(second[i]);
                                        }

                                    }
                                }
                            }
                        }
                    }
                }
            }
            if (b.relations().size() >= used.size()){
                for (Relation rs : b.relations()){
                    if (rs.toString().contains(".")){
                        for (Relation sr : used){
                            if ((!sr.name().equals(rs.name())) && (sr.name().contains("."))){
                                int[] second = translation.primaryVariables(rs).toArray();
                                for (int i = 0; i < second.length; i++){
                                    positive.add(second[i]);
                                }
                            }
                        }
                    }
                }
            }

            int[] solved;
            if (b.relations().size() > used.size()){
                solved = new int[positive.size()];
                for (int q = 0; q < solved.length; q++){
                    solved[q] = positive.get(q);
                }
            }else{
                solved = new int[less.size()];
                for (int q = 0; q < solved.length; q++){
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

            System.out.println("second solving time is "+translTime);


            int[] notModel = new int[primaryVars];


            while (isSat){
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
