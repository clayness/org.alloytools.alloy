package edu.mit.csail.sdg.alloy4whole;

import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.Date;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.slicing.SATResult;
import kodkod.engine.slicing.SATResult.Output;

public class PlatinumTest {

    public static void main(String[] args) throws IOException {
        PrintStream stdout = System.out;
        System.setOut(System.err);

        A4Reporter rep = new SimpleReporter();

        A4Options opt = new A4Options();
        opt.solver = SatSolver.SAT4J;

        int cmd = args.length < 3 ? 0 : Integer.parseInt(args[2]);

        PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:" + args[1]);

        Files.list(Paths.get(args[0])).filter(matcher::matches).sorted().forEachOrdered(path -> {
            System.err.printf("[%s] solving with Platinum: %s%n", new Date(), path);
            Module module = CompUtil.parseEverything_fromFile(rep, null, path.toString());
            A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, module.getAllReachableSigs(), module.getAllCommands().get(0), opt);
            String sat = sol.satisfiable() ? "SATISFIABLE" : "UNSATISFIABLE";
            Output output = SATResult.getOutput();
            stdout.printf("%s,%d,%d,%d,%d,%d%n", sat, output.numPrimary, output.numVars, output.numClauses, output.transTime, output.solveTime);
        });
    }


    private static final class SimpleReporter extends A4Reporter {

        @Override
        public void debug(String msg) {
            //log(msg);
        }

        @Override
        public void parse(String msg) {
            //log(msg);
        }

        @Override
        public void typecheck(String msg) {
            //log(msg);
        }

        @Override
        public void warning(ErrorWarning msg) {
            log(msg.dump());
        }

        @Override
        public void scope(String msg) {
            //log(msg);
        }

        @Override
        public void bound(String msg) {
            //log(msg);
        }

        @Override
        public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
            log("   Solver=" + solver + " Bitwidth=" + bitwidth + " MaxSeq=" + maxseq + " Symmetry=" + (symmetry > 0 ? ("" + symmetry) : "OFF") + "\n");
        }

        @Override
        public void solve(int primaryVars, int totalVars, int clauses) {
            log("   " + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses.");
        }

        @Override
        public void resultCNF(String filename) {
        }

        @Override
        public void resultSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command))
                return;
            Command cmd = (Command) command;
            StringBuilder sb = new StringBuilder();
            sb.append(cmd.check ? "   Counterexample found. " : "   Instance found. ");
            if (cmd.check)
                sb.append("Assertion is invalid");
            else
                sb.append("Predicate is consistent");
            if (cmd.expects == 0)
                sb.append(", contrary to expectation");
            else if (cmd.expects == 1)
                sb.append(", as expected");
            sb.append(". " + solvingTime + "ms.\n\n");
            log(sb.toString());
        }

        @Override
        public void resultUNSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command))
                return;
            Command cmd = (Command) command;
            StringBuilder sb = new StringBuilder();
            sb.append(cmd.check ? "   No counterexample found." : "   No instance found.");
            if (cmd.check)
                sb.append(" Assertion may be valid");
            else
                sb.append(" Predicate may be inconsistent");
            if (cmd.expects == 1)
                sb.append(", contrary to expectation");
            else if (cmd.expects == 0)
                sb.append(", as expected");
            sb.append(". " + solvingTime + "ms.\n\n");
            log(sb.toString());
        }

        private void log(String message) {
            System.err.println(message);
        }
    }

}