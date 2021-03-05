package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.File;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Main {

    public static void main(String[] args) throws IOException {

        A4Reporter rep = new A4Reporter();
        Module world = CompUtil.parseEverything_fromFile(rep, null, "/Users/yuchenxi/1.als");
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.SAT4J;
        options.skolemDepth = 1;

        for (Command command : world.getAllCommands()) {
            A4Solution ans = null;
            try {
                ans = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), command, options);
                System.out.println(ans);
                while (ans.next() != null){
                    ans = ans.next();
                    System.out.println(ans);
                }
            } catch (Err ex) {
                Logger.getLogger(Main.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
    }
}
