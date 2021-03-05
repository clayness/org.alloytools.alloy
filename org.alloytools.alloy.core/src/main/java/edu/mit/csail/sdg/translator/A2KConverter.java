package edu.mit.csail.sdg.translator;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.FormulaFlattener;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.util.nodes.AnnotatedNode;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.List;

/**
 * Alloy-to-Kodkod converter utility. Extracts the Kodkod formula, bounds, and
 * options from a set of Alloy signatures, command, and options to allow for
 * lower-level manipulation.
 */
public class A2KConverter {

    /**
     * Convets the passed Alloy options into Kodkod options
     * 
     * @param opt
     * @return
     */
    private static Options convert(A4Solution frame, A4Options opt) {
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

    @SuppressWarnings("unchecked")
    private static Formula getFormula(A4Solution frame) throws Exception {
        Field formulasField = frame.getClass().getDeclaredField("formulas");
        formulasField.setAccessible(true);

        List<Formula> original = (List<Formula>) formulasField.get(frame);

        AnnotatedNode<Formula> annotated = AnnotatedNode.annotate(Formula.and(original));
        AnnotatedNode<Formula> flattened = FormulaFlattener.flatten(annotated, true);
        assert flattened.node() instanceof NaryFormula;
        return flattened.node();
    }

    private static A4Solution getFrame(A4Reporter rep, Iterable<Sig> sigs, Command cmd, A4Options opt)
            throws Exception {
        Constructor<TranslateAlloyToKodkod> cons = TranslateAlloyToKodkod.class.getDeclaredConstructor(A4Reporter.class,
                A4Options.class, Iterable.class, Command.class);
        cons.setAccessible(true);
        TranslateAlloyToKodkod tatk = cons.newInstance(rep, opt, sigs, cmd);

        Method makeFactsMethod = tatk.getClass().getDeclaredMethod("makeFacts", Expr.class);
        makeFactsMethod.setAccessible(true);
        makeFactsMethod.invoke(tatk, cmd.formula);

        Field frameField = tatk.getClass().getDeclaredField("frame");
        frameField.setAccessible(true);
        return (A4Solution) frameField.get(tatk);
    }

    private final A4Solution a4solution;
    private final Formula formula;
    private final Options options;

    /**
     * Creates a new converter to extract the Kodkod formula, bounds, and options
     * from the passed Alloy signatures, command, and options.
     * 
     * @param rep
     * @param sigs
     * @param cmd
     * @param opt
     * @throws Exception
     */
    public A2KConverter(A4Reporter rep, Iterable<Sig> sigs, Command cmd, A4Options opt) throws Exception {
        this.a4solution = getFrame(rep, sigs, cmd, opt);
        this.options = convert(this.a4solution, opt);
        this.formula = getFormula(this.a4solution);
    }

    /**
     * Returns the Kodkod bounds.
     * 
     * @return
     */
    public Bounds getBounds() { return this.a4solution.getBounds(); }

    /**
     * Returns the Kodkod formula.
     * 
     * @return
     */
    public Formula getFormula() { return this.formula; }

    /**
     * Returns the Kodkod options.
     * 
     * @return
     */
    public Options getOptions() { return this.options.clone(); }
}
