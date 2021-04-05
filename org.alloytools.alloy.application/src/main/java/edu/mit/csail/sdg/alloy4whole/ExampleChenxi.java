package edu.mit.csail.sdg.alloy4whole;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.IntStream;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A2KConverter;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;

public class ExampleChenxi {

    private static A4Options options = null;

    private static Bounds adjustBounds(Bounds tight, Bounds loose) {
        long beg = System.currentTimeMillis();
        try {
            if (tight == null)
                return loose;
            Bounds retval = loose.clone();
            for (Relation tr : tight.relations()) {
                Relation lr = retval.findRelByName(tr.name());
                if (lr == null)
                    continue;
                // adjust the lower bound, starting with the lower bound
                // of the loose bounds and adding in all the items from
                // the lower bounds of the tight bounds
                TupleSet newLB = loose.lowerBound(lr).clone();
                for (Tuple t : tight.lowerBound(tr)) {
                    List<Object> newtuple = new ArrayList<>();
                    for (int i = 0; i < t.arity(); i++) {
                        newtuple.add(t.atom(i));
                    }
                    newLB.add(retval.universe().factory().tuple(newtuple));
                }
                // adjust the upper bound. start with loose upper bound,
                // and only keep those tuples that include an atom
                // that doesn't appear in the universe of the tight bound
                TupleSet newUB = loose.upperBound(lr).clone();
                newUB.removeIf(t -> {
                    for (int i = 0; i < t.arity(); i++) {
                        if (!tight.universe().contains(t.atom(i))) {
                            return false;
                        }
                    }
                    return true;
                });
                // now add the tuples from the tight bound, remade in
                // the new universe
                for (Tuple t : tight.upperBound(tr)) {
                    List<Object> newtuple = new ArrayList<>();
                    for (int i = 0; i < t.arity(); i++) {
                        newtuple.add(t.atom(i));
                    }
                    newUB.add(retval.universe().factory().tuple(newtuple));
                }
                // set the new bounds
                retval.bound(lr, newLB, newUB);
            }
            return retval;
        } finally {
            System.err.printf("    bounds adjusted   : time=%10dms%n", System.currentTimeMillis() - beg);
        }
    }

    private static Bounds buildBounds(IntSet upper, IntSet lower, Translation translation) {
        long beg = System.currentTimeMillis();
        try {
            Bounds retval = translation.bounds().clone();
            for (Relation r : retval.relations()) {
                // start with the lower bounds for the relation for each one,
                // since the upper bound MUST contain the lower bound
                TupleSet lowerTS = retval.lowerBound(r).clone();
                TupleSet upperTS = retval.lowerBound(r).clone();
                // get the upper - lower for each variable relation
                TupleSet variable = retval.upperBound(r).clone();
                variable.removeAll(retval.lowerBound(r));
                // iterate over the tuples and the variable positions simultaneously
                Iterator<Tuple> titer = variable.iterator();
                IntIterator viter = translation.primaryVariables(r).iterator();
                while (viter.hasNext()) {
                    int i = viter.next();
                    Tuple t = titer.next();
                    if (upper.contains(i))
                        upperTS.add(t);
                    if (lower.contains(i))
                        lowerTS.add(t);
                }
                retval.bound(r, lowerTS, upperTS);
            }
            return retval;
        } finally {
            System.err.printf("    bounds built      : time=%10dms%n", System.currentTimeMillis() - beg);
        }
    }

    private static void enumerateAlloy(String filename) throws Exception {
        long beg = System.currentTimeMillis();
        Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        Command command = world.getAllCommands().get(0);

        A2KConverter a2k = new A2KConverter(world, A4Reporter.NOP, world.getAllReachableSigs(), command, options());
        System.err.printf("    parsed file       : time=%10dms%n", System.currentTimeMillis() - beg);
        long tbeg = System.currentTimeMillis();
        Translation translation = Translator.translate(a2k.getFormula(), a2k.getBounds(), a2k.getOptions());
        System.err.printf("    translated        : time=%10dms,  vars=%10d, clauses=%10d%n", System.currentTimeMillis() - tbeg, translation.cnf().numberOfVariables(), translation.cnf().numberOfClauses());

        SATSolver cnf = translation.cnf();
        int numVariables = translation.numPrimaryVariables();

        long sbeg = System.currentTimeMillis();
        boolean isSat = cnf.solve();
        System.err.printf("    solved one        : time=%10dms%n", System.currentTimeMillis() - sbeg);

        long count = 0;
        while (isSat) {
            int[] notModel = new int[numVariables];
            for (int i = 1; i <= numVariables; i++) {
                notModel[i - 1] = cnf.valueOf(i) ? -i : i;
            }
            cnf.addClause(notModel);
            isSat = cnf.solve();
            count++;
        }
        long end = System.currentTimeMillis();
        System.err.printf("    enumerated models : time=%10dms, count=%10d%n", end - sbeg, count);
        translation.cnf().free();
        System.err.printf("ran file with Alloy   : time=%10dms, count=%10d, file=%s%n", end - beg, count, filename);
    }

    private static Bounds enumerateChenxi(String filename, Bounds bounds) throws Exception {
        long beg = System.currentTimeMillis();
        Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        Command command = world.getAllCommands().get(0);
        A2KConverter a2k = new A2KConverter(world, A4Reporter.NOP, world.getAllReachableSigs(), command, options());
        System.err.printf("    parsed file       : time=%10dms%n", System.currentTimeMillis() - beg);
        Bounds b = adjustBounds(bounds, a2k.getBounds());

        long tbeg = System.currentTimeMillis();
        Options opts = a2k.getOptions().clone();
        opts.setSymmetryBreaking(0);
        Translation translation = Translator.translate(a2k.getFormula(), a2k.getBounds(), opts);
        adjustCnf(translation, b);
        System.err.printf("    translated        : time=%10dms,  vars=%10d, clauses=%10d%n", System.currentTimeMillis() - tbeg, translation.cnf().numberOfVariables(), translation.cnf().numberOfClauses());

        IntSet upper = new IntTreeSet();
        IntSet lower = new IntTreeSet();
        long bCount = getChenxiUpperBound(translation, upper, lower);
        getChenxiLowerBound(a2k, b, lower);
        Bounds retval = buildBounds(upper, lower, translation);
        translation.cnf().free();
        // now get the actual isntance set
        long iCount = getChenxiInstances(a2k, retval);
        System.err.printf("ran file with Chenxi  : time=%10dms, count=%10d, file=%s%n", System.currentTimeMillis() - beg, iCount, filename);
        return retval;
    }

    private static void adjustCnf(Translation transl, Bounds b) {
        Bounds ref = transl.bounds();
        for (Relation r : ref.relations()) {
            IntIterator viter = transl.primaryVariables(r).iterator();
            TupleSet vtuples = ref.upperBound(r).clone();
            vtuples.removeAll(ref.lowerBound(r));
            Iterator<Tuple> titer = vtuples.iterator();
            while (titer.hasNext()) {
                int v = viter.next();
                Tuple t = titer.next();
                if (b.lowerBound(r).contains(t)) {
                    transl.cnf().addClause(new int[] {
                                                      v
                    });
                } else if (!b.upperBound(r).contains(t)) {
                    transl.cnf().addClause(new int[] {
                                                      -v
                    });
                }
            }
        }
    }

    private static Bounds enumerateTitanium(String filename, Bounds bounds) throws Exception {
        long beg = System.currentTimeMillis();
        Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        Command command = world.getAllCommands().get(0);

        A2KConverter a2k = new A2KConverter(world, A4Reporter.NOP, world.getAllReachableSigs(), command, options());
        System.err.printf("    parsed file       : time=%10dms%n", System.currentTimeMillis() - beg);
        Bounds b = adjustBounds(bounds, a2k.getBounds());

        long tbeg = System.currentTimeMillis();
        Translation translation = Translator.translate(a2k.getFormula(), b, a2k.getOptions());
        System.err.printf("    translated        : time=%10dms,  vars=%10d, clauses=%10d%n", System.currentTimeMillis() - tbeg, translation.cnf().numberOfVariables(), translation.cnf().numberOfClauses());

        IntSet upper = new IntTreeSet();
        IntSet lower = new IntTreeSet();
        long count = getTitaniumSolutions(translation, upper, lower);
        Bounds retval = buildBounds(upper, lower, translation);
        translation.cnf().free();
        System.err.printf("ran file with Titanium: time=%10dms, count=%10d, file=%s%n", System.currentTimeMillis() - beg, count, filename);
        return retval;
    }

    private static long getChenxiInstances(A2KConverter a2k, Bounds b) {
        long beg = System.currentTimeMillis(), count = 0;
        Translation translation = Translator.translate(a2k.getFormula(), a2k.getBounds(), a2k.getOptions());
        adjustCnf(translation, b);
        System.err.printf("    translated        : time=%10dms,  vars=%10d, clauses=%10d%n", System.currentTimeMillis() - beg, translation.cnf().numberOfVariables(), translation.cnf().numberOfClauses());
        try {
            int numVariables = translation.numPrimaryVariables();
            SATSolver cnf = translation.cnf();
            int[] notModel = new int[numVariables];
            long sbeg = System.currentTimeMillis();
            boolean isSat = cnf.solve();
            System.err.printf("    solved one        : time=%10dms%n", System.currentTimeMillis() - sbeg);

            while (isSat) {
                IntSet track = new IntTreeSet();
                for (int i = 1; i <= numVariables; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                }
                cnf.addClause(notModel);
                isSat = cnf.solve();
                ++count;
            }
            return count;
        } finally {
            translation.cnf().free();
            System.err.printf("    enumerated models : time=%10dms, count=%10d%n", System.currentTimeMillis() - beg, count);
        }
    }

    private static void getChenxiLowerBound(A2KConverter a2k, Bounds b, IntSet lower) {
        long beg = System.currentTimeMillis();
        try {
            IntIterator iter = lower.iterator();
            while (iter.hasNext()) {
                Translation transl = Translator.translate(a2k.getFormula(), b, a2k.getOptions());
                SATSolver cnf = transl.cnf();
                cnf.addClause(new int[] {
                                         -iter.next()
                });
                if (cnf.solve()) {
                    iter.remove();
                }
                cnf.free();
            }
        } finally {
            System.err.printf("    found lower bound : time=%10dms, lower=%10d%n", System.currentTimeMillis() - beg, lower.size());
        }
    }

    private static long getChenxiUpperBound(Translation translation, IntSet upper, IntSet lower) {
        long beg = System.currentTimeMillis(), count = 0;
        try {
            int numVariables = translation.numPrimaryVariables();
            SATSolver cnf = translation.cnf();
            IntSet notSeen = new IntTreeSet();
            IntStream.rangeClosed(1, numVariables).forEachOrdered(notSeen::add);
            boolean isSat = cnf.solve();
            boolean first = true;
            while (isSat) {
                IntSet track = new IntTreeSet();
                for (int i = 1; i <= numVariables; i++) {
                    if (cnf.valueOf(i))
                        track.add(i);
                }
                upper.addAll(track);
                if (first) {
                    lower.addAll(track);
                    first = false;
                } else {
                    lower.retainAll(track);
                }
                notSeen.removeAll(track);
                cnf.addClause(notSeen.toArray());
                isSat = cnf.solve();
                ++count;
            }
            return count;
        } finally {
            System.err.printf("    computed bounds   : time=%10dms, count=%10d, upper=%10d%n", System.currentTimeMillis() - beg, count, upper.size());
        }
    }

    private static long getTitaniumSolutions(Translation translation, IntSet upper, IntSet lower) {
        long beg = System.currentTimeMillis(), count = 0;
        try {
            int numVariables = translation.numPrimaryVariables();
            SATSolver cnf = translation.cnf();
            int[] notModel = new int[numVariables];

            long sbeg = System.currentTimeMillis();
            boolean isSat = cnf.solve();
            System.err.printf("    solved one        : time=%10dms%n", System.currentTimeMillis() - sbeg);

            boolean first = true;
            while (isSat) {
                IntSet track = new IntTreeSet();
                for (int i = 1; i <= numVariables; i++) {
                    notModel[i - 1] = cnf.valueOf(i) ? -i : i;
                    if (cnf.valueOf(i))
                        track.add(i);
                }
                upper.addAll(track);
                if (first) {
                    lower.addAll(track);
                    first = false;
                } else {
                    lower.retainAll(track);
                }
                cnf.addClause(notModel);
                isSat = cnf.solve();
                ++count;
            }
            return count;
        } finally {
            System.err.printf("    enumerated models : time=%10dms, count=%10d%n", System.currentTimeMillis() - beg, count);
        }
    }

    public static void main(String[] args) throws Exception {
        primeTheSolver();
        System.err.println("======================");
        enumerateAlloy(args[0]);
        System.err.println("----------------------");
        Bounds b1 = enumerateTitanium(args[0], null);
        System.err.println("----------------------");
        Bounds b2 = enumerateChenxi(args[0], null);
        System.err.println("======================");
        enumerateAlloy(args[1]);
        System.err.println("----------------------");
        Bounds c1 = enumerateTitanium(args[1], b1);
        System.err.println("----------------------");
        Bounds c2 = enumerateChenxi(args[1], b2);
        System.err.println("======================");
    }

    private static A4Options options() {
        if (options == null) {
            options = new A4Options();
            options.solver = SatSolver.MiniSatJNI;
            options.symmetry = 20;
        }
        return options;
    }

    private static void primeTheSolver() {
        PrintStream stdout = System.out;
        try (PrintStream devnull = new PrintStream(new OutputStream() {

            @Override
            public void write(int b) throws IOException {
                //no-op
            }
        })) {
            System.setOut(devnull);
            Module world = CompUtil.parseEverything_fromString(A4Reporter.NOP, "sig A { child: one A } run {} for 2 A");
            Command command = world.getAllCommands().get(0);
            TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(), command, options());
        } finally {
            System.setOut(stdout);
        }
    }
}
