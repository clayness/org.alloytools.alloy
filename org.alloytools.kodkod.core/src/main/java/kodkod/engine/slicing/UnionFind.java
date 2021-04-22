package kodkod.engine.slicing;

import java.util.List;

import kodkod.engine.bool.BooleanFormula;

/**
 * Created by guolongzheng on 3/30/17.
 */
public interface UnionFind {

    int root(int i);

    boolean find(int p, int q);

    void union(int p, int q, List<BooleanFormula> independentSetP, List<BooleanFormula> independentSetQ);

    void simpleUnion(int p, int q);
}
