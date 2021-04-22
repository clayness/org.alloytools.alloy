package kodkod.engine.slicing;

import java.util.HashMap;
import java.util.LinkedList;

import kodkod.engine.bool.BooleanFormula;

/**
 * Created by guolongzheng on 1/25/17.
 */
public final class ExtendBooleanFormula {

    public BooleanFormula                       booleanFormulaForm;
    public int                                  numPrimiryVariables;
    public int                                  numClauses;
    public int                                  weight;
    public int                                  hashCode;
    public int[]                                hashCodeSet;
    public HashMap<Integer,Integer>             reverseLabelMap;
    public HashMap<Integer,LinkedList<Integer>> reverseLabelMapSet;    //map the normalized label to original label

    public ExtendBooleanFormula(BooleanFormula bf, int numLits, int numClauses, HashMap<Integer,Integer> reverseLabelMap) {
        this.booleanFormulaForm = bf;
        this.numPrimiryVariables = numLits;
        this.numClauses = numClauses;
        this.hashCodeSet = new int[3];
        this.hashCodeSet[0] = numLits;
        this.hashCodeSet[1] = numClauses;
        this.hashCodeSet[2] = booleanFormulaForm.toString().hashCode();
        this.hashCode = hashCodeSet[0] + hashCodeSet[1] + hashCodeSet[2];
        this.reverseLabelMap = reverseLabelMap;
        this.reverseLabelMapSet = new HashMap<>();
    }

    public Integer getOriginalLabel(int i) {
        return reverseLabelMap.get(i);
    }

    public LinkedList<Integer> getOriginalLabels(int i) {
        return reverseLabelMapSet.get(i);
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    public boolean equals(ExtendBooleanFormula input) {
        if (input.hashCode != this.hashCode) {
            return false;
        } else if (input.hashCodeSet[0] != this.hashCodeSet[0]) {
            return false;
        } else if (input.hashCodeSet[1] != this.hashCodeSet[1]) {
            return false;
        } else if (input.hashCodeSet[2] != this.hashCodeSet[2]) {
            return false;
        } else {
            return true;
        }
    }
}
