package pku;

import java.util.Arrays;
import java.util.TreeMap;
import java.util.TreeSet;

/** { [test_id] : point-to-set }, where point-to-set = { obj_id | test_id points-to obj_id } */
public class PointerAnalysisResult extends TreeMap<Integer, TreeSet<Integer>> {
    public String toString(){
        return String.join("\n", this.keySet().stream().map(key->{
            var objs = this.get(key);
            var objs_string = String.join(" ",
                Arrays.stream(objs.toArray(new Integer[0]))
                .map(String::valueOf)
                .toArray(String[]::new)
            );
            return key.toString()+" : "+objs_string;
        }).toArray(String[]::new));
    }
}

