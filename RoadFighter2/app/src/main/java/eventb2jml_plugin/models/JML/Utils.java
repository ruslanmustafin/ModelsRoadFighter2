package eventb2jml_plugin.models.JML;

/** utility methods for sets and relations
 * 
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

import org.jmlspecs.models.JMLEqualsEqualsPair;

public class Utils {
	
	/*@ assignable \nothing;
	    ensures (\forall E e; \result.has(e) <==> 
	      (\exists int i; 0 <= 1 && i < elems.length; elems[i].equals(e)));
	 */
	public static <E> BSet<E> extension(E ... elems) {
		BSet<E> res = new BSet<E>();
		for (E e : elems) {
			res = res.insert(e);
		}
		return res;
	}
	
	/*@ assignable \nothing;
	    ensures (\forall E e; \result.has(e) <==>
	      (\exists int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
	 */
	public static <E> BSet<E> union(BSet<E> ... sets) {
		BSet<E> res = new BSet<E>();
		for (BSet<E> set : sets) {
			res = res.union(set);
		}
		return res;
	}
	
	/*@ assignable \nothing;
	    ensures \result.isEmpty();
	 */
	public static <E> BSet<E> union() {
		return new BSet<E>();
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> e; \result.has(e) <==>
          (\exists int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
     */
	public static <K, V> BRelation<K, V> union(BRelation<K, V> ... sets) {
		BRelation<K, V> res = new BRelation<K, V>();
		for (BRelation<K, V> set : sets) {
			res = res.union(set);
		}
		return res;
	}
	
	/*@ public exceptional_behavior
	    requires true;
	    assignable \nothing;
	    signals (IllegalStateException);
	 */
	public static <E> BSet<E> intersection() {
		throw new IllegalStateException("Error: generalized intersection over 0 sets.");
	}
	
	/*@ assignable \nothing;
        ensures (\forall E e; \result.has(e) <==>
          (\forall int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
     */
	public static <E> BSet<E> intersection(BSet<E> ... sets) {
		BSet<E> res = sets[0];
		for (int i = 1; i < sets.length; i++) {
			res = res.intersection(sets[i]);
		}
		return res;
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> e; \result.has(e) <==>
          (\forall int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
     */
	public static <K, V> BRelation<K, V> intersection(BRelation<K, V> ... sets) {
		BRelation<K, V> res = sets[0];
		for (int i = 1; i < sets.length; i++) {
			res = res.intersection(sets[i]);
		}
		return res;
	}

	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<K, V> e; \result.has(e) <==>
	      domain.has(e.key) && range.has(e.value));
	 */
	public static <K, V> BRelation<K, V> cross(BSet<K> domain, BSet<V> range) {
		BRelation<K, V> res = new BRelation<K, V>();
		for (K key : domain) {
			for (V value : range) {
				res = res.add(key, value);
			}
		}
		return res;
	}
}
