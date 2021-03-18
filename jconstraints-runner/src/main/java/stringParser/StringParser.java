package stringParser;

import dk.brics.automaton.Automaton;
import dk.brics.automaton.RegExp;
public class StringParser {

	public static void main(String args[]){
		RegExp exp = new RegExp("W.*\\\\d[0-35-9]-\\\\d\\\\d-\\\\d\\\\d");

		RegExp exp2 = new RegExp("[^a-h]xdf.+");
//		(define-const c (RegEx String) (re.++ (re.inter re.allchar (re.union (re.range "\x00" "\x60") (re.range "\x68" "\xff"))) (str.to.re "xdf") (re.+ re.allchar)))
//		(declare-const d String)
//		(assert (= d "axdfh"))
//		(assert (str.in.re d c))
//		(check-sat)
//		(get-model)


		Automaton a1 = exp.toAutomaton();
		Automaton a1_minimized = exp.toAutomaton(true);
		System.out.println("This is how it should work");
	}
}
