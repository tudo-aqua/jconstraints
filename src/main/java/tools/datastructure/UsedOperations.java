package tools.datastructure;

import java.util.HashMap;

public class UsedOperations {
	public String file;
	public HashMap<String, Integer> operators;
	public UsedOperations(String file, HashMap<String, Integer> operators){
		this.file = file;
		this.operators = operators;
	}
}
