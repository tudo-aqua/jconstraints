package structuralEquivalence;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class Scanner {

	private File baseFolder;
	public Scanner(File smtFolder){
		this.baseFolder = smtFolder;
	}

	public List<File> getCollectedFiles(){
		return collect(baseFolder);
	}

	private List<File> collect(File folder){
		ArrayList<File> collected = new ArrayList<>();
		for(File f: folder.listFiles()){
			if (f.isDirectory()){
				collected.addAll(collect(f));
			} else if(f.getAbsolutePath().endsWith(".smt") || f.getAbsolutePath().endsWith(".smt2")|| f.getAbsolutePath().endsWith(".smt25")) {
				collected.add(f);
			}
		}
		return collected;
	}
}
