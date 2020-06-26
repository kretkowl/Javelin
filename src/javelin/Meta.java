package javelin;

public class Meta {

    private String name;
    private String sourceFile;
    private int sourceLine;

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }
    
    public Meta name(String name) { 
        this.setName(name);
        return this;
    }
    
    public String name() {
        return getName();
    }
    
    public void setSourceFile(String sourceFile) {
        this.sourceFile = sourceFile;
    }

    public Meta sourceFile(String sourceFile) { 
        this.setSourceFile(sourceFile);
        return this;
    }

    public String getSourceFile() {
        return sourceFile;
    }

    public String sourceFile() {
        return getSourceFile();
    }

    public void setSourceLine(int sourceLine) {
        this.sourceLine = sourceLine;
    }

    public Meta sourceLine(int sourceLine) { 
        this.setSourceLine(sourceLine);
        return this;
    }

    public int getSourceLine() {
        return sourceLine;
    }

    
    public int sourceLine() {
        return getSourceLine();
    }
}
