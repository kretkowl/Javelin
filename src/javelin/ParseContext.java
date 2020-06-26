package javelin;

class ParseContext {

    String filename;
    int line;
    
    public ParseContext(String name) {
        this.filename = name;
        this.line = 1;
    }
    
    public void nextLine() {
        line++;
    }
}
