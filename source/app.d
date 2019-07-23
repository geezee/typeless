import std.stdio;
import std.array : replace, split;
import std.string : strip;
import std.range : repeat;
import std.algorithm.iteration : joiner;
import std.file : readText;
import std.algorithm.searching : count;
import std.ascii : isWhite;
import std.conv : text;

enum TType { VAR, APP, ABS };

struct Term {
    TType type;
    string a;
    Term* t1;
    Term* t2;
}

alias Env = Term*[string];

bool isValue(Term* term) {
    return term.type == TType.VAR || term.type == TType.ABS;
}

bool hasHoles(Term* t) {
    return (t.type == TType.ABS && t.t1 == null)
        || (t.type == TType.APP && (t.t1 == null || t.t2 == null));
}

string toString(Term* t) {
    if (t == null) return ".";
    if (t.type == TType.VAR) return t.a;
    if (t.type == TType.ABS) return "^" ~ t.a ~ "." ~ t.t1.toString;
    if (t.type == TType.APP) return "(" ~ t.t1.toString ~ " " ~ t.t2.toString ~ ")";
    return "";
}

Term* dup(Term* t) {
    if (t == null) return null;
    return new Term(t.type, t.a, t.t1.dup, t.t2.dup);
}


Term* parse(string s) {
    string[] tokens = s.replace("(", " ( ").replace(")", " ) ").split!isWhite;
    int depth = 0;
    Term*[] stack = [];

    void pushToStack(Term* t) {
        if (stack.length == 0 || t.hasHoles) {
            stack ~= t;
        } else {
            Term* front = stack[$-1];
            while (true) {
                if (!front.hasHoles) return;
                if (front.type == TType.ABS) {
                    front.t1 = t;
                } else if (front.type == TType.APP) {
                    if (front.t1 == null) front.t1 = t;
                    else if (front.t2 == null) front.t2 = t;
                }
                if (!front.hasHoles) {
                    t = front;
                    stack = stack[0..$-1];
                    if (stack.length == 0) { stack ~= front; return; }
                    front = stack[$-1];
                } else return;
            }
        }
    }

    for (int i=0; i < tokens.length; i++) {
        string token = tokens[i];
        if (token.length == 0) continue;
        if (token == "(") {
            depth++;
            if(tokens[i+1] != "lambda") pushToStack(new Term(TType.APP));
        } else if (token == "lambda")  {
            pushToStack(new Term(TType.ABS, tokens[i+1]));
            i++; // skip the var
        } else if (token == ")") {
            depth--;
        } else pushToStack(new Term(TType.VAR, token));
    }
    assert (depth == 0, "unbalanced parans");
    return stack[0];
}


Term* beta(Term* term, string var, Term* val) {
    if (term == null) return term;
    if (term.type == TType.VAR && term.a == var) return val.dup;
    if (term.type == TType.ABS) {
        if (term.a == var) return term;
        if (term.t1 == null) {
            writefln("error, can't do that");
            return null;
        } else {
            term.t1 = beta(term.t1, var, val);
            return term;
        }
    } else if (term.t1 != null && term.t2 != null) {
        term.t1 = beta(term.t1, var, val);
        term.t2 = beta(term.t2, var, val);
        return term;
    }
    return term;
}


Term* eval(Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0) {
    interfunc(term, depth);

    if (term.type == TType.VAR) {
        if (term.a == "print" || term.a == "eval") {
            return new Term(TType.VAR, term.a);
        } else if ((term.a in env) !is null) {
            return eval(env[term.a].dup, env, interfunc, depth);
        } else assert(false, "Unbound variable " ~ term.a);
    } else if (term.type == TType.ABS) {
        return term;
    } else if (term.type == TType.APP) {
        if (term.t1.type == TType.ABS) {
            term.t1.t1 = beta(term.t1.t1, term.t1.a, term.t2);
            return eval(term.t1.t1, env, interfunc, depth);
        } else {
            if (term.t1.type == TType.VAR) {
                if (term.t1.a == "eval") {
                    auto result = eval(term.t2, env, interfunc, depth-1);
                    writefln("[eval] %s", result.toString);
                    return result;
                } else if (term.t1.a == "print") {
                    writefln("[print] %s", term.t2.toString);
                    return eval(term.t2, env, interfunc, depth-1);
                }
            }
            term.t1 = eval(term.t1, env, interfunc, depth+1);
            term.t2 = eval(term.t2, env, interfunc, depth+1);
            return eval(term, env, interfunc, depth);
        }
    } else return term;
}


void main(string[] argv) {
    bool debugMode = false;
    string source = "";
    Env env;

    if (argv.length == 2 && argv[1] == "-d") debugMode = true;
    if (argv.length == 3 && (argv[2] == "-d" || argv[1] == "-d")) debugMode = true;
    if (argv.length == 2 && argv[1] != "-" && argv[1] != "-d") source = argv[1];
    if (argv.length == 3 && argv[1] != "-" && argv[1] != "-d") source = argv[1];
    if (argv.length == 3 && argv[2] != "-" && argv[2] != "-d") source = argv[2];

    void delegate(Term*,int) debugCont = (Term* step, int depth) {
        writefln("  >%s %s", ">".repeat(depth).joiner(""), toString(step));
    };
    void delegate(Term*,int) normalCont = (Term* step, int depth) {};

    void handle(string exprs) {
        foreach (expr; exprs.split(";")) {
            if (expr.length == 0) continue;
            string[] tokens = expr.split("=");
            try
                if (tokens.length > 1) env[tokens[0].strip] = parse(tokens[1..$].joiner("=").text);
                else if (tokens.length == 1 && tokens[0].strip.length > 0)
                    expr.parse.eval(env, debugMode ? debugCont : normalCont).toString.writeln;
            catch (Exception e) writefln("error: %s", e.msg);
            catch (Error e) writefln("error: %s", e.msg);
        }
    }

    if (source.length > 0) {
        handle(source.readText);
        env["main"].eval(env, debugMode ? debugCont : normalCont).toString.writeln;
    } else {
        string exprs = "";
        do {
            writef("\r%s> ", exprs.length == 0 ? "" : ">");
            exprs ~= readln();
            if (exprs.length == 0) return;
            size_t openParans = exprs.count("(") - exprs.count(")");
            if (openParans == 0) {
                handle(exprs);
                exprs = "";
            } else if (openParans < 0) {
                writefln("error: unbalanced parans");
                exprs = "";
            }
            foreach (expr; exprs.split(";")) {
                if (expr.length == 0) continue;
                string[] tokens = expr.split("=");
            }
        } while(true);
    }
}
