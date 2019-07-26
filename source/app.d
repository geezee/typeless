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

struct DupCont {
    Term* term;
    bool inner;
    Term* ans1;
    DupCont* next;
}

Term* dupCPS(Term* t, Term* delegate(Term*) cont) {
    if (t == null) return cont(null);
    return dupCPS(t.t1, (Term* ans1) {
        return dupCPS(t.t2, (Term* ans2) {
            return cont(new Term(t.type, t.a, ans1, ans2));
        });
    });
}

Term* applyDup(Term* ans, DupCont* cont) {
    do {
        if (cont == null) return ans;
        if (cont.inner) {
            ans = new Term(cont.term.type, cont.term.a, cont.ans1, ans);
            cont = cont.next.next;
        } else return dupDefun(cont.term.t2, new DupCont(cont.term, true, ans, cont));
    } while (true);
}

Term* dupDefun(Term* t, DupCont* cont = null) {
    if (t == null) return applyDup(t, cont);
    return dupDefun(t.t1, new DupCont(t, false, null, cont));
}


Term* parse(string s) {
    string[] tokens = s.replace("(", " ( ").replace(")", " ) ").replace("'", " ' ").split!isWhite;
    Term*[] stack = [];

    void fillStackHole() {
        if (stack.length < 2) return;
        Term* parent = stack[$-2];
        Term* front = stack[$-1];
        final switch (parent.type) {
            case TType.APP:
                if (parent.t1 == null) { parent.t1 = front; break; }
                else if (parent.t2 == null) { parent.t2 = front; break; }
                goto case;
            case TType.ABS:
                if (parent.t1 == null) { parent.t1 = front; break; }
                goto case;
            case TType.VAR:
                stack[$-2] = new Term(TType.APP, null, parent, front);
        }
        stack = stack[0..$-1];
    }

    for (int i=0; i < tokens.length; i++) {
        string token = tokens[i];
        if (token.length == 0) continue;
        if (token == "(") {
            if(tokens[i+1] != "lambda") stack ~= new Term(TType.APP);
        } else if (token == "lambda")  {
            stack ~= new Term(TType.ABS, tokens[i+1]);
            i++; // skip the var
        } else if (token == ")") fillStackHole();
        else { stack ~= new Term(TType.VAR, token); fillStackHole(); }
    }

    assert (stack.length == 1, "unbalanced parans");
    return stack[0];
}


struct BetaCont {
    TType type;
    int argNum;
    Term* term;
    BetaCont* next;
}

Term* applyBetaCont(Term* ans, string var, Term* val, BetaCont* cont) { // var, val in here because they never change
    while(true) {
        if (cont == null) return ans;
        switch (cont.type) {
            case TType.ABS:
                cont.term.t1 = ans;
                ans = cont.term;
                cont = cont.next;
                break;
            case TType.APP:
                if (cont.argNum == 1) {
                    cont.term.t1 = ans;
                    return betaDefun(cont.term.t2, var, val, new BetaCont(cont.type, 2, cont.term, cont.next));
                } else {
                    cont.term.t2 = ans;
                    ans = cont.term;
                    cont = cont.next;
                }
                break;
            default:
                cont = cont.next; break;
        }
    }
}

Term* betaDefun(Term* term, string var, Term* val, BetaCont* cont = null) {
    if (term == null) return term;
    final switch (term.type) {
        case TType.VAR:
            return applyBetaCont(term.a == var ? val : term, var, val, cont);
        case TType.ABS:
            if (term.a == var) return applyBetaCont(term, var, val, cont);
            else return betaDefun(term.t1, var, val, new BetaCont(TType.ABS, 0, term, cont));
        case TType.APP:
            return betaDefun(term.t1, var, val, new BetaCont(TType.APP, 1, term, cont));
    }
}


// full blown optimization
Term* betaOpt(Term* term, string var, Term* val, BetaCont* cont = null) {
    Term* ans = null;
    bool computeAns = false;
    while (true) {
        if (term == null) return term;
        computeAns = false;

        if (term.type == TType.VAR) {
            ans = term.a == var ? val : term;
            computeAns = true;
        } else if (term.type == TType.ABS) {
            if (term.a == var) {
                ans = term;
                cont = cont.next;
                computeAns = true;
            } else {
                term = term.t1;
                cont = new BetaCont(TType.ABS, -1, term, cont);
            }
        } else if (term.type == TType.APP) {
            term = term.t1;
            cont = new BetaCont(TType.APP, 1, term, cont);
        }

        if (!computeAns) continue;

        while(true) {
            if (cont == null) return ans;
            if (cont.type == TType.ABS) {
                cont.term.t1 = ans;
                ans = cont.term;
                cont = cont.next;
            } else if (cont.type == TType.APP) {
                if (cont.argNum == 1) {
                    cont.term.t1 = ans;
                    ans = cont.term.t2;
                    cont = new BetaCont(cont.type, 2, cont.term, cont.next);
                    break;
                } else {
                    cont.term.t2 = ans;
                    ans = cont.term;
                    cont = cont.next;
                }
            } else cont = cont.next;
        }

        term = ans;
    }
}


// Rewrote beta so it uses CPS
Term* beta(Term* term, string var, Term* val, Term* delegate(Term*) cont = (Term* t) { return t; }) {
    if (term == null) return term;
    final switch (term.type) {
        case TType.VAR:
            return cont(term.a == var ? val : term);
        case TType.ABS:
            if (term.a == var) return cont(term);
            return beta(term.t1, var, val, (Term* ans) {
                term.t1 = ans;
                return cont(term);
            });
        case TType.APP:
            return beta(term.t1, var, val, (Term* ans1) {
                term.t1 = ans1;
                return beta(term.t2, var, val, (Term* ans2) {
                    term.t2 = ans2;
                    return cont(term);
                });
            });
    }
}


Term* eval(Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0) {
    interfunc(term, depth);

    final switch (term.type) {
        case TType.VAR:
            if (term.a == "print") {
                return new Term(TType.VAR, term.a);
            } else if ((term.a in env) !is null) {
                Term* duped = env[term.a].dupDefun;
                return eval(duped, env, interfunc, depth);
            } else assert(false, "Unbound variable " ~ term.a);
        case TType.APP:
            if (term.t1.type == TType.ABS) {
                Term* duped = term.t2.dupDefun;
                term.t1.t1 = betaDefun(term.t1.t1, term.t1.a, duped);
                return eval(term.t1.t1, env, interfunc, depth);
            } else {
                if (term.t1.type == TType.VAR && term.t1.a == "print") {
                    writefln("[print] %s", term.t2.toString);
                    return eval(term.t2, env, interfunc, depth-1);
                }
                term.t1 = eval(term.t1, env, interfunc, depth+1);
                term.t2 = eval(term.t2, env, interfunc, depth+1);
                return eval(term, env, interfunc, depth);
            }
        case TType.ABS:
            return term;
    }
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
