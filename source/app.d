import std.stdio;
import std.array : replace, split;
import std.string : strip;
import std.range : repeat;
import std.algorithm.iteration : joiner;
import std.file : readText;
import std.algorithm.searching : count;
import std.ascii : isWhite;
import std.conv : text;
import std.getopt;

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

Term* dupCPS(Term* t, Term* delegate(Term*) cont) {
    if (t == null) return cont(null);
    return dupCPS(t.t1, (Term* ans1) {
        return dupCPS(t.t2, (Term* ans2) {
            return new Term(t.type, t.a, ans1, ans2);
        });
    });
}


struct DupCont {
    Term* term;
    bool inner;
    Term* ans1;
    DupCont* next;
}

Term* applyDup(Term* ans, DupCont* cont) {
    if (cont == null) return ans;
    if (cont.inner) {
        Term* t = new Term(cont.term.type, cont.term.a, cont.ans1, ans);
        return applyDup(t, cont.next);
    } else {
        return dupDefun(cont.term.t2, new DupCont(cont.term, true, ans, cont.next));
    }
}

Term* dupDefun(Term* t, DupCont* cont = null) {
    if (t == null) return applyDup(t, cont);
    return dupDefun(t.t1, new DupCont(t, false, null, cont));
}

Term* dupOpt(Term* t, DupCont* cont = null) {
    while (true) {
        if (t == null) {
            Term* ans = t;
            DupCont* acont = cont;
            while (true) {
                if (acont == null) return ans;
                if (acont.inner) {
                    ans = new Term(acont.term.type, acont.term.a, acont.ans1, ans);
                    acont = acont.next;
                } else {
                    t = acont.term.t2;
                    cont = new DupCont(acont.term, true, ans, acont.next);
                    break;
                }
            }
        } else {
            cont = new DupCont(t, false, null, cont);
            t = t.t1;
        }
    }
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
    if (term == null) return applyBetaCont(term, var, val, cont);
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
    Term* ans;
    BetaCont* acont;
    do {
        bool computeAns = false;
        if (term == null) {
            computeAns = true;
            ans = term; acont = cont;
        } else if (term.type == TType.VAR) {
            computeAns = true;
            ans = term.a == var ? val : term; acont = cont;
        } else if (term.type == TType.ABS) {
            if (term.a == var) {
                computeAns = true;
                ans = term; acont = cont;
            } else {
                cont = new BetaCont(TType.ABS, 0, term, cont);
                term = term.t1;
            }
        } else {
            cont = new BetaCont(TType.APP, 1, term, cont);
            term = term.t1;
        }
        if (computeAns) {
            while(true) {
                if (acont == null) return ans;
                if (acont.type == TType.ABS) {
                        acont.term.t1 = ans;
                        ans = acont.term;
                        acont = acont.next;
                } else if (acont.type == TType.APP) {
                    if (acont.argNum == 1) {
                        acont.term.t1 = ans;
                        term = acont.term.t2;
                        cont = new BetaCont(acont.type, 2, acont.term, acont.next);
                        break;
                    } else {
                        acont.term.t2 = ans;
                        ans = acont.term;
                        acont = acont.next;
                    }
                } else {
                    acont = acont.next;
                }
            }
        }
    } while (true);
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


Term* evalCPS(Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0,
              Term* delegate(Term*) cont = (Term* t) { return t; }) {
    interfunc(term, depth);

    if (term.type == TType.VAR) {
        if (term.a == "print") {
            return cont(term);
        } else if ((term.a in env) !is null) {
            return evalCPS(env[term.a].dup, env, interfunc, depth, cont);
        } else assert(false, "Unbounded variable " ~ term.a);
    } else if (term.type == TType.APP) {
        if (term.t1.type == TType.ABS) {
            term.t1.t1 = betaOpt(term.t1.t1, term.t1.a, term.t2.dup);
            return evalCPS(term.t1.t1, env, interfunc, depth, cont);
        } else {
            if (term.t1.type == TType.VAR && term.t1.a == "print") {
                writefln("[print] ", term.t2.toString);
                return evalCPS(term.t2, env, interfunc, depth-1, cont);
            }
            return evalCPS(term.t1, env, interfunc, depth+1, (Term* ans) {
                term.t1 = ans;
                return evalCPS(term.t2, env, interfunc, depth+1, (Term* ans) {
                    term.t2 = ans;
                    return evalCPS(term, env, interfunc, depth, cont);
                });
            });
        }
    } else {
        return cont(term);
    }
}


struct EvalCont {
    Term* term;
    bool inner;
    int depth;
    EvalCont* next;
}

string toString(EvalCont* c) {
    import std.conv : to;
    if (c == null) return "NULL";
    return "(" ~ toString(c.term) ~ ", " ~ c.inner.to!string ~ ") -> " ~ toString(c.next);
}

Term* applyEvalCont(Term* ans, Env env, void delegate(Term*, int) interfunc, EvalCont* cont) {
    if (cont == null) return ans;
    if (cont.inner) {
        cont.term.t2 = ans;
        return evalDefun(cont.term, env, interfunc, cont.depth+1, cont.next);
    } else {
        cont.term.t1 = ans;
        return evalDefun(cont.term.t2, env, interfunc, cont.depth, new EvalCont(cont.term, true,
                    cont.depth, cont.next));
    }
}

Term* evalDefun(Term* term, Env env, void delegate(Term*, int) interfunc,
                int depth = 0, EvalCont* cont = null) {
    interfunc(term, depth);
    if (term.type == TType.VAR) {
        if (term.a == "print")
            return applyEvalCont(term, env, interfunc, cont);
        else if ((term.a in env) !is null)
            return evalDefun(env[term.a].dup, env, interfunc, depth, cont);
        else assert(false, "Unbounded variable " ~ term.a);
    } else if (term.type == TType.APP) {
        if (term.t1.type == TType.ABS) {
            term.t1.t1 = betaOpt(term.t1.t1, term.t1.a, term.t2.dup);
            return evalDefun(term.t1.t1, env, interfunc, depth-1, cont);
        }
        if (term.t1.type == TType.VAR && term.t1.a == "print") {
            writefln("[print] %s", term.t2.toString);
            return evalDefun(term.t2, env, interfunc, depth-1, cont);
        }
        return evalDefun(term.t1, env, interfunc, depth+1, new EvalCont(term, false, depth, cont));
    } else return applyEvalCont(term, env, interfunc, cont);
}


Term* evalOpt(Term* term, Env env, void delegate(Term*, int) interfunc,
              bool doBetaOpt, bool doDupOpt, int depth = 0, EvalCont* cont = null) {
    Term* ans;
    EvalCont* acont;
    do {
        interfunc(term, depth);
        int computeAns = false;
        if (term.type == TType.VAR) {
            if (term.a == "print") {
                computeAns = true;
                ans = term; acont = cont;
            } else if ((term.a in env) !is null) {
                term = doDupOpt ? env[term.a].dupOpt : env[term.a].dup;
            } else assert(false, "Unbounded variable " ~ term.a);
        } else if (term.type == TType.APP) {
            if (term.t1.type == TType.ABS) {
                Term* duped = doDupOpt ? term.t2.dupOpt : term.t2.dup;
                term.t1.t1 = doBetaOpt ? betaOpt(term.t1.t1, term.t1.a, duped)
                                       : beta(term.t1.t1, term.t1.a, duped);
                term = term.t1.t1;
                depth--;
            } else if (term.t1.type == TType.VAR && term.t1.a == "print") {
                writefln("[print] %s", term.t2.toString);
                term = term.t2;
                depth--;
            } else {
                cont = new EvalCont(term, false, depth, cont);
                term = term.t1;
                depth++;
            }
        } else {
            computeAns = true;
            ans = term; acont = cont;
        }

        if (computeAns) {
            if (acont == null) return ans;
            if (acont.inner) {
                acont.term.t2 = ans;
                term = acont.term;
                depth = acont.depth+1;
                cont = acont.next;
            } else {
                acont.term.t1 = ans;
                term = acont.term.t2;
                depth = acont.depth;
                cont = new EvalCont(acont.term, true, acont.depth, acont.next);
            }
        }
    } while (true);
}


Term* eval(Term* term, Env env, void delegate(Term*, int) interfunc, bool doBetaOpt,
           bool doDupOpt, int depth = 0) {
    interfunc(term, depth);

    final switch (term.type) {
        case TType.VAR:
            if (term.a == "print") {
                return term;
            } else if ((term.a in env) !is null) {
                Term* dupped = doDupOpt ? env[term.a].dupOpt : env[term.a].dup;
                return eval(dupped, env, interfunc, doBetaOpt, doDupOpt, depth);
            } else assert(false, "Unbound variable " ~ term.a);
        case TType.APP:
            if (term.t1.type == TType.ABS) {
                Term* duped = doDupOpt ? term.t2.dupOpt : term.t2.dup;
                term.t1.t1 = doBetaOpt ? betaOpt(term.t1.t1, term.t1.a, duped)
                                       : beta(term.t1.t1, term.t1.a, duped);
                return eval(term.t1.t1, env, interfunc, doBetaOpt, doDupOpt, depth);
            } else {
                if (term.t1.type == TType.VAR && term.t1.a == "print") {
                    writefln("[print] %s", term.t2.toString);
                    return eval(term.t2, env, interfunc, doBetaOpt, doDupOpt, depth-1);
                }
                term.t1 = eval(term.t1, env, interfunc, doBetaOpt, doDupOpt, depth+1);
                term.t2 = eval(term.t2, env, interfunc, doBetaOpt, doDupOpt, depth+1);
                return eval(term, env, interfunc, doBetaOpt, doDupOpt, depth);
            }
        case TType.ABS:
            return term;
    }
}



void main(string[] args) {
    bool debugMode = false;
    bool doEvalOpt = false;
    bool doBetaOpt = false;
    bool doDupOpt = false;
    string source = "";
    int evalCount = 0;
    Env env;

    getopt(
        args,
        "debug", &debugMode,
        "e", &doEvalOpt,
        "b", &doBetaOpt,
        "d", &doDupOpt
    );
    if (args.length > 1) source = args[1];

    void delegate(Term*,int) debugCont = (Term* step, int depth) {
        writefln("  >%s %s", ">".repeat(depth).joiner(""), toString(step));
        evalCount++;
    };
    void delegate(Term*,int) normalCont = (Term* step, int depth) {
        evalCount++;
    };

    void handle(string exprs) {
        foreach (expr; exprs.split(";")) {
            if (expr.length == 0) continue;
            string[] tokens = expr.split("=");
            try
                if (tokens.length > 1)
                    env[tokens[0].strip] = parse(tokens[1..$].joiner("=").text);
                else if (tokens.length == 1 && tokens[0].strip.length > 0) {
                    if (doEvalOpt) {
                        evalOpt(expr.parse, env,
                                debugMode ? debugCont : normalCont,
                                doBetaOpt, doDupOpt).toString.writeln;
                    } else {
                        eval(expr.parse, env,
                             debugMode ? debugCont : normalCont,
                             doBetaOpt, doDupOpt).toString.writeln;
                    }
                    writefln("\t%d reductions", evalCount);
                    evalCount = 0;
                }
            catch (Exception e) writefln("error: %s", e.msg);
            catch (Error e) writefln("error: %s", e.msg);
        }
    }

    if (source.length > 0) {
        handle(source.readText ~ "; main");
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
