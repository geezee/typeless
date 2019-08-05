module evals;

import std.stdio : writefln;

import lambdacalc;

Term* evalCPS(alias beta, alias dup)(Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0,
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


Term* applyEvalCont(alias beta, alias dup)(Term* ans, Env env, void delegate(Term*, int) interfunc, EvalCont* cont) {
    if (cont == null) return ans;
    if (cont.inner) {
        cont.term.t2 = ans;
        return evalDefun!(beta,dup)(cont.term, env, interfunc, cont.depth+1, cont.next);
    } else {
        cont.term.t1 = ans;
        return evalDefun!(beta,dup)(cont.term.t2, env, interfunc, cont.depth, new EvalCont(cont.term, true,
                    cont.depth, cont.next));
    }
}


struct EvalCont {
    Term* term;
    bool inner;
    int depth;
    EvalCont* next;
}

Term* evalDefun(alias beta, alias dup)(Term* term, Env env, void delegate(Term*, int) interfunc,
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


Term* evalOpt(alias beta, alias dup)
             (Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0, EvalCont* cont = null) {
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
                term = dup(env[term.a]);
            } else assert(false, "Unbounded variable " ~ term.a);
        } else if (term.type == TType.APP) {
            if (term.t1.type == TType.ABS) {
                term.t1.t1 = beta(term.t1.t1, term.t1.a, dup(term.t2));
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

struct EvalData {
    Term* term;
    bool inner;
    int depth;
}

Term* evalOptStack(alias beta, alias dup)
                  (Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0,
                   Stack!(EvalData*)* stack = new Stack!(EvalData*)()) {
    Term* ans;
    EvalData* cont;
    while (true) {
        interfunc(term, depth);
        bool computeAns = false;
        if (term.type == TType.VAR) {
            if (term.a == "print") {
                computeAns = true;
                ans = term;
            } else if ((term.a in env) !is null) {
                term = dup(env[term.a]);
            } else assert(false, "Unbound variable " ~ term.a);
        } else if (term.type == TType.APP) {
            if (term.t1.type == TType.ABS) {
                term.t1.t1 = beta(term.t1.t1, term.t1.a, dup(term.t2));
                term = term.t1.t1;
                depth--;
            } else if (term.t1.type == TType.VAR && term.t1.a == "print") {
                writefln("[print] %s", term.t2.toString);
                term = term.t2;
                depth--;
            } else {
                stack.insertFront(new EvalData(term, false, depth));
                term = term.t1;
                depth++;
            }
        } else {
            computeAns = true;
            ans = term;
        }

        if (computeAns) {
            if (stack.empty) return ans;
            cont = stack.front;
            stack.removeFront();
            if (cont.inner) {
                cont.term.t2 = ans;
                term = cont.term;
                depth = cont.depth + 1;
            } else {
                cont.term.t1 = ans;
                term = cont.term.t2;
                depth = cont.depth;
                stack.insertFront(new EvalData(cont.term, true, cont.depth));
            }
        }
    }
}


Term* eval(alias beta, alias dup)
          (Term* term, Env env, void delegate(Term*, int) interfunc, int depth = 0) {
    interfunc(term, depth);

    final switch (term.type) {
        case TType.VAR:
            if (term.a == "print") {
                return term;
            } else if ((term.a in env) !is null) {
                return eval!(beta,dup)(dup(env[term.a]), env, interfunc, depth);
            } else assert(false, "Unbound variable " ~ term.a);
        case TType.APP:
            if (term.t1.type == TType.ABS) {
                term.t1.t1 = beta(term.t1.t1, term.t1.a, dup(term.t2));
                return eval!(beta,dup)(term.t1.t1, env, interfunc, depth);
            } else {
                if (term.t1.type == TType.VAR && term.t1.a == "print") {
                    writefln("[print] %s", term.t2.toString);
                    return eval!(beta,dup)(term.t2, env, interfunc, depth-1);
                }
                term.t1 = eval!(beta,dup)(term.t1, env, interfunc, depth+1);
                term.t2 = eval!(beta,dup)(term.t2, env, interfunc, depth+1);
                return eval!(beta,dup)(term, env, interfunc, depth);
            }
        case TType.ABS:
            return term;
    }
}
