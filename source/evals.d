/*
Copyright 2019 - George Zakhour

This file is part of typeless.git

typeless.git is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

typeless.git is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with typeless.git. If not, see <https://www.gnu.org/licenses/>.
*/
module evals;

import std.stdio : writefln;
import std.conv : to;

import lambdacalc;


// Original recursive function
// the two template parameters `beta` and `dup` are the beta/dup functions to use
Term* eval(alias beta, alias dup)
          (Term* term, ref Env env, DFunc interfunc, int depth = 0) {
    interfunc(term, depth);

    final switch (term.type) {
        case TType.VAR:
            switch (term.a) {
                case "print": return term;
                case "qeq?": return parse("lambda a (lambda b (__builtin_qeq_1? a b))");
                default: break;
            }
            if ((term.a in env) !is null) {
                return eval!(beta,dup)(dup(env[term.a]), env, interfunc, depth);
            } else {
                writefln("variable %s is unbound", term.a);
                assert(false, "Unbound variable " ~ term.a);
            }
        case TType.APP:
            if (term.t1.type == TType.ABS) {
                term.t1.t1 = beta!dup(term.t1.t1, term.t1.a, term.t2);
                return eval!(beta,dup)(term.t1.t1, env, interfunc, depth);
            } else {
                if (term.t1.type == TType.VAR) {
                    string[] tokens = term.t1.a.split("-");
                    string varName = tokens[0];
                    string[] args = tokens[1..$];
                    switch (varName) {
                        case "print":
                            writefln("[print] %s", term.t2.toString);
                            return eval!(beta,dup)(term.t2, env, interfunc, depth+1);
                        case "__builtin_qeq_1?":
                            term.t2 = eval!(beta,dup)(term.t2, env, interfunc, depth+1);
                            string vName = freshVar();
                            env[vName] = term.t2;
                            return parse("lambda b (__builtin_qeq_2?-" ~ vName ~ " b)");
                        case "__builtin_qeq_2?":
                            term.t2 = eval!(beta,dup)(term.t2, env, interfunc, depth+1);
                            Term* left = env[args[0]]; // assume: args.length == 1, env contains arg
                            if (term.t2.type != TType.QUOTE || left.type != TType.QUOTE)
                                assert(false, "qeq? takens two quotes, you have provided it " ~
                                        left.type.to!string ~ " and " ~ term.t2.type.to!string);
                            else if (term.t2.a == left.a) return parse("lambda t (lambda f t)");
                            else return parse("lambda t (lambda f f)");
                        default: break;
                    }
                }
                term.t1 = eval!(beta,dup)(term.t1, env, interfunc, depth+1);
                term.t2 = eval!(beta,dup)(term.t2, env, interfunc, depth+1);
                return eval!(beta,dup)(term, env, interfunc, depth);
            }
        case TType.ABS:
            return term;
        case TType.QUOTE:
            return term;
    }
}



// recursive version rewritten in continuation-passing style
// the two template parameters `beta` and `dup` are the beta/dup functions to use
Term* evalCPS(alias beta, alias dup)
             (Term* term, ref Env env, DFunc interfunc, int depth = 0,
              Term* delegate(Term*) cont = (Term* t) { return t; }) { // default continuation: do nothing
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



enum EvalLabel {
    INNER,
    OUTER,
    __BUILTIN_QEQ_1,
    __BUILTIN_QEQ_2
}

// For defunctionalization we need to represent every lambda passed to evalCPS
struct EvalCont {
    Term* term;
    EvalLabel label;
    int depth;
    EvalCont* next;
    string[] args;
}

// the special apply function needed for defunctionalization
// the two template parameters `beta` and `dup` are the beta/dup functions to use
Term* applyEval(alias beta, alias dup)
               (Term* ans, ref Env env, DFunc interfunc, EvalCont* cont) {
    if (cont == null) return ans;
    if (cont.label == EvalLabel.INNER) {
        cont.term.t2 = ans;
        return evalDefun!(beta,dup)(cont.term, env, interfunc, cont.depth+1, cont.next);
    } else {
        cont.term.t1 = ans;
        return evalDefun!(beta,dup)(cont.term.t2, env, interfunc, cont.depth,
                new EvalCont(cont.term, EvalLabel.INNER, cont.depth, cont.next));
    }
}

// the defunctionalized version of eval
// the two template parameters `beta` and `dup` are the beta/dup functions to use
Term* evalDefun(alias beta, alias dup)
               (Term* term, ref Env env, DFunc interfunc, int depth = 0, EvalCont* cont = null) {
    interfunc(term, depth);
    if (term.type == TType.VAR) {
        if (term.a == "print")
            return applyEval(term, env, interfunc, cont);
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
        return evalDefun(term.t1, env, interfunc, depth+1,
                new EvalCont(term, EvalLabel.OUTER, depth, cont));
    } else return applyEval(term, env, interfunc, cont);
}



// After performing inlining and tail-call optimization on evalDefun and applyEval
// the two template parameters `beta` and `dup` are the beta/dup functions to use
Term* evalOpt(alias beta, alias dup)
             (Term* term, ref Env env, DFunc interfunc, int depth = 0, EvalCont* cont = null) {
    Term* ans;
    EvalCont* acont;
    do {
        interfunc(term, depth);
        int computeAns = false;
        if (term.type == TType.VAR) {
            switch (term.a.split("-")[0]) {
                case "print":
                    computeAns = true; ans = term; acont = cont;
                    break;
                case "qeq?":
                    computeAns = true;
                    ans = parse("lambda a (lambda b (__builtin_qeq_1? a b))");
                    acont = cont;
                    break;
                default:
                    if ((term.a in env) !is null) {
                        term = dup(env[term.a]);
                    } else assert(false, "Unbounded variable " ~ term.a);
            }
        } else if (term.type == TType.APP) {
            if (term.t1.type == TType.ABS) {
                term.t1.t1 = beta!dup(term.t1.t1, term.t1.a, term.t2);
                term = term.t1.t1;
                depth--;
            } else {
                string[] tokens = term.t1.a.split("-");
                string varName = tokens.length > 0 ? tokens[0] : "";
                string[] args = tokens.length > 1 ? tokens[1..$] : [];
                switch (varName) {
                    case "print":
                        writefln("[print] %s", term.t2.toString);
                        term = term.t2;
                        depth++;
                        break;
                    case "__builtin_qeq_1?":
                        depth++;
                        term = term.t2;
                        cont = new EvalCont(term, EvalLabel.__BUILTIN_QEQ_1, depth, cont);
                        break;
                    case "__builtin_qeq_2?":
                        depth++;
                        cont = new EvalCont(term, EvalLabel.__BUILTIN_QEQ_2, depth, cont, args);
                        term = term.t2;
                        break;
                    default:
                        depth++;
                        cont = new EvalCont(term, EvalLabel.OUTER, depth, cont);
                        term = term.t1;
                }
            }
        } else {
            computeAns = true;
            ans = term; acont = cont;
        }

        while (computeAns) {
            computeAns = false;
            if (acont == null) return ans;
            final switch (acont.label) {
                case EvalLabel.INNER:
                    acont.term.t2 = ans;
                    term = acont.term;
                    depth = acont.depth+1;
                    cont = acont.next;
                    break;
                case EvalLabel.OUTER:
                    acont.term.t1 = ans;
                    term = acont.term.t2;
                    depth = acont.depth;
                    cont = new EvalCont(acont.term, EvalLabel.INNER, acont.depth, acont.next);
                    break;
                case EvalLabel.__BUILTIN_QEQ_1:
                    acont.term.t2 = ans;
                    string vName = freshVar();
                    env[vName] = ans;
                    computeAns = true;
                    acont = acont.next;
                    ans = parse("lambda b (__builtin_qeq_2?-" ~ vName ~ " b)");
                    break;
                case EvalLabel.__BUILTIN_QEQ_2:
                    acont.term.t2 = ans;
                    Term* left = env[acont.args[0]];
                    if (ans.type != TType.QUOTE || left.type != TType.QUOTE)
                        assert(false, "qeq? takens two quotes, you have provided it " ~
                                left.type.to!string ~ " and " ~ term.t2.type.to!string);
                    computeAns = true;
                    acont = acont.next;
                    if (ans.a == left.a) ans = parse("lambda t (lambda f t)");
                    else ans = parse("lambda t (lambda f f)");
            }
        }
    } while (true);
}
