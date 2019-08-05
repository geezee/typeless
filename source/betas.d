module betas;

import lambdacalc;

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

struct BetaData {
    int argNum;
    Term* term;
}

Term* betaOptStack(Term* term, string var, Term* val, Stack!(BetaData*)* stack = new Stack!(BetaData*)()) {
    Term* ans;
    BetaData* cont;
    while (true) {
        bool computeAns = false;
        if (term == null) {
            computeAns = true;
            ans = term;
        } else if (term.type == TType.VAR) {
            computeAns = true;
            ans = term.a == var ? val : term;
        } else if (term.type == TType.ABS) {
            if (term.a == var) {
                computeAns = true;
                ans = term;
            } else {
                stack.insertFront(new BetaData(0, term));
                term = term.t1;
            }
        } else {
            stack.insertFront(new BetaData(1, term));
            term = term.t1;
        }
        if (computeAns) {
            while (true) {
                if (stack.empty) return ans;
                cont = stack.front;
                stack.removeFront();
                if (cont.term.type == TType.ABS) {
                    cont.term.t1 = ans;
                    ans = cont.term;
                } else if (cont.term.type == TType.APP) {
                    if (cont.argNum == 1) {
                        cont.term.t1 = ans;
                        term = cont.term.t2;
                        stack.insertFront(new BetaData(2, cont.term));
                        break;
                    } else {
                        cont.term.t2 = ans;
                        ans = cont.term;
                    }
                }
            }
        }
    }
}

// Rewrote beta so it uses CPS
Term* betaCPS(Term* term, string var, Term* val, Term* delegate(Term*) cont = (Term* t) { return t; }) {
    if (term == null) return term;
    final switch (term.type) {
        case TType.VAR:
            return cont(term.a == var ? val : term);
        case TType.ABS:
            if (term.a == var) return cont(term);
            return betaCPS(term.t1, var, val, (Term* ans) {
                term.t1 = ans;
                return cont(term);
            });
        case TType.APP:
            return betaCPS(term.t1, var, val, (Term* ans1) {
                term.t1 = ans1;
                return betaCPS(term.t2, var, val, (Term* ans2) {
                    term.t2 = ans2;
                    return cont(term);
                });
            });
    }
}

Term* beta(Term* term, string var, Term* val) {
    if (term == null) return term;
    final switch (term.type) {
        case TType.VAR:
            return term.a == var ? val : term;
        case TType.ABS:
            if (term.a == var) return term;
            term.t1 = beta(term.t1, var, val);
            return term;
        case TType.APP:
            term.t1 = beta(term.t1, var, val);
            term.t2 = beta(term.t2, var, val);
            return term;
    }
}
