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
module betas;

import lambdacalc;



// Original recursive function
Term* beta(alias dup)(Term* term, string var, Term* val) {
    if (term == null) return term;
    final switch (term.type) {
        case TType.VAR:
            return term.a == var ? dup(val) : term;
        case TType.ABS:
            if (term.a == var) return term;
            term.t1 = beta!dup(term.t1, var, val);
            return term;
        case TType.APP:
            term.t1 = beta!dup(term.t1, var, val);
            term.t2 = beta!dup(term.t2, var, val);
            return term;
    }
}



// recursive version rewritten in continuation-passing style
Term* betaCPS(alias dup)(Term* term, string var, Term* val, Term* delegate(Term*) cont = (Term* t) { return t; }) {
    if (term == null) return term;
    final switch (term.type) {
        case TType.VAR:
            return cont(term.a == var ? dup(val) : term);
        case TType.ABS:
            if (term.a == var) return cont(term);
            return betaCPS!dup(term.t1, var, val, (Term* ans) {
                term.t1 = ans;
                return cont(term);
            });
        case TType.APP:
            return betaCPS!dup(term.t1, var, val, (Term* ans1) {
                term.t1 = ans1;
                return betaCPS!dup(term.t2, var, val, (Term* ans2) {
                    term.t2 = ans2;
                    return cont(term);
                });
            });
    }
}



// For defunctionalization we ned to represent every lambda passed to betaCPS
struct BetaCont {
    TType type;
    int argNum;     // when type=APP: 0 means lambda at line 40, 1 is the one at line 42;
    Term* term;
    BetaCont* next;
}

// the special apply function needed for defunctionalization
// var, val in here because they never change
Term* applyBeta(alias dup)(Term* ans, string var, Term* val, BetaCont* cont) {
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
                    return betaDefun!dup(cont.term.t2, var, val, new BetaCont(cont.type, 2, cont.term, cont.next));
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

// the defunctionalized version of beta
Term* betaDefun(alias dup)(Term* term, string var, Term* val, BetaCont* cont = null) {
    if (term == null) return applyBeta!dup(term, var, val, cont);
    final switch (term.type) {
        case TType.VAR:
            return applyBeta!dup(term.a == var ? dup(val) : term, var, val, cont);
        case TType.ABS:
            if (term.a == var) return applyBeta!dup(term, var, val, cont);
            else return betaDefun!dup(term.t1, var, val, new BetaCont(TType.ABS, 0, term, cont));
        case TType.APP:
            return betaDefun!dup(term.t1, var, val, new BetaCont(TType.APP, 1, term, cont));
    }
}


// After performing inlining and tail-call optimization on betaDefun and applyBeta
Term* betaOpt(alias dup)(Term* term, string var, Term* val, BetaCont* cont = null) {
    Term* ans;
    BetaCont* acont;
    do {
        bool computeAns = false;
        if (term == null) {
            computeAns = true;
            ans = term; acont = cont;
        } else if (term.type == TType.VAR) {
            computeAns = true;
            ans = term.a == var ? dup(val) : term; acont = cont;
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
