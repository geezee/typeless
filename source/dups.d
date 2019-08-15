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
module dups;

import lambdacalc;



// Original recursive function
Term* dup(Term* t) {
    if (t == null) return null;
    return new Term(t.type, t.a, t.t1.dup, t.t2.dup);
}



// recursive version rewritten in continuation-passing style
Term* dupCPS(Term* t, Term* delegate(Term*) cont) {
    if (t == null) return cont(null);
    return dupCPS(t.t1, (Term* ans1) {
        return dupCPS(t.t2, (Term* ans2) {
            return new Term(t.type, t.a, ans1, ans2);
        });
    });
}



// For defunctionalization we need to represent every lambda passed to dupCPS
struct DupCont {
    Term* term;     
    bool inner;     // true represents the lambda at line 20, false is the one at line 19
    Term* ans1;     // ans1 is the argument to the outer lambda
    DupCont* next;  // next is basically the continuation
}

// the special apply function needed for defunctionalization
Term* applyDup(Term* ans, DupCont* cont) {
    if (cont == null) return ans;
    if (cont.inner) {
        Term* t = new Term(cont.term.type, cont.term.a, cont.ans1, ans);
        return applyDup(t, cont.next);
    } else {
        return dupDefun(cont.term.t2, new DupCont(cont.term, true, ans, cont.next));
    }
}

// the defunctionalized version of dup
Term* dupDefun(Term* t, DupCont* cont = null) {
    if (t == null) return applyDup(t, cont);
    return dupDefun(t.t1, new DupCont(t, false, null, cont));
}



// After performing inlining and tail-call optimization on dupDefun and applyDup
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
