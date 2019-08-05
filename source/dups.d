module dups;

import lambdacalc;

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


struct DupData {
    Term* term;
    bool inner;
    Term* ans1;
}

Term* dupOptStack(Term* t, Stack!(DupData*)* stack = new Stack!(DupData*)()) {
    Term* ans;
    DupData* cont;
    while (true) {
        if (t == null) {
            ans = t;
            while (true) {
                if (stack.empty) return ans;
                cont = stack.front;
                stack.removeFront();
                if (cont.inner) {
                    ans = new Term(cont.term.type, cont.term.a, cont.ans1, ans);
                } else {
                    t = cont.term.t2;
                    stack.insertFront(new DupData(cont.term, true, ans));
                    break;
                }
            }
        } else {
            stack.insertFront(new DupData(t, false, null));
            t = t.t1;
        }
    }
}
