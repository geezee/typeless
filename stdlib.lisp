id = lambda t t;
const = lambda c (lambda _ c);

true = lambda t (lambda f t);
false = lambda t (lambda f f);
not = lambda b (b false true);
if = lambda b (lambda t (lambda f (b t f)));
and = lambda a (lambda b (a b false));
or = lambda a (lambda b (a true b));
eq-b? = and;

pair = lambda a (lambda b (lambda c (if c a b)));
left = lambda p (p true);
right = lambda p (p false);
apply-if-true = lambda f (lambda p (if (left p) (pair (left p) (f (right p))) p));
apply-first = lambda f (lambda p (pair (f (left p)) (right p)));
apply-second = lambda f (lambda p (pair (left p) (f (right p))));
apply-if-else = lambda f (lambda g (lambda p (if (left p) (f p) (g p))));

zero = lambda S (lambda z z);
succ = lambda n (lambda S (lambda z (n S (S z))));
zero? = lambda b (b (const false) true);
add = lambda n (lambda m (lambda S (lambda z (n S (m S z)))));
mult = lambda n (lambda m (lambda S (lambda z (m (n S) z))));
odd? = lambda b (b not false);
even? = lambda b (b not true);
pred_h = lambda n (n (lambda p (apply-if-else (apply-first not)
                                              (apply-second succ)
                                              p))
                     (pair true zero));
pred = lambda n (right (pred_h n));
minus = lambda n (lambda m (m pred n));
eq-n? = lambda n (lambda m (and (zero? (minus n m))
                                (zero? (minus m n))));

0 = zero;
1 = (succ 0);
2 = (succ 1);
3 = ((mult (succ 2)) 1);
4 = ((add 3) 1);
5 = (pred ((add 2) 4));
8 = ((add 4) ((mult 2) 2));
10 = ((mult 5) 2);

nil = lambda c (lambda z z);
cons = lambda hd (lambda tl
            (lambda c (lambda z (if c hd (if z c tl)))));

nil? = lambda l (l false true);
head = lambda l (l true false);
tail = lambda l (l false false);

length = lambda l ((if (nil? l)
                       (lambda _ zero)
                       (lambda _ (succ (length (tail l))))) id);

map = lambda f (lambda l
            ((if (nil? l)
                 (lambda _ nil)
                 (lambda _ (cons (f (head l)) (map f (tail l))))) id));

filter = lambda f (lambda l
            ((if (nil? l)
                 (lambda _ nil)
                 (lambda _ (if (f (head l))
                               (cons (head l) (filter f (tail l)))
                               (filter f (tail l))))) id));

foldr = lambda proc (lambda init (lambda lst
            ((if (nil? lst)
                 (lambda _ init)
                 (lambda _ (foldr proc
                                  (proc (head lst) init)
                                  (tail lst)))) id)));

append = lambda lst1 (lambda lst2
            ((if (nil? lst1)
                 (lambda _ lst2)
                 (lambda _ (cons (head lst1) (append (tail lst1) lst2)))) id));

reverse = lambda lst ((if (nil? lst)
                          (lambda _ nil)
                          (lambda _ (append (reverse (tail lst))
                                            (cons (head lst) nil)))) id);

dummy-list = (cons 3 (cons 2 (cons 1 nil)));

print-num = lambda n (n (const (print 1)) 0);
print-bool = lambda b ((if b (lambda _ (print true)) (lambda _ (print false))) id);


fact = lambda n ((if (zero? n) (lambda _ 1) (lambda _ (mult n (fact (pred n))))) id);

Y = lambda f (
        (lambda x (f (x x)))
        (lambda x (f (x x))));

fact-y = lambda self (lambda n ((if (zero? n)
                                    (lambda _ 1)
                                    (lambda _ (mult n (self (pred n))))) id));

fib-y = lambda self (lambda n
            ((if (zero? n)
                 (lambda _ 1)
                 (lambda _ (if (eq-n? n 1)
                               1
                               (add (self (pred n))
                                    (self (pred (pred n))))))) id));


fibonacci = (Y fib-y);

main = (print-num (fact 8));
