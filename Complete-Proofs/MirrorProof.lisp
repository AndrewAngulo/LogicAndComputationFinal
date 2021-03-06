; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(cons 1 (cons 2 (cons 3 (cons 4 ()))))
;; Which can be simplified to what is known
;; as dot form, where the cons is replaced
;; by a .
'(1 . (2 . (3 . (4 . ()))))

;; ALL -> ALL
;; The mirror function reverses the construction of the input
;; if it is a cons otherwise it returns its input
;; this function recurs deeply, reversing the construction of any elements
;; of the list that are also cons'
(definec mirror (tr :all) :all 
  (if (consp tr) 
    (cons (mirror (cdr tr)) 
          (mirror (car tr)))
    tr))

;; Examples of mirror functionality
(check= (mirror '(1 2 3)) '(((() . 3) . 2) . 1))
(check= (mirror '()) '())
(check= (mirror "apple") "apple")
(check= (mirror '(1 2 (3 4))) '(((() (() . 4) . 3) . 2) . 1))
(check= (mirror '((1 2)(3 4)(5 6))) 
        '(((() (() . 6) . 5) (() . 4) . 3)(() . 2) . 1))


;; TL X TL -> TL
;; Function which appends two lists
;; If the first list is empty, the second list is returned
(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
      (cons (first a) 
            (app2 (rest a) b))))

(check= (app2 '(1 2 3) '(4 5 6)) '(1 2 3 4 5 6))
(check= (app2 '() '(4 5 6)) '(4 5 6))
(check= (app2 '(1 2 3) '()) '(1 2 3))
(check= (app2 '() '()) '())
(check= (app2 '(1 2 3) '((4 5 6)(7 8 9))) '(1 2 3 (4 5 6)(7 8 9)))

;; TL -> TL
;; Function that returns the reverse of the input list
;; returns and empty list in the case where the input
;; list is empty
(definec rev2 (x :tl) :tl
  (if (endp x)
      nil
      (app2 (rev2 (rest x)) 
            (list (first x)))))

;; rev2 examples
(check= (rev2 '(1 2 3)) '(3 2 1))
(check= (rev2 '()) '())
(check= (rev2 '(1 2 (3 4))) '((3 4) 2 1))
(check= (rev2 '((1 2)(3 4))) '((3 4)(1 2)))

;; We want to check that this theorem cannot be disproved quickly
;; with a counter example

(test?
 (implies (tlp x)
          (equal (rev2 (mirror (mirror (rev2 x))))
                 x)))

;; This check passes
;; Here are some visual examples to help understand the problem

(check= (rev2 '(1 2 3 4)) '(4 3 2 1))
(check= (mirror (rev2 '(1 2 3 4))) '((((() . 1) . 2) . 3) . 4))
(check= (mirror (mirror (rev2 '(1 2 3 4)))) '(4 3 2 1))
(check= (rev2 (mirror (mirror (rev2 '(1 2 3 4))))) '(1 2 3 4))

;; To prove this theorem we can ignore the reverse operation at the beggining and the
;; end as they will obviously cancel each other. The goal of our theorem then becomes 
;; proving that the (mirror (mirror x)) is equal to x.

;; This can be proved inductively, where we assume that the (mirror (mirror (cdr x))) is 
;; equal to the (cdr x), however that is not enough for ACL2 to automatically assume the 
;; theorem

;; Inductive Hypothesis 1
(implies (tlp (cdr x))
         (equal (mirror (mirror (cdr x))) (cdr x)))

;; Inductive Hypothesis 2
(implies (tlp (car x))
         (equal (mirror (mirror (car x))) (car x)))

;; Expansion of (mirror (mirror x)) in the inductive case
(mirror (cons (mirror (cdr x)) (mirror (car x))))

;; In the expansion of (mirror x) in our lemma mirror-mirror can be expanded out to
;; (mirror (cons (mirror (cdr x)) (mirror (car x)))), which can be rewritten as 
;; (cons (mirror (mirror (car x))) (mirror (mirror (cdr x)))). This is automatically proved
;; by ACL2 and does not need a lemma. 

;; At this point it is clear that the above statement must be reduced to (cons (car x) (cdr x))
;; in order for our lemma mirror-mirror to be proved. The cdr case is already handled by the 
;; inductive hypothesis from the induction scheme (mirror x), but the car case is not, and is 
;; where ACL2 is unable to solve the theorem automatically, as the car of x can either be a 
;; non cons element, or a cons that the function must recur deeply on.

;; This problem is simply solved by proving that (mirror (mirror (car x))) is equal to (car x)
;; by induction on tlp, which ACL2 can prove automatically

(defthm mirror-mirror-car
  (implies (tlp x)
           (equal (mirror (mirror (car x)))
                  (car x))))

;; With the above theorem proved, acl2 can now prove the mirror-mirror lemma

(defthm mirror-mirror
  (implies (tlp x)
           (equal (mirror (mirror x))
                  x)))

;; And with this lemma proved, we can prove the target theorem as the reverses have no effect
;; on the output of the function which ACL2 can prove automatically by induction of (rev2 x)

(defthm mirror-claim
  (implies (tlp x)
           (equal (rev2 
                   (mirror (mirror (rev2 x))))
                  x)))

;;#| ;; This was used originally but is not necessary for proving the above theorem
(defthm mirror-distr
  (implies (and (tlp x) (consp x))
           (equal (mirror (cons (mirror (cdr x)) (mirror (car x))))
                  (cons (mirror (mirror (car x))) (mirror (mirror (cdr x)))))))
;;|#
