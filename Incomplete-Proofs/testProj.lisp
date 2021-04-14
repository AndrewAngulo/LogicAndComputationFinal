; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;; Final Project
;; Proving Theorems over Heap Sort

;; I will be representing heaps as a true list of an atom

;; Step one will be creating a function two swap two items in
;; an list by their indices, returning the modified list

(definec len2 (x :tl) :nat
  (if (endp x)
    0
    (+ 1 (len2 (rest x)))))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
    b
    (cons (first a) (app2 (rest a) b))))

(defdata lon (listof nat))

(definec get-at (index :nat list :lon) :nat
  :ic (and (< index (len2 list)) (not (endp list)))
  (cond ((== index 0) (car list))
        (t (get-at (- index 1) (cdr list)))))

(check= (get-at 3 '(1 2 3 4 5)) 4)
(check= (get-at 0 '(1 2 3 4 5)) 1)

(definec put (l :lon index :nat val :nat) :lon
  :ic (and (< index (len2 l)) (not (endp l)))
  (if (== index 0)
    (cons val (rest l))
    (cons (first l) (put (rest l) (- index 1) val))))

(check= (put '(1 2 3 4 5) 2 17) '(1 2 17 4 5))
(check= (put '(1 2 3 4 5) 0 100) '(100 2 3 4 5))
(check= (put '(1 2 3 4 5) 4 1) '(1 2 3 4 1))

(set-gag-mode nil)

#|
(PROGN
 (ENCAPSULATE
   NIL
   (ENCAPSULATE
        ((ACL2S-TRUE-LIST-UNDEFINED2 (X Y)
                                    T
                                    :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
        (LOCAL (DEFUN ACL2S-TRUE-LIST-UNDEFINED2 (X Y)
                      (DECLARE (IGNORABLE X Y))
                      'NIL))
        (DEFTHM ACL2S-TRUE-LIST-UNDEFINED2-TRUE-LISTP
                (TRUE-LISTP (ACL2S-TRUE-LIST-UNDEFINED2 X Y))
                :RULE-CLASSES ((:TYPE-PRESCRIPTION) (:REWRITE))))
   (DEFUN ACL2S-TRUE-LIST-UNDEFINED2-ATTACHED (X Y)
          (DECLARE (XARGS :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
          (PROG2$ (CGEN::CW? (SHOW-CONTRACT-VIOLATIONS?)
                             "~|**Input contract  violation in ~x0**: ~x1 ~%"
                             'ACL2S-TRUE-LIST-UNDEFINED2-ATTACHED
                             (CONS X Y))
                  'NIL))
   (DEFATTACH ACL2S-TRUE-LIST-UNDEFINED2
              ACL2S-TRUE-LIST-UNDEFINED2-ATTACHED))
 (ENCAPSULATE
  NIL
  (WITH-OUTPUT
   :OFF :ALL :ON (ERROR)
   (DEFUN SWAP (L INDEX1 INDEX2)
          (DECLARE (XARGS :GUARD (AND (NON-EMPTY-TRUE-LISTP L)
                                      (NATP INDEX1)
                                      (NATP INDEX2)
                                      (< INDEX1 (LEN2 L))
                                      (< INDEX2 (LEN2 L)))
                          :VERIFY-GUARDS NIL
                          :NORMALIZE NIL
                          :TIME-LIMIT 75/2))
          (MBE :LOGIC (IF (AND (NON-EMPTY-TRUE-LISTP L)
                               (NATP INDEX1)
                               (NATP INDEX2)
                               (< INDEX1 (LEN2 L))
                               (< INDEX2 (LEN2 L)))
                          (PUT (PUT L INDEX1 (GET-AT INDEX2 L))
                               INDEX2 (GET-AT INDEX1 L))
                          (ACL2S-TRUE-LIST-UNDEFINED2 'SWAP
                                                     (LIST L INDEX1 INDEX2)))
               :EXEC (PUT (PUT L INDEX1 (GET-AT INDEX2 L))
                          INDEX2 (GET-AT INDEX1 L))))))
 (DEFTHM SWAP-CONTRACT
         (IMPLIES (AND (FORCE (NON-EMPTY-TRUE-LISTP L))
                       (FORCE (NATP INDEX1))
                       (FORCE (NATP INDEX2))
                       (FORCE (< INDEX1 (LEN2 L)))
                       (FORCE (< INDEX2 (LEN2 L))))
                  (TRUE-LISTP (SWAP L INDEX1 INDEX2))))
 (ENCAPSULATE
    NIL
         (VERIFY-GUARDS SWAP
                        :GUARD-DEBUG T
                        :HINTS (("Goal" 
                                        :DO-NOT '(GENERALIZE FERTILIZE))))))
|#

(definec ne-lonp (l :lon) :bool
  (not (endp l)))#|ACL2s-ToDo-Line|#


;; NOTE: I changed back to more specific and removed ne-tl
(definec swap (l :lon index1 :nat index2 :nat) :lon
  ;;(declare (xargs :mode :program))
  :ic (and (ne-lonp l) (< index1 (len2 l)) (< index2 (len2 l)))
    (put (put l index1 (get-at index2 l)) index2 (get-at index1 l)))


(check= (swap '(1 2 3 4 5) 0 4) '(5 2 3 4 1))
(check= (swap '(1 2 3 4 5) 0 0) '(1 2 3 4 5))
(check= (swap '(1) 0 0) '(1))
(check= (swap '(1 2 3 4 5) 4 0) '(5 2 3 4 1))

(definec largest-index (l :lon i1 :nat i2 :nat) :nat
  :ic (and (< i1 (len2 l)) (< i2 (len2 l)))
  (cond ((> (get-at i1 l) (get-at i2 l)) i1)
        (t i2)))

(check= (largest-index '(115 22 14 99) 0 1) 0)
(check= (largest-index '(115 22 14 99) 1 2) 1)
(check= (largest-index '(115 22 14 99) 1 3) 3)

;; returns the index of the largest
(definec get-largest (l :lon size :nat root :nat) :nat
  :ic (and (<= size (len2 l)) (< root size))
  (let ((left (+ (* root 2) 1)) (right (+ (* root 2) 2)))
    (cond ((and (< left size) (< right size)) 
           (largest-index l root (largest-index l left right)))
          ((< left size)(largest-index l root left))
          ((< right size)(largest-index l root right))
          (t root))))

(check= (get-largest '(1 2 3 4 5) 5 0) 2)
(check= (get-largest '(1 2) 2 0) 1)
(check= (get-largest '(1) 1 0) 0)

(definec heapify (l :lon size :nat root :nat)  :lon
  ;;(declare (xargs :mode :program))
  :ic (and (<= size (len2 l)) (< root size))
  (let ((largest (get-largest l size root)))
    (cond ((not (== largest root)) 
           (heapify (swap l root largest) size largest))
          (t l))))

(check= (heapify '(4 10 3 5 1) 5 0) '(10 5 3 4 1))
(check= (heapify '(4 10 3 5 1) 5 1) '(4 10 3 5 1))
(check= (heapify '(4 10 3 5 1) 5 3) '(4 10 3 5 1))
(check= (heapify '(4 10 3 5 1) 5 4) '(4 10 3 5 1))

(definec build-heap-itr (l :lon size :nat i :int) :lon
  (declare (xargs :mode :program))
  :ic (and (<= size (len2 l)) (< i size))
  (cond ((< i 0) l)
        (t (build-heap-itr (heapify l size i) size (- i 1)))))

(definec build-heap (l :lon size :nat) :lon
  (declare (xargs :mode :program))
  :ic (<= size (len2 l))
  (build-heap-itr l size (- (floor size 2) 1)))

(check= (build-heap '(1 12 9 5 6 10) 6) '(12 6 10 5 1 9))

(definec heap-sort-help-v2 (l :lon last :nat) :lon
  (declare (xargs :mode :program))
  :ic (and (< last (len2 l)) (not (endp l)))
  (cond ((== last 0) l)
        (t (heap-sort-help-v2 (heapify (swap l 0 last) last 0) (- last 1)))))

#|
(definec heap-sort-help (l :lon pointer :nat) :lon
  (declare (xargs :mode :program))
  :ic (< pointer (len2 l))
  (let ((swapped (swap l 0 pointer)))
    (if (== pointer 0)
      (heapify swapped pointer 0)
      (heap-sort-help (heapify swapped pointer 0) (- pointer 1)))))
|#

(definec heap-sort (l :lon) :lon
  (declare (xargs :mode :program))
  (if (endp l)
    l
  (heap-sort-help-v2 (build-heap l (len2 l)) (- (len2 l) 1))))

;; SWAP doesn't pass the proof checking for some reason

(definec del (a :nat l :lon) :lon
  (cond ((endp l) l)
        ((equal a (car l)) (cdr l))
        (t (cons (car l) (del a (cdr l))))))

(definec permp (x :lon y :lon) :bool
  (if (endp x) 
    (endp y)
    (and (in (car x) y) (permp (cdr x) (del (car x) y)))))

(definec orderedp (l :lon) :bool 
  (or (endp (cdr l)) 
      (and (<= (car l) (second l))
           (orderedp (cdr l)))))

(defthm heap-sort-permp
  (implies (lonp l)
           (permp l (heap-sort l))))

(defthm heap-sort-permp
  (implies (lonp l)
           (orderedp (heap-sort l))))

(defthm)
