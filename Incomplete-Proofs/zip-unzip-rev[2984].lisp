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
(definec len2 (l :tl) :nat
  (if (endp l)
      0
    (+ 1 (len2 (cdr l)))))

(definec zip2 (l :tl l2 :tl) :tl
  :ic (equal (len2 l) (len2 l2))
  (if (endp l)
      l
    (cons (cons (car l) (car l2)) (zip2 (cdr l) (cdr l2)))))

(defdata lol (list tl tl))

(definec unzip (al :alist) :lol
  (if (endp al)
      (list nil nil)
    (list (cons (car (car al)) (car (unzip (cdr al))))
          (cons (cdr (car al)) (car (cdr (unzip (cdr al))))))))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

(definec rev2 (x :tl) :tl
  (if (endp x)
      nil
    (app2 (rev2 (rest x)) (list (first x)))))

(defthm zip-loses-none 
  (implies (and (tlp l1) (tlp l2) (equal (len2 l1) (len2 l2)))
           (equal (len2 l1) 
                  (len2 (zip2 l1 l2)))))

(defthm app2-nil
  (implies (tlp l)
           (equal (app2 l '()) l)))#|ACL2s-ToDo-Line|#


#|
(defthm upzip-zip
  (implies (and (tlp l1) (tlp l2) (equal (len2 l1) (len2 l2)))
           (equal (unzip (zip2 l1 l2))
                  (list l1 l2))))
|#

;; An initial statement of the theorem
(defthm to-prove
  (implies (and (tlp l1)
                (tlp l2)
                (equal (len2 l1) (len2 l2)))
           (and (equal (rev2 (car (unzip (rev2 (zip2 l1 l2))))) l1)
                (equal (rev2 (car (cdr (unzip (rev2 (zip2 l1 l2)))))) l2))))
