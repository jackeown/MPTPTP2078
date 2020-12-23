%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t111_relat_1,conjecture,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc17_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ( v1_xboole_0(k7_relat_1(X1,X2))
        & v1_relat_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t111_relat_1])).

fof(c_0_7,negated_conjecture,(
    k7_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X3,X4] :
      ( ~ v1_xboole_0(X3)
      | X3 = X4
      | ~ v1_xboole_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_9,plain,(
    ! [X5] : v1_relat_1(k6_relat_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_10,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( v1_xboole_0(k7_relat_1(X6,X7))
        | ~ v1_xboole_0(X6)
        | ~ v1_relat_1(X6) )
      & ( v1_relat_1(k7_relat_1(X6,X7))
        | ~ v1_xboole_0(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_relat_1])])])).

cnf(c_0_14,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(k7_relat_1(k1_xboole_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11])]),c_0_12])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(k7_relat_1(X1,X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n011.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 14:20:42 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.35  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.027 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t111_relat_1, conjecture, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 0.13/0.35  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.13/0.35  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.35  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.35  fof(fc17_relat_1, axiom, ![X1, X2]:((v1_xboole_0(X1)&v1_relat_1(X1))=>(v1_xboole_0(k7_relat_1(X1,X2))&v1_relat_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_relat_1)).
% 0.13/0.35  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.13/0.35  fof(c_0_6, negated_conjecture, ~(![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t111_relat_1])).
% 0.13/0.35  fof(c_0_7, negated_conjecture, k7_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.35  fof(c_0_8, plain, ![X3, X4]:(~v1_xboole_0(X3)|X3=X4|~v1_xboole_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.13/0.35  fof(c_0_9, plain, ![X5]:v1_relat_1(k6_relat_1(X5)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.35  cnf(c_0_10, negated_conjecture, (k7_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.35  cnf(c_0_11, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.35  cnf(c_0_12, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.35  fof(c_0_13, plain, ![X6, X7]:((v1_xboole_0(k7_relat_1(X6,X7))|(~v1_xboole_0(X6)|~v1_relat_1(X6)))&(v1_relat_1(k7_relat_1(X6,X7))|(~v1_xboole_0(X6)|~v1_relat_1(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_relat_1])])])).
% 0.13/0.35  cnf(c_0_14, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.35  cnf(c_0_15, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.13/0.35  cnf(c_0_16, negated_conjecture, (~v1_xboole_0(k7_relat_1(k1_xboole_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11])]), c_0_12])])).
% 0.13/0.35  cnf(c_0_17, plain, (v1_xboole_0(k7_relat_1(X1,X2))|~v1_xboole_0(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.35  cnf(c_0_18, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.35  cnf(c_0_19, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_12])]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 20
% 0.13/0.35  # Proof object clause steps            : 9
% 0.13/0.35  # Proof object formula steps           : 11
% 0.13/0.35  # Proof object conjectures             : 6
% 0.13/0.35  # Proof object clause conjectures      : 3
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 6
% 0.13/0.35  # Proof object initial formulas used   : 6
% 0.13/0.35  # Proof object generating inferences   : 3
% 0.13/0.35  # Proof object simplifying inferences  : 6
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 6
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 7
% 0.13/0.35  # Removed in clause preprocessing      : 0
% 0.13/0.35  # Initial clauses in saturation        : 7
% 0.13/0.35  # Processed clauses                    : 17
% 0.13/0.35  # ...of these trivial                  : 0
% 0.13/0.35  # ...subsumed                          : 1
% 0.13/0.35  # ...remaining for further processing  : 16
% 0.13/0.35  # Other redundant clauses eliminated   : 4
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 0
% 0.13/0.35  # Backward-rewritten                   : 0
% 0.13/0.35  # Generated clauses                    : 38
% 0.13/0.35  # ...of the previous two non-trivial   : 29
% 0.13/0.35  # Contextual simplify-reflections      : 0
% 0.13/0.35  # Paramodulations                      : 34
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 4
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 9
% 0.13/0.35  #    Positive orientable unit clauses  : 4
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 2
% 0.13/0.35  #    Non-unit-clauses                  : 3
% 0.13/0.35  # Current number of unprocessed clauses: 24
% 0.13/0.35  # ...number of literals in the above   : 59
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 7
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.35  # Unit Clause-clause subsumption calls : 0
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 0
% 0.13/0.35  # BW rewrite match successes           : 0
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 529
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.028 s
% 0.13/0.35  # System time              : 0.002 s
% 0.13/0.35  # Total time               : 0.030 s
% 0.13/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
