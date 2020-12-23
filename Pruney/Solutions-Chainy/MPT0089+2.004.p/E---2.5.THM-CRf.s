%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:41 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   22 (  36 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 189 expanded)
%              Number of equality atoms :   16 (  55 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t82_xboole_1,conjecture,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_3,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_4,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_5,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t82_xboole_1])).

fof(c_0_13,plain,(
    ! [X23,X24] : r1_xboole_0(k4_xboole_0(X23,X24),X24) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_7])).

fof(c_0_16,negated_conjecture,(
    ~ r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.72/0.90  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.72/0.90  # and selection function SelectComplexExceptRRHorn.
% 0.72/0.90  #
% 0.72/0.90  # Preprocessing time       : 0.027 s
% 0.72/0.90  # Presaturation interreduction done
% 0.72/0.90  
% 0.72/0.90  # Proof found!
% 0.72/0.90  # SZS status Theorem
% 0.72/0.90  # SZS output start CNFRefutation
% 0.72/0.90  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.72/0.90  fof(t82_xboole_1, conjecture, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.72/0.90  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.72/0.90  fof(c_0_3, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.72/0.90  cnf(c_0_4, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.72/0.90  cnf(c_0_5, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.72/0.90  cnf(c_0_6, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.72/0.90  cnf(c_0_7, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_4])).
% 0.72/0.90  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.72/0.90  cnf(c_0_9, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_5])).
% 0.72/0.90  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_7])).
% 0.72/0.90  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_8])).
% 0.72/0.90  fof(c_0_12, negated_conjecture, ~(![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t82_xboole_1])).
% 0.72/0.90  fof(c_0_13, plain, ![X23, X24]:r1_xboole_0(k4_xboole_0(X23,X24),X24), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.72/0.90  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.72/0.90  cnf(c_0_15, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_11, c_0_7])).
% 0.72/0.90  fof(c_0_16, negated_conjecture, ~r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.72/0.90  cnf(c_0_17, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.72/0.90  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.72/0.90  cnf(c_0_19, negated_conjecture, (~r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.72/0.90  cnf(c_0_20, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.72/0.90  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])]), ['proof']).
% 0.72/0.90  # SZS output end CNFRefutation
% 0.72/0.90  # Proof object total steps             : 22
% 0.72/0.90  # Proof object clause steps            : 15
% 0.72/0.90  # Proof object formula steps           : 7
% 0.72/0.90  # Proof object conjectures             : 5
% 0.72/0.90  # Proof object clause conjectures      : 2
% 0.72/0.90  # Proof object formula conjectures     : 3
% 0.72/0.90  # Proof object initial clauses used    : 6
% 0.72/0.90  # Proof object initial formulas used   : 3
% 0.72/0.90  # Proof object generating inferences   : 6
% 0.72/0.90  # Proof object simplifying inferences  : 5
% 0.72/0.90  # Training examples: 0 positive, 0 negative
% 0.72/0.90  # Parsed axioms                        : 7
% 0.72/0.90  # Removed by relevancy pruning/SinE    : 0
% 0.72/0.90  # Initial clauses                      : 14
% 0.72/0.90  # Removed in clause preprocessing      : 1
% 0.72/0.90  # Initial clauses in saturation        : 13
% 0.72/0.90  # Processed clauses                    : 4434
% 0.72/0.90  # ...of these trivial                  : 79
% 0.72/0.90  # ...subsumed                          : 3810
% 0.72/0.90  # ...remaining for further processing  : 545
% 0.72/0.90  # Other redundant clauses eliminated   : 89
% 0.72/0.90  # Clauses deleted for lack of memory   : 0
% 0.72/0.90  # Backward-subsumed                    : 11
% 0.72/0.90  # Backward-rewritten                   : 109
% 0.72/0.90  # Generated clauses                    : 46582
% 0.72/0.90  # ...of the previous two non-trivial   : 36019
% 0.72/0.90  # Contextual simplify-reflections      : 4
% 0.72/0.90  # Paramodulations                      : 46409
% 0.72/0.90  # Factorizations                       : 84
% 0.72/0.90  # Equation resolutions                 : 89
% 0.72/0.90  # Propositional unsat checks           : 0
% 0.72/0.90  #    Propositional check models        : 0
% 0.72/0.90  #    Propositional check unsatisfiable : 0
% 0.72/0.90  #    Propositional clauses             : 0
% 0.72/0.90  #    Propositional clauses after purity: 0
% 0.72/0.90  #    Propositional unsat core size     : 0
% 0.72/0.90  #    Propositional preprocessing time  : 0.000
% 0.72/0.90  #    Propositional encoding time       : 0.000
% 0.72/0.90  #    Propositional solver time         : 0.000
% 0.72/0.90  #    Success case prop preproc time    : 0.000
% 0.72/0.90  #    Success case prop encoding time   : 0.000
% 0.72/0.90  #    Success case prop solver time     : 0.000
% 0.72/0.90  # Current number of processed clauses  : 409
% 0.72/0.90  #    Positive orientable unit clauses  : 69
% 0.72/0.90  #    Positive unorientable unit clauses: 0
% 0.72/0.90  #    Negative unit clauses             : 1
% 0.72/0.90  #    Non-unit-clauses                  : 339
% 0.72/0.90  # Current number of unprocessed clauses: 31225
% 0.72/0.90  # ...number of literals in the above   : 94081
% 0.72/0.90  # Current number of archived formulas  : 0
% 0.72/0.90  # Current number of archived clauses   : 134
% 0.72/0.90  # Clause-clause subsumption calls (NU) : 33867
% 0.72/0.90  # Rec. Clause-clause subsumption calls : 27422
% 0.72/0.90  # Non-unit clause-clause subsumptions  : 1899
% 0.72/0.90  # Unit Clause-clause subsumption calls : 334
% 0.72/0.90  # Rewrite failures with RHS unbound    : 0
% 0.72/0.90  # BW rewrite match attempts            : 647
% 0.72/0.90  # BW rewrite match successes           : 33
% 0.72/0.90  # Condensation attempts                : 0
% 0.72/0.90  # Condensation successes               : 0
% 0.72/0.90  # Termbank termtop insertions          : 887427
% 0.72/0.90  
% 0.72/0.90  # -------------------------------------------------
% 0.72/0.90  # User time                : 0.527 s
% 0.72/0.90  # System time              : 0.030 s
% 0.72/0.90  # Total time               : 0.557 s
% 0.72/0.90  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
