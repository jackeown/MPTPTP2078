%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   19 (  43 expanded)
%              Number of clauses        :   14 (  20 expanded)
%              Number of leaves         :    2 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 185 expanded)
%              Number of equality atoms :   50 ( 147 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t10_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( k2_tarski(X1,X2) = k2_tarski(X3,X4)
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(c_0_2,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( k2_tarski(X1,X2) = k2_tarski(X3,X4)
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t10_zfmisc_1])).

cnf(c_0_4,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_5,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = k2_tarski(esk4_0,esk5_0)
    & esk2_0 != esk4_0
    & esk2_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X2,X3)) ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = k2_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_9,negated_conjecture,
    ( X1 = esk3_0
    | X1 = esk2_0
    | ~ r2_hidden(X1,k2_tarski(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( X1 = esk2_0
    | X1 = esk3_0
    | k2_tarski(esk4_0,esk5_0) != k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_14,plain,
    ( X1 = X2
    | X1 = X3
    | k2_tarski(X3,X2) != k2_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k2_tarski(esk2_0,esk4_0) = k2_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_7,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( esk2_0 = X1
    | esk2_0 = X2
    | k2_tarski(X1,X2) != k2_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_12]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.14/0.38  # and selection function SelectVGNonCR.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.38  fof(t10_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((k2_tarski(X1,X2)=k2_tarski(X3,X4)&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 0.14/0.38  fof(c_0_2, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:~(((k2_tarski(X1,X2)=k2_tarski(X3,X4)&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t10_zfmisc_1])).
% 0.14/0.38  cnf(c_0_4, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ((k2_tarski(esk2_0,esk3_0)=k2_tarski(esk4_0,esk5_0)&esk2_0!=esk4_0)&esk2_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.14/0.38  cnf(c_0_6, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X2,X3))), inference(er,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_7, negated_conjecture, (k2_tarski(esk2_0,esk3_0)=k2_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_8, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.14/0.38  cnf(c_0_9, negated_conjecture, (X1=esk3_0|X1=esk2_0|~r2_hidden(X1,k2_tarski(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(X1,X2)|X2!=k2_tarski(X1,X3)), inference(er,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (X1=esk2_0|X1=esk3_0|k2_tarski(esk4_0,esk5_0)!=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (esk3_0=esk4_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12])).
% 0.14/0.38  cnf(c_0_14, plain, (X1=X2|X1=X3|k2_tarski(X3,X2)!=k2_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_6, c_0_10])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (k2_tarski(esk2_0,esk4_0)=k2_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_7, c_0_13])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (esk2_0=X1|esk2_0=X2|k2_tarski(X1,X2)!=k2_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (esk2_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_12]), c_0_17]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 19
% 0.14/0.38  # Proof object clause steps            : 14
% 0.14/0.38  # Proof object formula steps           : 5
% 0.14/0.38  # Proof object conjectures             : 12
% 0.14/0.38  # Proof object clause conjectures      : 9
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 5
% 0.14/0.38  # Proof object initial formulas used   : 2
% 0.14/0.38  # Proof object generating inferences   : 7
% 0.14/0.38  # Proof object simplifying inferences  : 5
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 5
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 12
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 11
% 0.14/0.38  # Processed clauses                    : 38
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 2
% 0.14/0.38  # ...remaining for further processing  : 36
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 4
% 0.14/0.38  # Generated clauses                    : 28
% 0.14/0.38  # ...of the previous two non-trivial   : 27
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 19
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 9
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 19
% 0.14/0.38  #    Positive orientable unit clauses  : 2
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 14
% 0.14/0.38  # Current number of unprocessed clauses: 10
% 0.14/0.38  # ...number of literals in the above   : 38
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 16
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 61
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 61
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 2
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 882
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.024 s
% 0.14/0.38  # System time              : 0.007 s
% 0.14/0.38  # Total time               : 0.031 s
% 0.14/0.38  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
