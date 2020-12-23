%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:05 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  39 expanded)
%              Number of clauses        :   12 (  18 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  94 expanded)
%              Number of equality atoms :   33 (  66 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
     => ( k1_mcart_1(X1) = X2
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
       => ( k1_mcart_1(X1) = X2
          & k2_mcart_1(X1) = X3 ) ) ),
    inference(assume_negation,[status(cth)],[t14_mcart_1])).

fof(c_0_5,plain,(
    ! [X4,X5,X6,X7,X8,X9] :
      ( ( ~ r2_hidden(X6,X5)
        | X6 = X4
        | X5 != k1_tarski(X4) )
      & ( X7 != X4
        | r2_hidden(X7,X5)
        | X5 != k1_tarski(X4) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) != X8
        | X9 = k1_tarski(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) = X8
        | X9 = k1_tarski(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0)))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | k2_mcart_1(esk2_0) != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X11,X12] : k2_zfmisc_1(k1_tarski(X11),k1_tarski(X12)) = k1_tarski(k4_tarski(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( k1_mcart_1(k4_tarski(X13,X14)) = X13
      & k2_mcart_1(k4_tarski(X13,X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tarski(k4_tarski(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(esk3_0,esk4_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | k2_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_15]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:28:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.13/0.35  # and selection function HSelectMinInfpos.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.026 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t14_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))=>(k1_mcart_1(X1)=X2&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_mcart_1)).
% 0.13/0.35  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.35  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.13/0.35  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.35  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))=>(k1_mcart_1(X1)=X2&k2_mcart_1(X1)=X3))), inference(assume_negation,[status(cth)],[t14_mcart_1])).
% 0.13/0.35  fof(c_0_5, plain, ![X4, X5, X6, X7, X8, X9]:(((~r2_hidden(X6,X5)|X6=X4|X5!=k1_tarski(X4))&(X7!=X4|r2_hidden(X7,X5)|X5!=k1_tarski(X4)))&((~r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)!=X8|X9=k1_tarski(X8))&(r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)=X8|X9=k1_tarski(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.35  fof(c_0_6, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0)))&(k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.35  fof(c_0_7, plain, ![X11, X12]:k2_zfmisc_1(k1_tarski(X11),k1_tarski(X12))=k1_tarski(k4_tarski(X11,X12)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.13/0.35  cnf(c_0_8, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_9, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.35  cnf(c_0_10, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.35  fof(c_0_11, plain, ![X13, X14]:(k1_mcart_1(k4_tarski(X13,X14))=X13&k2_mcart_1(k4_tarski(X13,X14))=X14), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.35  cnf(c_0_12, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_8])).
% 0.13/0.35  cnf(c_0_13, negated_conjecture, (r2_hidden(esk2_0,k1_tarski(k4_tarski(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.35  cnf(c_0_14, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.35  cnf(c_0_15, negated_conjecture, (k4_tarski(esk3_0,esk4_0)=esk2_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.35  cnf(c_0_16, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.35  cnf(c_0_17, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.35  cnf(c_0_18, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.35  cnf(c_0_19, negated_conjecture, (k2_mcart_1(esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17])])).
% 0.13/0.35  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_15]), c_0_19]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 21
% 0.13/0.35  # Proof object clause steps            : 12
% 0.13/0.35  # Proof object formula steps           : 9
% 0.13/0.35  # Proof object conjectures             : 10
% 0.13/0.35  # Proof object clause conjectures      : 7
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 6
% 0.13/0.35  # Proof object initial formulas used   : 4
% 0.13/0.35  # Proof object generating inferences   : 3
% 0.13/0.35  # Proof object simplifying inferences  : 5
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 4
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 9
% 0.13/0.35  # Removed in clause preprocessing      : 0
% 0.13/0.35  # Initial clauses in saturation        : 9
% 0.13/0.35  # Processed clauses                    : 25
% 0.13/0.35  # ...of these trivial                  : 0
% 0.13/0.35  # ...subsumed                          : 0
% 0.13/0.35  # ...remaining for further processing  : 24
% 0.13/0.35  # Other redundant clauses eliminated   : 3
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 0
% 0.13/0.35  # Backward-rewritten                   : 3
% 0.13/0.35  # Generated clauses                    : 6
% 0.13/0.35  # ...of the previous two non-trivial   : 8
% 0.13/0.35  # Contextual simplify-reflections      : 0
% 0.13/0.35  # Paramodulations                      : 4
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 3
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
% 0.13/0.35  # Current number of processed clauses  : 10
% 0.13/0.35  #    Positive orientable unit clauses  : 6
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 1
% 0.13/0.35  #    Non-unit-clauses                  : 3
% 0.13/0.35  # Current number of unprocessed clauses: 1
% 0.13/0.35  # ...number of literals in the above   : 3
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 12
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.35  # Unit Clause-clause subsumption calls : 0
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 5
% 0.13/0.35  # BW rewrite match successes           : 3
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 576
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.026 s
% 0.13/0.35  # System time              : 0.004 s
% 0.13/0.35  # Total time               : 0.030 s
% 0.13/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
