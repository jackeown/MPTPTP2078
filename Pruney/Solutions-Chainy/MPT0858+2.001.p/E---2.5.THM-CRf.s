%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   18 (  31 expanded)
%              Number of clauses        :   11 (  14 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  94 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
     => ( k1_mcart_1(X1) = X2
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
       => ( k1_mcart_1(X1) = X2
          & k2_mcart_1(X1) = X3 ) ) ),
    inference(assume_negation,[status(cth)],[t14_mcart_1])).

fof(c_0_4,plain,(
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

fof(c_0_5,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(k1_mcart_1(X11),X12)
        | ~ r2_hidden(X11,k2_zfmisc_1(X12,X13)) )
      & ( r2_hidden(k2_mcart_1(X11),X13)
        | ~ r2_hidden(X11,k2_zfmisc_1(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0)))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | k2_mcart_1(esk2_0) != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | k2_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k1_tarski(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14])])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:26:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.026 s
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t14_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))=>(k1_mcart_1(X1)=X2&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 0.19/0.36  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.36  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.36  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))=>(k1_mcart_1(X1)=X2&k2_mcart_1(X1)=X3))), inference(assume_negation,[status(cth)],[t14_mcart_1])).
% 0.19/0.36  fof(c_0_4, plain, ![X4, X5, X6, X7, X8, X9]:(((~r2_hidden(X6,X5)|X6=X4|X5!=k1_tarski(X4))&(X7!=X4|r2_hidden(X7,X5)|X5!=k1_tarski(X4)))&((~r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)!=X8|X9=k1_tarski(X8))&(r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)=X8|X9=k1_tarski(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.36  fof(c_0_5, plain, ![X11, X12, X13]:((r2_hidden(k1_mcart_1(X11),X12)|~r2_hidden(X11,k2_zfmisc_1(X12,X13)))&(r2_hidden(k2_mcart_1(X11),X13)|~r2_hidden(X11,k2_zfmisc_1(X12,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.36  fof(c_0_6, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0)))&(k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.19/0.36  cnf(c_0_7, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.36  cnf(c_0_8, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.36  cnf(c_0_9, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k1_tarski(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_10, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_7])).
% 0.19/0.36  cnf(c_0_11, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.36  cnf(c_0_12, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.36  cnf(c_0_13, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_14, negated_conjecture, (k2_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.36  cnf(c_0_15, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k1_tarski(esk3_0))), inference(spm,[status(thm)],[c_0_12, c_0_9])).
% 0.19/0.36  cnf(c_0_16, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14])])).
% 0.19/0.36  cnf(c_0_17, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_15]), c_0_16]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 18
% 0.19/0.36  # Proof object clause steps            : 11
% 0.19/0.36  # Proof object formula steps           : 7
% 0.19/0.36  # Proof object conjectures             : 10
% 0.19/0.36  # Proof object clause conjectures      : 7
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 5
% 0.19/0.36  # Proof object initial formulas used   : 3
% 0.19/0.36  # Proof object generating inferences   : 4
% 0.19/0.36  # Proof object simplifying inferences  : 4
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 3
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 8
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 8
% 0.19/0.36  # Processed clauses                    : 14
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 13
% 0.19/0.36  # Other redundant clauses eliminated   : 3
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 2
% 0.19/0.36  # Generated clauses                    : 9
% 0.19/0.36  # ...of the previous two non-trivial   : 10
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 7
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 3
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 9
% 0.19/0.36  #    Positive orientable unit clauses  : 4
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 4
% 0.19/0.36  # Current number of unprocessed clauses: 4
% 0.19/0.36  # ...number of literals in the above   : 12
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 2
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 0
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 1
% 0.19/0.36  # BW rewrite match successes           : 1
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 563
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.024 s
% 0.19/0.36  # System time              : 0.005 s
% 0.19/0.36  # Total time               : 0.029 s
% 0.19/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
