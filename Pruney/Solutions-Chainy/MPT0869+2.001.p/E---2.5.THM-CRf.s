%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 137 expanded)
%              Number of clauses        :   18 (  65 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :   48 ( 282 expanded)
%              Number of equality atoms :   47 ( 281 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
       => ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ),
    inference(assume_negation,[status(cth)],[t28_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk3_0) = k3_mcart_1(esk4_0,esk5_0,esk6_0)
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X11,X12,X13] : k3_mcart_1(X11,X12,X13) = k4_tarski(k4_tarski(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10] :
      ( ( X7 = X9
        | k4_tarski(X7,X8) != k4_tarski(X9,X10) )
      & ( X8 = X10
        | k4_tarski(X7,X8) != k4_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_7,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk3_0) = k3_mcart_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) = k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( X1 = esk3_0
    | k4_tarski(X2,X1) != k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( esk3_0 = esk6_0 ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_13,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk6_0) = k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = X1
    | k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = k4_tarski(esk4_0,esk5_0) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = X1
    | k4_tarski(esk4_0,esk5_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 = esk5_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(esk1_0,esk5_0) = k4_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_12])])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 = X1
    | k4_tarski(esk4_0,esk5_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t28_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(k3_mcart_1(X1,X2,X3)=k3_mcart_1(X4,X5,X6)=>((X1=X4&X2=X5)&X3=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 0.19/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.37  fof(t33_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k4_tarski(X1,X2)=k4_tarski(X3,X4)=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 0.19/0.37  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(k3_mcart_1(X1,X2,X3)=k3_mcart_1(X4,X5,X6)=>((X1=X4&X2=X5)&X3=X6))), inference(assume_negation,[status(cth)],[t28_mcart_1])).
% 0.19/0.37  fof(c_0_4, negated_conjecture, (k3_mcart_1(esk1_0,esk2_0,esk3_0)=k3_mcart_1(esk4_0,esk5_0,esk6_0)&(esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.19/0.37  fof(c_0_5, plain, ![X11, X12, X13]:k3_mcart_1(X11,X12,X13)=k4_tarski(k4_tarski(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.37  fof(c_0_6, plain, ![X7, X8, X9, X10]:((X7=X9|k4_tarski(X7,X8)!=k4_tarski(X9,X10))&(X8=X10|k4_tarski(X7,X8)!=k4_tarski(X9,X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_7, negated_conjecture, (k3_mcart_1(esk1_0,esk2_0,esk3_0)=k3_mcart_1(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_8, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_9, plain, (X1=X2|k4_tarski(X3,X1)!=k4_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0)=k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_8])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (X1=esk3_0|k4_tarski(X2,X1)!=k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (esk3_0=esk6_0), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_13, plain, (X1=X2|k4_tarski(X1,X3)!=k4_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (k4_tarski(k4_tarski(esk1_0,esk2_0),esk6_0)=k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_10, c_0_12])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (k4_tarski(esk1_0,esk2_0)=X1|k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0)!=k4_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (k4_tarski(esk1_0,esk2_0)=k4_tarski(esk4_0,esk5_0)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (esk2_0=X1|k4_tarski(esk4_0,esk5_0)!=k4_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_9, c_0_16])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (esk2_0=esk5_0), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (k4_tarski(esk1_0,esk5_0)=k4_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_16, c_0_18])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (esk1_0!=esk4_0|esk2_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_12])])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (esk1_0=X1|k4_tarski(esk4_0,esk5_0)!=k4_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_20])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (esk1_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_18])])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 25
% 0.19/0.37  # Proof object clause steps            : 18
% 0.19/0.37  # Proof object formula steps           : 7
% 0.19/0.37  # Proof object conjectures             : 18
% 0.19/0.37  # Proof object clause conjectures      : 15
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 5
% 0.19/0.37  # Proof object initial formulas used   : 3
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 9
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 3
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 5
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 4
% 0.19/0.37  # Processed clauses                    : 26
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 7
% 0.19/0.37  # ...remaining for further processing  : 19
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 8
% 0.19/0.37  # Generated clauses                    : 22
% 0.19/0.37  # ...of the previous two non-trivial   : 26
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 16
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 6
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 7
% 0.19/0.37  #    Positive orientable unit clauses  : 3
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 3
% 0.19/0.37  # Current number of unprocessed clauses: 2
% 0.19/0.37  # ...number of literals in the above   : 4
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 13
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 28
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 28
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 504
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.026 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.030 s
% 0.19/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
