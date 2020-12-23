%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:03 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   18 (  83 expanded)
%              Number of clauses        :   11 (  33 expanded)
%              Number of leaves         :    3 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 346 expanded)
%              Number of equality atoms :   79 ( 345 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(t56_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t58_mcart_1])).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( X13 = X17
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X14 = X18
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X15 = X19
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X16 = X20
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0) = k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X5,X1) != k4_zfmisc_1(X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0) = k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) != k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = X1
    | k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) != k4_zfmisc_1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

cnf(c_0_13,plain,
    ( k4_zfmisc_1(k1_xboole_0,X1,X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_12]),c_0_12]),c_0_12]),c_0_12]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t58_mcart_1, conjecture, ![X1, X2]:(k4_zfmisc_1(X1,X1,X1,X1)=k4_zfmisc_1(X2,X2,X2,X2)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 0.13/0.38  fof(t56_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 0.13/0.38  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.13/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(k4_zfmisc_1(X1,X1,X1,X1)=k4_zfmisc_1(X2,X2,X2,X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t58_mcart_1])).
% 0.13/0.38  fof(c_0_4, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((X13=X17|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20))&(X14=X18|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20)))&(X15=X19|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20)))&(X16=X20|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_mcart_1])])])).
% 0.13/0.38  fof(c_0_5, negated_conjecture, (k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0)=k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)&esk1_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.13/0.38  cnf(c_0_6, plain, (X1=X2|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X1=k1_xboole_0|k4_zfmisc_1(X3,X4,X5,X1)!=k4_zfmisc_1(X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_7, negated_conjecture, (k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0)=k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  fof(c_0_8, plain, ![X9, X10, X11, X12]:((X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)!=k1_xboole_0)&((((X9!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0)&(X10!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0))&(X11!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0))&(X12!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (esk1_0=k1_xboole_0|esk1_0=X1|k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)!=k4_zfmisc_1(X2,X3,X4,X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_11, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])).
% 0.13/0.38  cnf(c_0_13, plain, (k4_zfmisc_1(k1_xboole_0,X1,X2,X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_14, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_12]), c_0_12]), c_0_12]), c_0_12]), c_0_13])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_10, c_0_12])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 18
% 0.13/0.38  # Proof object clause steps            : 11
% 0.13/0.38  # Proof object formula steps           : 7
% 0.13/0.38  # Proof object conjectures             : 10
% 0.13/0.38  # Proof object clause conjectures      : 7
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 5
% 0.13/0.38  # Proof object initial formulas used   : 3
% 0.13/0.38  # Proof object generating inferences   : 3
% 0.13/0.38  # Proof object simplifying inferences  : 9
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 3
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 11
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 11
% 0.13/0.38  # Processed clauses                    : 29
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 29
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 27
% 0.13/0.38  # ...of the previous two non-trivial   : 24
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 20
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 10
% 0.13/0.38  #    Positive orientable unit clauses  : 6
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 3
% 0.13/0.38  # Current number of unprocessed clauses: 15
% 0.13/0.38  # ...number of literals in the above   : 75
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 15
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 14
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 14
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 11
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 928
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.031 s
% 0.13/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
