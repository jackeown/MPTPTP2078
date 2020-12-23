%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:39 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  70 expanded)
%              Number of clauses        :   11 (  28 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 232 expanded)
%              Number of equality atoms :   62 ( 231 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k3_zfmisc_1(X1,X1,X1) = k3_zfmisc_1(X2,X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_zfmisc_1(X1,X1,X1) = k3_zfmisc_1(X2,X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t38_mcart_1])).

fof(c_0_4,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( X10 = X13
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) )
      & ( X11 = X14
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) )
      & ( X12 = X15
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk1_0,esk1_0) = k3_zfmisc_1(esk2_0,esk2_0,esk2_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk1_0,esk1_0) = k3_zfmisc_1(esk2_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ( X7 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) != k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = X1
    | k3_zfmisc_1(esk2_0,esk2_0,esk2_0) != k3_zfmisc_1(X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k3_zfmisc_1(esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_12]),c_0_12]),c_0_12]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.049 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t38_mcart_1, conjecture, ![X1, X2]:(k3_zfmisc_1(X1,X1,X1)=k3_zfmisc_1(X2,X2,X2)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_mcart_1)).
% 0.20/0.40  fof(t36_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.20/0.40  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.20/0.40  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(k3_zfmisc_1(X1,X1,X1)=k3_zfmisc_1(X2,X2,X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t38_mcart_1])).
% 0.20/0.40  fof(c_0_4, plain, ![X10, X11, X12, X13, X14, X15]:(((X10=X13|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0)|k3_zfmisc_1(X10,X11,X12)!=k3_zfmisc_1(X13,X14,X15))&(X11=X14|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0)|k3_zfmisc_1(X10,X11,X12)!=k3_zfmisc_1(X13,X14,X15)))&(X12=X15|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0)|k3_zfmisc_1(X10,X11,X12)!=k3_zfmisc_1(X13,X14,X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).
% 0.20/0.40  fof(c_0_5, negated_conjecture, (k3_zfmisc_1(esk1_0,esk1_0,esk1_0)=k3_zfmisc_1(esk2_0,esk2_0,esk2_0)&esk1_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.20/0.40  cnf(c_0_6, plain, (X1=X2|X3=k1_xboole_0|X4=k1_xboole_0|X1=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_7, negated_conjecture, (k3_zfmisc_1(esk1_0,esk1_0,esk1_0)=k3_zfmisc_1(esk2_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.40  fof(c_0_8, plain, ![X7, X8, X9]:((X7=k1_xboole_0|X8=k1_xboole_0|X9=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)!=k1_xboole_0)&(((X7!=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)=k1_xboole_0)&(X8!=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)=k1_xboole_0))&(X9!=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.20/0.40  cnf(c_0_9, negated_conjecture, (esk1_0=k1_xboole_0|esk1_0=X1|k3_zfmisc_1(esk2_0,esk2_0,esk2_0)!=k3_zfmisc_1(X2,X3,X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.20/0.40  cnf(c_0_10, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.40  cnf(c_0_11, plain, (k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_12, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])).
% 0.20/0.40  cnf(c_0_13, plain, (k3_zfmisc_1(k1_xboole_0,X1,X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_14, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (k3_zfmisc_1(esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_12]), c_0_12]), c_0_12]), c_0_13])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_10, c_0_12])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 18
% 0.20/0.40  # Proof object clause steps            : 11
% 0.20/0.40  # Proof object formula steps           : 7
% 0.20/0.40  # Proof object conjectures             : 10
% 0.20/0.40  # Proof object clause conjectures      : 7
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 5
% 0.20/0.40  # Proof object initial formulas used   : 3
% 0.20/0.40  # Proof object generating inferences   : 3
% 0.20/0.40  # Proof object simplifying inferences  : 8
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 3
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 9
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 9
% 0.20/0.40  # Processed clauses                    : 26
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 0
% 0.20/0.40  # ...remaining for further processing  : 26
% 0.20/0.40  # Other redundant clauses eliminated   : 3
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 4
% 0.20/0.40  # Generated clauses                    : 33
% 0.20/0.40  # ...of the previous two non-trivial   : 31
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 26
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 7
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 10
% 0.20/0.40  #    Positive orientable unit clauses  : 5
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 4
% 0.20/0.40  # Current number of unprocessed clauses: 17
% 0.20/0.40  # ...number of literals in the above   : 71
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 13
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 12
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 12
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 0
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 5
% 0.20/0.40  # BW rewrite match successes           : 1
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 804
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.052 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.055 s
% 0.20/0.40  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
