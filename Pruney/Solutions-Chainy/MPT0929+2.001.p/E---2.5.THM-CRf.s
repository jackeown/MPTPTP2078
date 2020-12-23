%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:35 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  42 expanded)
%              Number of clauses        :    9 (  15 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  73 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t89_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X1
      & k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X2
      & k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X4
      & k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X5 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_mcart_1)).

fof(d14_mcart_1,axiom,(
    ! [X1] : k17_mcart_1(X1) = k1_mcart_1(k1_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_mcart_1)).

fof(d15_mcart_1,axiom,(
    ! [X1] : k18_mcart_1(X1) = k2_mcart_1(k1_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_mcart_1)).

fof(d16_mcart_1,axiom,(
    ! [X1] : k19_mcart_1(X1) = k1_mcart_1(k2_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_mcart_1)).

fof(d17_mcart_1,axiom,(
    ! [X1] : k20_mcart_1(X1) = k2_mcart_1(k2_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X1
        & k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X2
        & k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X4
        & k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X5 ) ),
    inference(assume_negation,[status(cth)],[t89_mcart_1])).

fof(c_0_7,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk1_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk2_0
    | k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk4_0
    | k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X7] : k17_mcart_1(X7) = k1_mcart_1(k1_mcart_1(X7)) ),
    inference(variable_rename,[status(thm)],[d14_mcart_1])).

fof(c_0_9,plain,(
    ! [X8] : k18_mcart_1(X8) = k2_mcart_1(k1_mcart_1(X8)) ),
    inference(variable_rename,[status(thm)],[d15_mcart_1])).

fof(c_0_10,plain,(
    ! [X9] : k19_mcart_1(X9) = k1_mcart_1(k2_mcart_1(X9)) ),
    inference(variable_rename,[status(thm)],[d16_mcart_1])).

fof(c_0_11,plain,(
    ! [X10] : k20_mcart_1(X10) = k2_mcart_1(k2_mcart_1(X10)) ),
    inference(variable_rename,[status(thm)],[d17_mcart_1])).

cnf(c_0_12,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk1_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk2_0
    | k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk4_0
    | k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k17_mcart_1(X1) = k1_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k18_mcart_1(X1) = k2_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k19_mcart_1(X1) = k1_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k20_mcart_1(X1) = k2_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( k1_mcart_1(k4_tarski(X11,X12)) = X11
      & k2_mcart_1(k4_tarski(X11,X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_18,negated_conjecture,
    ( k1_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk4_0
    | k2_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk5_0
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk1_0
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_19,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_19])]),c_0_20]),c_0_19]),c_0_20]),c_0_20]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:27:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic H_____047_B31_F1_PI_AE_R4_CS_SP_S2S
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t89_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(((k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3))=X1&k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3))=X2)&k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5)))=X4)&k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5)))=X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_mcart_1)).
% 0.12/0.37  fof(d14_mcart_1, axiom, ![X1]:k17_mcart_1(X1)=k1_mcart_1(k1_mcart_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_mcart_1)).
% 0.12/0.37  fof(d15_mcart_1, axiom, ![X1]:k18_mcart_1(X1)=k2_mcart_1(k1_mcart_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_mcart_1)).
% 0.12/0.37  fof(d16_mcart_1, axiom, ![X1]:k19_mcart_1(X1)=k1_mcart_1(k2_mcart_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_mcart_1)).
% 0.12/0.37  fof(d17_mcart_1, axiom, ![X1]:k20_mcart_1(X1)=k2_mcart_1(k2_mcart_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_mcart_1)).
% 0.12/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(((k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3))=X1&k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3))=X2)&k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5)))=X4)&k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5)))=X5)), inference(assume_negation,[status(cth)],[t89_mcart_1])).
% 0.12/0.37  fof(c_0_7, negated_conjecture, (k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))!=esk1_0|k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))!=esk2_0|k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))!=esk4_0|k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X7]:k17_mcart_1(X7)=k1_mcart_1(k1_mcart_1(X7)), inference(variable_rename,[status(thm)],[d14_mcart_1])).
% 0.12/0.37  fof(c_0_9, plain, ![X8]:k18_mcart_1(X8)=k2_mcart_1(k1_mcart_1(X8)), inference(variable_rename,[status(thm)],[d15_mcart_1])).
% 0.12/0.37  fof(c_0_10, plain, ![X9]:k19_mcart_1(X9)=k1_mcart_1(k2_mcart_1(X9)), inference(variable_rename,[status(thm)],[d16_mcart_1])).
% 0.12/0.37  fof(c_0_11, plain, ![X10]:k20_mcart_1(X10)=k2_mcart_1(k2_mcart_1(X10)), inference(variable_rename,[status(thm)],[d17_mcart_1])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))!=esk1_0|k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))!=esk2_0|k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))!=esk4_0|k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_13, plain, (k17_mcart_1(X1)=k1_mcart_1(k1_mcart_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_14, plain, (k18_mcart_1(X1)=k2_mcart_1(k1_mcart_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_15, plain, (k19_mcart_1(X1)=k1_mcart_1(k2_mcart_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_16, plain, (k20_mcart_1(X1)=k2_mcart_1(k2_mcart_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_17, plain, ![X11, X12]:(k1_mcart_1(k4_tarski(X11,X12))=X11&k2_mcart_1(k4_tarski(X11,X12))=X12), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (k1_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))))!=esk4_0|k2_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))))!=esk5_0|k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)))!=esk1_0|k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)))!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])).
% 0.12/0.37  cnf(c_0_19, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_20, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_19])]), c_0_20]), c_0_19]), c_0_20]), c_0_20]), c_0_20])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 22
% 0.12/0.37  # Proof object clause steps            : 9
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 6
% 0.12/0.37  # Proof object clause conjectures      : 3
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 7
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 0
% 0.12/0.37  # Proof object simplifying inferences  : 14
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 7
% 0.12/0.37  # Removed in clause preprocessing      : 4
% 0.12/0.37  # Initial clauses in saturation        : 3
% 0.12/0.37  # Processed clauses                    : 4
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 3
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 0
% 0.12/0.37  # ...of the previous two non-trivial   : 1
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 0
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 2
% 0.12/0.37  #    Positive orientable unit clauses  : 2
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 0
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 5
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 392
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.026 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.030 s
% 0.12/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
