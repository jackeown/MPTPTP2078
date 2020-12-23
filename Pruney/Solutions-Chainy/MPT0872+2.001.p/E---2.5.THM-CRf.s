%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:36 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   20 (  35 expanded)
%              Number of clauses        :   11 (  18 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  67 expanded)
%              Number of equality atoms :   35 (  66 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k3_mcart_1(k4_tarski(X1,X2),X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k3_mcart_1(k4_tarski(X1,X2),X3,X4) ),
    inference(assume_negation,[status(cth)],[t32_mcart_1])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != k1_mcart_1(X5)
        | X5 != k4_tarski(X9,X10)
        | X8 = X9
        | X5 != k4_tarski(X6,X7) )
      & ( X5 = k4_tarski(esk1_2(X5,X11),esk2_2(X5,X11))
        | X11 = k1_mcart_1(X5)
        | X5 != k4_tarski(X6,X7) )
      & ( X11 != esk1_2(X5,X11)
        | X11 = k1_mcart_1(X5)
        | X5 != k4_tarski(X6,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) != k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17] : k4_mcart_1(X14,X15,X16,X17) = k4_tarski(k3_mcart_1(X14,X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X18,X19,X20,X21] : k4_mcart_1(X18,X19,X20,X21) = k4_tarski(k4_tarski(k4_tarski(X18,X19),X20),X21) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

cnf(c_0_9,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) != k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k3_mcart_1(esk3_0,esk4_0,esk5_0),esk6_0) != k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k4_tarski(k3_mcart_1(X1,X2,X3),X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_16,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0) != k4_tarski(k4_tarski(k4_tarski(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.038 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t32_mcart_1, conjecture, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k3_mcart_1(k4_tarski(X1,X2),X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_mcart_1)).
% 0.13/0.39  fof(d1_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k1_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_mcart_1)).
% 0.13/0.39  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.13/0.39  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.13/0.39  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k3_mcart_1(k4_tarski(X1,X2),X3,X4)), inference(assume_negation,[status(cth)],[t32_mcart_1])).
% 0.13/0.39  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11]:((X8!=k1_mcart_1(X5)|(X5!=k4_tarski(X9,X10)|X8=X9)|X5!=k4_tarski(X6,X7))&((X5=k4_tarski(esk1_2(X5,X11),esk2_2(X5,X11))|X11=k1_mcart_1(X5)|X5!=k4_tarski(X6,X7))&(X11!=esk1_2(X5,X11)|X11=k1_mcart_1(X5)|X5!=k4_tarski(X6,X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).
% 0.13/0.39  fof(c_0_6, negated_conjecture, k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)!=k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.39  fof(c_0_7, plain, ![X14, X15, X16, X17]:k4_mcart_1(X14,X15,X16,X17)=k4_tarski(k3_mcart_1(X14,X15,X16),X17), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.13/0.39  fof(c_0_8, plain, ![X18, X19, X20, X21]:k4_mcart_1(X18,X19,X20,X21)=k4_tarski(k4_tarski(k4_tarski(X18,X19),X20),X21), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.13/0.39  cnf(c_0_9, plain, (X1=X3|X1!=k1_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_10, negated_conjecture, (k4_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)!=k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_11, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_12, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_13, plain, (k1_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X3,X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (k4_tarski(k3_mcart_1(esk3_0,esk4_0,esk5_0),esk6_0)!=k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.39  cnf(c_0_15, plain, (k4_tarski(k3_mcart_1(X1,X2,X3),X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_12, c_0_11])).
% 0.13/0.39  cnf(c_0_16, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (k3_mcart_1(k4_tarski(esk3_0,esk4_0),esk5_0,esk6_0)!=k4_tarski(k4_tarski(k4_tarski(esk3_0,esk4_0),esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.39  cnf(c_0_18, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_15]), c_0_16])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 20
% 0.13/0.39  # Proof object clause steps            : 11
% 0.13/0.39  # Proof object formula steps           : 9
% 0.13/0.39  # Proof object conjectures             : 7
% 0.13/0.39  # Proof object clause conjectures      : 4
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 4
% 0.13/0.39  # Proof object initial formulas used   : 4
% 0.13/0.39  # Proof object generating inferences   : 2
% 0.13/0.39  # Proof object simplifying inferences  : 8
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 4
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 6
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 5
% 0.13/0.39  # Processed clauses                    : 18
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 18
% 0.13/0.39  # Other redundant clauses eliminated   : 4
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 5
% 0.13/0.39  # Generated clauses                    : 19
% 0.13/0.39  # ...of the previous two non-trivial   : 21
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 14
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 6
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 5
% 0.13/0.39  #    Positive orientable unit clauses  : 2
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 3
% 0.13/0.39  # Current number of unprocessed clauses: 13
% 0.13/0.39  # ...number of literals in the above   : 30
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 11
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 4
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 4
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 5
% 0.13/0.39  # BW rewrite match successes           : 5
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 608
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.037 s
% 0.13/0.39  # System time              : 0.006 s
% 0.13/0.39  # Total time               : 0.043 s
% 0.13/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
