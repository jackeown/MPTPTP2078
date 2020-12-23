%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:00 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  52 expanded)
%              Number of equality atoms :   51 (  51 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

fof(t7_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(c_0_3,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] :
      ( ( X17 != k2_mcart_1(X14)
        | X14 != k4_tarski(X18,X19)
        | X17 = X19
        | X14 != k4_tarski(X15,X16) )
      & ( X14 = k4_tarski(esk3_2(X14,X20),esk4_2(X14,X20))
        | X20 = k2_mcart_1(X14)
        | X14 != k4_tarski(X15,X16) )
      & ( X20 != esk4_2(X14,X20)
        | X20 = k2_mcart_1(X14)
        | X14 != k4_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k1_mcart_1(k4_tarski(X1,X2)) = X1
        & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    inference(assume_negation,[status(cth)],[t7_mcart_1])).

cnf(c_0_5,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,plain,(
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

fof(c_0_7,negated_conjecture,
    ( k1_mcart_1(k4_tarski(esk5_0,esk6_0)) != esk5_0
    | k2_mcart_1(k4_tarski(esk5_0,esk6_0)) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_5])])).

cnf(c_0_9,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k1_mcart_1(k4_tarski(esk5_0,esk6_0)) != esk5_0
    | k2_mcart_1(k4_tarski(esk5_0,esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_13,negated_conjecture,
    ( k1_mcart_1(k4_tarski(esk5_0,esk6_0)) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11])])).

cnf(c_0_14,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:24:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d2_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k2_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_mcart_1)).
% 0.12/0.37  fof(t7_mcart_1, conjecture, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.37  fof(d1_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k1_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_mcart_1)).
% 0.12/0.37  fof(c_0_3, plain, ![X14, X15, X16, X17, X18, X19, X20]:((X17!=k2_mcart_1(X14)|(X14!=k4_tarski(X18,X19)|X17=X19)|X14!=k4_tarski(X15,X16))&((X14=k4_tarski(esk3_2(X14,X20),esk4_2(X14,X20))|X20=k2_mcart_1(X14)|X14!=k4_tarski(X15,X16))&(X20!=esk4_2(X14,X20)|X20=k2_mcart_1(X14)|X14!=k4_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2)), inference(assume_negation,[status(cth)],[t7_mcart_1])).
% 0.12/0.37  cnf(c_0_5, plain, (X1=X4|X1!=k2_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10, X11]:((X8!=k1_mcart_1(X5)|(X5!=k4_tarski(X9,X10)|X8=X9)|X5!=k4_tarski(X6,X7))&((X5=k4_tarski(esk1_2(X5,X11),esk2_2(X5,X11))|X11=k1_mcart_1(X5)|X5!=k4_tarski(X6,X7))&(X11!=esk1_2(X5,X11)|X11=k1_mcart_1(X5)|X5!=k4_tarski(X6,X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).
% 0.12/0.37  fof(c_0_7, negated_conjecture, (k1_mcart_1(k4_tarski(esk5_0,esk6_0))!=esk5_0|k2_mcart_1(k4_tarski(esk5_0,esk6_0))!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.12/0.37  cnf(c_0_8, plain, (k2_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X4,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_5])])).
% 0.12/0.37  cnf(c_0_9, plain, (X1=X3|X1!=k1_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (k1_mcart_1(k4_tarski(esk5_0,esk6_0))!=esk5_0|k2_mcart_1(k4_tarski(esk5_0,esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(er,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, plain, (k1_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X3,X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (k1_mcart_1(k4_tarski(esk5_0,esk6_0))!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11])])).
% 0.12/0.37  cnf(c_0_14, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 16
% 0.12/0.37  # Proof object clause steps            : 9
% 0.12/0.37  # Proof object formula steps           : 7
% 0.12/0.37  # Proof object conjectures             : 6
% 0.12/0.37  # Proof object clause conjectures      : 3
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 3
% 0.12/0.37  # Proof object initial formulas used   : 3
% 0.12/0.37  # Proof object generating inferences   : 2
% 0.12/0.37  # Proof object simplifying inferences  : 8
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 3
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 7
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 7
% 0.12/0.37  # Processed clauses                    : 23
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 23
% 0.12/0.37  # Other redundant clauses eliminated   : 8
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 7
% 0.12/0.37  # Generated clauses                    : 22
% 0.12/0.37  # ...of the previous two non-trivial   : 27
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 14
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 10
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
% 0.12/0.37  # Current number of processed clauses  : 3
% 0.12/0.37  #    Positive orientable unit clauses  : 2
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 1
% 0.12/0.37  # Current number of unprocessed clauses: 15
% 0.12/0.37  # ...number of literals in the above   : 41
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 14
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 6
% 0.12/0.37  # BW rewrite match successes           : 6
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 750
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
