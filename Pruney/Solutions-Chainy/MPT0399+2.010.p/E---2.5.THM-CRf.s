%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:25 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   24 (  35 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  74 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_setfam_1,conjecture,(
    ! [X1] :
      ( r1_setfam_1(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( r1_setfam_1(X1,k1_xboole_0)
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t21_setfam_1])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X15,X16,X18] :
      ( ( r2_hidden(esk3_3(X11,X12,X13),X12)
        | ~ r2_hidden(X13,X11)
        | ~ r1_setfam_1(X11,X12) )
      & ( r1_tarski(X13,esk3_3(X11,X12,X13))
        | ~ r2_hidden(X13,X11)
        | ~ r1_setfam_1(X11,X12) )
      & ( r2_hidden(esk4_2(X15,X16),X15)
        | r1_setfam_1(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r1_tarski(esk4_2(X15,X16),X18)
        | r1_setfam_1(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( r1_setfam_1(esk5_0,k1_xboole_0)
    & esk5_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_9,plain,(
    v1_xboole_0(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_setfam_1(esk5_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,k1_xboole_0,X1),k1_xboole_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,k1_xboole_0,esk1_1(esk5_0)),k1_xboole_0)
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:10:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.15/0.38  # and selection function SelectNewComplexAHP.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.026 s
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(t21_setfam_1, conjecture, ![X1]:(r1_setfam_1(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 0.15/0.38  fof(d2_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,X2)&r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 0.15/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.15/0.38  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.15/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.15/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:(r1_setfam_1(X1,k1_xboole_0)=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t21_setfam_1])).
% 0.15/0.38  fof(c_0_6, plain, ![X11, X12, X13, X15, X16, X18]:(((r2_hidden(esk3_3(X11,X12,X13),X12)|~r2_hidden(X13,X11)|~r1_setfam_1(X11,X12))&(r1_tarski(X13,esk3_3(X11,X12,X13))|~r2_hidden(X13,X11)|~r1_setfam_1(X11,X12)))&((r2_hidden(esk4_2(X15,X16),X15)|r1_setfam_1(X15,X16))&(~r2_hidden(X18,X16)|~r1_tarski(esk4_2(X15,X16),X18)|r1_setfam_1(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).
% 0.15/0.38  fof(c_0_7, negated_conjecture, (r1_setfam_1(esk5_0,k1_xboole_0)&esk5_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.15/0.38  fof(c_0_8, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.15/0.38  fof(c_0_9, plain, v1_xboole_0(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.15/0.38  cnf(c_0_10, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X3,X1)|~r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.38  cnf(c_0_11, negated_conjecture, (r1_setfam_1(esk5_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.38  fof(c_0_12, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.15/0.38  cnf(c_0_13, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.38  cnf(c_0_14, plain, (v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(esk3_3(esk5_0,k1_xboole_0,X1),k1_xboole_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.15/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.38  cnf(c_0_17, plain, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.15/0.38  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_3(esk5_0,k1_xboole_0,esk1_1(esk5_0)),k1_xboole_0)|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.38  cnf(c_0_20, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_14, c_0_17])).
% 0.15/0.38  cnf(c_0_21, negated_conjecture, (v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.15/0.38  cnf(c_0_22, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.38  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_21]), c_0_22]), ['proof']).
% 0.15/0.38  # SZS output end CNFRefutation
% 0.15/0.38  # Proof object total steps             : 24
% 0.15/0.38  # Proof object clause steps            : 13
% 0.15/0.38  # Proof object formula steps           : 11
% 0.15/0.38  # Proof object conjectures             : 9
% 0.15/0.38  # Proof object clause conjectures      : 6
% 0.15/0.38  # Proof object formula conjectures     : 3
% 0.15/0.38  # Proof object initial clauses used    : 7
% 0.15/0.38  # Proof object initial formulas used   : 5
% 0.15/0.38  # Proof object generating inferences   : 5
% 0.15/0.38  # Proof object simplifying inferences  : 4
% 0.15/0.38  # Training examples: 0 positive, 0 negative
% 0.15/0.38  # Parsed axioms                        : 5
% 0.15/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.38  # Initial clauses                      : 10
% 0.15/0.38  # Removed in clause preprocessing      : 0
% 0.15/0.38  # Initial clauses in saturation        : 10
% 0.15/0.38  # Processed clauses                    : 22
% 0.15/0.38  # ...of these trivial                  : 0
% 0.15/0.38  # ...subsumed                          : 2
% 0.15/0.38  # ...remaining for further processing  : 20
% 0.15/0.38  # Other redundant clauses eliminated   : 0
% 0.15/0.38  # Clauses deleted for lack of memory   : 0
% 0.15/0.38  # Backward-subsumed                    : 0
% 0.15/0.38  # Backward-rewritten                   : 2
% 0.15/0.38  # Generated clauses                    : 23
% 0.15/0.38  # ...of the previous two non-trivial   : 17
% 0.15/0.38  # Contextual simplify-reflections      : 0
% 0.15/0.38  # Paramodulations                      : 23
% 0.15/0.38  # Factorizations                       : 0
% 0.15/0.38  # Equation resolutions                 : 0
% 0.15/0.38  # Propositional unsat checks           : 0
% 0.15/0.38  #    Propositional check models        : 0
% 0.15/0.38  #    Propositional check unsatisfiable : 0
% 0.15/0.38  #    Propositional clauses             : 0
% 0.15/0.38  #    Propositional clauses after purity: 0
% 0.15/0.38  #    Propositional unsat core size     : 0
% 0.15/0.38  #    Propositional preprocessing time  : 0.000
% 0.15/0.38  #    Propositional encoding time       : 0.000
% 0.15/0.38  #    Propositional solver time         : 0.000
% 0.15/0.38  #    Success case prop preproc time    : 0.000
% 0.15/0.38  #    Success case prop encoding time   : 0.000
% 0.15/0.38  #    Success case prop solver time     : 0.000
% 0.15/0.38  # Current number of processed clauses  : 18
% 0.15/0.38  #    Positive orientable unit clauses  : 5
% 0.15/0.38  #    Positive unorientable unit clauses: 0
% 0.15/0.38  #    Negative unit clauses             : 1
% 0.15/0.38  #    Non-unit-clauses                  : 12
% 0.15/0.38  # Current number of unprocessed clauses: 5
% 0.15/0.38  # ...number of literals in the above   : 10
% 0.15/0.38  # Current number of archived formulas  : 0
% 0.15/0.38  # Current number of archived clauses   : 2
% 0.15/0.38  # Clause-clause subsumption calls (NU) : 4
% 0.15/0.38  # Rec. Clause-clause subsumption calls : 4
% 0.15/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.15/0.38  # Unit Clause-clause subsumption calls : 0
% 0.15/0.38  # Rewrite failures with RHS unbound    : 0
% 0.15/0.38  # BW rewrite match attempts            : 2
% 0.15/0.38  # BW rewrite match successes           : 2
% 0.15/0.38  # Condensation attempts                : 0
% 0.15/0.38  # Condensation successes               : 0
% 0.15/0.38  # Termbank termtop insertions          : 803
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.027 s
% 0.15/0.38  # System time              : 0.003 s
% 0.15/0.38  # Total time               : 0.030 s
% 0.15/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
