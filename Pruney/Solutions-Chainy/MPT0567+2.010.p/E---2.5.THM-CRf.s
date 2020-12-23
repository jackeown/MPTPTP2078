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
% DateTime   : Thu Dec  3 10:51:12 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  34 expanded)
%              Number of clauses        :   10 (  14 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 (  89 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t171_relat_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_8,plain,(
    ! [X13] : r1_xboole_0(X13,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_9,plain,(
    ! [X14,X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( r2_hidden(k4_tarski(X17,esk2_4(X14,X15,X16,X17)),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k10_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_4(X14,X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k10_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X14)
        | ~ r2_hidden(X20,X15)
        | r2_hidden(X19,X16)
        | X16 != k10_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(esk3_3(X14,X21,X22),X22)
        | ~ r2_hidden(k4_tarski(esk3_3(X14,X21,X22),X24),X14)
        | ~ r2_hidden(X24,X21)
        | X22 = k10_relat_1(X14,X21)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk3_3(X14,X21,X22),esk4_3(X14,X21,X22)),X14)
        | r2_hidden(esk3_3(X14,X21,X22),X22)
        | X22 = k10_relat_1(X14,X21)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk4_3(X14,X21,X22),X21)
        | r2_hidden(esk3_3(X14,X21,X22),X22)
        | X22 = k10_relat_1(X14,X21)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,negated_conjecture,
    ( X1 = k10_relat_1(esk5_0,X2)
    | r2_hidden(esk4_3(esk5_0,X2,X1),X2)
    | r2_hidden(esk3_3(esk5_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( X1 = k10_relat_1(esk5_0,k1_xboole_0)
    | r2_hidden(esk3_3(esk5_0,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:59:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.22/0.39  # and selection function SelectComplexExceptRRHorn.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.027 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(t171_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 0.22/0.39  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.22/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.22/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.22/0.39  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.22/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t171_relat_1])).
% 0.22/0.39  fof(c_0_6, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.22/0.39  fof(c_0_7, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.22/0.39  fof(c_0_8, plain, ![X13]:r1_xboole_0(X13,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.22/0.39  fof(c_0_9, plain, ![X14, X15, X16, X17, X19, X20, X21, X22, X24]:((((r2_hidden(k4_tarski(X17,esk2_4(X14,X15,X16,X17)),X14)|~r2_hidden(X17,X16)|X16!=k10_relat_1(X14,X15)|~v1_relat_1(X14))&(r2_hidden(esk2_4(X14,X15,X16,X17),X15)|~r2_hidden(X17,X16)|X16!=k10_relat_1(X14,X15)|~v1_relat_1(X14)))&(~r2_hidden(k4_tarski(X19,X20),X14)|~r2_hidden(X20,X15)|r2_hidden(X19,X16)|X16!=k10_relat_1(X14,X15)|~v1_relat_1(X14)))&((~r2_hidden(esk3_3(X14,X21,X22),X22)|(~r2_hidden(k4_tarski(esk3_3(X14,X21,X22),X24),X14)|~r2_hidden(X24,X21))|X22=k10_relat_1(X14,X21)|~v1_relat_1(X14))&((r2_hidden(k4_tarski(esk3_3(X14,X21,X22),esk4_3(X14,X21,X22)),X14)|r2_hidden(esk3_3(X14,X21,X22),X22)|X22=k10_relat_1(X14,X21)|~v1_relat_1(X14))&(r2_hidden(esk4_3(X14,X21,X22),X21)|r2_hidden(esk3_3(X14,X21,X22),X22)|X22=k10_relat_1(X14,X21)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.22/0.39  fof(c_0_10, negated_conjecture, (v1_relat_1(esk5_0)&k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.22/0.39  cnf(c_0_11, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.39  cnf(c_0_12, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.22/0.39  cnf(c_0_13, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.39  cnf(c_0_14, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.39  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.39  cnf(c_0_16, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.22/0.39  cnf(c_0_17, negated_conjecture, (X1=k10_relat_1(esk5_0,X2)|r2_hidden(esk4_3(esk5_0,X2,X1),X2)|r2_hidden(esk3_3(esk5_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.22/0.39  cnf(c_0_18, negated_conjecture, (X1=k10_relat_1(esk5_0,k1_xboole_0)|r2_hidden(esk3_3(esk5_0,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.22/0.39  cnf(c_0_19, negated_conjecture, (k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.39  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_18]), c_0_19]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 21
% 0.22/0.39  # Proof object clause steps            : 10
% 0.22/0.39  # Proof object formula steps           : 11
% 0.22/0.39  # Proof object conjectures             : 8
% 0.22/0.39  # Proof object clause conjectures      : 5
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 6
% 0.22/0.39  # Proof object initial formulas used   : 5
% 0.22/0.39  # Proof object generating inferences   : 4
% 0.22/0.39  # Proof object simplifying inferences  : 3
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 5
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 12
% 0.22/0.39  # Removed in clause preprocessing      : 0
% 0.22/0.39  # Initial clauses in saturation        : 12
% 0.22/0.39  # Processed clauses                    : 56
% 0.22/0.39  # ...of these trivial                  : 0
% 0.22/0.39  # ...subsumed                          : 5
% 0.22/0.39  # ...remaining for further processing  : 51
% 0.22/0.39  # Other redundant clauses eliminated   : 3
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 0
% 0.22/0.39  # Generated clauses                    : 120
% 0.22/0.39  # ...of the previous two non-trivial   : 116
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 117
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 3
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 36
% 0.22/0.39  #    Positive orientable unit clauses  : 3
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 2
% 0.22/0.39  #    Non-unit-clauses                  : 31
% 0.22/0.39  # Current number of unprocessed clauses: 65
% 0.22/0.39  # ...number of literals in the above   : 333
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 12
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 513
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 21
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.22/0.39  # Unit Clause-clause subsumption calls : 0
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 0
% 0.22/0.39  # BW rewrite match successes           : 0
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 3391
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.034 s
% 0.22/0.39  # System time              : 0.001 s
% 0.22/0.39  # Total time               : 0.035 s
% 0.22/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
