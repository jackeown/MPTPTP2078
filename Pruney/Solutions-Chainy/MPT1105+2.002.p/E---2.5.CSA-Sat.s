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
% DateTime   : Thu Dec  3 11:09:01 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   15 (  18 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    3
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = k3_subset_1(u1_struct_0(X1),k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => k2_struct_0(X1) = k3_subset_1(u1_struct_0(X1),k1_struct_0(X1)) ) ),
    inference(assume_negation,[status(cth)],[t27_pre_topc])).

fof(c_0_5,plain,(
    ! [X4] : k2_subset_1(X4) = k3_subset_1(X4,k1_subset_1(X4)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_6,plain,(
    ! [X3] : k2_subset_1(X3) = X3 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_7,plain,(
    ! [X2] : k1_subset_1(X2) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_8,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & k2_struct_0(esk1_0) != k3_subset_1(u1_struct_0(esk1_0),k1_struct_0(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_9,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k2_struct_0(esk1_0) != k3_subset_1(u1_struct_0(esk1_0),k1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:51 EST 2020
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
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(t27_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=k3_subset_1(u1_struct_0(X1),k1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 0.19/0.37  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.19/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.37  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=k3_subset_1(u1_struct_0(X1),k1_struct_0(X1)))), inference(assume_negation,[status(cth)],[t27_pre_topc])).
% 0.19/0.37  fof(c_0_5, plain, ![X4]:k2_subset_1(X4)=k3_subset_1(X4,k1_subset_1(X4)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.19/0.37  fof(c_0_6, plain, ![X3]:k2_subset_1(X3)=X3, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.37  fof(c_0_7, plain, ![X2]:k1_subset_1(X2)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.37  fof(c_0_8, negated_conjecture, (l1_struct_0(esk1_0)&k2_struct_0(esk1_0)!=k3_subset_1(u1_struct_0(esk1_0),k1_struct_0(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.37  cnf(c_0_9, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_10, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (k2_struct_0(esk1_0)!=k3_subset_1(u1_struct_0(esk1_0),k1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  cnf(c_0_13, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_11]), ['final']).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 15
% 0.19/0.37  # Proof object clause steps            : 6
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 5
% 0.19/0.37  # Proof object clause conjectures      : 2
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 5
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 0
% 0.19/0.37  # Proof object simplifying inferences  : 2
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 5
% 0.19/0.37  # Removed in clause preprocessing      : 2
% 0.19/0.37  # Initial clauses in saturation        : 3
% 0.19/0.37  # Processed clauses                    : 6
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 6
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 0
% 0.19/0.37  # ...of the previous two non-trivial   : 0
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 0
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
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
% 0.19/0.37  # Current number of processed clauses  : 3
% 0.19/0.37  #    Positive orientable unit clauses  : 2
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 0
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 5
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 153
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.026 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.029 s
% 0.19/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
