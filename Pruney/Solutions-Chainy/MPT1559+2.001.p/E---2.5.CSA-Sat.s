%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:21 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   24 (  54 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   42 ( 180 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_yellow_0,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r2_yellow_0(X1,X2)
            & r2_yellow_0(X1,X3)
            & r2_yellow_0(X1,k2_xboole_0(X2,X3)) )
         => k2_yellow_0(X1,k2_xboole_0(X2,X3)) = k11_lattice3(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( ( r2_yellow_0(X1,X2)
              & r2_yellow_0(X1,X3)
              & r2_yellow_0(X1,k2_xboole_0(X2,X3)) )
           => k2_yellow_0(X1,k2_xboole_0(X2,X3)) = k11_lattice3(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t37_yellow_0])).

fof(c_0_5,plain,(
    ! [X6,X7] : r1_tarski(X6,k2_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_6,plain,(
    ! [X8,X9] : k3_tarski(k2_tarski(X8,X9)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_8,negated_conjecture,
    ( v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & r2_yellow_0(esk1_0,esk2_0)
    & r2_yellow_0(esk1_0,esk3_0)
    & r2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    & k2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k11_lattice3(esk1_0,k2_yellow_0(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k11_lattice3(esk1_0,k2_yellow_0(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_10]),c_0_10]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( r2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( k2_yellow_0(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0))) != k11_lattice3(esk1_0,k2_yellow_0(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_10]),
    [final]).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( r2_yellow_0(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:37:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.026 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # No proof found!
% 0.18/0.36  # SZS status CounterSatisfiable
% 0.18/0.36  # SZS output start Saturation
% 0.18/0.36  fof(t37_yellow_0, conjecture, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2, X3]:(((r2_yellow_0(X1,X2)&r2_yellow_0(X1,X3))&r2_yellow_0(X1,k2_xboole_0(X2,X3)))=>k2_yellow_0(X1,k2_xboole_0(X2,X3))=k11_lattice3(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow_0)).
% 0.18/0.36  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.18/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.18/0.36  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.36  fof(c_0_4, negated_conjecture, ~(![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2, X3]:(((r2_yellow_0(X1,X2)&r2_yellow_0(X1,X3))&r2_yellow_0(X1,k2_xboole_0(X2,X3)))=>k2_yellow_0(X1,k2_xboole_0(X2,X3))=k11_lattice3(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3))))), inference(assume_negation,[status(cth)],[t37_yellow_0])).
% 0.18/0.36  fof(c_0_5, plain, ![X6, X7]:r1_tarski(X6,k2_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.18/0.36  fof(c_0_6, plain, ![X8, X9]:k3_tarski(k2_tarski(X8,X9))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.18/0.36  fof(c_0_7, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.36  fof(c_0_8, negated_conjecture, (((v4_orders_2(esk1_0)&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(((r2_yellow_0(esk1_0,esk2_0)&r2_yellow_0(esk1_0,esk3_0))&r2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)))&k2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k11_lattice3(esk1_0,k2_yellow_0(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.18/0.36  cnf(c_0_9, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.36  cnf(c_0_10, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.36  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_12, negated_conjecture, (k2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k11_lattice3(esk1_0,k2_yellow_0(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_13, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_10]), c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (r2_yellow_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, (k2_yellow_0(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0)))!=k11_lattice3(esk1_0,k2_yellow_0(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk3_0))), inference(rw,[status(thm)],[c_0_12, c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_17, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.18/0.36  cnf(c_0_18, negated_conjecture, (r2_yellow_0(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_15, c_0_10]), ['final']).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (r2_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, (r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  # SZS output end Saturation
% 0.18/0.36  # Proof object total steps             : 24
% 0.18/0.36  # Proof object clause steps            : 15
% 0.18/0.36  # Proof object formula steps           : 9
% 0.18/0.36  # Proof object conjectures             : 12
% 0.18/0.36  # Proof object clause conjectures      : 9
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 10
% 0.18/0.36  # Proof object initial formulas used   : 4
% 0.18/0.36  # Proof object generating inferences   : 1
% 0.18/0.36  # Proof object simplifying inferences  : 5
% 0.18/0.36  # Parsed axioms                        : 4
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 10
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 9
% 0.18/0.36  # Processed clauses                    : 20
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 19
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 0
% 0.18/0.36  # Generated clauses                    : 4
% 0.18/0.36  # ...of the previous two non-trivial   : 2
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 4
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 10
% 0.18/0.36  #    Positive orientable unit clauses  : 8
% 0.18/0.36  #    Positive unorientable unit clauses: 1
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 0
% 0.18/0.36  # Current number of unprocessed clauses: 0
% 0.18/0.36  # ...number of literals in the above   : 0
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 10
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.36  # Unit Clause-clause subsumption calls : 0
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 9
% 0.18/0.36  # BW rewrite match successes           : 8
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 484
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.027 s
% 0.18/0.36  # System time              : 0.002 s
% 0.18/0.36  # Total time               : 0.029 s
% 0.18/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
