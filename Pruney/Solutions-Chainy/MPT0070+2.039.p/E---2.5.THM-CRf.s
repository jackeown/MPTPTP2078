%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  48 expanded)
%              Number of clauses        :   18 (  21 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  91 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t63_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_6,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(k3_xboole_0(X17,X19),k3_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_xboole_1])])).

fof(c_0_7,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_9,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X2,X3) )
       => r1_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_xboole_1])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_14,plain,(
    ! [X16] : k2_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_10])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & r1_xboole_0(esk4_0,esk5_0)
    & ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_xboole_0)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),k1_xboole_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)) = k1_xboole_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.20/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.048 s
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t26_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 0.20/0.47  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.47  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.47  fof(t63_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.47  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.47  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.47  fof(c_0_6, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|r1_tarski(k3_xboole_0(X17,X19),k3_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_xboole_1])])).
% 0.20/0.47  fof(c_0_7, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.47  fof(c_0_8, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.47  cnf(c_0_9, plain, (r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_10, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.47  cnf(c_0_11, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t63_xboole_1])).
% 0.20/0.47  fof(c_0_13, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.47  fof(c_0_14, plain, ![X16]:k2_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.47  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 0.20/0.47  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_10])).
% 0.20/0.47  fof(c_0_17, negated_conjecture, ((r1_tarski(esk3_0,esk4_0)&r1_xboole_0(esk4_0,esk5_0))&~r1_xboole_0(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.47  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_19, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_xboole_0)|~r1_tarski(X1,X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.47  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  cnf(c_0_23, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.47  cnf(c_0_24, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),k1_xboole_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.47  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_10])).
% 0.20/0.47  cnf(c_0_26, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))=k1_xboole_0|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.47  cnf(c_0_27, negated_conjecture, (r1_xboole_0(X1,esk5_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.47  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_29, negated_conjecture, (~r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 31
% 0.20/0.47  # Proof object clause steps            : 18
% 0.20/0.47  # Proof object formula steps           : 13
% 0.20/0.47  # Proof object conjectures             : 10
% 0.20/0.47  # Proof object clause conjectures      : 7
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 9
% 0.20/0.47  # Proof object initial formulas used   : 6
% 0.20/0.47  # Proof object generating inferences   : 6
% 0.20/0.47  # Proof object simplifying inferences  : 5
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 11
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 15
% 0.20/0.47  # Removed in clause preprocessing      : 1
% 0.20/0.47  # Initial clauses in saturation        : 14
% 0.20/0.47  # Processed clauses                    : 905
% 0.20/0.47  # ...of these trivial                  : 63
% 0.20/0.47  # ...subsumed                          : 654
% 0.20/0.47  # ...remaining for further processing  : 188
% 0.20/0.47  # Other redundant clauses eliminated   : 0
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 13
% 0.20/0.47  # Backward-rewritten                   : 3
% 0.20/0.47  # Generated clauses                    : 3101
% 0.20/0.47  # ...of the previous two non-trivial   : 2202
% 0.20/0.47  # Contextual simplify-reflections      : 0
% 0.20/0.47  # Paramodulations                      : 3098
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 0
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 171
% 0.20/0.47  #    Positive orientable unit clauses  : 9
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 3
% 0.20/0.47  #    Non-unit-clauses                  : 159
% 0.20/0.47  # Current number of unprocessed clauses: 1233
% 0.20/0.47  # ...number of literals in the above   : 4887
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 17
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 9146
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 5777
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 656
% 0.20/0.47  # Unit Clause-clause subsumption calls : 25
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 7
% 0.20/0.47  # BW rewrite match successes           : 2
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 34910
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.119 s
% 0.20/0.47  # System time              : 0.004 s
% 0.20/0.47  # Total time               : 0.123 s
% 0.20/0.47  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
