%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of clauses        :   16 (  23 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  96 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,k3_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,k3_relat_1(X1)) = X1 ) ),
    inference(assume_negation,[status(cth)],[t30_wellord1])).

fof(c_0_8,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k3_relat_1(X7) = k2_xboole_0(k1_relat_1(X7),k2_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & k2_wellord1(esk1_0,k3_relat_1(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X5,X6] : r1_tarski(X5,k2_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_11,plain,(
    ! [X3,X4] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_12,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | k2_wellord1(X13,X12) = k8_relat_1(X12,k7_relat_1(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(k1_relat_1(X11),X10)
      | k7_relat_1(X11,X10) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk1_0),k2_relat_1(esk1_0)) = k3_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(k2_relat_1(X9),X8)
      | k8_relat_1(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_24,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k8_relat_1(X1,k7_relat_1(esk1_0,X1)) = k2_wellord1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( k7_relat_1(esk1_0,k3_relat_1(esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_13])])).

cnf(c_0_28,negated_conjecture,
    ( k8_relat_1(k3_relat_1(esk1_0),esk1_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( k2_wellord1(esk1_0,k3_relat_1(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.19/0.36  # and selection function SelectComplexG.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.016 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t30_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>k2_wellord1(X1,k3_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 0.19/0.36  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.19/0.36  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.36  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.36  fof(t18_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k8_relat_1(X1,k7_relat_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_wellord1)).
% 0.19/0.36  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.36  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 0.19/0.36  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k2_wellord1(X1,k3_relat_1(X1))=X1)), inference(assume_negation,[status(cth)],[t30_wellord1])).
% 0.19/0.36  fof(c_0_8, plain, ![X7]:(~v1_relat_1(X7)|k3_relat_1(X7)=k2_xboole_0(k1_relat_1(X7),k2_relat_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.19/0.36  fof(c_0_9, negated_conjecture, (v1_relat_1(esk1_0)&k2_wellord1(esk1_0,k3_relat_1(esk1_0))!=esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.36  fof(c_0_10, plain, ![X5, X6]:r1_tarski(X5,k2_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.36  fof(c_0_11, plain, ![X3, X4]:k2_xboole_0(X3,X4)=k2_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.36  cnf(c_0_12, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.36  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  fof(c_0_16, plain, ![X12, X13]:(~v1_relat_1(X13)|k2_wellord1(X13,X12)=k8_relat_1(X12,k7_relat_1(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).
% 0.19/0.36  fof(c_0_17, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(k1_relat_1(X11),X10)|k7_relat_1(X11,X10)=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (k2_xboole_0(k1_relat_1(esk1_0),k2_relat_1(esk1_0))=k3_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.36  fof(c_0_19, plain, ![X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(k2_relat_1(X9),X8)|k8_relat_1(X8,X9)=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.19/0.36  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.36  cnf(c_0_21, plain, (k2_wellord1(X1,X2)=k8_relat_1(X2,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.36  cnf(c_0_22, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.36  cnf(c_0_23, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k3_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.19/0.36  cnf(c_0_24, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k3_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.36  cnf(c_0_26, negated_conjecture, (k8_relat_1(X1,k7_relat_1(esk1_0,X1))=k2_wellord1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.19/0.36  cnf(c_0_27, negated_conjecture, (k7_relat_1(esk1_0,k3_relat_1(esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_13])])).
% 0.19/0.36  cnf(c_0_28, negated_conjecture, (k8_relat_1(k3_relat_1(esk1_0),esk1_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_13])])).
% 0.19/0.36  cnf(c_0_29, negated_conjecture, (k2_wellord1(esk1_0,k3_relat_1(esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 31
% 0.19/0.36  # Proof object clause steps            : 16
% 0.19/0.36  # Proof object formula steps           : 15
% 0.19/0.36  # Proof object conjectures             : 12
% 0.19/0.36  # Proof object clause conjectures      : 9
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 8
% 0.19/0.36  # Proof object initial formulas used   : 7
% 0.19/0.36  # Proof object generating inferences   : 8
% 0.19/0.36  # Proof object simplifying inferences  : 6
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 7
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 8
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 8
% 0.19/0.36  # Processed clauses                    : 30
% 0.19/0.36  # ...of these trivial                  : 1
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 29
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 0
% 0.19/0.36  # Generated clauses                    : 24
% 0.19/0.36  # ...of the previous two non-trivial   : 18
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 24
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 21
% 0.19/0.36  #    Positive orientable unit clauses  : 11
% 0.19/0.36  #    Positive unorientable unit clauses: 1
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 8
% 0.19/0.36  # Current number of unprocessed clauses: 4
% 0.19/0.36  # ...number of literals in the above   : 4
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 8
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 4
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 4
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 0
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 5
% 0.19/0.36  # BW rewrite match successes           : 4
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 748
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.018 s
% 0.19/0.36  # System time              : 0.002 s
% 0.19/0.36  # Total time               : 0.020 s
% 0.19/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
