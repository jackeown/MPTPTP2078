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
% DateTime   : Thu Dec  3 10:33:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  76 expanded)
%              Number of clauses        :   20 (  33 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 119 expanded)
%              Number of equality atoms :   26 (  60 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t86_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_7,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_8,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t86_xboole_1])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] : k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k4_xboole_0(k3_xboole_0(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_11,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

fof(c_0_24,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_23]),c_0_14])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,X1)) = k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.19/0.38  # and selection function SelectNewComplexAHP.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.38  fof(t86_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.19/0.38  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.38  fof(c_0_7, plain, ![X8, X9]:r1_tarski(k4_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.38  fof(c_0_8, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t86_xboole_1])).
% 0.19/0.38  fof(c_0_10, plain, ![X13, X14, X15]:k3_xboole_0(X13,k4_xboole_0(X14,X15))=k4_xboole_0(k3_xboole_0(X13,X14),X15), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.38  fof(c_0_11, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.38  fof(c_0_12, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.38  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_14, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_xboole_0(esk1_0,esk3_0))&~r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.38  cnf(c_0_16, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.19/0.38  cnf(c_0_22, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.19/0.38  fof(c_0_24, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_14])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_23]), c_0_14])).
% 0.19/0.38  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,X1))=k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (~r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 35
% 0.19/0.38  # Proof object clause steps            : 20
% 0.19/0.38  # Proof object formula steps           : 15
% 0.19/0.38  # Proof object conjectures             : 12
% 0.19/0.38  # Proof object clause conjectures      : 9
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 7
% 0.19/0.38  # Proof object generating inferences   : 9
% 0.19/0.38  # Proof object simplifying inferences  : 6
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 8
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 12
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 11
% 0.19/0.38  # Processed clauses                    : 105
% 0.19/0.38  # ...of these trivial                  : 12
% 0.19/0.38  # ...subsumed                          : 20
% 0.19/0.38  # ...remaining for further processing  : 73
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 8
% 0.19/0.38  # Generated clauses                    : 663
% 0.19/0.38  # ...of the previous two non-trivial   : 253
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 660
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 3
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 54
% 0.19/0.38  #    Positive orientable unit clauses  : 37
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 16
% 0.19/0.38  # Current number of unprocessed clauses: 167
% 0.19/0.38  # ...number of literals in the above   : 194
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 20
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 49
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 49
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 20
% 0.19/0.38  # Unit Clause-clause subsumption calls : 11
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 34
% 0.19/0.38  # BW rewrite match successes           : 4
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7130
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.037 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
