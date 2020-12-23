%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:37 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 112 expanded)
%              Number of clauses        :   29 (  50 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 140 expanded)
%              Number of equality atoms :   40 (  98 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t81_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_10,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k4_xboole_0(X21,X22)) = k4_xboole_0(k3_xboole_0(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_11,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_13,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
       => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    inference(assume_negation,[status(cth)],[t81_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k3_xboole_0(X16,X17)) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_29,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk1_0)) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_44]),c_0_22]),c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 15:37:42 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.45  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.17/0.45  # and selection function SelectNewComplexAHP.
% 0.17/0.45  #
% 0.17/0.45  # Preprocessing time       : 0.026 s
% 0.17/0.45  # Presaturation interreduction done
% 0.17/0.45  
% 0.17/0.45  # Proof found!
% 0.17/0.45  # SZS status Theorem
% 0.17/0.45  # SZS output start CNFRefutation
% 0.17/0.45  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.17/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.17/0.45  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.17/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.17/0.45  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.17/0.45  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.17/0.45  fof(t81_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.17/0.45  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.17/0.45  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.17/0.45  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.17/0.45  fof(c_0_10, plain, ![X20, X21, X22]:k3_xboole_0(X20,k4_xboole_0(X21,X22))=k4_xboole_0(k3_xboole_0(X20,X21),X22), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.17/0.45  fof(c_0_11, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.17/0.45  fof(c_0_12, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.17/0.45  fof(c_0_13, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.17/0.45  fof(c_0_14, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.17/0.45  cnf(c_0_15, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.45  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.45  fof(c_0_17, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.17/0.45  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t81_xboole_1])).
% 0.17/0.45  fof(c_0_19, plain, ![X16, X17]:k4_xboole_0(X16,k3_xboole_0(X16,X17))=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.17/0.45  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.45  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.45  cnf(c_0_22, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.45  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.17/0.45  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.45  fof(c_0_25, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.17/0.45  cnf(c_0_26, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_27, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.17/0.45  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 0.17/0.45  fof(c_0_29, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.17/0.45  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_16])).
% 0.17/0.45  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.45  fof(c_0_32, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.17/0.45  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_16])).
% 0.17/0.45  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.17/0.45  cnf(c_0_35, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.17/0.45  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.17/0.45  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.17/0.45  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.17/0.45  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.17/0.45  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_36]), c_0_35])).
% 0.17/0.45  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.45  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk1_0))=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_22])).
% 0.17/0.45  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.45  cnf(c_0_44, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.17/0.45  cnf(c_0_45, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.17/0.45  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_43, c_0_16])).
% 0.17/0.45  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_44]), c_0_22]), c_0_45])).
% 0.17/0.45  cnf(c_0_48, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.45  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.17/0.45  # SZS output end CNFRefutation
% 0.17/0.45  # Proof object total steps             : 50
% 0.17/0.45  # Proof object clause steps            : 29
% 0.17/0.45  # Proof object formula steps           : 21
% 0.17/0.45  # Proof object conjectures             : 11
% 0.17/0.45  # Proof object clause conjectures      : 8
% 0.17/0.45  # Proof object formula conjectures     : 3
% 0.17/0.45  # Proof object initial clauses used    : 12
% 0.17/0.45  # Proof object initial formulas used   : 10
% 0.17/0.45  # Proof object generating inferences   : 12
% 0.17/0.45  # Proof object simplifying inferences  : 13
% 0.17/0.45  # Training examples: 0 positive, 0 negative
% 0.17/0.45  # Parsed axioms                        : 10
% 0.17/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.45  # Initial clauses                      : 13
% 0.17/0.45  # Removed in clause preprocessing      : 1
% 0.17/0.45  # Initial clauses in saturation        : 12
% 0.17/0.45  # Processed clauses                    : 730
% 0.17/0.45  # ...of these trivial                  : 248
% 0.17/0.45  # ...subsumed                          : 83
% 0.17/0.45  # ...remaining for further processing  : 399
% 0.17/0.45  # Other redundant clauses eliminated   : 0
% 0.17/0.45  # Clauses deleted for lack of memory   : 0
% 0.17/0.45  # Backward-subsumed                    : 0
% 0.17/0.45  # Backward-rewritten                   : 23
% 0.17/0.45  # Generated clauses                    : 12819
% 0.17/0.45  # ...of the previous two non-trivial   : 5892
% 0.17/0.45  # Contextual simplify-reflections      : 0
% 0.17/0.45  # Paramodulations                      : 12814
% 0.17/0.45  # Factorizations                       : 0
% 0.17/0.45  # Equation resolutions                 : 5
% 0.17/0.45  # Propositional unsat checks           : 0
% 0.17/0.45  #    Propositional check models        : 0
% 0.17/0.45  #    Propositional check unsatisfiable : 0
% 0.17/0.45  #    Propositional clauses             : 0
% 0.17/0.45  #    Propositional clauses after purity: 0
% 0.17/0.45  #    Propositional unsat core size     : 0
% 0.17/0.45  #    Propositional preprocessing time  : 0.000
% 0.17/0.45  #    Propositional encoding time       : 0.000
% 0.17/0.45  #    Propositional solver time         : 0.000
% 0.17/0.45  #    Success case prop preproc time    : 0.000
% 0.17/0.45  #    Success case prop encoding time   : 0.000
% 0.17/0.45  #    Success case prop solver time     : 0.000
% 0.17/0.45  # Current number of processed clauses  : 364
% 0.17/0.45  #    Positive orientable unit clauses  : 328
% 0.17/0.45  #    Positive unorientable unit clauses: 1
% 0.17/0.45  #    Negative unit clauses             : 1
% 0.17/0.45  #    Non-unit-clauses                  : 34
% 0.17/0.45  # Current number of unprocessed clauses: 5137
% 0.17/0.45  # ...number of literals in the above   : 5677
% 0.17/0.45  # Current number of archived formulas  : 0
% 0.17/0.45  # Current number of archived clauses   : 36
% 0.17/0.45  # Clause-clause subsumption calls (NU) : 293
% 0.17/0.45  # Rec. Clause-clause subsumption calls : 288
% 0.17/0.45  # Non-unit clause-clause subsumptions  : 77
% 0.17/0.45  # Unit Clause-clause subsumption calls : 9
% 0.17/0.45  # Rewrite failures with RHS unbound    : 0
% 0.17/0.45  # BW rewrite match attempts            : 681
% 0.17/0.45  # BW rewrite match successes           : 23
% 0.17/0.45  # Condensation attempts                : 0
% 0.17/0.45  # Condensation successes               : 0
% 0.17/0.45  # Termbank termtop insertions          : 126987
% 0.17/0.45  
% 0.17/0.45  # -------------------------------------------------
% 0.17/0.45  # User time                : 0.126 s
% 0.17/0.45  # System time              : 0.010 s
% 0.17/0.45  # Total time               : 0.136 s
% 0.17/0.45  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
