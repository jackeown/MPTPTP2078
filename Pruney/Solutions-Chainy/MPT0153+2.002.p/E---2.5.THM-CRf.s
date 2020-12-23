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
% DateTime   : Thu Dec  3 10:35:29 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 148 expanded)
%              Number of clauses        :   30 (  71 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 216 expanded)
%              Number of equality atoms :   45 ( 128 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t69_enumset1,conjecture,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_11,plain,(
    ! [X22,X23] : k3_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_12,plain,(
    ! [X24,X25] : k2_xboole_0(X24,X25) = k5_xboole_0(X24,k4_xboole_0(X25,X24)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X15,X16] : r1_tarski(k3_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_17,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ( k4_xboole_0(X13,X14) != k1_xboole_0
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | k4_xboole_0(X13,X14) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,k4_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] : k4_xboole_0(X17,k3_xboole_0(X18,X19)) = k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ( ~ r1_xboole_0(X20,X21)
        | k4_xboole_0(X20,X21) = X20 )
      & ( k4_xboole_0(X20,X21) != X20
        | r1_xboole_0(X20,X21) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X26,X27] : k2_tarski(X26,X27) = k2_xboole_0(k1_tarski(X26),k1_tarski(X27)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,negated_conjecture,(
    k2_tarski(esk2_0,esk2_0) != k1_tarski(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k4_xboole_0(X3,X2)))) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_15]),c_0_19])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_15])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_25]),c_0_41])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = X1
    | k1_xboole_0 != X2 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk2_0))) != k1_tarski(esk2_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1
    | k1_xboole_0 != X2 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,k1_tarski(esk2_0)) != k1_tarski(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_37]),c_0_41])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:14:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.15/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.026 s
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.15/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.15/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.15/0.38  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.15/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.15/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.15/0.38  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 0.15/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.15/0.38  fof(t69_enumset1, conjecture, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.15/0.38  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.15/0.38  fof(c_0_11, plain, ![X22, X23]:k3_xboole_0(X22,X23)=k5_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.15/0.38  fof(c_0_12, plain, ![X24, X25]:k2_xboole_0(X24,X25)=k5_xboole_0(X24,k4_xboole_0(X25,X24)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.15/0.38  fof(c_0_13, plain, ![X15, X16]:r1_tarski(k3_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.15/0.38  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.38  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.38  fof(c_0_16, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.15/0.38  fof(c_0_17, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.15/0.38  cnf(c_0_18, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.38  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.15/0.38  cnf(c_0_20, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.38  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.38  fof(c_0_23, plain, ![X13, X14]:((k4_xboole_0(X13,X14)!=k1_xboole_0|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|k4_xboole_0(X13,X14)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.15/0.38  cnf(c_0_24, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X1)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.15/0.38  cnf(c_0_25, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,k4_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.15/0.38  fof(c_0_26, plain, ![X17, X18, X19]:k4_xboole_0(X17,k3_xboole_0(X18,X19))=k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 0.15/0.38  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.15/0.38  fof(c_0_28, plain, ![X20, X21]:((~r1_xboole_0(X20,X21)|k4_xboole_0(X20,X21)=X20)&(k4_xboole_0(X20,X21)!=X20|r1_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.15/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.15/0.38  fof(c_0_31, negated_conjecture, ~(![X1]:k2_tarski(X1,X1)=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t69_enumset1])).
% 0.15/0.38  fof(c_0_32, plain, ![X26, X27]:k2_tarski(X26,X27)=k2_xboole_0(k1_tarski(X26),k1_tarski(X27)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.15/0.38  cnf(c_0_33, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.15/0.38  fof(c_0_34, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.15/0.38  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.15/0.38  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.38  fof(c_0_38, negated_conjecture, k2_tarski(esk2_0,esk2_0)!=k1_tarski(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.15/0.38  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.15/0.38  cnf(c_0_40, plain, (k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k4_xboole_0(X3,X2))))=k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_15]), c_0_19])).
% 0.15/0.38  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.38  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.38  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|k1_xboole_0!=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.15/0.38  cnf(c_0_44, negated_conjecture, (k2_tarski(esk2_0,esk2_0)!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.15/0.38  cnf(c_0_45, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_39, c_0_15])).
% 0.15/0.38  cnf(c_0_46, plain, (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_25]), c_0_41])).
% 0.15/0.38  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=X1|k1_xboole_0!=X2), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.15/0.38  cnf(c_0_48, negated_conjecture, (k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk2_0)))!=k1_tarski(esk2_0)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.15/0.38  cnf(c_0_49, plain, (k5_xboole_0(k1_xboole_0,X1)=X1|k1_xboole_0!=X2), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.15/0.38  cnf(c_0_50, negated_conjecture, (k5_xboole_0(k1_xboole_0,k1_tarski(esk2_0))!=k1_tarski(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_37]), c_0_41])).
% 0.15/0.38  cnf(c_0_51, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(er,[status(thm)],[c_0_49])).
% 0.15/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])]), ['proof']).
% 0.15/0.38  # SZS output end CNFRefutation
% 0.15/0.38  # Proof object total steps             : 53
% 0.15/0.38  # Proof object clause steps            : 30
% 0.15/0.38  # Proof object formula steps           : 23
% 0.15/0.38  # Proof object conjectures             : 7
% 0.15/0.38  # Proof object clause conjectures      : 4
% 0.15/0.38  # Proof object formula conjectures     : 3
% 0.15/0.38  # Proof object initial clauses used    : 13
% 0.15/0.38  # Proof object initial formulas used   : 11
% 0.15/0.38  # Proof object generating inferences   : 9
% 0.15/0.38  # Proof object simplifying inferences  : 14
% 0.15/0.38  # Training examples: 0 positive, 0 negative
% 0.15/0.38  # Parsed axioms                        : 11
% 0.15/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.38  # Initial clauses                      : 15
% 0.15/0.38  # Removed in clause preprocessing      : 3
% 0.15/0.38  # Initial clauses in saturation        : 12
% 0.15/0.38  # Processed clauses                    : 44
% 0.15/0.38  # ...of these trivial                  : 10
% 0.15/0.38  # ...subsumed                          : 0
% 0.15/0.38  # ...remaining for further processing  : 34
% 0.15/0.38  # Other redundant clauses eliminated   : 0
% 0.15/0.38  # Clauses deleted for lack of memory   : 0
% 0.15/0.38  # Backward-subsumed                    : 0
% 0.15/0.38  # Backward-rewritten                   : 10
% 0.15/0.38  # Generated clauses                    : 226
% 0.15/0.38  # ...of the previous two non-trivial   : 148
% 0.15/0.38  # Contextual simplify-reflections      : 0
% 0.15/0.38  # Paramodulations                      : 224
% 0.15/0.38  # Factorizations                       : 0
% 0.15/0.38  # Equation resolutions                 : 2
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
% 0.15/0.38  # Current number of processed clauses  : 24
% 0.15/0.38  #    Positive orientable unit clauses  : 10
% 0.15/0.38  #    Positive unorientable unit clauses: 2
% 0.15/0.38  #    Negative unit clauses             : 0
% 0.15/0.38  #    Non-unit-clauses                  : 12
% 0.15/0.38  # Current number of unprocessed clauses: 113
% 0.15/0.38  # ...number of literals in the above   : 127
% 0.15/0.38  # Current number of archived formulas  : 0
% 0.15/0.38  # Current number of archived clauses   : 13
% 0.15/0.38  # Clause-clause subsumption calls (NU) : 19
% 0.15/0.38  # Rec. Clause-clause subsumption calls : 19
% 0.15/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.38  # Unit Clause-clause subsumption calls : 2
% 0.15/0.38  # Rewrite failures with RHS unbound    : 0
% 0.15/0.38  # BW rewrite match attempts            : 25
% 0.15/0.38  # BW rewrite match successes           : 8
% 0.15/0.38  # Condensation attempts                : 0
% 0.15/0.38  # Condensation successes               : 0
% 0.15/0.38  # Termbank termtop insertions          : 3004
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.029 s
% 0.15/0.38  # System time              : 0.004 s
% 0.15/0.38  # Total time               : 0.033 s
% 0.15/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
