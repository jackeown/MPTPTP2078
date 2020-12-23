%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:07 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 514 expanded)
%              Number of clauses        :   50 ( 239 expanded)
%              Number of leaves         :   10 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          :   92 ( 768 expanded)
%              Number of equality atoms :   48 ( 429 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_10,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_11,plain,(
    ! [X10] : k2_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,X12) != k1_xboole_0
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | k4_xboole_0(X11,X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X15,X16,X17] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_19,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_28,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_29,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_24])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_33])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_39]),c_0_40]),c_0_27])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_41])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_42]),c_0_40]),c_0_27])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_43])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_47])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_52]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_48]),c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_50])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,k1_xboole_0)) = k4_xboole_0(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(k4_xboole_0(esk2_0,k1_xboole_0),X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_24])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_48]),c_0_20]),c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_21]),c_0_50]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.21/0.38  # and selection function SelectNewComplexAHP.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.026 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.38  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.21/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.38  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.38  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.21/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.21/0.38  fof(c_0_10, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.38  fof(c_0_11, plain, ![X10]:k2_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.21/0.38  fof(c_0_12, plain, ![X11, X12]:((k4_xboole_0(X11,X12)!=k1_xboole_0|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|k4_xboole_0(X11,X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.38  cnf(c_0_13, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_14, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  fof(c_0_15, plain, ![X15, X16, X17]:k4_xboole_0(k4_xboole_0(X15,X16),X17)=k4_xboole_0(X15,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.38  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_17, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.38  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.21/0.38  fof(c_0_19, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.38  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_21, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.38  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 0.21/0.38  fof(c_0_23, negated_conjecture, ((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))&r1_xboole_0(esk1_0,esk3_0))&~r1_tarski(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.21/0.38  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  fof(c_0_25, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.38  cnf(c_0_26, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_27, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.21/0.38  fof(c_0_28, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.38  fof(c_0_29, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.38  fof(c_0_30, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.38  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_13, c_0_24])).
% 0.21/0.38  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.38  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.38  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.38  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_31])).
% 0.21/0.38  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_20]), c_0_20]), c_0_20])).
% 0.21/0.38  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_32])).
% 0.21/0.38  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_33])).
% 0.21/0.38  cnf(c_0_43, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.38  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 0.21/0.38  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 0.21/0.38  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_39]), c_0_40]), c_0_27])).
% 0.21/0.38  cnf(c_0_48, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k2_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_41])).
% 0.21/0.38  cnf(c_0_49, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_42]), c_0_40]), c_0_27])).
% 0.21/0.38  cnf(c_0_50, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_24, c_0_43])).
% 0.21/0.38  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_47])).
% 0.21/0.38  cnf(c_0_54, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_50])).
% 0.21/0.38  cnf(c_0_55, plain, (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_26, c_0_51])).
% 0.21/0.38  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_52]), c_0_27])).
% 0.21/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.38  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k4_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_55])).
% 0.21/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_26, c_0_56])).
% 0.21/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_48]), c_0_20])).
% 0.21/0.38  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,k1_xboole_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_60])).
% 0.21/0.38  cnf(c_0_63, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_50])).
% 0.21/0.38  cnf(c_0_64, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_26, c_0_49])).
% 0.21/0.38  cnf(c_0_65, negated_conjecture, (k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,k1_xboole_0))=k4_xboole_0(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_63])).
% 0.21/0.38  cnf(c_0_66, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(k4_xboole_0(esk2_0,k1_xboole_0),X1))), inference(spm,[status(thm)],[c_0_66, c_0_24])).
% 0.21/0.38  cnf(c_0_68, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_48]), c_0_20]), c_0_43])).
% 0.21/0.38  cnf(c_0_69, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_21]), c_0_50]), c_0_69]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 71
% 0.21/0.38  # Proof object clause steps            : 50
% 0.21/0.38  # Proof object formula steps           : 21
% 0.21/0.38  # Proof object conjectures             : 22
% 0.21/0.38  # Proof object clause conjectures      : 19
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 13
% 0.21/0.38  # Proof object initial formulas used   : 10
% 0.21/0.38  # Proof object generating inferences   : 35
% 0.21/0.38  # Proof object simplifying inferences  : 19
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 10
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 14
% 0.21/0.38  # Removed in clause preprocessing      : 1
% 0.21/0.38  # Initial clauses in saturation        : 13
% 0.21/0.38  # Processed clauses                    : 144
% 0.21/0.38  # ...of these trivial                  : 42
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 102
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 2
% 0.21/0.38  # Generated clauses                    : 918
% 0.21/0.38  # ...of the previous two non-trivial   : 471
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 918
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 87
% 0.21/0.38  #    Positive orientable unit clauses  : 73
% 0.21/0.38  #    Positive unorientable unit clauses: 4
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 9
% 0.21/0.38  # Current number of unprocessed clauses: 341
% 0.21/0.38  # ...number of literals in the above   : 382
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 16
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 2
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 2
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.38  # Unit Clause-clause subsumption calls : 2
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 94
% 0.21/0.38  # BW rewrite match successes           : 18
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 8632
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.035 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.040 s
% 0.21/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
