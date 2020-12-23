%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:01 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  107 (16370 expanded)
%              Number of clauses        :   80 (7341 expanded)
%              Number of leaves         :   13 (4194 expanded)
%              Depth                    :   21
%              Number of atoms          :  127 (23576 expanded)
%              Number of equality atoms :   84 (12541 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_20,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_24,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_25,plain,(
    ! [X20,X21] : r1_tarski(k4_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] : k3_xboole_0(X24,k4_xboole_0(X25,X26)) = k4_xboole_0(k3_xboole_0(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X10,X11,X12] : k3_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_28])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_27]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_21]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_22]),c_0_41])).

fof(c_0_46,plain,(
    ! [X28,X29,X30] : k5_xboole_0(k5_xboole_0(X28,X29),X30) = k5_xboole_0(X28,k5_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_47,plain,(
    ! [X27] : k5_xboole_0(X27,k1_xboole_0) = X27 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_43]),c_0_39]),c_0_22])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_41]),c_0_49])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_40]),c_0_31]),c_0_48]),c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_41])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_54]),c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_53]),c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_58]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_60]),c_0_61])).

fof(c_0_65,plain,(
    ! [X31,X32] : k2_xboole_0(X31,X32) = k5_xboole_0(X31,k4_xboole_0(X32,X31)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(esk3_0,X2))) = k5_xboole_0(esk3_0,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_64])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_62]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_67]),c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(X1,esk3_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_53])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_70,c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_67]),c_0_52]),c_0_31]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_68,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) != k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_27]),c_0_27]),c_0_27]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_53]),c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(esk2_0,X1)) = k5_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_76]),c_0_59])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_69]),c_0_53])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_80]),c_0_81])).

cnf(c_0_86,plain,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_56])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44]),c_0_39]),c_0_39])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_83]),c_0_52])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_22]),c_0_22]),c_0_52])).

cnf(c_0_91,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0)) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_85]),c_0_85])).

cnf(c_0_92,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_86]),c_0_52]),c_0_31]),c_0_87]),c_0_50]),c_0_88]),c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_85]),c_0_85])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

cnf(c_0_95,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_56]),c_0_31])).

cnf(c_0_96,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)) = k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0)) = k5_xboole_0(k3_xboole_0(X1,esk2_0),k3_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_22]),c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_83])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_61]),c_0_44])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_39])).

cnf(c_0_102,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1) = k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_96]),c_0_91]),c_0_97]),c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(X1,X2),X3) = k5_xboole_0(X3,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_99]),c_0_53])).

cnf(c_0_104,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_87]),c_0_101]),c_0_96]),c_0_64]),c_0_53])).

cnf(c_0_105,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1) = k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.52/0.71  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.52/0.71  # and selection function SelectNewComplexAHP.
% 0.52/0.71  #
% 0.52/0.71  # Preprocessing time       : 0.026 s
% 0.52/0.71  
% 0.52/0.71  # Proof found!
% 0.52/0.71  # SZS status Theorem
% 0.52/0.71  # SZS output start CNFRefutation
% 0.52/0.71  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 0.52/0.71  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.52/0.71  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.52/0.71  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.52/0.71  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.52/0.71  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.52/0.71  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.52/0.71  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.52/0.71  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.52/0.71  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.52/0.71  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.52/0.71  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.52/0.71  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.52/0.71  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 0.52/0.71  fof(c_0_14, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.52/0.71  fof(c_0_15, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.52/0.71  fof(c_0_16, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.52/0.71  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.52/0.71  cnf(c_0_18, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.71  fof(c_0_19, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.52/0.71  fof(c_0_20, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.52/0.71  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.52/0.71  cnf(c_0_22, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.52/0.71  fof(c_0_23, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.52/0.71  fof(c_0_24, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.52/0.71  fof(c_0_25, plain, ![X20, X21]:r1_tarski(k4_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.52/0.71  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.71  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.71  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.52/0.71  fof(c_0_29, plain, ![X24, X25, X26]:k3_xboole_0(X24,k4_xboole_0(X25,X26))=k4_xboole_0(k3_xboole_0(X24,X25),X26), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.52/0.71  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.71  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.52/0.71  fof(c_0_32, plain, ![X10, X11, X12]:k3_xboole_0(k3_xboole_0(X10,X11),X12)=k3_xboole_0(X10,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.52/0.71  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.52/0.71  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.52/0.71  cnf(c_0_35, negated_conjecture, (k3_xboole_0(esk3_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_17, c_0_28])).
% 0.52/0.71  cnf(c_0_36, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.52/0.71  cnf(c_0_37, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_18])).
% 0.52/0.71  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.52/0.71  cnf(c_0_39, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.52/0.71  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_33, c_0_27])).
% 0.52/0.71  cnf(c_0_41, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_35])).
% 0.52/0.71  cnf(c_0_42, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_27]), c_0_27])).
% 0.52/0.71  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.52/0.71  cnf(c_0_44, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_21]), c_0_39])).
% 0.52/0.71  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_22]), c_0_41])).
% 0.52/0.71  fof(c_0_46, plain, ![X28, X29, X30]:k5_xboole_0(k5_xboole_0(X28,X29),X30)=k5_xboole_0(X28,k5_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.52/0.71  fof(c_0_47, plain, ![X27]:k5_xboole_0(X27,k1_xboole_0)=X27, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.52/0.71  cnf(c_0_48, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_42, c_0_39])).
% 0.52/0.71  cnf(c_0_49, negated_conjecture, (k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_43]), c_0_39]), c_0_22])).
% 0.52/0.71  cnf(c_0_50, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 0.52/0.71  cnf(c_0_51, negated_conjecture, (r1_tarski(k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 0.52/0.71  cnf(c_0_52, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.52/0.71  cnf(c_0_53, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.52/0.71  cnf(c_0_54, negated_conjecture, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_41]), c_0_49])).
% 0.52/0.71  cnf(c_0_55, plain, (k5_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_40]), c_0_31]), c_0_48]), c_0_50])).
% 0.52/0.71  cnf(c_0_56, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.52/0.71  cnf(c_0_57, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_51])).
% 0.52/0.71  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_41])).
% 0.52/0.71  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.52/0.71  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_54]), c_0_53])).
% 0.52/0.71  cnf(c_0_61, negated_conjecture, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_54]), c_0_53]), c_0_53])).
% 0.52/0.71  cnf(c_0_62, negated_conjecture, (r1_tarski(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53])).
% 0.52/0.71  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k1_xboole_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_58]), c_0_59])).
% 0.52/0.71  cnf(c_0_64, negated_conjecture, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_60]), c_0_61])).
% 0.52/0.71  fof(c_0_65, plain, ![X31, X32]:k2_xboole_0(X31,X32)=k5_xboole_0(X31,k4_xboole_0(X32,X31)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.52/0.71  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk2_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_17, c_0_62])).
% 0.52/0.71  cnf(c_0_67, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_22])).
% 0.52/0.71  cnf(c_0_68, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(esk3_0,X2)))=k5_xboole_0(esk3_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_52])).
% 0.52/0.71  cnf(c_0_69, negated_conjecture, (k1_xboole_0=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_64])).
% 0.52/0.71  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.52/0.71  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_62]), c_0_66])).
% 0.52/0.71  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_67]), c_0_31])).
% 0.52/0.71  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(X1,esk3_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_53])).
% 0.52/0.71  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.71  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_70, c_0_27])).
% 0.52/0.71  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_71])).
% 0.52/0.71  cnf(c_0_77, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_67]), c_0_52]), c_0_31]), c_0_72])).
% 0.52/0.71  cnf(c_0_78, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(spm,[status(thm)],[c_0_68, c_0_73])).
% 0.52/0.71  cnf(c_0_79, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))!=k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_27]), c_0_27]), c_0_27]), c_0_75])).
% 0.52/0.71  cnf(c_0_80, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_53]), c_0_63])).
% 0.52/0.71  cnf(c_0_81, negated_conjecture, (k5_xboole_0(k1_xboole_0,k5_xboole_0(esk2_0,X1))=k5_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_76]), c_0_59])).
% 0.52/0.71  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.52/0.71  cnf(c_0_83, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_69]), c_0_53])).
% 0.52/0.71  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31])).
% 0.52/0.71  cnf(c_0_85, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k5_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_80]), c_0_81])).
% 0.52/0.71  cnf(c_0_86, plain, (r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_82, c_0_56])).
% 0.52/0.71  cnf(c_0_87, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 0.52/0.71  cnf(c_0_88, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_44]), c_0_39]), c_0_39])).
% 0.52/0.71  cnf(c_0_89, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_83]), c_0_52])).
% 0.52/0.71  cnf(c_0_90, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_22]), c_0_22]), c_0_52])).
% 0.52/0.71  cnf(c_0_91, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0))=k5_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_85]), c_0_85])).
% 0.52/0.71  cnf(c_0_92, plain, (k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_86]), c_0_52]), c_0_31]), c_0_87]), c_0_50]), c_0_88]), c_0_89])).
% 0.52/0.71  cnf(c_0_93, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_85]), c_0_85])).
% 0.52/0.71  cnf(c_0_94, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_39])).
% 0.52/0.71  cnf(c_0_95, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_56]), c_0_31])).
% 0.52/0.71  cnf(c_0_96, negated_conjecture, (k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1))=k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_91])).
% 0.52/0.71  cnf(c_0_97, negated_conjecture, (k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0))=k5_xboole_0(k3_xboole_0(X1,esk2_0),k3_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_22]), c_0_85])).
% 0.52/0.71  cnf(c_0_98, negated_conjecture, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_78, c_0_83])).
% 0.52/0.71  cnf(c_0_99, negated_conjecture, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_61]), c_0_44])).
% 0.52/0.71  cnf(c_0_100, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.52/0.71  cnf(c_0_101, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_31]), c_0_39])).
% 0.52/0.71  cnf(c_0_102, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)=k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_96]), c_0_91]), c_0_97]), c_0_98])).
% 0.52/0.71  cnf(c_0_103, negated_conjecture, (k5_xboole_0(k3_xboole_0(X1,X2),X3)=k5_xboole_0(X3,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_99]), c_0_53])).
% 0.52/0.71  cnf(c_0_104, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_87]), c_0_101]), c_0_96]), c_0_64]), c_0_53])).
% 0.52/0.71  cnf(c_0_105, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)=k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_103])).
% 0.52/0.71  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105]), c_0_83])]), ['proof']).
% 0.52/0.71  # SZS output end CNFRefutation
% 0.52/0.71  # Proof object total steps             : 107
% 0.52/0.71  # Proof object clause steps            : 80
% 0.52/0.71  # Proof object formula steps           : 27
% 0.52/0.71  # Proof object conjectures             : 52
% 0.52/0.71  # Proof object clause conjectures      : 49
% 0.52/0.71  # Proof object formula conjectures     : 3
% 0.52/0.71  # Proof object initial clauses used    : 14
% 0.52/0.71  # Proof object initial formulas used   : 13
% 0.52/0.71  # Proof object generating inferences   : 53
% 0.52/0.71  # Proof object simplifying inferences  : 81
% 0.52/0.71  # Training examples: 0 positive, 0 negative
% 0.52/0.71  # Parsed axioms                        : 14
% 0.52/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.71  # Initial clauses                      : 16
% 0.52/0.71  # Removed in clause preprocessing      : 2
% 0.52/0.71  # Initial clauses in saturation        : 14
% 0.52/0.71  # Processed clauses                    : 4323
% 0.52/0.71  # ...of these trivial                  : 1102
% 0.52/0.71  # ...subsumed                          : 2595
% 0.52/0.71  # ...remaining for further processing  : 626
% 0.52/0.71  # Other redundant clauses eliminated   : 0
% 0.52/0.71  # Clauses deleted for lack of memory   : 0
% 0.52/0.71  # Backward-subsumed                    : 16
% 0.52/0.71  # Backward-rewritten                   : 228
% 0.52/0.71  # Generated clauses                    : 51586
% 0.52/0.71  # ...of the previous two non-trivial   : 30149
% 0.52/0.71  # Contextual simplify-reflections      : 0
% 0.52/0.71  # Paramodulations                      : 51575
% 0.52/0.71  # Factorizations                       : 0
% 0.52/0.71  # Equation resolutions                 : 11
% 0.52/0.71  # Propositional unsat checks           : 0
% 0.52/0.71  #    Propositional check models        : 0
% 0.52/0.71  #    Propositional check unsatisfiable : 0
% 0.52/0.71  #    Propositional clauses             : 0
% 0.52/0.71  #    Propositional clauses after purity: 0
% 0.52/0.71  #    Propositional unsat core size     : 0
% 0.52/0.71  #    Propositional preprocessing time  : 0.000
% 0.52/0.71  #    Propositional encoding time       : 0.000
% 0.52/0.71  #    Propositional solver time         : 0.000
% 0.52/0.71  #    Success case prop preproc time    : 0.000
% 0.52/0.71  #    Success case prop encoding time   : 0.000
% 0.52/0.71  #    Success case prop solver time     : 0.000
% 0.52/0.71  # Current number of processed clauses  : 382
% 0.52/0.71  #    Positive orientable unit clauses  : 265
% 0.52/0.71  #    Positive unorientable unit clauses: 14
% 0.52/0.71  #    Negative unit clauses             : 0
% 0.52/0.71  #    Non-unit-clauses                  : 103
% 0.52/0.71  # Current number of unprocessed clauses: 25049
% 0.52/0.71  # ...number of literals in the above   : 30489
% 0.52/0.71  # Current number of archived formulas  : 0
% 0.52/0.71  # Current number of archived clauses   : 246
% 0.52/0.71  # Clause-clause subsumption calls (NU) : 8462
% 0.52/0.71  # Rec. Clause-clause subsumption calls : 8462
% 0.52/0.71  # Non-unit clause-clause subsumptions  : 1943
% 0.52/0.71  # Unit Clause-clause subsumption calls : 432
% 0.52/0.71  # Rewrite failures with RHS unbound    : 100
% 0.52/0.71  # BW rewrite match attempts            : 3993
% 0.52/0.71  # BW rewrite match successes           : 1115
% 0.52/0.71  # Condensation attempts                : 0
% 0.52/0.71  # Condensation successes               : 0
% 0.52/0.71  # Termbank termtop insertions          : 690560
% 0.52/0.71  
% 0.52/0.71  # -------------------------------------------------
% 0.52/0.71  # User time                : 0.343 s
% 0.52/0.71  # System time              : 0.029 s
% 0.52/0.71  # Total time               : 0.372 s
% 0.52/0.71  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
