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
% DateTime   : Thu Dec  3 10:34:02 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   87 (17317 expanded)
%              Number of clauses        :   60 (8102 expanded)
%              Number of leaves         :   13 (4607 expanded)
%              Depth                    :   25
%              Number of atoms          :   92 (18097 expanded)
%              Number of equality atoms :   83 (16848 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(c_0_13,plain,(
    ! [X16] : k3_xboole_0(X16,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_14,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X19] : k4_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] : k4_xboole_0(k4_xboole_0(X20,X21),X22) = k4_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_22,plain,(
    ! [X25,X26,X27] : k3_xboole_0(X25,k4_xboole_0(X26,X27)) = k4_xboole_0(k3_xboole_0(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_26,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X15] : k2_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_16]),c_0_16])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X28,X29,X30] : k4_xboole_0(X28,k4_xboole_0(X29,X30)) = k2_xboole_0(k4_xboole_0(X28,X29),k3_xboole_0(X28,X30)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_40])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_16])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_20])).

fof(c_0_47,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24]),c_0_35])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_23]),c_0_23])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_16]),c_0_16])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_50])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_50]),c_0_24]),c_0_20]),c_0_20])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_23])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_24]),c_0_35])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_20]),c_0_46]),c_0_31])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_53])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_51])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_31])).

fof(c_0_62,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_20]),c_0_31])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_48]),c_0_30]),c_0_37]),c_0_20]),c_0_31]),c_0_58])).

fof(c_0_65,negated_conjecture,(
    k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_62])])])).

fof(c_0_66,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_63]),c_0_53])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_31]),c_0_57])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_64]),c_0_23]),c_0_63]),c_0_36]),c_0_37]),c_0_23]),c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_31])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_16]),c_0_71]),c_0_71])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_69]),c_0_23])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_69]),c_0_72])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_73]),c_0_23])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_41]),c_0_20]),c_0_31])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_46])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0))) != k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_51])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k2_xboole_0(X1,X4)) = k4_xboole_0(X3,k2_xboole_0(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_75])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k4_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_31])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))) != k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_23]),c_0_63]),c_0_41]),c_0_35])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_53]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.73/0.90  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.73/0.90  # and selection function SelectNewComplexAHP.
% 0.73/0.90  #
% 0.73/0.90  # Preprocessing time       : 0.028 s
% 0.73/0.90  # Presaturation interreduction done
% 0.73/0.90  
% 0.73/0.90  # Proof found!
% 0.73/0.90  # SZS status Theorem
% 0.73/0.90  # SZS output start CNFRefutation
% 0.73/0.90  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.73/0.90  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.73/0.90  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.73/0.90  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.73/0.90  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.73/0.90  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.73/0.90  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.73/0.90  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.73/0.90  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.73/0.90  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.73/0.90  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.73/0.90  fof(t95_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.73/0.90  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.73/0.90  fof(c_0_13, plain, ![X16]:k3_xboole_0(X16,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.73/0.90  fof(c_0_14, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.73/0.90  cnf(c_0_15, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.73/0.90  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.73/0.90  fof(c_0_17, plain, ![X19]:k4_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.73/0.90  fof(c_0_18, plain, ![X20, X21, X22]:k4_xboole_0(k4_xboole_0(X20,X21),X22)=k4_xboole_0(X20,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.73/0.90  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.73/0.90  cnf(c_0_20, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.73/0.90  fof(c_0_21, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.73/0.90  fof(c_0_22, plain, ![X25, X26, X27]:k3_xboole_0(X25,k4_xboole_0(X26,X27))=k4_xboole_0(k3_xboole_0(X25,X26),X27), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.73/0.90  cnf(c_0_23, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.73/0.90  cnf(c_0_24, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.73/0.90  fof(c_0_25, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.73/0.90  fof(c_0_26, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.73/0.90  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.73/0.90  cnf(c_0_28, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.73/0.90  fof(c_0_29, plain, ![X15]:k2_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.73/0.90  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.73/0.90  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.73/0.90  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.73/0.90  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.73/0.90  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_16]), c_0_16])).
% 0.73/0.90  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.73/0.90  cnf(c_0_36, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.73/0.90  cnf(c_0_37, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.73/0.90  fof(c_0_38, plain, ![X28, X29, X30]:k4_xboole_0(X28,k4_xboole_0(X29,X30))=k2_xboole_0(k4_xboole_0(X28,X29),k3_xboole_0(X28,X30)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.73/0.90  cnf(c_0_39, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_34, c_0_23])).
% 0.73/0.90  cnf(c_0_40, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 0.73/0.90  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.73/0.90  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.73/0.90  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_24]), c_0_40])).
% 0.73/0.90  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 0.73/0.90  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_42, c_0_16])).
% 0.73/0.90  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_20])).
% 0.73/0.90  fof(c_0_47, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.73/0.90  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24]), c_0_35])).
% 0.73/0.90  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.73/0.90  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_23]), c_0_23])).
% 0.73/0.90  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_16]), c_0_16])).
% 0.73/0.90  cnf(c_0_52, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_50])).
% 0.73/0.90  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_50]), c_0_24]), c_0_20]), c_0_20])).
% 0.73/0.90  cnf(c_0_54, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_53, c_0_23])).
% 0.73/0.90  cnf(c_0_55, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_24]), c_0_35])).
% 0.73/0.90  cnf(c_0_56, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X2))=X1), inference(spm,[status(thm)],[c_0_55, c_0_31])).
% 0.73/0.90  cnf(c_0_57, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_20]), c_0_46]), c_0_31])).
% 0.73/0.90  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_56, c_0_53])).
% 0.73/0.90  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_57, c_0_51])).
% 0.73/0.90  cnf(c_0_60, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_37])).
% 0.73/0.90  cnf(c_0_61, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_58, c_0_31])).
% 0.73/0.90  fof(c_0_62, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t95_xboole_1])).
% 0.73/0.90  cnf(c_0_63, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_20]), c_0_31])).
% 0.73/0.90  cnf(c_0_64, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_58]), c_0_48]), c_0_30]), c_0_37]), c_0_20]), c_0_31]), c_0_58])).
% 0.73/0.90  fof(c_0_65, negated_conjecture, k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_62])])])).
% 0.73/0.90  fof(c_0_66, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.73/0.90  cnf(c_0_67, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_63]), c_0_53])).
% 0.73/0.90  cnf(c_0_68, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_51]), c_0_31]), c_0_57])).
% 0.73/0.90  cnf(c_0_69, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_64]), c_0_23]), c_0_63]), c_0_36]), c_0_37]), c_0_23]), c_0_35])).
% 0.73/0.90  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.73/0.90  cnf(c_0_71, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.73/0.90  cnf(c_0_72, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.73/0.90  cnf(c_0_73, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_31])).
% 0.73/0.90  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_16]), c_0_71]), c_0_71])).
% 0.73/0.90  cnf(c_0_75, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_69]), c_0_23])).
% 0.73/0.90  cnf(c_0_76, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_69]), c_0_72])).
% 0.73/0.90  cnf(c_0_77, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_73]), c_0_23])).
% 0.73/0.90  cnf(c_0_78, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_41]), c_0_20]), c_0_31])).
% 0.73/0.90  cnf(c_0_79, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_46])).
% 0.73/0.90  cnf(c_0_80, negated_conjecture, (k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0)))!=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_51])).
% 0.73/0.90  cnf(c_0_81, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k2_xboole_0(X1,X4))=k4_xboole_0(X3,k2_xboole_0(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_75])).
% 0.73/0.90  cnf(c_0_82, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))=k4_xboole_0(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.73/0.90  cnf(c_0_83, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_79, c_0_31])).
% 0.73/0.90  cnf(c_0_84, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)))!=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_23]), c_0_63]), c_0_41]), c_0_35])).
% 0.73/0.90  cnf(c_0_85, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_53]), c_0_83])).
% 0.73/0.90  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])]), ['proof']).
% 0.73/0.90  # SZS output end CNFRefutation
% 0.73/0.90  # Proof object total steps             : 87
% 0.73/0.90  # Proof object clause steps            : 60
% 0.73/0.90  # Proof object formula steps           : 27
% 0.73/0.90  # Proof object conjectures             : 8
% 0.73/0.90  # Proof object clause conjectures      : 5
% 0.73/0.90  # Proof object formula conjectures     : 3
% 0.73/0.90  # Proof object initial clauses used    : 13
% 0.73/0.90  # Proof object initial formulas used   : 13
% 0.73/0.90  # Proof object generating inferences   : 35
% 0.73/0.90  # Proof object simplifying inferences  : 64
% 0.73/0.90  # Training examples: 0 positive, 0 negative
% 0.73/0.90  # Parsed axioms                        : 14
% 0.73/0.90  # Removed by relevancy pruning/SinE    : 0
% 0.73/0.90  # Initial clauses                      : 15
% 0.73/0.90  # Removed in clause preprocessing      : 2
% 0.73/0.90  # Initial clauses in saturation        : 13
% 0.73/0.90  # Processed clauses                    : 2178
% 0.73/0.90  # ...of these trivial                  : 965
% 0.73/0.90  # ...subsumed                          : 804
% 0.73/0.90  # ...remaining for further processing  : 409
% 0.73/0.90  # Other redundant clauses eliminated   : 0
% 0.73/0.90  # Clauses deleted for lack of memory   : 0
% 0.73/0.90  # Backward-subsumed                    : 1
% 0.73/0.90  # Backward-rewritten                   : 126
% 0.73/0.90  # Generated clauses                    : 62644
% 0.73/0.90  # ...of the previous two non-trivial   : 38006
% 0.73/0.90  # Contextual simplify-reflections      : 0
% 0.73/0.90  # Paramodulations                      : 62638
% 0.73/0.90  # Factorizations                       : 0
% 0.73/0.90  # Equation resolutions                 : 6
% 0.73/0.90  # Propositional unsat checks           : 0
% 0.73/0.90  #    Propositional check models        : 0
% 0.73/0.90  #    Propositional check unsatisfiable : 0
% 0.73/0.90  #    Propositional clauses             : 0
% 0.73/0.90  #    Propositional clauses after purity: 0
% 0.73/0.90  #    Propositional unsat core size     : 0
% 0.73/0.90  #    Propositional preprocessing time  : 0.000
% 0.73/0.90  #    Propositional encoding time       : 0.000
% 0.73/0.90  #    Propositional solver time         : 0.000
% 0.73/0.90  #    Success case prop preproc time    : 0.000
% 0.73/0.90  #    Success case prop encoding time   : 0.000
% 0.73/0.90  #    Success case prop solver time     : 0.000
% 0.73/0.90  # Current number of processed clauses  : 269
% 0.73/0.90  #    Positive orientable unit clauses  : 235
% 0.73/0.90  #    Positive unorientable unit clauses: 8
% 0.73/0.90  #    Negative unit clauses             : 0
% 0.73/0.90  #    Non-unit-clauses                  : 26
% 0.73/0.90  # Current number of unprocessed clauses: 34851
% 0.73/0.90  # ...number of literals in the above   : 36610
% 0.73/0.90  # Current number of archived formulas  : 0
% 0.73/0.90  # Current number of archived clauses   : 142
% 0.73/0.90  # Clause-clause subsumption calls (NU) : 780
% 0.73/0.90  # Rec. Clause-clause subsumption calls : 780
% 0.73/0.90  # Non-unit clause-clause subsumptions  : 238
% 0.73/0.90  # Unit Clause-clause subsumption calls : 67
% 0.73/0.90  # Rewrite failures with RHS unbound    : 0
% 0.73/0.90  # BW rewrite match attempts            : 1840
% 0.73/0.90  # BW rewrite match successes           : 319
% 0.73/0.90  # Condensation attempts                : 0
% 0.73/0.90  # Condensation successes               : 0
% 0.73/0.90  # Termbank termtop insertions          : 656539
% 0.73/0.91  
% 0.73/0.91  # -------------------------------------------------
% 0.73/0.91  # User time                : 0.538 s
% 0.73/0.91  # System time              : 0.025 s
% 0.73/0.91  # Total time               : 0.563 s
% 0.73/0.91  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
