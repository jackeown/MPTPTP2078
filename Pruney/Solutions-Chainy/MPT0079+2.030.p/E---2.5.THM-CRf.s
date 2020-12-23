%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:04 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   98 (1316 expanded)
%              Number of clauses        :   65 ( 555 expanded)
%              Number of leaves         :   16 ( 360 expanded)
%              Depth                    :   15
%              Number of atoms          :  122 (1769 expanded)
%              Number of equality atoms :   99 (1438 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_16,plain,(
    ! [X18,X19] : k4_xboole_0(k2_xboole_0(X18,X19),X19) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_17,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_19,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_20,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,plain,(
    ! [X30,X31] : k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) = X30 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_22,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk3_0,esk1_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & esk3_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_26,plain,(
    ! [X32,X33,X34] : k4_xboole_0(X32,k4_xboole_0(X33,X34)) = k2_xboole_0(k4_xboole_0(X32,X33),k3_xboole_0(X32,X34)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X16,X15)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_32,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k3_xboole_0(X23,X24)) = k4_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_44,plain,(
    ! [X27,X28,X29] : k2_xboole_0(k2_xboole_0(X27,X28),X29) = k2_xboole_0(X27,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_45,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_46,plain,(
    ! [X20,X21,X22] : k4_xboole_0(k4_xboole_0(X20,X21),X22) = k4_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk1_0) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_24]),c_0_40]),c_0_24])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_35])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_47]),c_0_40]),c_0_35])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38]),c_0_24]),c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_53]),c_0_40]),c_0_24]),c_0_54]),c_0_24]),c_0_35])).

fof(c_0_61,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_57]),c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk4_0,esk2_0)) = k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_60])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk1_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

fof(c_0_68,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1))) = k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_60]),c_0_54]),c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk2_0,k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0)))) = k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_65]),c_0_54]),c_0_54]),c_0_24]),c_0_54]),c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0)))) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_65]),c_0_54])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_24]),c_0_54])).

cnf(c_0_74,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(X1,esk2_0))) = k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_24])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1)) = k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_35]),c_0_54])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_xboole_0(X1,esk4_0)) = k2_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_49]),c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_76]),c_0_38])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_54])).

cnf(c_0_84,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_35]),c_0_78]),c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_24]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_23])).

cnf(c_0_88,negated_conjecture,
    ( esk2_0 = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_85]),c_0_23]),c_0_86])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_40])).

cnf(c_0_90,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,k4_xboole_0(esk3_0,esk4_0))) = k2_xboole_0(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_87]),c_0_54])).

cnf(c_0_91,negated_conjecture,
    ( k2_xboole_0(esk1_0,k4_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_89]),c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_95,negated_conjecture,
    ( k2_xboole_0(esk1_0,k4_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_94,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_95]),c_0_23]),c_0_59]),c_0_56]),c_0_24]),c_0_74]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:47:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.18/0.39  # and selection function SelectComplexG.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.026 s
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.18/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.39  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.18/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.18/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.18/0.39  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.18/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.18/0.39  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.18/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.39  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.18/0.39  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.18/0.39  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.18/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.18/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.39  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.18/0.39  fof(c_0_16, plain, ![X18, X19]:k4_xboole_0(k2_xboole_0(X18,X19),X19)=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.18/0.39  fof(c_0_17, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.39  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.18/0.39  fof(c_0_19, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.18/0.39  fof(c_0_20, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.18/0.39  fof(c_0_21, plain, ![X30, X31]:k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31))=X30, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.18/0.39  fof(c_0_22, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.18/0.39  cnf(c_0_23, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.39  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.39  fof(c_0_25, negated_conjecture, (((k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)&r1_xboole_0(esk3_0,esk1_0))&r1_xboole_0(esk4_0,esk2_0))&esk3_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.18/0.39  fof(c_0_26, plain, ![X32, X33, X34]:k4_xboole_0(X32,k4_xboole_0(X33,X34))=k2_xboole_0(k4_xboole_0(X32,X33),k3_xboole_0(X32,X34)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.18/0.39  cnf(c_0_27, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.39  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  fof(c_0_29, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.39  cnf(c_0_30, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  fof(c_0_31, plain, ![X15, X16]:k2_xboole_0(X15,k4_xboole_0(X16,X15))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.18/0.39  fof(c_0_32, plain, ![X23, X24]:k4_xboole_0(X23,k3_xboole_0(X23,X24))=k4_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.18/0.39  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_34, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.39  cnf(c_0_35, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.39  cnf(c_0_38, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.39  cnf(c_0_39, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_30, c_0_28])).
% 0.18/0.39  cnf(c_0_40, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_41, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.39  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_28])).
% 0.18/0.39  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  fof(c_0_44, plain, ![X27, X28, X29]:k2_xboole_0(k2_xboole_0(X27,X28),X29)=k2_xboole_0(X27,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.18/0.39  fof(c_0_45, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.39  fof(c_0_46, plain, ![X20, X21, X22]:k4_xboole_0(k4_xboole_0(X20,X21),X22)=k4_xboole_0(X20,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.18/0.39  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk2_0,esk1_0)=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk1_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.39  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_36, c_0_28])).
% 0.18/0.39  cnf(c_0_49, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.39  cnf(c_0_50, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_24]), c_0_40]), c_0_24])).
% 0.18/0.39  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_28])).
% 0.18/0.39  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.39  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_35])).
% 0.18/0.39  cnf(c_0_54, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.39  cnf(c_0_55, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_56, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.39  cnf(c_0_57, negated_conjecture, (k2_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_47]), c_0_40]), c_0_35])).
% 0.18/0.39  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38]), c_0_24]), c_0_50])).
% 0.18/0.39  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_38])).
% 0.18/0.39  cnf(c_0_60, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_53]), c_0_40]), c_0_24]), c_0_54]), c_0_24]), c_0_35])).
% 0.18/0.39  fof(c_0_61, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.39  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.39  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_57]), c_0_49])).
% 0.18/0.39  cnf(c_0_64, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.39  cnf(c_0_65, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk4_0,esk2_0))=k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_60])).
% 0.18/0.39  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.39  cnf(c_0_67, negated_conjecture, (r1_tarski(esk1_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.18/0.39  fof(c_0_68, plain, ![X13]:k2_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.18/0.39  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_70, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1)))=k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_60]), c_0_54]), c_0_54])).
% 0.18/0.39  cnf(c_0_71, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk2_0,k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0))))=k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_65]), c_0_54]), c_0_54]), c_0_24]), c_0_54]), c_0_60])).
% 0.18/0.39  cnf(c_0_72, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0))))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_65]), c_0_54])).
% 0.18/0.39  cnf(c_0_73, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_24]), c_0_54])).
% 0.18/0.39  cnf(c_0_74, negated_conjecture, (k2_xboole_0(esk1_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.39  cnf(c_0_75, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.39  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_69])).
% 0.18/0.39  cnf(c_0_77, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(X1,esk2_0)))=k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_70, c_0_24])).
% 0.18/0.39  cnf(c_0_78, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.18/0.39  cnf(c_0_79, negated_conjecture, (k2_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))=k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_35]), c_0_54])).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk1_0,k2_xboole_0(X1,esk4_0))=k2_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.18/0.39  cnf(c_0_81, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_49]), c_0_75])).
% 0.18/0.39  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_76]), c_0_38])).
% 0.18/0.39  cnf(c_0_83, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_23, c_0_54])).
% 0.18/0.39  cnf(c_0_84, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_35]), c_0_78]), c_0_24])).
% 0.18/0.39  cnf(c_0_85, negated_conjecture, (k2_xboole_0(esk4_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_24]), c_0_81])).
% 0.18/0.39  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=esk2_0), inference(spm,[status(thm)],[c_0_58, c_0_82])).
% 0.18/0.39  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_23])).
% 0.18/0.39  cnf(c_0_88, negated_conjecture, (esk2_0=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_85]), c_0_23]), c_0_86])).
% 0.18/0.39  cnf(c_0_89, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_40])).
% 0.18/0.39  cnf(c_0_90, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,k4_xboole_0(esk3_0,esk4_0)))=k2_xboole_0(esk3_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_87]), c_0_54])).
% 0.18/0.39  cnf(c_0_91, negated_conjecture, (k2_xboole_0(esk1_0,k4_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_35, c_0_88])).
% 0.18/0.39  cnf(c_0_92, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_89]), c_0_24])).
% 0.18/0.39  cnf(c_0_93, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk3_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91]), c_0_92])).
% 0.18/0.39  cnf(c_0_94, negated_conjecture, (esk3_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_95, negated_conjecture, (k2_xboole_0(esk1_0,k4_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_91, c_0_93])).
% 0.18/0.39  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)!=esk3_0), inference(rw,[status(thm)],[c_0_94, c_0_88])).
% 0.18/0.39  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_95]), c_0_23]), c_0_59]), c_0_56]), c_0_24]), c_0_74]), c_0_96]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 98
% 0.18/0.39  # Proof object clause steps            : 65
% 0.18/0.39  # Proof object formula steps           : 33
% 0.18/0.39  # Proof object conjectures             : 39
% 0.18/0.39  # Proof object clause conjectures      : 36
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 19
% 0.18/0.39  # Proof object initial formulas used   : 16
% 0.18/0.39  # Proof object generating inferences   : 34
% 0.18/0.39  # Proof object simplifying inferences  : 57
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 16
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 21
% 0.18/0.39  # Removed in clause preprocessing      : 1
% 0.18/0.39  # Initial clauses in saturation        : 20
% 0.18/0.39  # Processed clauses                    : 259
% 0.18/0.39  # ...of these trivial                  : 28
% 0.18/0.39  # ...subsumed                          : 68
% 0.18/0.39  # ...remaining for further processing  : 163
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 2
% 0.18/0.39  # Backward-rewritten                   : 80
% 0.18/0.39  # Generated clauses                    : 1861
% 0.18/0.39  # ...of the previous two non-trivial   : 1340
% 0.18/0.39  # Contextual simplify-reflections      : 0
% 0.18/0.39  # Paramodulations                      : 1856
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 5
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 81
% 0.18/0.39  #    Positive orientable unit clauses  : 48
% 0.18/0.39  #    Positive unorientable unit clauses: 4
% 0.18/0.39  #    Negative unit clauses             : 1
% 0.18/0.39  #    Non-unit-clauses                  : 28
% 0.18/0.39  # Current number of unprocessed clauses: 1082
% 0.18/0.39  # ...number of literals in the above   : 1304
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 83
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 257
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 257
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 68
% 0.18/0.39  # Unit Clause-clause subsumption calls : 53
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 198
% 0.18/0.39  # BW rewrite match successes           : 110
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 19750
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.049 s
% 0.18/0.39  # System time              : 0.005 s
% 0.18/0.39  # Total time               : 0.054 s
% 0.18/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
