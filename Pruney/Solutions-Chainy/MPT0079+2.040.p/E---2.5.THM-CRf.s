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
% DateTime   : Thu Dec  3 10:33:05 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 (3789 expanded)
%              Number of clauses        :   63 (1665 expanded)
%              Number of leaves         :   13 (1016 expanded)
%              Depth                    :   19
%              Number of atoms          :  108 (4906 expanded)
%              Number of equality atoms :   89 (4064 expanded)
%              Maximal formula depth    :    9 (   2 average)
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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_13,plain,(
    ! [X21,X22,X23] : k3_xboole_0(X21,k4_xboole_0(X22,X23)) = k4_xboole_0(k3_xboole_0(X21,X22),X23) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_14,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_17,plain,(
    ! [X10] : k3_xboole_0(X10,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk3_0,esk1_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & esk3_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_25,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_26,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X14,X15] : k4_xboole_0(k2_xboole_0(X14,X15),X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_40,plain,(
    ! [X27,X28] : k2_xboole_0(X27,k2_xboole_0(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32]),c_0_37]),c_0_38])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_44,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk1_0,X1)) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37])).

fof(c_0_48,plain,(
    ! [X24,X25,X26] : k2_xboole_0(k2_xboole_0(X24,X25),X26) = k2_xboole_0(X24,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_33]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1)) = k2_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_54]),c_0_32]),c_0_37]),c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_55]),c_0_49]),c_0_34]),c_0_52]),c_0_34]),c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(X1,esk2_0)) = k2_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_58]),c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_62]),c_0_52]),c_0_33]),c_0_52]),c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(X1,esk2_0)) = k4_xboole_0(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_49]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_64]),c_0_55]),c_0_59])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk4_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_50]),c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_37])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_69,c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk4_0),esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk4_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_72]),c_0_33])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk1_0,esk4_0)) = k4_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_66])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_35])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_49])).

cnf(c_0_79,negated_conjecture,
    ( esk4_0 = k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk1_0,esk4_0)) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_45])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_79])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_75]),c_0_79]),c_0_49]),c_0_42]),c_0_41]),c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_82]),c_0_34]),c_0_46]),c_0_79]),c_0_49]),c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_85]),c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_87]),c_0_33]),c_0_53]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.20/0.41  # and selection function SelectComplexG.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.026 s
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.41  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.41  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.20/0.41  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.41  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.41  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.41  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.41  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.20/0.41  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.41  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.41  fof(c_0_13, plain, ![X21, X22, X23]:k3_xboole_0(X21,k4_xboole_0(X22,X23))=k4_xboole_0(k3_xboole_0(X21,X22),X23), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.41  fof(c_0_14, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.41  fof(c_0_15, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.41  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.20/0.41  fof(c_0_17, plain, ![X10]:k3_xboole_0(X10,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.41  cnf(c_0_18, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_20, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.41  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  fof(c_0_22, negated_conjecture, (((k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)&r1_xboole_0(esk3_0,esk1_0))&r1_xboole_0(esk4_0,esk2_0))&esk3_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.41  cnf(c_0_23, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  fof(c_0_24, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.41  fof(c_0_25, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.41  fof(c_0_26, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.41  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.20/0.41  cnf(c_0_28, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_19])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_19])).
% 0.20/0.41  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.41  cnf(c_0_37, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.41  cnf(c_0_38, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.41  fof(c_0_39, plain, ![X14, X15]:k4_xboole_0(k2_xboole_0(X14,X15),X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.41  fof(c_0_40, plain, ![X27, X28]:k2_xboole_0(X27,k2_xboole_0(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32]), c_0_37]), c_0_38])).
% 0.20/0.41  cnf(c_0_42, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_43, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.41  fof(c_0_44, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk1_0,X1))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_41])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37])).
% 0.20/0.41  fof(c_0_48, plain, ![X24, X25, X26]:k2_xboole_0(k2_xboole_0(X24,X25),X26)=k2_xboole_0(X24,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.41  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_52, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_33]), c_0_34])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_51])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_46])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1))=k2_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.41  cnf(c_0_57, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_34])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (k2_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_46])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_54]), c_0_32]), c_0_37]), c_0_38])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk2_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_55]), c_0_49]), c_0_34]), c_0_52]), c_0_34]), c_0_46])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(X1,esk2_0))=k2_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_58]), c_0_37])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_59])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (k2_xboole_0(esk4_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.41  cnf(c_0_65, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_62]), c_0_52]), c_0_33]), c_0_52]), c_0_34])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(X1,esk2_0))=k4_xboole_0(esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_49]), c_0_63])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_64]), c_0_55]), c_0_59])).
% 0.20/0.41  cnf(c_0_69, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk4_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_65])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_50]), c_0_32])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk4_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_37])).
% 0.20/0.41  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_69, c_0_19])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk4_0),esk3_0)=esk4_0), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (k2_xboole_0(esk1_0,esk4_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_72]), c_0_33])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk1_0,esk4_0))=k4_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_66])).
% 0.20/0.41  cnf(c_0_77, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_35])).
% 0.20/0.41  cnf(c_0_78, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_49])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (esk4_0=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk1_0,esk4_0))=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_76, c_0_45])).
% 0.20/0.41  cnf(c_0_81, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_68, c_0_79])).
% 0.20/0.41  cnf(c_0_83, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_75]), c_0_79]), c_0_49]), c_0_42]), c_0_41]), c_0_79])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_82]), c_0_34]), c_0_46]), c_0_79]), c_0_49]), c_0_83]), c_0_84])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_85]), c_0_86])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (esk3_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_87]), c_0_33]), c_0_53]), c_0_88]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 90
% 0.20/0.41  # Proof object clause steps            : 63
% 0.20/0.41  # Proof object formula steps           : 27
% 0.20/0.41  # Proof object conjectures             : 39
% 0.20/0.41  # Proof object clause conjectures      : 36
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 17
% 0.20/0.41  # Proof object initial formulas used   : 13
% 0.20/0.41  # Proof object generating inferences   : 34
% 0.20/0.41  # Proof object simplifying inferences  : 56
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 13
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 17
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 16
% 0.20/0.41  # Processed clauses                    : 467
% 0.20/0.41  # ...of these trivial                  : 83
% 0.20/0.41  # ...subsumed                          : 184
% 0.20/0.41  # ...remaining for further processing  : 200
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 2
% 0.20/0.41  # Backward-rewritten                   : 80
% 0.20/0.41  # Generated clauses                    : 3493
% 0.20/0.41  # ...of the previous two non-trivial   : 2381
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 3490
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 3
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 118
% 0.20/0.42  #    Positive orientable unit clauses  : 76
% 0.20/0.42  #    Positive unorientable unit clauses: 4
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 37
% 0.20/0.42  # Current number of unprocessed clauses: 1863
% 0.20/0.42  # ...number of literals in the above   : 2240
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 83
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 861
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 856
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 161
% 0.20/0.42  # Unit Clause-clause subsumption calls : 127
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 231
% 0.20/0.42  # BW rewrite match successes           : 137
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 40162
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.068 s
% 0.20/0.42  # System time              : 0.006 s
% 0.20/0.42  # Total time               : 0.074 s
% 0.20/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
