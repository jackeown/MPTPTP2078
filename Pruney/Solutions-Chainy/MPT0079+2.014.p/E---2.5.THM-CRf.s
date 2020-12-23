%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 (2743 expanded)
%              Number of clauses        :   65 (1183 expanded)
%              Number of leaves         :   13 ( 749 expanded)
%              Depth                    :   15
%              Number of atoms          :  112 (3589 expanded)
%              Number of equality atoms :   98 (3042 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_14,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_16,plain,(
    ! [X25,X26] : k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26)) = X25 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_17,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k2_xboole_0(X21,X22)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_18,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk3_0,esk1_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & esk3_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X16,X15)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_24,plain,(
    ! [X13,X14] :
      ( k4_xboole_0(X13,X14) != k4_xboole_0(X14,X13)
      | X13 = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

fof(c_0_25,plain,(
    ! [X18,X19,X20] : k4_xboole_0(k4_xboole_0(X18,X19),X20) = k4_xboole_0(X18,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_26,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_27,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_29]),c_0_34]),c_0_29])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = X3
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k4_xboole_0(X3,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_20]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_20])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_43]),c_0_44]),c_0_29]),c_0_45])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = X1
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_48]),c_0_44]),c_0_29]),c_0_45])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_51]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_52])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk1_0,X1)) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_55])])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk2_0,X1) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(X1,esk2_0)) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_44]),c_0_60]),c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_42]),c_0_28])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_55]),c_0_28])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk4_0,k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_41])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_66]),c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0),esk2_0) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_70]),c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1)) = k2_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_72]),c_0_44]),c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0),esk2_0) = k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_74]),c_0_74]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk2_0,X1) = k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_74]),c_0_74])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X1),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_36])).

cnf(c_0_79,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(X1,esk2_0)) = k2_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_29])).

cnf(c_0_81,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_29]),c_0_45])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_76]),c_0_77]),c_0_29]),c_0_78]),c_0_41]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0)) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_74]),c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_36]),c_0_29]),c_0_42]),c_0_74]),c_0_55]),c_0_36]),c_0_44]),c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0)) = k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_74]),c_0_74]),c_0_74]),c_0_74])).

cnf(c_0_87,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( esk2_0 = k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_89]),c_0_36]),c_0_29]),c_0_55]),c_0_36]),c_0_44]),c_0_79]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.20/0.45  # and selection function SelectComplexG.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.027 s
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.45  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.20/0.45  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.45  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.45  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.45  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.45  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.20/0.45  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.45  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.45  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.45  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.45  fof(c_0_13, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.45  fof(c_0_14, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.45  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.20/0.45  fof(c_0_16, plain, ![X25, X26]:k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26))=X25, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.45  fof(c_0_17, plain, ![X21, X22]:k4_xboole_0(X21,k2_xboole_0(X21,X22))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.45  fof(c_0_18, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.45  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.45  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.45  fof(c_0_21, negated_conjecture, (((k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)&r1_xboole_0(esk3_0,esk1_0))&r1_xboole_0(esk4_0,esk2_0))&esk3_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.45  cnf(c_0_22, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.45  fof(c_0_23, plain, ![X15, X16]:k2_xboole_0(X15,k4_xboole_0(X16,X15))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.45  fof(c_0_24, plain, ![X13, X14]:(k4_xboole_0(X13,X14)!=k4_xboole_0(X14,X13)|X13=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.20/0.45  fof(c_0_25, plain, ![X18, X19, X20]:k4_xboole_0(k4_xboole_0(X18,X19),X20)=k4_xboole_0(X18,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.45  fof(c_0_26, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.45  fof(c_0_27, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.45  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.45  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.45  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  fof(c_0_32, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.45  cnf(c_0_33, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.20/0.45  cnf(c_0_34, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_35, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_39, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.45  fof(c_0_40, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.45  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.45  cnf(c_0_42, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.45  cnf(c_0_44, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_45, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_29]), c_0_34]), c_0_29])).
% 0.20/0.45  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=X3|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k4_xboole_0(X3,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.45  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_20]), c_0_20])).
% 0.20/0.45  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 0.20/0.45  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_20])).
% 0.20/0.45  cnf(c_0_50, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.45  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.45  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_43]), c_0_44]), c_0_29]), c_0_45])).
% 0.20/0.45  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=X1|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_41])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_48]), c_0_44]), c_0_29]), c_0_45])).
% 0.20/0.45  cnf(c_0_55, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.45  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_51]), c_0_50])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_52])).
% 0.20/0.45  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 0.20/0.45  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk1_0,X1))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 0.20/0.45  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_55])])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk2_0,X1)=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0),X1))), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.20/0.45  cnf(c_0_64, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(X1,esk2_0))=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_29])).
% 0.20/0.45  cnf(c_0_65, negated_conjecture, (k2_xboole_0(esk1_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_44]), c_0_60]), c_0_29])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_42]), c_0_28])).
% 0.20/0.45  cnf(c_0_67, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_55]), c_0_28])).
% 0.20/0.45  cnf(c_0_68, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 0.20/0.45  cnf(c_0_69, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk4_0,k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_29])).
% 0.20/0.45  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk4_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_42]), c_0_41])).
% 0.20/0.45  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk1_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_65])).
% 0.20/0.45  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_66]), c_0_67])).
% 0.20/0.45  cnf(c_0_73, negated_conjecture, (k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0),esk2_0)=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.45  cnf(c_0_74, negated_conjecture, (esk4_0=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_70]), c_0_71])])).
% 0.20/0.45  cnf(c_0_75, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,X1))=k2_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_72]), c_0_44]), c_0_29])).
% 0.20/0.45  cnf(c_0_76, negated_conjecture, (k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0),esk2_0)=k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_74]), c_0_74]), c_0_74])).
% 0.20/0.45  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk2_0,X1)=k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_74]), c_0_74])).
% 0.20/0.45  cnf(c_0_78, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X1),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_36])).
% 0.20/0.45  cnf(c_0_79, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 0.20/0.45  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(X1,esk2_0))=k2_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_75, c_0_29])).
% 0.20/0.45  cnf(c_0_81, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_29]), c_0_45])).
% 0.20/0.45  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_76]), c_0_77]), c_0_29]), c_0_78]), c_0_41]), c_0_79])).
% 0.20/0.45  cnf(c_0_83, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0))=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_73])).
% 0.20/0.45  cnf(c_0_84, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_74]), c_0_74])).
% 0.20/0.45  cnf(c_0_85, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_36]), c_0_29]), c_0_42]), c_0_74]), c_0_55]), c_0_36]), c_0_44]), c_0_79])).
% 0.20/0.45  cnf(c_0_86, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0))=k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_74]), c_0_74]), c_0_74]), c_0_74])).
% 0.20/0.45  cnf(c_0_87, negated_conjecture, (esk3_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_88, negated_conjecture, (esk2_0=k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0)), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.45  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_86])).
% 0.20/0.45  cnf(c_0_90, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk1_0)!=esk3_0), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.45  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_89]), c_0_36]), c_0_29]), c_0_55]), c_0_36]), c_0_44]), c_0_79]), c_0_90]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 92
% 0.20/0.45  # Proof object clause steps            : 65
% 0.20/0.45  # Proof object formula steps           : 27
% 0.20/0.45  # Proof object conjectures             : 41
% 0.20/0.45  # Proof object clause conjectures      : 38
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 16
% 0.20/0.45  # Proof object initial formulas used   : 13
% 0.20/0.45  # Proof object generating inferences   : 36
% 0.20/0.45  # Proof object simplifying inferences  : 71
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 13
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 17
% 0.20/0.45  # Removed in clause preprocessing      : 1
% 0.20/0.45  # Initial clauses in saturation        : 16
% 0.20/0.45  # Processed clauses                    : 982
% 0.20/0.45  # ...of these trivial                  : 152
% 0.20/0.45  # ...subsumed                          : 425
% 0.20/0.45  # ...remaining for further processing  : 405
% 0.20/0.45  # Other redundant clauses eliminated   : 0
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 17
% 0.20/0.45  # Backward-rewritten                   : 266
% 0.20/0.45  # Generated clauses                    : 6702
% 0.20/0.45  # ...of the previous two non-trivial   : 3766
% 0.20/0.45  # Contextual simplify-reflections      : 0
% 0.20/0.45  # Paramodulations                      : 6691
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 11
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 122
% 0.20/0.45  #    Positive orientable unit clauses  : 52
% 0.20/0.45  #    Positive unorientable unit clauses: 4
% 0.20/0.45  #    Negative unit clauses             : 1
% 0.20/0.45  #    Non-unit-clauses                  : 65
% 0.20/0.45  # Current number of unprocessed clauses: 2634
% 0.20/0.45  # ...number of literals in the above   : 3861
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 284
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 4593
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 4215
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 438
% 0.20/0.45  # Unit Clause-clause subsumption calls : 205
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 248
% 0.20/0.45  # BW rewrite match successes           : 53
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 74591
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.113 s
% 0.20/0.45  # System time              : 0.004 s
% 0.20/0.45  # Total time               : 0.116 s
% 0.20/0.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
