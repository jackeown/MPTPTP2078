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
% DateTime   : Thu Dec  3 10:34:38 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   94 (2358 expanded)
%              Number of clauses        :   65 (1091 expanded)
%              Number of leaves         :   14 ( 632 expanded)
%              Depth                    :   19
%              Number of atoms          :  138 (2589 expanded)
%              Number of equality atoms :   62 (2097 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_14,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_15,plain,(
    ! [X33,X34] : k3_xboole_0(X33,X34) = k5_xboole_0(k5_xboole_0(X33,X34),k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_19,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X17,X18)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_22,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_17])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_17])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23])).

cnf(c_0_35,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

fof(c_0_40,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_39])])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_41]),c_0_23])).

fof(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_17]),c_0_17])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_23])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_50,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32]),c_0_32])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_55,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_56,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_xboole_0(X24,X25)
      | r1_xboole_0(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_26]),c_0_17])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_38])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_49,c_0_53])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_17])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_32])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_59])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_60,c_0_32])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_17])).

cnf(c_0_68,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_26]),c_0_17])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_65])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_52])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_32])).

cnf(c_0_73,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_32])).

fof(c_0_74,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)),X1) ),
    inference(rw,[status(thm)],[c_0_69,c_0_65])).

cnf(c_0_76,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_70])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1) ),
    inference(rw,[status(thm)],[c_0_73,c_0_65])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_26]),c_0_17])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_30]),c_0_58]),c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(esk1_0,k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_32])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0
    | ~ r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_70])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_73])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X2,k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_85,c_0_65])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n013.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 16:42:09 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 0.10/0.29  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.10/0.29  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.10/0.29  #
% 0.10/0.29  # Preprocessing time       : 0.012 s
% 0.10/0.29  # Presaturation interreduction done
% 0.10/0.29  
% 0.10/0.29  # Proof found!
% 0.10/0.29  # SZS status Theorem
% 0.10/0.29  # SZS output start CNFRefutation
% 0.10/0.29  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.10/0.29  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.10/0.29  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.10/0.29  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.10/0.29  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.10/0.29  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.10/0.29  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.10/0.29  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.10/0.29  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.10/0.29  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.10/0.29  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.10/0.29  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.10/0.29  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.10/0.29  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.10/0.29  fof(c_0_14, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.10/0.29  fof(c_0_15, plain, ![X33, X34]:k3_xboole_0(X33,X34)=k5_xboole_0(k5_xboole_0(X33,X34),k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.10/0.29  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.29  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.10/0.29  fof(c_0_18, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.10/0.29  fof(c_0_19, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.10/0.29  fof(c_0_20, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.10/0.29  fof(c_0_21, plain, ![X17, X18]:k4_xboole_0(X17,k2_xboole_0(X17,X18))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.10/0.29  cnf(c_0_22, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.10/0.29  cnf(c_0_23, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.29  fof(c_0_24, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.10/0.29  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.10/0.29  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.10/0.29  fof(c_0_27, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.10/0.29  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.10/0.29  cnf(c_0_29, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.10/0.29  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.10/0.29  cnf(c_0_31, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_17])).
% 0.10/0.29  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.10/0.29  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_17])).
% 0.10/0.29  cnf(c_0_34, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23])).
% 0.10/0.29  cnf(c_0_35, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.10/0.29  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_23])).
% 0.10/0.29  cnf(c_0_37, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.10/0.29  cnf(c_0_38, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.10/0.29  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 0.10/0.29  fof(c_0_40, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.10/0.29  cnf(c_0_41, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_39])])).
% 0.10/0.29  fof(c_0_42, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.10/0.29  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.29  cnf(c_0_44, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.10/0.29  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_41]), c_0_23])).
% 0.10/0.29  fof(c_0_46, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.10/0.29  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_17]), c_0_17])).
% 0.10/0.29  cnf(c_0_48, plain, (k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_23])).
% 0.10/0.29  cnf(c_0_49, plain, (k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.10/0.29  fof(c_0_50, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.10/0.29  cnf(c_0_51, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.10/0.29  cnf(c_0_52, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32]), c_0_32])).
% 0.10/0.29  cnf(c_0_53, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.10/0.29  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.10/0.29  fof(c_0_55, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.10/0.29  fof(c_0_56, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_xboole_0(X24,X25)|r1_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.10/0.29  cnf(c_0_57, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_26]), c_0_17])).
% 0.10/0.29  cnf(c_0_58, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_38])).
% 0.10/0.29  cnf(c_0_59, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[c_0_49, c_0_53])).
% 0.10/0.29  cnf(c_0_60, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_17])).
% 0.10/0.29  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.10/0.29  cnf(c_0_62, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.10/0.29  cnf(c_0_63, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.10/0.29  cnf(c_0_64, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))))), inference(rw,[status(thm)],[c_0_57, c_0_32])).
% 0.10/0.29  cnf(c_0_65, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_58]), c_0_59])).
% 0.10/0.29  cnf(c_0_66, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_60, c_0_32])).
% 0.10/0.29  cnf(c_0_67, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_17])).
% 0.10/0.29  cnf(c_0_68, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_26]), c_0_17])).
% 0.10/0.29  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))),X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.10/0.29  cnf(c_0_70, plain, (r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)), inference(rw,[status(thm)],[c_0_35, c_0_65])).
% 0.10/0.29  cnf(c_0_71, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_52])).
% 0.10/0.29  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_67, c_0_32])).
% 0.10/0.29  cnf(c_0_73, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2)), inference(rw,[status(thm)],[c_0_68, c_0_32])).
% 0.10/0.29  fof(c_0_74, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.10/0.29  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)),X1)), inference(rw,[status(thm)],[c_0_69, c_0_65])).
% 0.10/0.29  cnf(c_0_76, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_63, c_0_70])).
% 0.10/0.29  cnf(c_0_77, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.10/0.29  cnf(c_0_78, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1)), inference(rw,[status(thm)],[c_0_73, c_0_65])).
% 0.10/0.29  cnf(c_0_79, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.10/0.29  cnf(c_0_80, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.10/0.29  cnf(c_0_81, plain, (r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.10/0.29  cnf(c_0_82, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_26]), c_0_17])).
% 0.10/0.29  cnf(c_0_83, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_30]), c_0_58]), c_0_23])).
% 0.10/0.29  cnf(c_0_84, negated_conjecture, (r1_xboole_0(esk1_0,k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.10/0.29  cnf(c_0_85, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_32])).
% 0.10/0.29  cnf(c_0_86, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0|~r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_83, c_0_70])).
% 0.10/0.29  cnf(c_0_87, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)),esk1_0)), inference(spm,[status(thm)],[c_0_77, c_0_84])).
% 0.10/0.29  cnf(c_0_88, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.10/0.29  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_73])).
% 0.10/0.29  cnf(c_0_90, plain, (r1_tarski(X1,X2)|k5_xboole_0(X2,k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_85, c_0_65])).
% 0.10/0.29  cnf(c_0_91, negated_conjecture, (k5_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.10/0.29  cnf(c_0_92, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89])])).
% 0.10/0.29  cnf(c_0_93, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), ['proof']).
% 0.10/0.29  # SZS output end CNFRefutation
% 0.10/0.29  # Proof object total steps             : 94
% 0.10/0.29  # Proof object clause steps            : 65
% 0.10/0.29  # Proof object formula steps           : 29
% 0.10/0.29  # Proof object conjectures             : 16
% 0.10/0.29  # Proof object clause conjectures      : 13
% 0.10/0.29  # Proof object formula conjectures     : 3
% 0.10/0.29  # Proof object initial clauses used    : 16
% 0.10/0.29  # Proof object initial formulas used   : 14
% 0.10/0.29  # Proof object generating inferences   : 24
% 0.10/0.29  # Proof object simplifying inferences  : 44
% 0.10/0.29  # Training examples: 0 positive, 0 negative
% 0.10/0.29  # Parsed axioms                        : 16
% 0.10/0.29  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.29  # Initial clauses                      : 20
% 0.10/0.29  # Removed in clause preprocessing      : 2
% 0.10/0.29  # Initial clauses in saturation        : 18
% 0.10/0.29  # Processed clauses                    : 585
% 0.10/0.29  # ...of these trivial                  : 18
% 0.10/0.29  # ...subsumed                          : 332
% 0.10/0.29  # ...remaining for further processing  : 235
% 0.10/0.29  # Other redundant clauses eliminated   : 67
% 0.10/0.29  # Clauses deleted for lack of memory   : 0
% 0.10/0.29  # Backward-subsumed                    : 18
% 0.10/0.29  # Backward-rewritten                   : 56
% 0.10/0.29  # Generated clauses                    : 2956
% 0.10/0.29  # ...of the previous two non-trivial   : 2272
% 0.10/0.29  # Contextual simplify-reflections      : 8
% 0.10/0.29  # Paramodulations                      : 2889
% 0.10/0.29  # Factorizations                       : 0
% 0.10/0.29  # Equation resolutions                 : 67
% 0.10/0.29  # Propositional unsat checks           : 0
% 0.10/0.29  #    Propositional check models        : 0
% 0.10/0.29  #    Propositional check unsatisfiable : 0
% 0.10/0.29  #    Propositional clauses             : 0
% 0.10/0.29  #    Propositional clauses after purity: 0
% 0.10/0.29  #    Propositional unsat core size     : 0
% 0.10/0.29  #    Propositional preprocessing time  : 0.000
% 0.10/0.29  #    Propositional encoding time       : 0.000
% 0.10/0.29  #    Propositional solver time         : 0.000
% 0.10/0.29  #    Success case prop preproc time    : 0.000
% 0.10/0.29  #    Success case prop encoding time   : 0.000
% 0.10/0.29  #    Success case prop solver time     : 0.000
% 0.10/0.29  # Current number of processed clauses  : 142
% 0.10/0.29  #    Positive orientable unit clauses  : 29
% 0.10/0.29  #    Positive unorientable unit clauses: 6
% 0.10/0.29  #    Negative unit clauses             : 2
% 0.10/0.29  #    Non-unit-clauses                  : 105
% 0.10/0.29  # Current number of unprocessed clauses: 1523
% 0.10/0.29  # ...number of literals in the above   : 3639
% 0.10/0.29  # Current number of archived formulas  : 0
% 0.10/0.29  # Current number of archived clauses   : 94
% 0.10/0.29  # Clause-clause subsumption calls (NU) : 1816
% 0.10/0.29  # Rec. Clause-clause subsumption calls : 1760
% 0.10/0.29  # Non-unit clause-clause subsumptions  : 291
% 0.10/0.29  # Unit Clause-clause subsumption calls : 46
% 0.10/0.29  # Rewrite failures with RHS unbound    : 0
% 0.10/0.29  # BW rewrite match attempts            : 315
% 0.10/0.29  # BW rewrite match successes           : 176
% 0.10/0.29  # Condensation attempts                : 0
% 0.10/0.29  # Condensation successes               : 0
% 0.10/0.29  # Termbank termtop insertions          : 36057
% 0.10/0.29  
% 0.10/0.29  # -------------------------------------------------
% 0.10/0.29  # User time                : 0.033 s
% 0.10/0.29  # System time              : 0.003 s
% 0.10/0.29  # Total time               : 0.036 s
% 0.10/0.29  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
