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
% DateTime   : Thu Dec  3 10:34:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 736 expanded)
%              Number of clauses        :   56 ( 339 expanded)
%              Number of leaves         :   12 ( 192 expanded)
%              Depth                    :   22
%              Number of atoms          :  106 ( 995 expanded)
%              Number of equality atoms :   51 ( 492 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,k3_xboole_0(X13,X14))
      | r1_tarski(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_16,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = X1
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

fof(c_0_35,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_36,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_33]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

fof(c_0_45,plain,(
    ! [X19,X20,X21] : k3_xboole_0(X19,k4_xboole_0(X20,X21)) = k4_xboole_0(k3_xboole_0(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_44])).

fof(c_0_47,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_46])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_19]),c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_49]),c_0_39])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),X1)))) = k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_50])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_22])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_22]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_30]),c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_30]),c_0_49]),c_0_39]),c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_30])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_29]),c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0))) = k3_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_60]),c_0_39]),c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_28])).

fof(c_0_66,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0))) = k3_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_67])).

cnf(c_0_73,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_xboole_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_72]),c_0_30])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_73]),c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_74]),c_0_22])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_65])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_58]),c_0_78]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:44:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.027 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.42  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.19/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.42  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.42  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.42  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.42  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.42  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.42  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.42  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.42  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.19/0.42  fof(c_0_13, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.42  fof(c_0_14, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.42  fof(c_0_15, plain, ![X12, X13, X14]:(~r1_tarski(X12,k3_xboole_0(X13,X14))|r1_tarski(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.19/0.42  fof(c_0_16, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.42  fof(c_0_17, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.42  cnf(c_0_18, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  fof(c_0_20, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.42  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_24, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.42  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  fof(c_0_26, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.42  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=esk1_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.42  cnf(c_0_29, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_25, c_0_19])).
% 0.19/0.42  cnf(c_0_30, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (r1_tarski(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (r1_tarski(k1_xboole_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_30])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=X1|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_23, c_0_31])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk1_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 0.19/0.42  fof(c_0_35, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.42  fof(c_0_36, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_33]), c_0_30])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,esk1_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 0.19/0.42  cnf(c_0_39, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_40, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.42  cnf(c_0_42, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_42])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 0.19/0.42  fof(c_0_45, plain, ![X19, X20, X21]:k3_xboole_0(X19,k4_xboole_0(X20,X21))=k4_xboole_0(k3_xboole_0(X19,X20),X21), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_44])).
% 0.19/0.42  fof(c_0_47, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.42  cnf(c_0_48, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_46])).
% 0.19/0.42  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_51, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_19]), c_0_19])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_49]), c_0_39])).
% 0.19/0.42  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_50])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),X1))))=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_50])).
% 0.19/0.42  cnf(c_0_55, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_51, c_0_22])).
% 0.19/0.42  cnf(c_0_56, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_22]), c_0_51])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_52])).
% 0.19/0.42  cnf(c_0_58, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_30]), c_0_39])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_30]), c_0_49]), c_0_39]), c_0_28])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_30])).
% 0.19/0.42  cnf(c_0_61, plain, (r1_tarski(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_29]), c_0_51])).
% 0.19/0.42  cnf(c_0_62, negated_conjecture, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_52])).
% 0.19/0.42  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)))=k3_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_60]), c_0_39]), c_0_22])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_52])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_28])).
% 0.19/0.42  fof(c_0_66, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (r1_tarski(k3_xboole_0(k3_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_27, c_0_64])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_23, c_0_65])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_71, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)))=k3_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_67])).
% 0.19/0.42  cnf(c_0_73, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_xboole_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_72]), c_0_30])).
% 0.19/0.42  cnf(c_0_77, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_73]), c_0_22])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,X1))=k3_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_74]), c_0_22])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_65])])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_58]), c_0_78]), c_0_79]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 81
% 0.19/0.42  # Proof object clause steps            : 56
% 0.19/0.42  # Proof object formula steps           : 25
% 0.19/0.42  # Proof object conjectures             : 37
% 0.19/0.42  # Proof object clause conjectures      : 34
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 13
% 0.19/0.42  # Proof object initial formulas used   : 12
% 0.19/0.42  # Proof object generating inferences   : 38
% 0.19/0.42  # Proof object simplifying inferences  : 30
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 12
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 14
% 0.19/0.42  # Removed in clause preprocessing      : 1
% 0.19/0.42  # Initial clauses in saturation        : 13
% 0.19/0.42  # Processed clauses                    : 622
% 0.19/0.42  # ...of these trivial                  : 71
% 0.19/0.42  # ...subsumed                          : 312
% 0.19/0.42  # ...remaining for further processing  : 239
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 4
% 0.19/0.42  # Backward-rewritten                   : 70
% 0.19/0.42  # Generated clauses                    : 4153
% 0.19/0.42  # ...of the previous two non-trivial   : 2459
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 4153
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 0
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 152
% 0.19/0.42  #    Positive orientable unit clauses  : 79
% 0.19/0.42  #    Positive unorientable unit clauses: 5
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 66
% 0.19/0.42  # Current number of unprocessed clauses: 1815
% 0.19/0.42  # ...number of literals in the above   : 3027
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 88
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 2037
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2035
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 299
% 0.19/0.42  # Unit Clause-clause subsumption calls : 135
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 298
% 0.19/0.42  # BW rewrite match successes           : 101
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 51872
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.079 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.086 s
% 0.19/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
