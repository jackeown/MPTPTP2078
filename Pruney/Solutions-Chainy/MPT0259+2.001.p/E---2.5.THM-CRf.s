%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:50 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 708 expanded)
%              Number of clauses        :   49 ( 332 expanded)
%              Number of leaves         :   16 ( 187 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 842 expanded)
%              Number of equality atoms :   66 ( 614 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t71_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t54_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

fof(t76_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t88_enumset1,axiom,(
    ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(c_0_16,plain,(
    ! [X9,X10] : r1_tarski(k3_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_17,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_19,plain,(
    ! [X27,X28] : k2_xboole_0(X27,X28) = k5_xboole_0(k5_xboole_0(X27,X28),k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X16,X17,X18] : k4_xboole_0(X16,k3_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_28,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k3_xboole_0(X11,X12)) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X15] : k4_xboole_0(k1_xboole_0,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_34,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X19,X20,X21] :
      ( k2_xboole_0(X19,X20) != k2_xboole_0(X21,X20)
      | ~ r1_xboole_0(X19,X20)
      | ~ r1_xboole_0(X21,X20)
      | X19 = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t71_xboole_1])])).

fof(c_0_37,plain,(
    ! [X25,X26] : r1_xboole_0(k4_xboole_0(X25,X26),X26) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_21]),c_0_30])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_21])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( r1_xboole_0(k1_tarski(X1),X2)
          & r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t54_zfmisc_1])).

cnf(c_0_44,plain,
    ( X1 = X3
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X2)
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_39])).

fof(c_0_48,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_xboole_0(X22,X23)
      | r1_xboole_0(k3_xboole_0(X24,X22),k3_xboole_0(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).

fof(c_0_49,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk1_0),esk2_0)
    & r2_hidden(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

fof(c_0_50,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_51,plain,(
    ! [X30,X31] : k4_enumset1(X30,X30,X30,X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t88_enumset1])).

cnf(c_0_52,plain,
    ( X1 = X3
    | k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) != k5_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2)))
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_30]),c_0_30])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_42])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) != X2
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_40]),c_0_41]),c_0_53])]),c_0_54])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_21]),c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_42]),c_0_38])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_59])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,X2))) != X2
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_41])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k4_xboole_0(X1,k4_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_47]),c_0_47]),c_0_42])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_38]),c_0_39]),c_0_47])])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k4_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_64]),c_0_47])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_67])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_47])).

fof(c_0_73,plain,(
    ! [X32,X33] :
      ( ( k4_xboole_0(k1_tarski(X32),X33) != k1_tarski(X32)
        | ~ r2_hidden(X32,X33) )
      & ( r2_hidden(X32,X33)
        | k4_xboole_0(k1_tarski(X32),X33) = k1_tarski(X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_41]),c_0_47]),c_0_39]),c_0_41]),c_0_54])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_74]),c_0_47])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) != k4_enumset1(X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_57]),c_0_57]),c_0_58]),c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_39]),c_0_47])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.12/0.39  # and selection function SelectCQIArNpEqFirst.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.027 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.12/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.12/0.39  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.12/0.39  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 0.12/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.12/0.39  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.12/0.39  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.12/0.39  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.12/0.39  fof(t71_xboole_1, axiom, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 0.12/0.39  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.12/0.39  fof(t54_zfmisc_1, conjecture, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 0.12/0.39  fof(t76_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 0.12/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.39  fof(t88_enumset1, axiom, ![X1, X2]:k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 0.12/0.39  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.12/0.39  fof(c_0_16, plain, ![X9, X10]:r1_tarski(k3_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.12/0.39  fof(c_0_17, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.39  fof(c_0_18, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.12/0.39  fof(c_0_19, plain, ![X27, X28]:k2_xboole_0(X27,X28)=k5_xboole_0(k5_xboole_0(X27,X28),k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.12/0.39  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_22, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  fof(c_0_23, plain, ![X16, X17, X18]:k4_xboole_0(X16,k3_xboole_0(X17,X18))=k2_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 0.12/0.39  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  fof(c_0_25, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.12/0.39  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.39  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.12/0.39  fof(c_0_28, plain, ![X11, X12]:k4_xboole_0(X11,k3_xboole_0(X11,X12))=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.12/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_21])).
% 0.12/0.39  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.39  fof(c_0_33, plain, ![X15]:k4_xboole_0(k1_xboole_0,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.12/0.39  fof(c_0_34, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.12/0.39  cnf(c_0_35, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  fof(c_0_36, plain, ![X19, X20, X21]:(k2_xboole_0(X19,X20)!=k2_xboole_0(X21,X20)|~r1_xboole_0(X19,X20)|~r1_xboole_0(X21,X20)|X19=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t71_xboole_1])])).
% 0.12/0.39  fof(c_0_37, plain, ![X25, X26]:r1_xboole_0(k4_xboole_0(X25,X26),X26), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.12/0.39  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_21]), c_0_30])).
% 0.12/0.39  cnf(c_0_39, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.39  cnf(c_0_40, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.39  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_21])).
% 0.12/0.39  fof(c_0_43, negated_conjecture, ~(![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2)))), inference(assume_negation,[status(cth)],[t54_zfmisc_1])).
% 0.12/0.39  cnf(c_0_44, plain, (X1=X3|k2_xboole_0(X1,X2)!=k2_xboole_0(X3,X2)|~r1_xboole_0(X1,X2)|~r1_xboole_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.39  cnf(c_0_45, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.39  cnf(c_0_46, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_42])).
% 0.12/0.39  cnf(c_0_47, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_27, c_0_39])).
% 0.12/0.39  fof(c_0_48, plain, ![X22, X23, X24]:(~r1_xboole_0(X22,X23)|r1_xboole_0(k3_xboole_0(X24,X22),k3_xboole_0(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).
% 0.12/0.39  fof(c_0_49, negated_conjecture, (r1_xboole_0(k1_tarski(esk1_0),esk2_0)&r2_hidden(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.12/0.39  fof(c_0_50, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.39  fof(c_0_51, plain, ![X30, X31]:k4_enumset1(X30,X30,X30,X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t88_enumset1])).
% 0.12/0.39  cnf(c_0_52, plain, (X1=X3|k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))!=k5_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,k4_xboole_0(X3,X2)))|~r1_xboole_0(X3,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_30]), c_0_30])).
% 0.12/0.39  cnf(c_0_53, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.12/0.39  cnf(c_0_54, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.39  cnf(c_0_55, plain, (r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k1_tarski(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.39  cnf(c_0_57, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.39  cnf(c_0_58, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.39  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_26, c_0_42])).
% 0.12/0.39  cnf(c_0_60, plain, (X1=k1_xboole_0|k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))!=X2|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_40]), c_0_40]), c_0_41]), c_0_53])]), c_0_54])).
% 0.12/0.39  cnf(c_0_61, plain, (r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_21]), c_0_21])).
% 0.12/0.39  cnf(c_0_62, negated_conjecture, (r1_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.12/0.39  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_42]), c_0_38])).
% 0.12/0.39  cnf(c_0_64, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_59])).
% 0.12/0.39  cnf(c_0_65, plain, (X1=k1_xboole_0|k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,X2)))!=X2|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_41])).
% 0.12/0.39  cnf(c_0_66, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.39  cnf(c_0_67, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_47]), c_0_47]), c_0_42])).
% 0.12/0.39  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_38]), c_0_39]), c_0_47])])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k4_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_64]), c_0_47])).
% 0.12/0.39  cnf(c_0_70, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_67])).
% 0.12/0.39  cnf(c_0_71, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_68, c_0_47])).
% 0.12/0.39  cnf(c_0_72, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_47])).
% 0.12/0.39  fof(c_0_73, plain, ![X32, X33]:((k4_xboole_0(k1_tarski(X32),X33)!=k1_tarski(X32)|~r2_hidden(X32,X33))&(r2_hidden(X32,X33)|k4_xboole_0(k1_tarski(X32),X33)=k1_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.12/0.39  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.12/0.39  cnf(c_0_75, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.39  cnf(c_0_76, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_41]), c_0_47]), c_0_39]), c_0_41]), c_0_54])).
% 0.12/0.39  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_74]), c_0_47])).
% 0.12/0.39  cnf(c_0_78, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)!=k4_enumset1(X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_57]), c_0_57]), c_0_58]), c_0_58])).
% 0.12/0.39  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_39]), c_0_47])).
% 0.12/0.39  cnf(c_0_80, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 82
% 0.12/0.39  # Proof object clause steps            : 49
% 0.12/0.39  # Proof object formula steps           : 33
% 0.12/0.39  # Proof object conjectures             : 13
% 0.12/0.39  # Proof object clause conjectures      : 10
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 17
% 0.12/0.39  # Proof object initial formulas used   : 16
% 0.12/0.39  # Proof object generating inferences   : 22
% 0.12/0.39  # Proof object simplifying inferences  : 45
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 16
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 19
% 0.12/0.39  # Removed in clause preprocessing      : 4
% 0.12/0.39  # Initial clauses in saturation        : 15
% 0.12/0.39  # Processed clauses                    : 200
% 0.12/0.39  # ...of these trivial                  : 19
% 0.12/0.39  # ...subsumed                          : 83
% 0.12/0.39  # ...remaining for further processing  : 98
% 0.12/0.39  # Other redundant clauses eliminated   : 7
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 2
% 0.12/0.39  # Backward-rewritten                   : 15
% 0.12/0.39  # Generated clauses                    : 930
% 0.12/0.39  # ...of the previous two non-trivial   : 552
% 0.12/0.39  # Contextual simplify-reflections      : 0
% 0.12/0.39  # Paramodulations                      : 921
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 9
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 66
% 0.12/0.39  #    Positive orientable unit clauses  : 34
% 0.12/0.39  #    Positive unorientable unit clauses: 1
% 0.12/0.39  #    Negative unit clauses             : 2
% 0.12/0.39  #    Non-unit-clauses                  : 29
% 0.12/0.39  # Current number of unprocessed clauses: 349
% 0.12/0.39  # ...number of literals in the above   : 764
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 36
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 246
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 245
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 64
% 0.12/0.39  # Unit Clause-clause subsumption calls : 17
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 63
% 0.12/0.39  # BW rewrite match successes           : 11
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 14497
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.044 s
% 0.12/0.39  # System time              : 0.003 s
% 0.12/0.39  # Total time               : 0.047 s
% 0.12/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
