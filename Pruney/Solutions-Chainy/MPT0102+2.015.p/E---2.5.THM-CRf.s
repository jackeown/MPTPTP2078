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
% DateTime   : Thu Dec  3 10:34:03 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 634 expanded)
%              Number of clauses        :   45 ( 273 expanded)
%              Number of leaves         :   14 ( 180 expanded)
%              Depth                    :   14
%              Number of atoms          :   84 ( 729 expanded)
%              Number of equality atoms :   67 ( 590 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(c_0_14,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_15,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_17,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] : k4_xboole_0(k4_xboole_0(X18,X19),X20) = k4_xboole_0(X18,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X16,X17] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_26,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X28,X29] :
      ( ( ~ r1_xboole_0(X28,X29)
        | k4_xboole_0(X28,X29) = X28 )
      & ( k4_xboole_0(X28,X29) != X28
        | r1_xboole_0(X28,X29) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

fof(c_0_34,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_35,plain,(
    ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_36,plain,(
    ! [X21,X22,X23] : k4_xboole_0(k2_xboole_0(X21,X22),X23) = k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_39])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_43]),c_0_44]),c_0_30])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_45])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_47])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_48])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_41])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_43]),c_0_39])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_50]),c_0_24]),c_0_40])).

fof(c_0_55,negated_conjecture,(
    k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

fof(c_0_56,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_28]),c_0_39])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_57]),c_0_58]),c_0_30])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_20]),c_0_60]),c_0_60])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X4,X2))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X3,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_44]),c_0_30])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k4_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_40])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_44]),c_0_43]),c_0_30])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_39])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0))) != k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_27])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),k2_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_41])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_44]),c_0_45])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_39]),c_0_67]),c_0_39]),c_0_71]),c_0_29]),c_0_40]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.54/0.73  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.54/0.73  # and selection function SelectNewComplexAHP.
% 0.54/0.73  #
% 0.54/0.73  # Preprocessing time       : 0.027 s
% 0.54/0.73  # Presaturation interreduction done
% 0.54/0.73  
% 0.54/0.73  # Proof found!
% 0.54/0.73  # SZS status Theorem
% 0.54/0.73  # SZS output start CNFRefutation
% 0.54/0.73  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.54/0.73  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.54/0.73  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.54/0.73  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.54/0.73  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.54/0.73  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.54/0.73  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.54/0.73  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.54/0.73  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.54/0.73  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.54/0.73  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.54/0.73  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.54/0.73  fof(t95_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.54/0.73  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.54/0.73  fof(c_0_14, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.54/0.73  fof(c_0_15, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.54/0.73  fof(c_0_16, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.54/0.73  fof(c_0_17, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.54/0.73  fof(c_0_18, plain, ![X18, X19, X20]:k4_xboole_0(k4_xboole_0(X18,X19),X20)=k4_xboole_0(X18,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.54/0.73  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.54/0.73  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.54/0.73  fof(c_0_21, plain, ![X16, X17]:k4_xboole_0(k2_xboole_0(X16,X17),X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.54/0.73  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.73  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.73  cnf(c_0_24, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.73  fof(c_0_25, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.54/0.73  fof(c_0_26, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.54/0.73  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 0.54/0.73  cnf(c_0_28, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.73  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.54/0.73  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.54/0.73  fof(c_0_31, plain, ![X28, X29]:((~r1_xboole_0(X28,X29)|k4_xboole_0(X28,X29)=X28)&(k4_xboole_0(X28,X29)!=X28|r1_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.54/0.73  cnf(c_0_32, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.73  cnf(c_0_33, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 0.54/0.73  fof(c_0_34, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.54/0.73  fof(c_0_35, plain, ![X12]:k2_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.54/0.73  fof(c_0_36, plain, ![X21, X22, X23]:k4_xboole_0(k2_xboole_0(X21,X22),X23)=k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.54/0.73  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.73  cnf(c_0_38, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.54/0.73  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.54/0.73  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.54/0.73  cnf(c_0_41, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.54/0.73  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.54/0.73  cnf(c_0_43, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_39])).
% 0.54/0.73  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_39])).
% 0.54/0.73  cnf(c_0_45, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.54/0.73  cnf(c_0_46, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.54/0.73  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_43]), c_0_44]), c_0_30])).
% 0.54/0.73  cnf(c_0_48, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_45])).
% 0.54/0.73  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_47])).
% 0.54/0.73  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_48])).
% 0.54/0.73  fof(c_0_51, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t95_xboole_1])).
% 0.54/0.73  cnf(c_0_52, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_41])).
% 0.54/0.73  cnf(c_0_53, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_43]), c_0_39])).
% 0.54/0.73  cnf(c_0_54, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_50]), c_0_24]), c_0_40])).
% 0.54/0.73  fof(c_0_55, negated_conjecture, k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.54/0.73  fof(c_0_56, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.54/0.73  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_28]), c_0_39])).
% 0.54/0.73  cnf(c_0_58, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_54])).
% 0.54/0.73  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.54/0.73  cnf(c_0_60, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.54/0.73  cnf(c_0_61, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_57]), c_0_58]), c_0_30])).
% 0.54/0.73  cnf(c_0_62, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_42])).
% 0.54/0.73  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_20]), c_0_60]), c_0_60])).
% 0.54/0.73  cnf(c_0_64, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X4,X2)))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X3,X4)),X2)), inference(spm,[status(thm)],[c_0_41, c_0_24])).
% 0.54/0.73  cnf(c_0_65, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_44]), c_0_30])).
% 0.54/0.73  cnf(c_0_66, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))=k4_xboole_0(X1,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_40])).
% 0.54/0.73  cnf(c_0_67, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_44]), c_0_43]), c_0_30])).
% 0.54/0.73  cnf(c_0_68, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_39])).
% 0.54/0.73  cnf(c_0_69, negated_conjecture, (k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0)))!=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_27])).
% 0.54/0.73  cnf(c_0_70, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),k2_xboole_0(X3,X4))=k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_41])).
% 0.54/0.73  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_44]), c_0_45])).
% 0.54/0.73  cnf(c_0_72, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.54/0.73  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_39]), c_0_67]), c_0_39]), c_0_71]), c_0_29]), c_0_40]), c_0_72])]), ['proof']).
% 0.54/0.73  # SZS output end CNFRefutation
% 0.54/0.73  # Proof object total steps             : 74
% 0.54/0.73  # Proof object clause steps            : 45
% 0.54/0.73  # Proof object formula steps           : 29
% 0.54/0.73  # Proof object conjectures             : 7
% 0.54/0.73  # Proof object clause conjectures      : 4
% 0.54/0.73  # Proof object formula conjectures     : 3
% 0.54/0.73  # Proof object initial clauses used    : 14
% 0.54/0.73  # Proof object initial formulas used   : 14
% 0.54/0.73  # Proof object generating inferences   : 27
% 0.54/0.73  # Proof object simplifying inferences  : 42
% 0.54/0.73  # Training examples: 0 positive, 0 negative
% 0.54/0.73  # Parsed axioms                        : 14
% 0.54/0.73  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.73  # Initial clauses                      : 16
% 0.54/0.73  # Removed in clause preprocessing      : 2
% 0.54/0.73  # Initial clauses in saturation        : 14
% 0.54/0.73  # Processed clauses                    : 1471
% 0.54/0.73  # ...of these trivial                  : 516
% 0.54/0.73  # ...subsumed                          : 558
% 0.54/0.73  # ...remaining for further processing  : 396
% 0.54/0.73  # Other redundant clauses eliminated   : 0
% 0.54/0.73  # Clauses deleted for lack of memory   : 0
% 0.54/0.73  # Backward-subsumed                    : 0
% 0.54/0.73  # Backward-rewritten                   : 107
% 0.54/0.73  # Generated clauses                    : 44099
% 0.54/0.73  # ...of the previous two non-trivial   : 25986
% 0.54/0.73  # Contextual simplify-reflections      : 0
% 0.54/0.73  # Paramodulations                      : 44087
% 0.54/0.73  # Factorizations                       : 0
% 0.54/0.73  # Equation resolutions                 : 12
% 0.54/0.73  # Propositional unsat checks           : 0
% 0.54/0.73  #    Propositional check models        : 0
% 0.54/0.73  #    Propositional check unsatisfiable : 0
% 0.54/0.73  #    Propositional clauses             : 0
% 0.54/0.73  #    Propositional clauses after purity: 0
% 0.54/0.73  #    Propositional unsat core size     : 0
% 0.54/0.73  #    Propositional preprocessing time  : 0.000
% 0.54/0.73  #    Propositional encoding time       : 0.000
% 0.54/0.73  #    Propositional solver time         : 0.000
% 0.54/0.73  #    Success case prop preproc time    : 0.000
% 0.54/0.73  #    Success case prop encoding time   : 0.000
% 0.54/0.73  #    Success case prop solver time     : 0.000
% 0.54/0.73  # Current number of processed clauses  : 275
% 0.54/0.73  #    Positive orientable unit clauses  : 231
% 0.54/0.73  #    Positive unorientable unit clauses: 6
% 0.54/0.73  #    Negative unit clauses             : 0
% 0.54/0.73  #    Non-unit-clauses                  : 38
% 0.54/0.73  # Current number of unprocessed clauses: 23766
% 0.54/0.73  # ...number of literals in the above   : 25390
% 0.54/0.73  # Current number of archived formulas  : 0
% 0.54/0.73  # Current number of archived clauses   : 123
% 0.54/0.73  # Clause-clause subsumption calls (NU) : 626
% 0.54/0.73  # Rec. Clause-clause subsumption calls : 626
% 0.54/0.73  # Non-unit clause-clause subsumptions  : 232
% 0.54/0.73  # Unit Clause-clause subsumption calls : 54
% 0.54/0.73  # Rewrite failures with RHS unbound    : 0
% 0.54/0.73  # BW rewrite match attempts            : 906
% 0.54/0.73  # BW rewrite match successes           : 220
% 0.54/0.73  # Condensation attempts                : 0
% 0.54/0.73  # Condensation successes               : 0
% 0.54/0.73  # Termbank termtop insertions          : 410699
% 0.54/0.73  
% 0.54/0.73  # -------------------------------------------------
% 0.54/0.73  # User time                : 0.366 s
% 0.54/0.73  # System time              : 0.020 s
% 0.54/0.73  # Total time               : 0.386 s
% 0.54/0.73  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
