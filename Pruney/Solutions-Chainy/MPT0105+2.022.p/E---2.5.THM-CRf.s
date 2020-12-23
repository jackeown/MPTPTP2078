%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:11 EST 2020

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 312 expanded)
%              Number of clauses        :   40 ( 137 expanded)
%              Number of leaves         :   15 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :   76 ( 322 expanded)
%              Number of equality atoms :   67 ( 305 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_15,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X17,X18)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_16,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_17,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X28,X29] :
      ( ( ~ r1_xboole_0(X28,X29)
        | k4_xboole_0(X28,X29) = X28 )
      & ( k4_xboole_0(X28,X29) != X28
        | r1_xboole_0(X28,X29) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X23,X24] : k2_xboole_0(k3_xboole_0(X23,X24),k4_xboole_0(X23,X24)) = X23 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_24,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_25,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k3_xboole_0(X19,X20)) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_26,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X7,X8),k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_27,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_34,plain,(
    ! [X33,X34] : k2_xboole_0(X33,X34) = k5_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_31])).

fof(c_0_43,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_18]),c_0_37])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_31]),c_0_42]),c_0_42])).

fof(c_0_47,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_48,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X13) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_36])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_22]),c_0_19])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_36]),c_0_19]),c_0_36]),c_0_40])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_36]),c_0_40])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_42]),c_0_42])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_50]),c_0_51])).

fof(c_0_59,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_56]),c_0_40])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))),X1) = k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,X3)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_50]),c_0_55]),c_0_39])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X1) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_54]),c_0_61]),c_0_55]),c_0_55]),c_0_61])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_51]),c_0_61]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_42])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_40])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_67]),c_0_36]),c_0_19]),c_0_22]),c_0_55]),c_0_40])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:52:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.58/0.75  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.58/0.75  # and selection function SelectNewComplexAHP.
% 0.58/0.75  #
% 0.58/0.75  # Preprocessing time       : 0.028 s
% 0.58/0.75  # Presaturation interreduction done
% 0.58/0.75  
% 0.58/0.75  # Proof found!
% 0.58/0.75  # SZS status Theorem
% 0.58/0.75  # SZS output start CNFRefutation
% 0.58/0.75  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.58/0.75  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.58/0.75  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.58/0.75  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.58/0.75  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.58/0.75  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.58/0.75  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.58/0.75  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.58/0.75  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.58/0.75  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.58/0.75  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.58/0.75  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.58/0.75  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.58/0.75  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.58/0.75  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.58/0.75  fof(c_0_15, plain, ![X17, X18]:k4_xboole_0(X17,k2_xboole_0(X17,X18))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.58/0.75  fof(c_0_16, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.58/0.75  fof(c_0_17, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.58/0.75  cnf(c_0_18, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.58/0.75  cnf(c_0_19, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.58/0.75  fof(c_0_20, plain, ![X28, X29]:((~r1_xboole_0(X28,X29)|k4_xboole_0(X28,X29)=X28)&(k4_xboole_0(X28,X29)!=X28|r1_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.58/0.75  cnf(c_0_21, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.58/0.75  cnf(c_0_22, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.58/0.75  fof(c_0_23, plain, ![X23, X24]:k2_xboole_0(k3_xboole_0(X23,X24),k4_xboole_0(X23,X24))=X23, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.58/0.75  fof(c_0_24, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.58/0.75  fof(c_0_25, plain, ![X19, X20]:k4_xboole_0(X19,k3_xboole_0(X19,X20))=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.58/0.75  fof(c_0_26, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k4_xboole_0(k2_xboole_0(X7,X8),k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.58/0.75  fof(c_0_27, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.58/0.75  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.58/0.75  cnf(c_0_29, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.58/0.75  cnf(c_0_30, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.58/0.75  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.58/0.75  cnf(c_0_32, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.58/0.75  fof(c_0_33, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.58/0.75  fof(c_0_34, plain, ![X33, X34]:k2_xboole_0(X33,X34)=k5_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.58/0.75  cnf(c_0_35, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.58/0.75  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.58/0.75  cnf(c_0_37, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.58/0.75  cnf(c_0_38, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.58/0.75  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_31])).
% 0.58/0.75  cnf(c_0_40, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.58/0.75  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.58/0.75  cnf(c_0_42, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_35, c_0_31])).
% 0.58/0.75  fof(c_0_43, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.58/0.75  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_18]), c_0_37])).
% 0.58/0.75  cnf(c_0_45, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.58/0.75  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_31]), c_0_42]), c_0_42])).
% 0.58/0.75  fof(c_0_47, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.58/0.75  fof(c_0_48, plain, ![X12, X13]:k4_xboole_0(k2_xboole_0(X12,X13),X13)=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.58/0.75  cnf(c_0_49, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.58/0.75  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_36])).
% 0.58/0.75  cnf(c_0_51, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_22]), c_0_19])).
% 0.58/0.75  fof(c_0_52, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 0.58/0.75  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_36]), c_0_19]), c_0_36]), c_0_40])).
% 0.58/0.75  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_36]), c_0_40])).
% 0.58/0.75  cnf(c_0_55, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.58/0.75  cnf(c_0_56, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.58/0.75  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_42]), c_0_42])).
% 0.58/0.75  cnf(c_0_58, plain, (k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_50]), c_0_51])).
% 0.58/0.75  fof(c_0_59, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 0.58/0.75  cnf(c_0_60, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.58/0.75  cnf(c_0_61, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_56]), c_0_40])).
% 0.58/0.75  cnf(c_0_62, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))),X1)=k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,X3)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_50]), c_0_55]), c_0_39])).
% 0.58/0.75  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.58/0.75  cnf(c_0_64, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X1)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_54]), c_0_61]), c_0_55]), c_0_55]), c_0_61])).
% 0.58/0.75  cnf(c_0_65, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_51]), c_0_61]), c_0_56])).
% 0.58/0.75  cnf(c_0_66, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[c_0_63, c_0_42])).
% 0.58/0.75  cnf(c_0_67, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.58/0.75  cnf(c_0_68, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_66, c_0_40])).
% 0.58/0.75  cnf(c_0_69, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_67]), c_0_36]), c_0_19]), c_0_22]), c_0_55]), c_0_40])).
% 0.58/0.75  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])]), ['proof']).
% 0.58/0.75  # SZS output end CNFRefutation
% 0.58/0.75  # Proof object total steps             : 71
% 0.58/0.75  # Proof object clause steps            : 40
% 0.58/0.75  # Proof object formula steps           : 31
% 0.58/0.75  # Proof object conjectures             : 7
% 0.58/0.75  # Proof object clause conjectures      : 4
% 0.58/0.75  # Proof object formula conjectures     : 3
% 0.58/0.75  # Proof object initial clauses used    : 15
% 0.58/0.75  # Proof object initial formulas used   : 15
% 0.58/0.75  # Proof object generating inferences   : 14
% 0.58/0.75  # Proof object simplifying inferences  : 40
% 0.58/0.75  # Training examples: 0 positive, 0 negative
% 0.58/0.75  # Parsed axioms                        : 17
% 0.58/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.58/0.75  # Initial clauses                      : 18
% 0.58/0.75  # Removed in clause preprocessing      : 2
% 0.58/0.75  # Initial clauses in saturation        : 16
% 0.58/0.75  # Processed clauses                    : 809
% 0.58/0.75  # ...of these trivial                  : 336
% 0.58/0.75  # ...subsumed                          : 148
% 0.58/0.75  # ...remaining for further processing  : 325
% 0.58/0.75  # Other redundant clauses eliminated   : 0
% 0.58/0.75  # Clauses deleted for lack of memory   : 0
% 0.58/0.75  # Backward-subsumed                    : 2
% 0.58/0.75  # Backward-rewritten                   : 84
% 0.58/0.75  # Generated clauses                    : 53323
% 0.58/0.75  # ...of the previous two non-trivial   : 22302
% 0.58/0.75  # Contextual simplify-reflections      : 0
% 0.58/0.75  # Paramodulations                      : 53313
% 0.58/0.75  # Factorizations                       : 0
% 0.58/0.75  # Equation resolutions                 : 10
% 0.58/0.75  # Propositional unsat checks           : 0
% 0.58/0.75  #    Propositional check models        : 0
% 0.58/0.75  #    Propositional check unsatisfiable : 0
% 0.58/0.75  #    Propositional clauses             : 0
% 0.58/0.75  #    Propositional clauses after purity: 0
% 0.58/0.75  #    Propositional unsat core size     : 0
% 0.58/0.75  #    Propositional preprocessing time  : 0.000
% 0.58/0.75  #    Propositional encoding time       : 0.000
% 0.58/0.75  #    Propositional solver time         : 0.000
% 0.58/0.75  #    Success case prop preproc time    : 0.000
% 0.58/0.75  #    Success case prop encoding time   : 0.000
% 0.58/0.75  #    Success case prop solver time     : 0.000
% 0.58/0.75  # Current number of processed clauses  : 223
% 0.58/0.75  #    Positive orientable unit clauses  : 203
% 0.58/0.75  #    Positive unorientable unit clauses: 1
% 0.58/0.75  #    Negative unit clauses             : 0
% 0.58/0.75  #    Non-unit-clauses                  : 19
% 0.58/0.75  # Current number of unprocessed clauses: 21059
% 0.58/0.75  # ...number of literals in the above   : 21691
% 0.58/0.75  # Current number of archived formulas  : 0
% 0.58/0.75  # Current number of archived clauses   : 104
% 0.58/0.75  # Clause-clause subsumption calls (NU) : 365
% 0.58/0.75  # Rec. Clause-clause subsumption calls : 365
% 0.58/0.75  # Non-unit clause-clause subsumptions  : 150
% 0.58/0.75  # Unit Clause-clause subsumption calls : 9
% 0.58/0.75  # Rewrite failures with RHS unbound    : 0
% 0.58/0.75  # BW rewrite match attempts            : 1088
% 0.58/0.75  # BW rewrite match successes           : 70
% 0.58/0.75  # Condensation attempts                : 0
% 0.58/0.75  # Condensation successes               : 0
% 0.58/0.75  # Termbank termtop insertions          : 578185
% 0.58/0.75  
% 0.58/0.75  # -------------------------------------------------
% 0.58/0.75  # User time                : 0.398 s
% 0.58/0.75  # System time              : 0.020 s
% 0.58/0.75  # Total time               : 0.418 s
% 0.58/0.75  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
