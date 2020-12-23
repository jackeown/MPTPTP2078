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
% DateTime   : Thu Dec  3 10:33:22 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 446 expanded)
%              Number of clauses        :   51 ( 206 expanded)
%              Number of leaves         :   10 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :   98 ( 514 expanded)
%              Number of equality atoms :   53 ( 418 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t76_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_10,plain,(
    ! [X8] : k3_xboole_0(X8,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_11,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X9] : k4_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_16,plain,(
    ! [X17,X18,X19] : k4_xboole_0(X17,k4_xboole_0(X18,X19)) = k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_17,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_18,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k4_xboole_0(X15,X16)) = k4_xboole_0(k3_xboole_0(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,X2)
       => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t76_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_14]),c_0_14])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    & ~ r1_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_26]),c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_42]),c_0_21])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_43])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_31]),c_0_31]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_44]),c_0_45])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_14])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1))) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_49])).

fof(c_0_53,plain,(
    ! [X20,X21,X22] :
      ( ( r1_xboole_0(X20,k2_xboole_0(X21,X22))
        | ~ r1_xboole_0(X20,X21)
        | ~ r1_xboole_0(X20,X22) )
      & ( r1_xboole_0(X20,X21)
        | ~ r1_xboole_0(X20,k2_xboole_0(X21,X22)) )
      & ( r1_xboole_0(X20,X22)
        | ~ r1_xboole_0(X20,k2_xboole_0(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_26]),c_0_21]),c_0_26])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk1_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_55]),c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(X1,esk2_0))
    | ~ r1_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_39])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_26])])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),esk2_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_67,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))),X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_31])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),esk2_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_65]),c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_14]),c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0)),k4_xboole_0(X2,k4_xboole_0(X2,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.46/1.62  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 1.46/1.62  # and selection function SelectNewComplexAHP.
% 1.46/1.62  #
% 1.46/1.62  # Preprocessing time       : 0.027 s
% 1.46/1.62  # Presaturation interreduction done
% 1.46/1.62  
% 1.46/1.62  # Proof found!
% 1.46/1.62  # SZS status Theorem
% 1.46/1.62  # SZS output start CNFRefutation
% 1.46/1.62  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.46/1.62  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.46/1.62  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.46/1.62  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.46/1.62  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.46/1.62  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.46/1.62  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.46/1.62  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.46/1.62  fof(t76_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 1.46/1.62  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.46/1.62  fof(c_0_10, plain, ![X8]:k3_xboole_0(X8,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.46/1.62  fof(c_0_11, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.46/1.62  fof(c_0_12, plain, ![X6, X7]:k2_xboole_0(X6,k3_xboole_0(X6,X7))=X6, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 1.46/1.62  cnf(c_0_13, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.46/1.62  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.46/1.62  fof(c_0_15, plain, ![X9]:k4_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.46/1.62  fof(c_0_16, plain, ![X17, X18, X19]:k4_xboole_0(X17,k4_xboole_0(X18,X19))=k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.46/1.62  fof(c_0_17, plain, ![X10, X11]:k4_xboole_0(X10,k3_xboole_0(X10,X11))=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 1.46/1.62  fof(c_0_18, plain, ![X14, X15, X16]:k3_xboole_0(X14,k4_xboole_0(X15,X16))=k4_xboole_0(k3_xboole_0(X14,X15),X16), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 1.46/1.62  cnf(c_0_19, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.46/1.62  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 1.46/1.62  cnf(c_0_21, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.46/1.62  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.46/1.62  cnf(c_0_23, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.46/1.62  cnf(c_0_24, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.46/1.62  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 1.46/1.62  cnf(c_0_26, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 1.46/1.62  fof(c_0_27, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 1.46/1.62  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)))), inference(assume_negation,[status(cth)],[t76_xboole_1])).
% 1.46/1.62  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_22, c_0_14])).
% 1.46/1.62  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_14])).
% 1.46/1.62  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_14]), c_0_14])).
% 1.46/1.62  cnf(c_0_32, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_21])).
% 1.46/1.62  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.46/1.62  fof(c_0_34, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)&~r1_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 1.46/1.62  cnf(c_0_35, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.46/1.62  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 1.46/1.62  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 1.46/1.62  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_14])).
% 1.46/1.62  cnf(c_0_39, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.46/1.62  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_29, c_0_35])).
% 1.46/1.62  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_30])).
% 1.46/1.62  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.46/1.62  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_26]), c_0_21])).
% 1.46/1.62  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_42]), c_0_21])).
% 1.46/1.62  cnf(c_0_45, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_25, c_0_30])).
% 1.46/1.62  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.46/1.62  cnf(c_0_47, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_43])).
% 1.46/1.62  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_31]), c_0_31]), c_0_31])).
% 1.46/1.62  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_44]), c_0_45])).
% 1.46/1.62  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_14])).
% 1.46/1.62  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_47])).
% 1.46/1.62  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1)))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_49])).
% 1.46/1.62  fof(c_0_53, plain, ![X20, X21, X22]:((r1_xboole_0(X20,k2_xboole_0(X21,X22))|~r1_xboole_0(X20,X21)|~r1_xboole_0(X20,X22))&((r1_xboole_0(X20,X21)|~r1_xboole_0(X20,k2_xboole_0(X21,X22)))&(r1_xboole_0(X20,X22)|~r1_xboole_0(X20,k2_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 1.46/1.62  cnf(c_0_54, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.46/1.62  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_26]), c_0_21]), c_0_26])).
% 1.46/1.62  cnf(c_0_56, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.46/1.62  cnf(c_0_57, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))), inference(spm,[status(thm)],[c_0_54, c_0_31])).
% 1.46/1.62  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk2_0,esk1_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_55]), c_0_21])).
% 1.46/1.62  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(X1,esk2_0))|~r1_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_39])).
% 1.46/1.62  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.46/1.62  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.46/1.62  cnf(c_0_62, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_26])])).
% 1.46/1.62  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.46/1.62  cnf(c_0_64, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.46/1.62  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),esk2_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_63])).
% 1.46/1.62  cnf(c_0_66, negated_conjecture, (~r1_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.46/1.62  cnf(c_0_67, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))),X3)), inference(spm,[status(thm)],[c_0_64, c_0_31])).
% 1.46/1.62  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),esk2_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_65]), c_0_21])).
% 1.46/1.62  cnf(c_0_69, negated_conjecture, (~r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_14]), c_0_14])).
% 1.46/1.62  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0)),k4_xboole_0(X2,k4_xboole_0(X2,esk2_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.46/1.62  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])]), ['proof']).
% 1.46/1.62  # SZS output end CNFRefutation
% 1.46/1.62  # Proof object total steps             : 72
% 1.46/1.62  # Proof object clause steps            : 51
% 1.46/1.62  # Proof object formula steps           : 21
% 1.46/1.62  # Proof object conjectures             : 19
% 1.46/1.62  # Proof object clause conjectures      : 16
% 1.46/1.62  # Proof object formula conjectures     : 3
% 1.46/1.62  # Proof object initial clauses used    : 13
% 1.46/1.62  # Proof object initial formulas used   : 10
% 1.46/1.62  # Proof object generating inferences   : 27
% 1.46/1.62  # Proof object simplifying inferences  : 30
% 1.46/1.62  # Training examples: 0 positive, 0 negative
% 1.46/1.62  # Parsed axioms                        : 10
% 1.46/1.62  # Removed by relevancy pruning/SinE    : 0
% 1.46/1.62  # Initial clauses                      : 14
% 1.46/1.62  # Removed in clause preprocessing      : 1
% 1.46/1.62  # Initial clauses in saturation        : 13
% 1.46/1.62  # Processed clauses                    : 4216
% 1.46/1.62  # ...of these trivial                  : 1152
% 1.46/1.62  # ...subsumed                          : 1548
% 1.46/1.62  # ...remaining for further processing  : 1516
% 1.46/1.62  # Other redundant clauses eliminated   : 0
% 1.46/1.62  # Clauses deleted for lack of memory   : 0
% 1.46/1.62  # Backward-subsumed                    : 5
% 1.46/1.62  # Backward-rewritten                   : 213
% 1.46/1.62  # Generated clauses                    : 273578
% 1.46/1.62  # ...of the previous two non-trivial   : 90209
% 1.46/1.62  # Contextual simplify-reflections      : 0
% 1.46/1.62  # Paramodulations                      : 273569
% 1.46/1.63  # Factorizations                       : 0
% 1.46/1.63  # Equation resolutions                 : 9
% 1.46/1.63  # Propositional unsat checks           : 0
% 1.46/1.63  #    Propositional check models        : 0
% 1.46/1.63  #    Propositional check unsatisfiable : 0
% 1.46/1.63  #    Propositional clauses             : 0
% 1.46/1.63  #    Propositional clauses after purity: 0
% 1.46/1.63  #    Propositional unsat core size     : 0
% 1.46/1.63  #    Propositional preprocessing time  : 0.000
% 1.46/1.63  #    Propositional encoding time       : 0.000
% 1.46/1.63  #    Propositional solver time         : 0.000
% 1.46/1.63  #    Success case prop preproc time    : 0.000
% 1.46/1.63  #    Success case prop encoding time   : 0.000
% 1.46/1.63  #    Success case prop solver time     : 0.000
% 1.46/1.63  # Current number of processed clauses  : 1285
% 1.46/1.63  #    Positive orientable unit clauses  : 1220
% 1.46/1.63  #    Positive unorientable unit clauses: 0
% 1.46/1.63  #    Negative unit clauses             : 0
% 1.46/1.63  #    Non-unit-clauses                  : 65
% 1.46/1.63  # Current number of unprocessed clauses: 85270
% 1.46/1.63  # ...number of literals in the above   : 91398
% 1.46/1.63  # Current number of archived formulas  : 0
% 1.46/1.63  # Current number of archived clauses   : 232
% 1.46/1.63  # Clause-clause subsumption calls (NU) : 3695
% 1.46/1.63  # Rec. Clause-clause subsumption calls : 3695
% 1.46/1.63  # Non-unit clause-clause subsumptions  : 1553
% 1.46/1.63  # Unit Clause-clause subsumption calls : 1226
% 1.46/1.63  # Rewrite failures with RHS unbound    : 0
% 1.46/1.63  # BW rewrite match attempts            : 9147
% 1.46/1.63  # BW rewrite match successes           : 208
% 1.46/1.63  # Condensation attempts                : 0
% 1.46/1.63  # Condensation successes               : 0
% 1.46/1.63  # Termbank termtop insertions          : 3097239
% 1.46/1.63  
% 1.46/1.63  # -------------------------------------------------
% 1.46/1.63  # User time                : 1.221 s
% 1.46/1.63  # System time              : 0.058 s
% 1.46/1.63  # Total time               : 1.279 s
% 1.46/1.63  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
