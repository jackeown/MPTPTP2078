%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:06 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   78 (9733 expanded)
%              Number of clauses        :   65 (4408 expanded)
%              Number of leaves         :    6 (2662 expanded)
%              Depth                    :   24
%              Number of atoms          :  115 (15714 expanded)
%              Number of equality atoms :   77 (10562 expanded)
%              Maximal formula depth    :   16 (   2 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t42_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_6,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_7,plain,(
    ! [X18,X19] : k4_xboole_0(k2_xboole_0(X18,X19),X19) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_9,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] : k4_xboole_0(k4_xboole_0(X20,X21),X22) = k4_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_9])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_15])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X2,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_18]),c_0_17]),c_0_19]),c_0_17])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X2),X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_9]),c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_25])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_26])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_29])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_9]),c_0_17])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_30]),c_0_31]),c_0_29])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_32])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X1) = k2_xboole_0(k4_xboole_0(X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X3) = k4_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_34]),c_0_17]),c_0_25])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_37]),c_0_9])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_17])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_28])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),X2) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_39])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_17])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X2)),X3) = k2_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X3)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_9]),c_0_9]),c_0_15]),c_0_14])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_19]),c_0_44])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_45]),c_0_9])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_46]),c_0_46])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_47])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_56,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_9]),c_0_15]),c_0_14]),c_0_9])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_40])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2),X3) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_17]),c_0_17])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_40])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_31]),c_0_59])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_15])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2) = k4_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_61])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(X3,X1)),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_62]),c_0_9])).

fof(c_0_68,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_xboole_1])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_47]),c_0_15]),c_0_64])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X2,X3),X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_19]),c_0_36]),c_0_47])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_61]),c_0_19])).

fof(c_0_72,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0) != k2_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_9]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0) != k2_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_47]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:23:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 1.19/1.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 1.19/1.44  # and selection function SelectCQIArNpEqFirst.
% 1.19/1.44  #
% 1.19/1.44  # Preprocessing time       : 0.026 s
% 1.19/1.44  # Presaturation interreduction done
% 1.19/1.44  
% 1.19/1.44  # Proof found!
% 1.19/1.44  # SZS status Theorem
% 1.19/1.44  # SZS output start CNFRefutation
% 1.19/1.44  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.19/1.44  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.19/1.44  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.19/1.44  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.19/1.44  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.19/1.44  fof(t42_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 1.19/1.44  fof(c_0_6, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.19/1.44  fof(c_0_7, plain, ![X18, X19]:k4_xboole_0(k2_xboole_0(X18,X19),X19)=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 1.19/1.44  fof(c_0_8, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.19/1.44  cnf(c_0_9, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.19/1.44  cnf(c_0_10, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.19/1.44  fof(c_0_11, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.19/1.44  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.44  fof(c_0_13, plain, ![X20, X21, X22]:k4_xboole_0(k4_xboole_0(X20,X21),X22)=k4_xboole_0(X20,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.19/1.44  cnf(c_0_14, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_9])).
% 1.19/1.44  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.19/1.44  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_12])).
% 1.19/1.44  cnf(c_0_17, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.19/1.44  cnf(c_0_18, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.19/1.44  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_10, c_0_15])).
% 1.19/1.44  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.44  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 1.19/1.44  cnf(c_0_22, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(k4_xboole_0(X2,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_18]), c_0_17]), c_0_19]), c_0_17])).
% 1.19/1.44  cnf(c_0_23, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_20])).
% 1.19/1.44  cnf(c_0_24, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X2),X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 1.19/1.44  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_9]), c_0_19])).
% 1.19/1.44  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.44  cnf(c_0_27, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_25])).
% 1.19/1.44  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_26])).
% 1.19/1.44  cnf(c_0_29, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.19/1.44  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X2)), inference(rw,[status(thm)],[c_0_22, c_0_29])).
% 1.19/1.44  cnf(c_0_31, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_9]), c_0_17])).
% 1.19/1.44  cnf(c_0_32, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_30]), c_0_31]), c_0_29])).
% 1.19/1.44  cnf(c_0_33, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_9, c_0_32])).
% 1.19/1.44  cnf(c_0_34, plain, (k2_xboole_0(X1,X1)=k2_xboole_0(k4_xboole_0(X2,X2),X1)), inference(spm,[status(thm)],[c_0_15, c_0_33])).
% 1.19/1.44  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X3)=k4_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_34]), c_0_17]), c_0_25])).
% 1.19/1.44  cnf(c_0_36, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_10, c_0_9])).
% 1.19/1.44  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_35])).
% 1.19/1.44  cnf(c_0_38, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.44  cnf(c_0_39, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_37]), c_0_9])).
% 1.19/1.44  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_17])).
% 1.19/1.44  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_28]), c_0_28])).
% 1.19/1.44  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=X1|~r2_hidden(esk1_3(X1,X2,X1),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_23, c_0_28])).
% 1.19/1.44  cnf(c_0_43, plain, (k2_xboole_0(k2_xboole_0(X1,X1),X2)=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_39])).
% 1.19/1.44  cnf(c_0_44, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X1),X2))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_9, c_0_17])).
% 1.19/1.44  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_29])).
% 1.19/1.44  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 1.19/1.44  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 1.19/1.44  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),k4_xboole_0(X2,X1))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X1)),X3)), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 1.19/1.44  cnf(c_0_49, plain, (k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X2)),X3)=k2_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 1.19/1.44  cnf(c_0_50, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X3))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_9]), c_0_9]), c_0_15]), c_0_14])).
% 1.19/1.44  cnf(c_0_51, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_19]), c_0_44])).
% 1.19/1.44  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_45]), c_0_9])).
% 1.19/1.44  cnf(c_0_53, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_46]), c_0_46])).
% 1.19/1.44  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_47])).
% 1.19/1.44  cnf(c_0_55, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),k4_xboole_0(X2,X1))=k4_xboole_0(X1,X3)), inference(rw,[status(thm)],[c_0_48, c_0_47])).
% 1.19/1.44  cnf(c_0_56, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X3,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_9]), c_0_15]), c_0_14]), c_0_9])).
% 1.19/1.44  cnf(c_0_57, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_50]), c_0_51])).
% 1.19/1.44  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 1.19/1.44  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_9, c_0_40])).
% 1.19/1.44  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.19/1.44  cnf(c_0_61, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 1.19/1.44  cnf(c_0_62, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2),X3)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_17]), c_0_17])).
% 1.19/1.44  cnf(c_0_63, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_40])).
% 1.19/1.44  cnf(c_0_64, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_31]), c_0_59])).
% 1.19/1.44  cnf(c_0_65, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X3))=k4_xboole_0(X1,k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_60, c_0_15])).
% 1.19/1.44  cnf(c_0_66, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2)=k4_xboole_0(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_61])).
% 1.19/1.44  cnf(c_0_67, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(X3,X1)),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_62]), c_0_9])).
% 1.19/1.44  fof(c_0_68, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t42_xboole_1])).
% 1.19/1.44  cnf(c_0_69, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_47]), c_0_15]), c_0_64])).
% 1.19/1.44  cnf(c_0_70, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X2,X3),X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_19]), c_0_36]), c_0_47])).
% 1.19/1.44  cnf(c_0_71, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_61]), c_0_19])).
% 1.19/1.44  fof(c_0_72, negated_conjecture, k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0)!=k2_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).
% 1.19/1.44  cnf(c_0_73, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 1.19/1.44  cnf(c_0_74, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_9]), c_0_66])).
% 1.19/1.44  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0)!=k2_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.19/1.44  cnf(c_0_76, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_47]), c_0_74])).
% 1.19/1.44  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 1.19/1.44  # SZS output end CNFRefutation
% 1.19/1.44  # Proof object total steps             : 78
% 1.19/1.44  # Proof object clause steps            : 65
% 1.19/1.44  # Proof object formula steps           : 13
% 1.19/1.44  # Proof object conjectures             : 5
% 1.19/1.44  # Proof object clause conjectures      : 2
% 1.19/1.44  # Proof object formula conjectures     : 3
% 1.19/1.44  # Proof object initial clauses used    : 9
% 1.19/1.44  # Proof object initial formulas used   : 6
% 1.19/1.44  # Proof object generating inferences   : 49
% 1.19/1.44  # Proof object simplifying inferences  : 49
% 1.19/1.44  # Training examples: 0 positive, 0 negative
% 1.19/1.44  # Parsed axioms                        : 6
% 1.19/1.44  # Removed by relevancy pruning/SinE    : 0
% 1.19/1.44  # Initial clauses                      : 11
% 1.19/1.44  # Removed in clause preprocessing      : 0
% 1.19/1.44  # Initial clauses in saturation        : 11
% 1.19/1.44  # Processed clauses                    : 7814
% 1.19/1.44  # ...of these trivial                  : 552
% 1.19/1.44  # ...subsumed                          : 6752
% 1.19/1.44  # ...remaining for further processing  : 510
% 1.19/1.44  # Other redundant clauses eliminated   : 3
% 1.19/1.44  # Clauses deleted for lack of memory   : 0
% 1.19/1.44  # Backward-subsumed                    : 28
% 1.19/1.44  # Backward-rewritten                   : 149
% 1.19/1.44  # Generated clauses                    : 102761
% 1.19/1.44  # ...of the previous two non-trivial   : 84675
% 1.19/1.44  # Contextual simplify-reflections      : 2
% 1.19/1.44  # Paramodulations                      : 102650
% 1.19/1.44  # Factorizations                       : 108
% 1.19/1.44  # Equation resolutions                 : 3
% 1.19/1.44  # Propositional unsat checks           : 0
% 1.19/1.44  #    Propositional check models        : 0
% 1.19/1.44  #    Propositional check unsatisfiable : 0
% 1.19/1.44  #    Propositional clauses             : 0
% 1.19/1.44  #    Propositional clauses after purity: 0
% 1.19/1.44  #    Propositional unsat core size     : 0
% 1.19/1.44  #    Propositional preprocessing time  : 0.000
% 1.19/1.44  #    Propositional encoding time       : 0.000
% 1.19/1.44  #    Propositional solver time         : 0.000
% 1.19/1.44  #    Success case prop preproc time    : 0.000
% 1.19/1.44  #    Success case prop encoding time   : 0.000
% 1.19/1.44  #    Success case prop solver time     : 0.000
% 1.19/1.44  # Current number of processed clauses  : 319
% 1.19/1.44  #    Positive orientable unit clauses  : 104
% 1.19/1.44  #    Positive unorientable unit clauses: 8
% 1.19/1.44  #    Negative unit clauses             : 1
% 1.19/1.44  #    Non-unit-clauses                  : 206
% 1.19/1.44  # Current number of unprocessed clauses: 74687
% 1.19/1.44  # ...number of literals in the above   : 184328
% 1.19/1.44  # Current number of archived formulas  : 0
% 1.19/1.44  # Current number of archived clauses   : 188
% 1.19/1.44  # Clause-clause subsumption calls (NU) : 33542
% 1.19/1.44  # Rec. Clause-clause subsumption calls : 25489
% 1.19/1.44  # Non-unit clause-clause subsumptions  : 2880
% 1.19/1.44  # Unit Clause-clause subsumption calls : 2486
% 1.19/1.44  # Rewrite failures with RHS unbound    : 743
% 1.19/1.44  # BW rewrite match attempts            : 1540
% 1.19/1.44  # BW rewrite match successes           : 345
% 1.19/1.44  # Condensation attempts                : 0
% 1.19/1.44  # Condensation successes               : 0
% 1.19/1.44  # Termbank termtop insertions          : 1432929
% 1.19/1.45  
% 1.19/1.45  # -------------------------------------------------
% 1.19/1.45  # User time                : 1.020 s
% 1.19/1.45  # System time              : 0.058 s
% 1.19/1.45  # Total time               : 1.078 s
% 1.19/1.45  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
