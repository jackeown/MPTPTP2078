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
% DateTime   : Thu Dec  3 10:33:15 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   93 (2497 expanded)
%              Number of clauses        :   72 (1193 expanded)
%              Number of leaves         :   10 ( 626 expanded)
%              Depth                    :   22
%              Number of atoms          :  158 (4545 expanded)
%              Number of equality atoms :   64 (1852 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t74_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(c_0_10,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_17,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_18,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_20,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_xboole_1])).

fof(c_0_22,plain,(
    ! [X22,X23] : k2_xboole_0(X22,k3_xboole_0(X22,X23)) = X22 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0))
    & r1_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_31,plain,(
    ! [X28,X29] : k2_xboole_0(k3_xboole_0(X28,X29),k4_xboole_0(X28,X29)) = X28 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_14])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_19])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

fof(c_0_45,plain,(
    ! [X19,X20,X21] : k3_xboole_0(k3_xboole_0(X19,X20),X21) = k3_xboole_0(X19,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_38,c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_42])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_32])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_14]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_52])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = X1
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_48])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_55])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_56]),c_0_52]),c_0_56])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_42])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_56]),c_0_52]),c_0_56]),c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(X1,X2) = X1
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_64]),c_0_52])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_26])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(X1,X2) = X1
    | k4_xboole_0(X1,X3) != k1_xboole_0
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_34])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))))
    | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4))))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_55])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(X1,esk3_0) = X1
    | k4_xboole_0(X1,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_42])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4))))
    | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_56])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_34])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_56]),c_0_78])])).

cnf(c_0_81,plain,
    ( r2_hidden(esk2_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_32])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_55]),c_0_55])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_63])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_82]),c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_56]),c_0_52])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_59]),c_0_32])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_88,c_0_14])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_89]),c_0_56])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.71/0.89  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.71/0.89  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.71/0.89  #
% 0.71/0.89  # Preprocessing time       : 0.027 s
% 0.71/0.89  # Presaturation interreduction done
% 0.71/0.89  
% 0.71/0.89  # Proof found!
% 0.71/0.89  # SZS status Theorem
% 0.71/0.89  # SZS output start CNFRefutation
% 0.71/0.89  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.71/0.89  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.71/0.89  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.71/0.89  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.71/0.89  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.71/0.89  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.71/0.89  fof(t74_xboole_1, conjecture, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 0.71/0.89  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.71/0.89  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.71/0.89  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.71/0.89  fof(c_0_10, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.71/0.89  fof(c_0_11, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.71/0.89  fof(c_0_12, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.71/0.89  cnf(c_0_13, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.71/0.89  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.71/0.89  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.71/0.89  fof(c_0_16, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.71/0.89  fof(c_0_17, plain, ![X24, X25]:k4_xboole_0(X24,k3_xboole_0(X24,X25))=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.71/0.89  cnf(c_0_18, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.71/0.89  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.71/0.89  fof(c_0_20, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.71/0.89  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t74_xboole_1])).
% 0.71/0.89  fof(c_0_22, plain, ![X22, X23]:k2_xboole_0(X22,k3_xboole_0(X22,X23))=X22, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.71/0.89  cnf(c_0_23, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.71/0.89  cnf(c_0_24, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.89  cnf(c_0_25, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.71/0.89  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.71/0.89  fof(c_0_27, negated_conjecture, (~r1_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0))&r1_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.71/0.89  cnf(c_0_28, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.89  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_23, c_0_14])).
% 0.71/0.89  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.71/0.89  fof(c_0_31, plain, ![X28, X29]:k2_xboole_0(k3_xboole_0(X28,X29),k4_xboole_0(X28,X29))=X28, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.71/0.89  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_14])).
% 0.71/0.89  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.71/0.89  cnf(c_0_34, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.71/0.89  cnf(c_0_35, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_28, c_0_14])).
% 0.71/0.89  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_18, c_0_29])).
% 0.71/0.89  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_14])).
% 0.71/0.89  cnf(c_0_38, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.71/0.89  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 0.71/0.89  cnf(c_0_40, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.71/0.89  cnf(c_0_41, plain, (k2_xboole_0(X1,k1_xboole_0)=X1|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_19])).
% 0.71/0.89  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.71/0.89  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.71/0.89  cnf(c_0_44, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_29])).
% 0.71/0.89  fof(c_0_45, plain, ![X19, X20, X21]:k3_xboole_0(k3_xboole_0(X19,X20),X21)=k3_xboole_0(X19,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.71/0.89  cnf(c_0_46, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_38, c_0_14])).
% 0.71/0.89  cnf(c_0_47, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.71/0.89  cnf(c_0_48, negated_conjecture, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.71/0.89  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_36, c_0_42])).
% 0.71/0.89  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.71/0.89  cnf(c_0_51, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.71/0.89  cnf(c_0_52, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.71/0.89  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_32])).
% 0.71/0.89  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.71/0.89  cnf(c_0_55, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_14]), c_0_14]), c_0_14]), c_0_14])).
% 0.71/0.89  cnf(c_0_56, negated_conjecture, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_52])).
% 0.71/0.89  cnf(c_0_57, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.71/0.89  cnf(c_0_58, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.71/0.89  cnf(c_0_59, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_52])).
% 0.71/0.89  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=X1|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_48])).
% 0.71/0.89  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.71/0.89  cnf(c_0_62, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_32, c_0_55])).
% 0.71/0.89  cnf(c_0_63, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_52])).
% 0.71/0.89  cnf(c_0_64, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_56]), c_0_52]), c_0_56])).
% 0.71/0.89  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_61, c_0_42])).
% 0.71/0.89  cnf(c_0_66, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_56]), c_0_52]), c_0_56]), c_0_52])).
% 0.71/0.89  cnf(c_0_67, negated_conjecture, (k4_xboole_0(X1,X2)=X1|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_64]), c_0_52])).
% 0.71/0.89  cnf(c_0_68, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_65, c_0_26])).
% 0.71/0.89  cnf(c_0_69, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_32])).
% 0.71/0.89  cnf(c_0_70, negated_conjecture, (k4_xboole_0(X1,X2)=X1|k4_xboole_0(X1,X3)!=k1_xboole_0|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.71/0.89  cnf(c_0_71, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_34])).
% 0.71/0.89  cnf(c_0_72, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))))|~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))))), inference(spm,[status(thm)],[c_0_69, c_0_55])).
% 0.71/0.89  cnf(c_0_73, negated_conjecture, (k4_xboole_0(X1,esk3_0)=X1|k4_xboole_0(X1,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.71/0.89  cnf(c_0_74, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_25, c_0_42])).
% 0.71/0.89  cnf(c_0_75, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.71/0.89  cnf(c_0_76, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4))))|~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4))))), inference(spm,[status(thm)],[c_0_72, c_0_32])).
% 0.71/0.89  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_73, c_0_56])).
% 0.71/0.89  cnf(c_0_78, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_34])).
% 0.71/0.89  cnf(c_0_79, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_75, c_0_14])).
% 0.71/0.89  cnf(c_0_80, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_56]), c_0_78])])).
% 0.71/0.89  cnf(c_0_81, plain, (r2_hidden(esk2_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_79, c_0_32])).
% 0.71/0.89  cnf(c_0_82, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_55]), c_0_55])).
% 0.71/0.89  cnf(c_0_83, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_32, c_0_63])).
% 0.71/0.89  cnf(c_0_84, negated_conjecture, (r1_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1))))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.71/0.89  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_82]), c_0_32])).
% 0.71/0.89  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1))=esk4_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.71/0.89  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_56]), c_0_52])).
% 0.71/0.89  cnf(c_0_88, negated_conjecture, (~r1_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.71/0.89  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_59]), c_0_32])).
% 0.71/0.89  cnf(c_0_90, negated_conjecture, (~r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_88, c_0_14])).
% 0.71/0.89  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_89]), c_0_56])])).
% 0.71/0.89  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])]), ['proof']).
% 0.71/0.89  # SZS output end CNFRefutation
% 0.71/0.89  # Proof object total steps             : 93
% 0.71/0.89  # Proof object clause steps            : 72
% 0.71/0.89  # Proof object formula steps           : 21
% 0.71/0.89  # Proof object conjectures             : 26
% 0.71/0.89  # Proof object clause conjectures      : 23
% 0.71/0.89  # Proof object formula conjectures     : 3
% 0.71/0.89  # Proof object initial clauses used    : 15
% 0.71/0.89  # Proof object initial formulas used   : 10
% 0.71/0.89  # Proof object generating inferences   : 45
% 0.71/0.89  # Proof object simplifying inferences  : 38
% 0.71/0.89  # Training examples: 0 positive, 0 negative
% 0.71/0.89  # Parsed axioms                        : 10
% 0.71/0.89  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.89  # Initial clauses                      : 15
% 0.71/0.89  # Removed in clause preprocessing      : 1
% 0.71/0.89  # Initial clauses in saturation        : 14
% 0.71/0.89  # Processed clauses                    : 4440
% 0.71/0.89  # ...of these trivial                  : 29
% 0.71/0.89  # ...subsumed                          : 4026
% 0.71/0.89  # ...remaining for further processing  : 385
% 0.71/0.89  # Other redundant clauses eliminated   : 0
% 0.71/0.89  # Clauses deleted for lack of memory   : 0
% 0.71/0.89  # Backward-subsumed                    : 26
% 0.71/0.89  # Backward-rewritten                   : 73
% 0.71/0.89  # Generated clauses                    : 57556
% 0.71/0.89  # ...of the previous two non-trivial   : 45287
% 0.71/0.89  # Contextual simplify-reflections      : 4
% 0.71/0.89  # Paramodulations                      : 57556
% 0.71/0.89  # Factorizations                       : 0
% 0.71/0.89  # Equation resolutions                 : 0
% 0.71/0.89  # Propositional unsat checks           : 0
% 0.71/0.89  #    Propositional check models        : 0
% 0.71/0.89  #    Propositional check unsatisfiable : 0
% 0.71/0.89  #    Propositional clauses             : 0
% 0.71/0.89  #    Propositional clauses after purity: 0
% 0.71/0.89  #    Propositional unsat core size     : 0
% 0.71/0.89  #    Propositional preprocessing time  : 0.000
% 0.71/0.89  #    Propositional encoding time       : 0.000
% 0.71/0.89  #    Propositional solver time         : 0.000
% 0.71/0.89  #    Success case prop preproc time    : 0.000
% 0.71/0.89  #    Success case prop encoding time   : 0.000
% 0.71/0.89  #    Success case prop solver time     : 0.000
% 0.71/0.89  # Current number of processed clauses  : 272
% 0.71/0.89  #    Positive orientable unit clauses  : 49
% 0.71/0.89  #    Positive unorientable unit clauses: 0
% 0.71/0.89  #    Negative unit clauses             : 12
% 0.71/0.89  #    Non-unit-clauses                  : 211
% 0.71/0.89  # Current number of unprocessed clauses: 39469
% 0.71/0.89  # ...number of literals in the above   : 102608
% 0.71/0.89  # Current number of archived formulas  : 0
% 0.71/0.89  # Current number of archived clauses   : 114
% 0.71/0.89  # Clause-clause subsumption calls (NU) : 25375
% 0.71/0.89  # Rec. Clause-clause subsumption calls : 23540
% 0.71/0.89  # Non-unit clause-clause subsumptions  : 2978
% 0.71/0.89  # Unit Clause-clause subsumption calls : 126
% 0.71/0.89  # Rewrite failures with RHS unbound    : 0
% 0.71/0.89  # BW rewrite match attempts            : 589
% 0.71/0.89  # BW rewrite match successes           : 35
% 0.71/0.89  # Condensation attempts                : 0
% 0.71/0.89  # Condensation successes               : 0
% 0.71/0.89  # Termbank termtop insertions          : 1201854
% 0.71/0.89  
% 0.71/0.89  # -------------------------------------------------
% 0.71/0.89  # User time                : 0.518 s
% 0.71/0.89  # System time              : 0.022 s
% 0.71/0.89  # Total time               : 0.540 s
% 0.71/0.89  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
