%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:54 EST 2020

% Result     : Theorem 51.21s
% Output     : CNFRefutation 51.21s
% Verified   : 
% Statistics : Number of formulae       :  152 (127952 expanded)
%              Number of clauses        :  145 (72697 expanded)
%              Number of leaves         :    3 (27627 expanded)
%              Depth                    :   25
%              Number of atoms          :  283 (842453 expanded)
%              Number of equality atoms :  154 (256549 expanded)
%              Maximal formula depth    :   17 (   2 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t23_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(c_0_3,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_4,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_6,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_7])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,X3),X2)
    | ~ r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_7])).

cnf(c_0_23,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_20]),c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X2)
    | r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_26,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | ~ r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4))) = k3_xboole_0(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_19])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),k2_xboole_0(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2))) = k3_xboole_0(X3,k3_xboole_0(X4,X2))
    | ~ r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)),k3_xboole_0(X3,k3_xboole_0(X4,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_35,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(X3,X2)
    | ~ r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2),k3_xboole_0(X3,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4)) = k3_xboole_0(k3_xboole_0(X2,X3),X4)
    | r2_hidden(esk2_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4)) = k3_xboole_0(k3_xboole_0(X2,X3),X4)
    | r2_hidden(esk2_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_22])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k3_xboole_0(X3,X2)) = k3_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4))) = k3_xboole_0(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)
    | r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_7])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2))) = k3_xboole_0(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_45,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X3),X2)) = k3_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X1),X2)) = k3_xboole_0(k3_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_39])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_49,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_50,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X2),X3)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_36])).

cnf(c_0_53,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_42])).

cnf(c_0_54,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | r2_hidden(esk2_3(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_43])).

cnf(c_0_55,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(X1,k3_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_44]),c_0_39]),c_0_45])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39]),c_0_48])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_13])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X1) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_61,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_55]),c_0_55])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X3)) = k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k3_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X3) = X3
    | r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_59])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk1_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_51])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_42])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(X1,X3)
    | r2_hidden(esk2_3(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3),k2_xboole_0(X1,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_62]),c_0_62]),c_0_52]),c_0_63])).

cnf(c_0_72,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_53,c_0_7])).

cnf(c_0_74,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X2),X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_61]),c_0_61])).

cnf(c_0_76,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4,X4),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_64])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_67]),c_0_67])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_39])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_61])).

cnf(c_0_82,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_22])).

cnf(c_0_83,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_84,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X3),X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,X1)) = k2_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_54])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_75])).

cnf(c_0_87,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_75])).

cnf(c_0_88,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2)) = k2_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_81])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_90,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_91,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_73])).

cnf(c_0_92,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_93,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_18,c_0_7])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_95,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X3,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_69]),c_0_39])).

cnf(c_0_97,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2))) = k3_xboole_0(X3,k3_xboole_0(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_23])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,X3)),X4),X5)) = X1 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_62]),c_0_71])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k3_xboole_0(X3,X1)) = k3_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_75])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_73])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_93])).

cnf(c_0_103,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_75]),c_0_39]),c_0_96]),c_0_75])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,k2_xboole_0(k2_xboole_0(k2_xboole_0(X3,k2_xboole_0(X1,X4)),X5),X6)),X7)) = k3_xboole_0(X7,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_105,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X2,X3))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_39]),c_0_39])).

cnf(c_0_106,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_43]),c_0_101])).

cnf(c_0_107,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_102])).

cnf(c_0_108,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1)
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(ef,[status(thm)],[c_0_41])).

cnf(c_0_109,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4))) = k3_xboole_0(X2,k2_xboole_0(X3,X4))
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X4)
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_105]),c_0_39]),c_0_48])).

cnf(c_0_112,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_106]),c_0_75]),c_0_107]),c_0_75]),c_0_75])])).

cnf(c_0_113,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_13])).

cnf(c_0_114,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_108]),c_0_108])).

cnf(c_0_115,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_116,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_109,c_0_101])).

cnf(c_0_117,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X3)
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_118,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k3_xboole_0(X2,k2_xboole_0(X1,X3))
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)),k3_xboole_0(X2,k2_xboole_0(X1,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_110])).

cnf(c_0_119,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_120,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_121,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = X1
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),X1),k2_xboole_0(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_114])).

cnf(c_0_122,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_116]),c_0_116])).

cnf(c_0_123,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_56])).

cnf(c_0_124,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_31])).

cnf(c_0_125,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,k3_xboole_0(X3,X1)),X4)) = k3_xboole_0(X1,X4)
    | ~ r2_hidden(esk2_3(k2_xboole_0(X2,k3_xboole_0(X3,X1)),k3_xboole_0(X1,X4),k3_xboole_0(X1,X4)),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_22]),c_0_62])).

cnf(c_0_126,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X2)
    | r2_hidden(esk2_3(X2,k3_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X1,k2_xboole_0(X2,X3))),X3) ),
    inference(rw,[status(thm)],[c_0_118,c_0_111])).

cnf(c_0_127,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X3))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_75])).

cnf(c_0_128,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_87,c_0_119])).

cnf(c_0_129,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X4,X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_130,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_122])).

cnf(c_0_131,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_87,c_0_123])).

cnf(c_0_132,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_124,c_0_71])).

cnf(c_0_133,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,k2_xboole_0(X3,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_75]),c_0_107]),c_0_75]),c_0_75])]),c_0_127])).

cnf(c_0_134,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X1),X2)) = k3_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_77]),c_0_75])).

cnf(c_0_135,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X4,X1)))) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130]),c_0_130])).

cnf(c_0_136,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_75])).

cnf(c_0_137,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_109,c_0_75])).

cnf(c_0_138,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_133]),c_0_39])).

cnf(c_0_139,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k3_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_81])).

cnf(c_0_140,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137]),c_0_136])).

cnf(c_0_141,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_138]),c_0_130]),c_0_139])).

fof(c_0_142,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t23_xboole_1])).

cnf(c_0_143,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

fof(c_0_144,negated_conjecture,(
    k3_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) != k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k3_xboole_0(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_142])])])).

cnf(c_0_145,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_133])).

cnf(c_0_146,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_75])).

cnf(c_0_147,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k3_xboole_0(X3,X2))) = k2_xboole_0(X1,k3_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_128]),c_0_39])).

cnf(c_0_148,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) != k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k3_xboole_0(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_149,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_147])).

cnf(c_0_150,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_39])).

cnf(c_0_151,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_149]),c_0_75]),c_0_149]),c_0_79]),c_0_101]),c_0_150])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 51.21/51.41  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 51.21/51.41  # and selection function SelectVGNonCR.
% 51.21/51.41  #
% 51.21/51.41  # Preprocessing time       : 0.036 s
% 51.21/51.41  # Presaturation interreduction done
% 51.21/51.41  
% 51.21/51.41  # Proof found!
% 51.21/51.41  # SZS status Theorem
% 51.21/51.41  # SZS output start CNFRefutation
% 51.21/51.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 51.21/51.41  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 51.21/51.41  fof(t23_xboole_1, conjecture, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 51.21/51.41  fof(c_0_3, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15))&(r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|~r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k3_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|~r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k3_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))&(r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 51.21/51.41  cnf(c_0_4, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 51.21/51.41  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 51.21/51.41  cnf(c_0_6, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 51.21/51.41  cnf(c_0_7, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_4])).
% 51.21/51.41  cnf(c_0_8, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 51.21/51.41  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 51.21/51.41  cnf(c_0_10, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 51.21/51.41  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 51.21/51.41  cnf(c_0_12, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_7])).
% 51.21/51.41  cnf(c_0_13, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_8])).
% 51.21/51.41  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_9])).
% 51.21/51.41  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 51.21/51.41  cnf(c_0_16, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_10])).
% 51.21/51.41  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_11])).
% 51.21/51.41  cnf(c_0_18, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 51.21/51.41  cnf(c_0_19, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_14, c_0_7])).
% 51.21/51.41  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_15])).
% 51.21/51.41  cnf(c_0_21, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,X3),X2)|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_12, c_0_16])).
% 51.21/51.41  cnf(c_0_22, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_7])).
% 51.21/51.41  cnf(c_0_23, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 51.21/51.41  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_20]), c_0_20])).
% 51.21/51.41  cnf(c_0_25, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,X2)|r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 51.21/51.41  cnf(c_0_26, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 51.21/51.41  cnf(c_0_27, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 51.21/51.41  cnf(c_0_28, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))=k3_xboole_0(X2,k3_xboole_0(X3,X4))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X4)), inference(spm,[status(thm)],[c_0_14, c_0_19])).
% 51.21/51.41  cnf(c_0_29, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),k2_xboole_0(X4,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 51.21/51.41  cnf(c_0_30, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 51.21/51.41  cnf(c_0_31, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_19])).
% 51.21/51.41  cnf(c_0_32, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 51.21/51.41  cnf(c_0_33, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_27])).
% 51.21/51.41  cnf(c_0_34, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)))=k3_xboole_0(X3,k3_xboole_0(X4,X2))|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)),k3_xboole_0(X3,k3_xboole_0(X4,X2))),X1)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 51.21/51.41  cnf(c_0_35, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X3,X2)|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2),k3_xboole_0(X3,X2)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 51.21/51.41  cnf(c_0_36, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))=k3_xboole_0(k3_xboole_0(X2,X3),X4)|r2_hidden(esk2_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 51.21/51.41  cnf(c_0_37, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))=k3_xboole_0(k3_xboole_0(X2,X3),X4)|r2_hidden(esk2_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X3)), inference(spm,[status(thm)],[c_0_14, c_0_22])).
% 51.21/51.41  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k3_xboole_0(X3,X2))=k3_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_26, c_0_29])).
% 51.21/51.41  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 51.21/51.41  cnf(c_0_40, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))=k3_xboole_0(X2,k3_xboole_0(X3,X4))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X3)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 51.21/51.41  cnf(c_0_41, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 51.21/51.41  cnf(c_0_42, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_32])).
% 51.21/51.41  cnf(c_0_43, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)|r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_33, c_0_7])).
% 51.21/51.41  cnf(c_0_44, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2)))=k3_xboole_0(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 51.21/51.41  cnf(c_0_45, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X3),X2))=k3_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 51.21/51.41  cnf(c_0_46, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X1),X2))=k3_xboole_0(k3_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 51.21/51.41  cnf(c_0_47, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_39])).
% 51.21/51.41  cnf(c_0_48, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 51.21/51.41  cnf(c_0_49, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 51.21/51.41  cnf(c_0_50, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 51.21/51.41  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_41])).
% 51.21/51.41  cnf(c_0_52, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_12, c_0_36])).
% 51.21/51.41  cnf(c_0_53, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_12, c_0_42])).
% 51.21/51.41  cnf(c_0_54, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|r2_hidden(esk2_3(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_18, c_0_43])).
% 51.21/51.41  cnf(c_0_55, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X1,k3_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_44]), c_0_39]), c_0_45])).
% 51.21/51.41  cnf(c_0_56, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 51.21/51.41  cnf(c_0_57, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39]), c_0_48])).
% 51.21/51.41  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_49, c_0_13])).
% 51.21/51.41  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51])).
% 51.21/51.41  cnf(c_0_60, plain, (k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X1)=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 51.21/51.41  cnf(c_0_61, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 51.21/51.41  cnf(c_0_62, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_55]), c_0_55])).
% 51.21/51.41  cnf(c_0_63, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X3))=k3_xboole_0(k3_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 51.21/51.41  cnf(c_0_64, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3))=k3_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_57, c_0_39])).
% 51.21/51.41  cnf(c_0_65, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 51.21/51.41  cnf(c_0_66, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X3)=X3|r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_17, c_0_59])).
% 51.21/51.41  cnf(c_0_67, plain, (k2_xboole_0(X1,X1)=X1|r2_hidden(esk1_3(X1,X1,X1),X1)), inference(ef,[status(thm)],[c_0_51])).
% 51.21/51.41  cnf(c_0_68, plain, (k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X2)), inference(spm,[status(thm)],[c_0_18, c_0_42])).
% 51.21/51.41  cnf(c_0_69, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(X1,X3)|r2_hidden(esk2_3(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3),k2_xboole_0(X1,X3)),X3)), inference(spm,[status(thm)],[c_0_53, c_0_43])).
% 51.21/51.41  cnf(c_0_70, plain, (k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X2,X1))=k3_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 51.21/51.41  cnf(c_0_71, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_62]), c_0_62]), c_0_52]), c_0_63])).
% 51.21/51.41  cnf(c_0_72, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 51.21/51.41  cnf(c_0_73, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_53, c_0_7])).
% 51.21/51.41  cnf(c_0_74, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X2),X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 51.21/51.41  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_61]), c_0_61])).
% 51.21/51.41  cnf(c_0_76, plain, (k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4,X4),X1)), inference(spm,[status(thm)],[c_0_53, c_0_42])).
% 51.21/51.41  cnf(c_0_77, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3))=k3_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_64])).
% 51.21/51.41  cnf(c_0_78, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 51.21/51.41  cnf(c_0_79, plain, (k2_xboole_0(X1,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_67]), c_0_67])).
% 51.21/51.41  cnf(c_0_80, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_39])).
% 51.21/51.41  cnf(c_0_81, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_61])).
% 51.21/51.41  cnf(c_0_82, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k3_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_22])).
% 51.21/51.41  cnf(c_0_83, plain, (k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2)=X2), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 51.21/51.41  cnf(c_0_84, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X3),X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 51.21/51.41  cnf(c_0_85, plain, (k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,X1))=k2_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_76, c_0_54])).
% 51.21/51.41  cnf(c_0_86, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3))=k3_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_77, c_0_75])).
% 51.21/51.41  cnf(c_0_87, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_75])).
% 51.21/51.41  cnf(c_0_88, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2))=k2_xboole_0(k3_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_78]), c_0_81])).
% 51.21/51.41  cnf(c_0_89, plain, (k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X3)), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 51.21/51.41  cnf(c_0_90, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 51.21/51.41  cnf(c_0_91, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_73])).
% 51.21/51.41  cnf(c_0_92, plain, (k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4),X2)=X2), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 51.21/51.41  cnf(c_0_93, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_18, c_0_7])).
% 51.21/51.41  cnf(c_0_94, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 51.21/51.41  cnf(c_0_95, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 51.21/51.41  cnf(c_0_96, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X3,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_69]), c_0_39])).
% 51.21/51.41  cnf(c_0_97, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)))=k3_xboole_0(X3,k3_xboole_0(X4,X2))), inference(spm,[status(thm)],[c_0_90, c_0_23])).
% 51.21/51.41  cnf(c_0_98, plain, (k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,X3)),X4),X5))=X1), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 51.21/51.41  cnf(c_0_99, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_62]), c_0_71])).
% 51.21/51.41  cnf(c_0_100, plain, (k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k3_xboole_0(X3,X1))=k3_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_75])).
% 51.21/51.41  cnf(c_0_101, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_30, c_0_73])).
% 51.21/51.41  cnf(c_0_102, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_25, c_0_93])).
% 51.21/51.41  cnf(c_0_103, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_75]), c_0_39]), c_0_96]), c_0_75])).
% 51.21/51.41  cnf(c_0_104, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,k2_xboole_0(k2_xboole_0(k2_xboole_0(X3,k2_xboole_0(X1,X4)),X5),X6)),X7))=k3_xboole_0(X7,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 51.21/51.41  cnf(c_0_105, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X2,X3)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_39]), c_0_39])).
% 51.21/51.41  cnf(c_0_106, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_43]), c_0_101])).
% 51.21/51.41  cnf(c_0_107, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_24, c_0_102])).
% 51.21/51.41  cnf(c_0_108, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(ef,[status(thm)],[c_0_41])).
% 51.21/51.41  cnf(c_0_109, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3))=k2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 51.21/51.41  cnf(c_0_110, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)))=k3_xboole_0(X2,k2_xboole_0(X3,X4))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X4)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X3)), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 51.21/51.41  cnf(c_0_111, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_105]), c_0_39]), c_0_48])).
% 51.21/51.41  cnf(c_0_112, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_106]), c_0_75]), c_0_107]), c_0_75]), c_0_75])])).
% 51.21/51.41  cnf(c_0_113, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X4)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_50, c_0_13])).
% 51.21/51.41  cnf(c_0_114, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_108]), c_0_108])).
% 51.21/51.41  cnf(c_0_115, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,k3_xboole_0(X4,X3))), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 51.21/51.41  cnf(c_0_116, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_109, c_0_101])).
% 51.21/51.41  cnf(c_0_117, plain, (k3_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X3)|~r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X2)), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 51.21/51.41  cnf(c_0_118, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k3_xboole_0(X2,k2_xboole_0(X1,X3))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)),k3_xboole_0(X2,k2_xboole_0(X1,X3))),X3)), inference(spm,[status(thm)],[c_0_12, c_0_110])).
% 51.21/51.41  cnf(c_0_119, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 51.21/51.41  cnf(c_0_120, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 51.21/51.41  cnf(c_0_121, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=X1|r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),X1),k2_xboole_0(X4,X3))), inference(spm,[status(thm)],[c_0_115, c_0_114])).
% 51.21/51.41  cnf(c_0_122, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_116]), c_0_116])).
% 51.21/51.41  cnf(c_0_123, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_63, c_0_56])).
% 51.21/51.41  cnf(c_0_124, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_91, c_0_31])).
% 51.21/51.41  cnf(c_0_125, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,k3_xboole_0(X3,X1)),X4))=k3_xboole_0(X1,X4)|~r2_hidden(esk2_3(k2_xboole_0(X2,k3_xboole_0(X3,X1)),k3_xboole_0(X1,X4),k3_xboole_0(X1,X4)),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_22]), c_0_62])).
% 51.21/51.41  cnf(c_0_126, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X2)|r2_hidden(esk2_3(X2,k3_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X1,k2_xboole_0(X2,X3))),X3)), inference(rw,[status(thm)],[c_0_118, c_0_111])).
% 51.21/51.41  cnf(c_0_127, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X3)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_75])).
% 51.21/51.41  cnf(c_0_128, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_87, c_0_119])).
% 51.21/51.41  cnf(c_0_129, plain, (k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X4,X3))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 51.21/51.41  cnf(c_0_130, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_75, c_0_122])).
% 51.21/51.41  cnf(c_0_131, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_87, c_0_123])).
% 51.21/51.41  cnf(c_0_132, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(k3_xboole_0(X1,X2),X3)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_124, c_0_71])).
% 51.21/51.41  cnf(c_0_133, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,k2_xboole_0(X3,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_75]), c_0_107]), c_0_75]), c_0_75])]), c_0_127])).
% 51.21/51.41  cnf(c_0_134, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X1),X2))=k3_xboole_0(k2_xboole_0(X3,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_77]), c_0_75])).
% 51.21/51.41  cnf(c_0_135, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X4,X1))))=k2_xboole_0(X3,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130]), c_0_130])).
% 51.21/51.41  cnf(c_0_136, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3))=k2_xboole_0(k3_xboole_0(X2,X1),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_75])).
% 51.21/51.41  cnf(c_0_137, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_109, c_0_75])).
% 51.21/51.41  cnf(c_0_138, plain, (k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_133]), c_0_39])).
% 51.21/51.41  cnf(c_0_139, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k3_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_134, c_0_81])).
% 51.21/51.41  cnf(c_0_140, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_137]), c_0_136])).
% 51.21/51.41  cnf(c_0_141, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(k3_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_138]), c_0_130]), c_0_139])).
% 51.21/51.41  fof(c_0_142, negated_conjecture, ~(![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t23_xboole_1])).
% 51.21/51.41  cnf(c_0_143, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_140, c_0_141])).
% 51.21/51.41  fof(c_0_144, negated_conjecture, k3_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))!=k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k3_xboole_0(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_142])])])).
% 51.21/51.41  cnf(c_0_145, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_81, c_0_133])).
% 51.21/51.41  cnf(c_0_146, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_143, c_0_75])).
% 51.21/51.41  cnf(c_0_147, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k3_xboole_0(X3,X2)))=k2_xboole_0(X1,k3_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_128]), c_0_39])).
% 51.21/51.41  cnf(c_0_148, negated_conjecture, (k3_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))!=k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k3_xboole_0(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_144])).
% 51.21/51.41  cnf(c_0_149, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_147])).
% 51.21/51.41  cnf(c_0_150, plain, (k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_138, c_0_39])).
% 51.21/51.41  cnf(c_0_151, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148, c_0_149]), c_0_75]), c_0_149]), c_0_79]), c_0_101]), c_0_150])]), ['proof']).
% 51.21/51.41  # SZS output end CNFRefutation
% 51.21/51.41  # Proof object total steps             : 152
% 51.21/51.41  # Proof object clause steps            : 145
% 51.21/51.41  # Proof object formula steps           : 7
% 51.21/51.41  # Proof object conjectures             : 5
% 51.21/51.41  # Proof object clause conjectures      : 2
% 51.21/51.41  # Proof object formula conjectures     : 3
% 51.21/51.41  # Proof object initial clauses used    : 13
% 51.21/51.41  # Proof object initial formulas used   : 3
% 51.21/51.41  # Proof object generating inferences   : 126
% 51.21/51.41  # Proof object simplifying inferences  : 67
% 51.21/51.41  # Training examples: 0 positive, 0 negative
% 51.21/51.41  # Parsed axioms                        : 3
% 51.21/51.41  # Removed by relevancy pruning/SinE    : 0
% 51.21/51.41  # Initial clauses                      : 13
% 51.21/51.41  # Removed in clause preprocessing      : 0
% 51.21/51.41  # Initial clauses in saturation        : 13
% 51.21/51.41  # Processed clauses                    : 91733
% 51.21/51.41  # ...of these trivial                  : 12066
% 51.21/51.41  # ...subsumed                          : 75347
% 51.21/51.41  # ...remaining for further processing  : 4320
% 51.21/51.41  # Other redundant clauses eliminated   : 9897
% 51.21/51.41  # Clauses deleted for lack of memory   : 3068645
% 51.21/51.41  # Backward-subsumed                    : 55
% 51.21/51.41  # Backward-rewritten                   : 2448
% 51.21/51.41  # Generated clauses                    : 6790964
% 51.21/51.41  # ...of the previous two non-trivial   : 6261746
% 51.21/51.41  # Contextual simplify-reflections      : 10
% 51.21/51.41  # Paramodulations                      : 6770731
% 51.21/51.41  # Factorizations                       : 10260
% 51.21/51.41  # Equation resolutions                 : 9973
% 51.21/51.41  # Propositional unsat checks           : 0
% 51.21/51.41  #    Propositional check models        : 0
% 51.21/51.41  #    Propositional check unsatisfiable : 0
% 51.21/51.41  #    Propositional clauses             : 0
% 51.21/51.41  #    Propositional clauses after purity: 0
% 51.21/51.41  #    Propositional unsat core size     : 0
% 51.21/51.41  #    Propositional preprocessing time  : 0.000
% 51.21/51.41  #    Propositional encoding time       : 0.000
% 51.21/51.41  #    Propositional solver time         : 0.000
% 51.21/51.41  #    Success case prop preproc time    : 0.000
% 51.21/51.41  #    Success case prop encoding time   : 0.000
% 51.21/51.41  #    Success case prop solver time     : 0.000
% 51.21/51.41  # Current number of processed clauses  : 1804
% 51.21/51.41  #    Positive orientable unit clauses  : 166
% 51.21/51.41  #    Positive unorientable unit clauses: 29
% 51.21/51.41  #    Negative unit clauses             : 0
% 51.21/51.41  #    Non-unit-clauses                  : 1609
% 51.21/51.41  # Current number of unprocessed clauses: 1847727
% 51.21/51.41  # ...number of literals in the above   : 6277000
% 51.21/51.41  # Current number of archived formulas  : 0
% 51.21/51.41  # Current number of archived clauses   : 2516
% 51.21/51.41  # Clause-clause subsumption calls (NU) : 2057591
% 51.21/51.41  # Rec. Clause-clause subsumption calls : 683011
% 51.21/51.41  # Non-unit clause-clause subsumptions  : 47320
% 51.21/51.41  # Unit Clause-clause subsumption calls : 388136
% 51.21/51.41  # Rewrite failures with RHS unbound    : 7774116
% 51.21/51.41  # BW rewrite match attempts            : 62474
% 51.21/51.41  # BW rewrite match successes           : 21871
% 51.21/51.41  # Condensation attempts                : 0
% 51.21/51.41  # Condensation successes               : 0
% 51.21/51.41  # Termbank termtop insertions          : 123995059
% 51.27/51.49  
% 51.27/51.49  # -------------------------------------------------
% 51.27/51.49  # User time                : 50.022 s
% 51.27/51.49  # System time              : 1.111 s
% 51.27/51.49  # Total time               : 51.133 s
% 51.27/51.49  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
