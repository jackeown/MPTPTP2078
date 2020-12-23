%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:55 EST 2020

% Result     : Theorem 39.70s
% Output     : CNFRefutation 39.70s
% Verified   : 
% Statistics : Number of formulae       :  142 (54124 expanded)
%              Number of clauses        :  135 (30681 expanded)
%              Number of leaves         :    3 (11721 expanded)
%              Depth                    :   25
%              Number of atoms          :  266 (357119 expanded)
%              Number of equality atoms :  145 (108827 expanded)
%              Maximal formula depth    :   17 (   2 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t24_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

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
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X2,X4))) = k3_xboole_0(X3,k3_xboole_0(X2,X4))
    | ~ r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X2,X4)),k3_xboole_0(X3,k3_xboole_0(X2,X4))),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_40])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(X1,k3_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_44]),c_0_39]),c_0_45])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39]),c_0_48])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_13])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51])).

cnf(c_0_61,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X1) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_22])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_56]),c_0_56])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X3)) = k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k3_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_39])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X3) = X3
    | r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_60])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk1_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_51])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_42])).

cnf(c_0_72,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(X1,X3)
    | r2_hidden(esk2_3(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3),k2_xboole_0(X1,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_74,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_64]),c_0_65]),c_0_52])).

cnf(c_0_75,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,k2_xboole_0(X2,X1))) = k3_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_62])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_62]),c_0_62])).

cnf(c_0_77,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_53,c_0_7])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_18,c_0_7])).

cnf(c_0_79,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X2),X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4,X4),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_67])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_70]),c_0_70])).

cnf(c_0_84,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_39])).

cnf(c_0_85,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_86,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k3_xboole_0(X3,X1)) = k3_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_76])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_77])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_78])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X3),X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_76])).

cnf(c_0_90,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,X1)) = k2_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_54])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_81,c_0_76])).

cnf(c_0_92,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_76])).

cnf(c_0_93,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2)) = k2_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_82]),c_0_85])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_95,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X2,X3))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_39]),c_0_39])).

cnf(c_0_96,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_43]),c_0_87])).

cnf(c_0_97,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_88])).

cnf(c_0_98,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_99,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X3,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_72]),c_0_39])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_95]),c_0_39]),c_0_48])).

cnf(c_0_102,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_96]),c_0_76]),c_0_97]),c_0_76]),c_0_76])])).

cnf(c_0_103,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_76]),c_0_39]),c_0_100]),c_0_76])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4))) = k3_xboole_0(X2,k2_xboole_0(X3,X4))
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X4)
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

cnf(c_0_107,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_108,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_105,c_0_87])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_77])).

cnf(c_0_110,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4) = X4
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X3)
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k3_xboole_0(X2,k2_xboole_0(X1,X3))
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)),k3_xboole_0(X2,k2_xboole_0(X1,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_106])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_57])).

cnf(c_0_113,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = X3 ),
    inference(spm,[status(thm)],[c_0_107,c_0_78])).

cnf(c_0_114,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_108]),c_0_108])).

cnf(c_0_115,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_109,c_0_31])).

cnf(c_0_116,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,k3_xboole_0(X3,X1)),X4)) = k3_xboole_0(X1,X4)
    | ~ r2_hidden(esk2_3(k2_xboole_0(X2,k3_xboole_0(X3,X1)),k3_xboole_0(X1,X4),k3_xboole_0(X1,X4)),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_22]),c_0_64])).

cnf(c_0_117,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X2)
    | r2_hidden(esk2_3(X2,k3_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X1,k2_xboole_0(X2,X3))),X3) ),
    inference(rw,[status(thm)],[c_0_111,c_0_101])).

cnf(c_0_118,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X3))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_76])).

cnf(c_0_119,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_92,c_0_104])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_92,c_0_112])).

cnf(c_0_121,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_113])).

cnf(c_0_122,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_114])).

cnf(c_0_123,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(k3_xboole_0(X2,X1),X3))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_115,c_0_74])).

cnf(c_0_124,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,k2_xboole_0(X3,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_76]),c_0_97]),c_0_76]),c_0_76])]),c_0_118])).

cnf(c_0_125,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X1),X2)) = k3_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_81]),c_0_76])).

cnf(c_0_126,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X4,X1)))) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122]),c_0_122])).

cnf(c_0_127,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_123]),c_0_76])).

cnf(c_0_128,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_105,c_0_76])).

cnf(c_0_129,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_124]),c_0_39])).

cnf(c_0_130,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k3_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_85])).

cnf(c_0_131,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128]),c_0_127])).

cnf(c_0_132,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_129]),c_0_122]),c_0_130])).

fof(c_0_133,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t24_xboole_1])).

cnf(c_0_134,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

fof(c_0_135,negated_conjecture,(
    k2_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0)) != k3_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_133])])])).

cnf(c_0_136,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_124])).

cnf(c_0_137,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_76])).

cnf(c_0_138,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k3_xboole_0(X3,X2))) = k2_xboole_0(X1,k3_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_119]),c_0_39])).

cnf(c_0_139,negated_conjecture,
    ( k2_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0)) != k3_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_140,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_140])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 39.70/39.88  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 39.70/39.88  # and selection function SelectVGNonCR.
% 39.70/39.88  #
% 39.70/39.88  # Preprocessing time       : 0.026 s
% 39.70/39.88  # Presaturation interreduction done
% 39.70/39.88  
% 39.70/39.88  # Proof found!
% 39.70/39.88  # SZS status Theorem
% 39.70/39.88  # SZS output start CNFRefutation
% 39.70/39.88  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 39.70/39.88  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 39.70/39.88  fof(t24_xboole_1, conjecture, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 39.70/39.88  fof(c_0_3, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15))&(r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|~r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k3_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|~r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k3_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))&(r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 39.70/39.88  cnf(c_0_4, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 39.70/39.88  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 39.70/39.88  cnf(c_0_6, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 39.70/39.88  cnf(c_0_7, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_4])).
% 39.70/39.88  cnf(c_0_8, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 39.70/39.88  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 39.70/39.88  cnf(c_0_10, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 39.70/39.88  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 39.70/39.88  cnf(c_0_12, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_7])).
% 39.70/39.88  cnf(c_0_13, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_8])).
% 39.70/39.88  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_9])).
% 39.70/39.88  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 39.70/39.88  cnf(c_0_16, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_10])).
% 39.70/39.88  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_11])).
% 39.70/39.88  cnf(c_0_18, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 39.70/39.88  cnf(c_0_19, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_14, c_0_7])).
% 39.70/39.88  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_15])).
% 39.70/39.88  cnf(c_0_21, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,X3),X2)|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_12, c_0_16])).
% 39.70/39.88  cnf(c_0_22, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_7])).
% 39.70/39.88  cnf(c_0_23, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 39.70/39.88  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_20]), c_0_20])).
% 39.70/39.88  cnf(c_0_25, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,X2)|r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 39.70/39.88  cnf(c_0_26, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 39.70/39.88  cnf(c_0_27, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 39.70/39.88  cnf(c_0_28, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))=k3_xboole_0(X2,k3_xboole_0(X3,X4))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X4)), inference(spm,[status(thm)],[c_0_14, c_0_19])).
% 39.70/39.88  cnf(c_0_29, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),k2_xboole_0(X4,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 39.70/39.88  cnf(c_0_30, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 39.70/39.88  cnf(c_0_31, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_19])).
% 39.70/39.88  cnf(c_0_32, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 39.70/39.88  cnf(c_0_33, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_27])).
% 39.70/39.88  cnf(c_0_34, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)))=k3_xboole_0(X3,k3_xboole_0(X4,X2))|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)),k3_xboole_0(X3,k3_xboole_0(X4,X2))),X1)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 39.70/39.88  cnf(c_0_35, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X3,X2)|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2),k3_xboole_0(X3,X2)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 39.70/39.88  cnf(c_0_36, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))=k3_xboole_0(k3_xboole_0(X2,X3),X4)|r2_hidden(esk2_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 39.70/39.88  cnf(c_0_37, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))=k3_xboole_0(k3_xboole_0(X2,X3),X4)|r2_hidden(esk2_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X3)), inference(spm,[status(thm)],[c_0_14, c_0_22])).
% 39.70/39.88  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k3_xboole_0(X3,X2))=k3_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_26, c_0_29])).
% 39.70/39.88  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 39.70/39.88  cnf(c_0_40, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))=k3_xboole_0(X2,k3_xboole_0(X3,X4))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X3)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 39.70/39.88  cnf(c_0_41, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 39.70/39.88  cnf(c_0_42, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_32])).
% 39.70/39.88  cnf(c_0_43, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)|r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_33, c_0_7])).
% 39.70/39.88  cnf(c_0_44, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2)))=k3_xboole_0(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 39.70/39.88  cnf(c_0_45, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X3),X2))=k3_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 39.70/39.88  cnf(c_0_46, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X1),X2))=k3_xboole_0(k3_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 39.70/39.88  cnf(c_0_47, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_39])).
% 39.70/39.88  cnf(c_0_48, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 39.70/39.88  cnf(c_0_49, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 39.70/39.88  cnf(c_0_50, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 39.70/39.88  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_41])).
% 39.70/39.88  cnf(c_0_52, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_12, c_0_36])).
% 39.70/39.88  cnf(c_0_53, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_12, c_0_42])).
% 39.70/39.88  cnf(c_0_54, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|r2_hidden(esk2_3(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_18, c_0_43])).
% 39.70/39.88  cnf(c_0_55, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X2,X4)))=k3_xboole_0(X3,k3_xboole_0(X2,X4))|~r2_hidden(esk2_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X2,X4)),k3_xboole_0(X3,k3_xboole_0(X2,X4))),X1)), inference(spm,[status(thm)],[c_0_21, c_0_40])).
% 39.70/39.88  cnf(c_0_56, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X1,k3_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_44]), c_0_39]), c_0_45])).
% 39.70/39.88  cnf(c_0_57, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 39.70/39.88  cnf(c_0_58, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39]), c_0_48])).
% 39.70/39.88  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_49, c_0_13])).
% 39.70/39.88  cnf(c_0_60, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51])).
% 39.70/39.88  cnf(c_0_61, plain, (k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X1)=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 39.70/39.88  cnf(c_0_62, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 39.70/39.88  cnf(c_0_63, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_55, c_0_22])).
% 39.70/39.88  cnf(c_0_64, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_56]), c_0_56])).
% 39.70/39.88  cnf(c_0_65, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X3))=k3_xboole_0(k3_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 39.70/39.88  cnf(c_0_66, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 39.70/39.88  cnf(c_0_67, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3))=k3_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_58, c_0_39])).
% 39.70/39.88  cnf(c_0_68, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 39.70/39.88  cnf(c_0_69, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X3)=X3|r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_17, c_0_60])).
% 39.70/39.88  cnf(c_0_70, plain, (k2_xboole_0(X1,X1)=X1|r2_hidden(esk1_3(X1,X1,X1),X1)), inference(ef,[status(thm)],[c_0_51])).
% 39.70/39.88  cnf(c_0_71, plain, (k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X2)), inference(spm,[status(thm)],[c_0_18, c_0_42])).
% 39.70/39.88  cnf(c_0_72, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(X1,X3)|r2_hidden(esk2_3(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3),k2_xboole_0(X1,X3)),X3)), inference(spm,[status(thm)],[c_0_53, c_0_43])).
% 39.70/39.88  cnf(c_0_73, plain, (k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X2,X1))=k3_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 39.70/39.88  cnf(c_0_74, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_64]), c_0_65]), c_0_52])).
% 39.70/39.88  cnf(c_0_75, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X3,k2_xboole_0(X2,X1)))=k3_xboole_0(X3,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_66, c_0_62])).
% 39.70/39.88  cnf(c_0_76, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_62]), c_0_62])).
% 39.70/39.88  cnf(c_0_77, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_53, c_0_7])).
% 39.70/39.88  cnf(c_0_78, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_18, c_0_7])).
% 39.70/39.88  cnf(c_0_79, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X2),X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 39.70/39.88  cnf(c_0_80, plain, (k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4,X4),X1)), inference(spm,[status(thm)],[c_0_53, c_0_42])).
% 39.70/39.88  cnf(c_0_81, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3))=k3_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_67])).
% 39.70/39.88  cnf(c_0_82, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 39.70/39.88  cnf(c_0_83, plain, (k2_xboole_0(X1,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_70]), c_0_70])).
% 39.70/39.88  cnf(c_0_84, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_39])).
% 39.70/39.88  cnf(c_0_85, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 39.70/39.88  cnf(c_0_86, plain, (k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),k3_xboole_0(X3,X1))=k3_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_76])).
% 39.70/39.88  cnf(c_0_87, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_30, c_0_77])).
% 39.70/39.88  cnf(c_0_88, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_25, c_0_78])).
% 39.70/39.88  cnf(c_0_89, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X3),X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_79, c_0_76])).
% 39.70/39.88  cnf(c_0_90, plain, (k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,X1))=k2_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_80, c_0_54])).
% 39.70/39.88  cnf(c_0_91, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3))=k3_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_81, c_0_76])).
% 39.70/39.88  cnf(c_0_92, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_76])).
% 39.70/39.88  cnf(c_0_93, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2))=k2_xboole_0(k3_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_82]), c_0_85])).
% 39.70/39.88  cnf(c_0_94, plain, (k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,X4),X3)), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 39.70/39.88  cnf(c_0_95, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X2,X3)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_39]), c_0_39])).
% 39.70/39.88  cnf(c_0_96, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_43]), c_0_87])).
% 39.70/39.88  cnf(c_0_97, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_24, c_0_88])).
% 39.70/39.88  cnf(c_0_98, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 39.70/39.88  cnf(c_0_99, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X1,X3),X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 39.70/39.88  cnf(c_0_100, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X3,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_72]), c_0_39])).
% 39.70/39.88  cnf(c_0_101, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_95]), c_0_39]), c_0_48])).
% 39.70/39.88  cnf(c_0_102, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_96]), c_0_76]), c_0_97]), c_0_76]), c_0_76])])).
% 39.70/39.88  cnf(c_0_103, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_76]), c_0_39]), c_0_100]), c_0_76])).
% 39.70/39.88  cnf(c_0_104, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 39.70/39.88  cnf(c_0_105, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3))=k2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 39.70/39.88  cnf(c_0_106, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)))=k3_xboole_0(X2,k2_xboole_0(X3,X4))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X4)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X3,X4)),k3_xboole_0(X2,k2_xboole_0(X3,X4))),X3)), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 39.70/39.88  cnf(c_0_107, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 39.70/39.88  cnf(c_0_108, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_105, c_0_87])).
% 39.70/39.88  cnf(c_0_109, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_77])).
% 39.70/39.88  cnf(c_0_110, plain, (k3_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4)=X4|~r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X3)|~r2_hidden(esk2_3(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X4,X4),X2)), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 39.70/39.88  cnf(c_0_111, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k3_xboole_0(X2,k2_xboole_0(X1,X3))|r2_hidden(esk2_3(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)),k3_xboole_0(X2,k2_xboole_0(X1,X3))),X3)), inference(spm,[status(thm)],[c_0_12, c_0_106])).
% 39.70/39.88  cnf(c_0_112, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_65, c_0_57])).
% 39.70/39.88  cnf(c_0_113, plain, (k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=X3), inference(spm,[status(thm)],[c_0_107, c_0_78])).
% 39.70/39.88  cnf(c_0_114, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_108]), c_0_108])).
% 39.70/39.88  cnf(c_0_115, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_109, c_0_31])).
% 39.70/39.88  cnf(c_0_116, plain, (k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,k3_xboole_0(X3,X1)),X4))=k3_xboole_0(X1,X4)|~r2_hidden(esk2_3(k2_xboole_0(X2,k3_xboole_0(X3,X1)),k3_xboole_0(X1,X4),k3_xboole_0(X1,X4)),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_22]), c_0_64])).
% 39.70/39.88  cnf(c_0_117, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X2)|r2_hidden(esk2_3(X2,k3_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X1,k2_xboole_0(X2,X3))),X3)), inference(rw,[status(thm)],[c_0_111, c_0_101])).
% 39.70/39.88  cnf(c_0_118, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X3)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_76])).
% 39.70/39.88  cnf(c_0_119, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_92, c_0_104])).
% 39.70/39.88  cnf(c_0_120, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_92, c_0_112])).
% 39.70/39.88  cnf(c_0_121, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_30, c_0_113])).
% 39.70/39.88  cnf(c_0_122, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_76, c_0_114])).
% 39.70/39.88  cnf(c_0_123, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(k3_xboole_0(X2,X1),X3)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_115, c_0_74])).
% 39.70/39.88  cnf(c_0_124, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,k2_xboole_0(X3,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_76]), c_0_97]), c_0_76]), c_0_76])]), c_0_118])).
% 39.70/39.88  cnf(c_0_125, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,X1),X2))=k3_xboole_0(k2_xboole_0(X3,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_81]), c_0_76])).
% 39.70/39.88  cnf(c_0_126, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X4,X1))))=k2_xboole_0(X3,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122]), c_0_122])).
% 39.70/39.88  cnf(c_0_127, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k3_xboole_0(X2,X1),X3))=k2_xboole_0(k3_xboole_0(X2,X1),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_123]), c_0_76])).
% 39.70/39.88  cnf(c_0_128, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_105, c_0_76])).
% 39.70/39.88  cnf(c_0_129, plain, (k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_124]), c_0_39])).
% 39.70/39.88  cnf(c_0_130, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k3_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_125, c_0_85])).
% 39.70/39.88  cnf(c_0_131, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128]), c_0_127])).
% 39.70/39.88  cnf(c_0_132, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(k3_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_129]), c_0_122]), c_0_130])).
% 39.70/39.88  fof(c_0_133, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t24_xboole_1])).
% 39.70/39.88  cnf(c_0_134, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 39.70/39.88  fof(c_0_135, negated_conjecture, k2_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0))!=k3_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_133])])])).
% 39.70/39.88  cnf(c_0_136, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_85, c_0_124])).
% 39.70/39.88  cnf(c_0_137, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_134, c_0_76])).
% 39.70/39.88  cnf(c_0_138, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k3_xboole_0(X3,X2)))=k2_xboole_0(X1,k3_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_119]), c_0_39])).
% 39.70/39.88  cnf(c_0_139, negated_conjecture, (k2_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0))!=k3_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_135])).
% 39.70/39.88  cnf(c_0_140, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_138])).
% 39.70/39.88  cnf(c_0_141, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_140])]), ['proof']).
% 39.70/39.88  # SZS output end CNFRefutation
% 39.70/39.88  # Proof object total steps             : 142
% 39.70/39.88  # Proof object clause steps            : 135
% 39.70/39.88  # Proof object formula steps           : 7
% 39.70/39.88  # Proof object conjectures             : 5
% 39.70/39.88  # Proof object clause conjectures      : 2
% 39.70/39.88  # Proof object formula conjectures     : 3
% 39.70/39.88  # Proof object initial clauses used    : 13
% 39.70/39.88  # Proof object initial formulas used   : 3
% 39.70/39.88  # Proof object generating inferences   : 117
% 39.70/39.88  # Proof object simplifying inferences  : 59
% 39.70/39.88  # Training examples: 0 positive, 0 negative
% 39.70/39.88  # Parsed axioms                        : 3
% 39.70/39.88  # Removed by relevancy pruning/SinE    : 0
% 39.70/39.88  # Initial clauses                      : 13
% 39.70/39.88  # Removed in clause preprocessing      : 0
% 39.70/39.88  # Initial clauses in saturation        : 13
% 39.70/39.88  # Processed clauses                    : 72740
% 39.70/39.88  # ...of these trivial                  : 10185
% 39.70/39.88  # ...subsumed                          : 58917
% 39.70/39.88  # ...remaining for further processing  : 3638
% 39.70/39.88  # Other redundant clauses eliminated   : 9923
% 39.70/39.88  # Clauses deleted for lack of memory   : 1791628
% 39.70/39.88  # Backward-subsumed                    : 52
% 39.70/39.88  # Backward-rewritten                   : 2105
% 39.70/39.88  # Generated clauses                    : 5538955
% 39.70/39.88  # ...of the previous two non-trivial   : 5017709
% 39.70/39.88  # Contextual simplify-reflections      : 10
% 39.70/39.88  # Paramodulations                      : 5521002
% 39.70/39.88  # Factorizations                       : 7958
% 39.70/39.88  # Equation resolutions                 : 9995
% 39.70/39.88  # Propositional unsat checks           : 0
% 39.70/39.88  #    Propositional check models        : 0
% 39.70/39.88  #    Propositional check unsatisfiable : 0
% 39.70/39.88  #    Propositional clauses             : 0
% 39.70/39.88  #    Propositional clauses after purity: 0
% 39.70/39.88  #    Propositional unsat core size     : 0
% 39.70/39.88  #    Propositional preprocessing time  : 0.000
% 39.70/39.88  #    Propositional encoding time       : 0.000
% 39.70/39.88  #    Propositional solver time         : 0.000
% 39.70/39.88  #    Success case prop preproc time    : 0.000
% 39.70/39.88  #    Success case prop encoding time   : 0.000
% 39.70/39.88  #    Success case prop solver time     : 0.000
% 39.70/39.88  # Current number of processed clauses  : 1468
% 39.70/39.88  #    Positive orientable unit clauses  : 176
% 39.70/39.88  #    Positive unorientable unit clauses: 9
% 39.70/39.88  #    Negative unit clauses             : 0
% 39.70/39.88  #    Non-unit-clauses                  : 1283
% 39.70/39.88  # Current number of unprocessed clauses: 1897976
% 39.70/39.88  # ...number of literals in the above   : 6113172
% 39.70/39.88  # Current number of archived formulas  : 0
% 39.70/39.88  # Current number of archived clauses   : 2170
% 39.70/39.88  # Clause-clause subsumption calls (NU) : 1516772
% 39.70/39.88  # Rec. Clause-clause subsumption calls : 606248
% 39.70/39.88  # Non-unit clause-clause subsumptions  : 44594
% 39.70/39.88  # Unit Clause-clause subsumption calls : 348325
% 39.70/39.88  # Rewrite failures with RHS unbound    : 171995
% 39.70/39.88  # BW rewrite match attempts            : 49931
% 39.70/39.88  # BW rewrite match successes           : 10636
% 39.70/39.88  # Condensation attempts                : 0
% 39.70/39.88  # Condensation successes               : 0
% 39.70/39.88  # Termbank termtop insertions          : 98494502
% 39.80/39.99  
% 39.80/39.99  # -------------------------------------------------
% 39.80/39.99  # User time                : 38.580 s
% 39.80/39.99  # System time              : 1.061 s
% 39.80/39.99  # Total time               : 39.641 s
% 39.80/39.99  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
