%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:04 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   93 (1979 expanded)
%              Number of clauses        :   72 ( 835 expanded)
%              Number of leaves         :   10 ( 553 expanded)
%              Depth                    :   18
%              Number of atoms          :  257 (4757 expanded)
%              Number of equality atoms :  122 (3239 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_11,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk4_0)
    & k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk5_0)
    & k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X34] : k2_tarski(X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X35,X36] : k1_enumset1(X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X37,X38,X39] : k2_enumset1(X37,X37,X38,X39) = k1_enumset1(X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X18
        | X19 != k1_tarski(X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_tarski(X18) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) != X22
        | X23 = k1_tarski(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) = X22
        | X23 = k1_tarski(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_24,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X25
        | X28 = X26
        | X27 != k2_tarski(X25,X26) )
      & ( X29 != X25
        | r2_hidden(X29,X27)
        | X27 != k2_tarski(X25,X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k2_tarski(X25,X26) )
      & ( esk3_3(X30,X31,X32) != X30
        | ~ r2_hidden(esk3_3(X30,X31,X32),X32)
        | X32 = k2_tarski(X30,X31) )
      & ( esk3_3(X30,X31,X32) != X31
        | ~ r2_hidden(esk3_3(X30,X31,X32),X32)
        | X32 = k2_tarski(X30,X31) )
      & ( r2_hidden(esk3_3(X30,X31,X32),X32)
        | esk3_3(X30,X31,X32) = X30
        | esk3_3(X30,X31,X32) = X31
        | X32 = k2_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_25,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_26,plain,
    ( esk2_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_18]),c_0_19]),c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( esk2_2(X1,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = X1
    | r2_hidden(esk2_2(X1,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_21])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_18]),c_0_19]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk4_0
    | r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_41,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_19]),c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_19]),c_0_19]),c_0_20]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_43,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))
    | ~ r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_25])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(k2_enumset1(X1,X1,X1,X2),X3)))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_19]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_55,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_20])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))
    | r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) = esk5_0
    | esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))
    | r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_43])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))
    | r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk5_0
    | r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_61])).

fof(c_0_66,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X40,X42)
        | ~ r1_tarski(k2_tarski(X40,X41),X42) )
      & ( r2_hidden(X41,X42)
        | ~ r1_tarski(k2_tarski(X40,X41),X42) )
      & ( ~ r2_hidden(X40,X42)
        | ~ r2_hidden(X41,X42)
        | r1_tarski(k2_tarski(X40,X41),X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk5_0
    | esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk4_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_64]),c_0_40])]),c_0_42])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_65]),c_0_40]),c_0_60])]),c_0_54])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk4_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk5_0
    | esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_70])).

fof(c_0_75,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_19]),c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_72]),c_0_25]),c_0_49])).

cnf(c_0_78,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_74]),c_0_40]),c_0_60])]),c_0_54])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,esk4_0),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_77])]),c_0_54])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_80,c_0_20])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_19]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_87,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_91]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.59/0.75  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.59/0.75  # and selection function SelectNegativeLiterals.
% 0.59/0.75  #
% 0.59/0.75  # Preprocessing time       : 0.028 s
% 0.59/0.75  # Presaturation interreduction done
% 0.59/0.75  
% 0.59/0.75  # Proof found!
% 0.59/0.75  # SZS status Theorem
% 0.59/0.75  # SZS output start CNFRefutation
% 0.59/0.75  fof(t74_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 0.59/0.75  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.59/0.75  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.59/0.75  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.59/0.75  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.59/0.75  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.59/0.75  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.59/0.75  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.59/0.75  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.59/0.75  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.59/0.75  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t74_zfmisc_1])).
% 0.59/0.75  fof(c_0_11, negated_conjecture, (((k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0&k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk4_0))&k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk5_0))&k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k2_tarski(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.59/0.75  fof(c_0_12, plain, ![X34]:k2_tarski(X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.59/0.75  fof(c_0_13, plain, ![X35, X36]:k1_enumset1(X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.59/0.75  fof(c_0_14, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.59/0.75  fof(c_0_15, plain, ![X37, X38, X39]:k2_enumset1(X37,X37,X38,X39)=k1_enumset1(X37,X38,X39), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.59/0.75  fof(c_0_16, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|X20=X18|X19!=k1_tarski(X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_tarski(X18)))&((~r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)!=X22|X23=k1_tarski(X22))&(r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)=X22|X23=k1_tarski(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.59/0.75  cnf(c_0_17, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.75  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.59/0.75  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.59/0.75  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.75  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.59/0.75  cnf(c_0_22, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.75  fof(c_0_23, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.59/0.75  fof(c_0_24, plain, ![X25, X26, X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X28,X27)|(X28=X25|X28=X26)|X27!=k2_tarski(X25,X26))&((X29!=X25|r2_hidden(X29,X27)|X27!=k2_tarski(X25,X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k2_tarski(X25,X26))))&(((esk3_3(X30,X31,X32)!=X30|~r2_hidden(esk3_3(X30,X31,X32),X32)|X32=k2_tarski(X30,X31))&(esk3_3(X30,X31,X32)!=X31|~r2_hidden(esk3_3(X30,X31,X32),X32)|X32=k2_tarski(X30,X31)))&(r2_hidden(esk3_3(X30,X31,X32),X32)|(esk3_3(X30,X31,X32)=X30|esk3_3(X30,X31,X32)=X31)|X32=k2_tarski(X30,X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.59/0.75  cnf(c_0_25, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_19]), c_0_20]), c_0_21]), c_0_21]), c_0_21])).
% 0.59/0.75  cnf(c_0_26, plain, (esk2_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_18]), c_0_19]), c_0_21])).
% 0.59/0.75  cnf(c_0_27, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.75  cnf(c_0_29, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.75  cnf(c_0_30, negated_conjecture, (esk2_2(X1,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=X1|r2_hidden(esk2_2(X1,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.59/0.75  cnf(c_0_31, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_20])).
% 0.59/0.75  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_21])).
% 0.59/0.75  cnf(c_0_33, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.75  cnf(c_0_34, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k2_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.75  cnf(c_0_35, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_37, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_18]), c_0_19]), c_0_21])).
% 0.59/0.75  cnf(c_0_38, negated_conjecture, (esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk4_0|r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))), inference(er,[status(thm)],[c_0_30])).
% 0.59/0.75  cnf(c_0_39, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_31])).
% 0.59/0.75  cnf(c_0_40, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 0.59/0.75  cnf(c_0_41, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_19]), c_0_21])).
% 0.59/0.75  cnf(c_0_42, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_19]), c_0_19]), c_0_20]), c_0_21]), c_0_21]), c_0_21])).
% 0.59/0.75  cnf(c_0_43, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_35, c_0_20])).
% 0.59/0.75  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.75  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.75  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_47, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_36, c_0_20])).
% 0.59/0.75  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))|~r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_25])).
% 0.59/0.75  cnf(c_0_49, plain, (r2_hidden(X1,k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(k2_enumset1(X1,X1,X1,X2),X3)))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.59/0.75  cnf(c_0_50, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_51, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.59/0.75  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43])])).
% 0.59/0.75  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_19]), c_0_21])).
% 0.59/0.75  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_18]), c_0_19]), c_0_19]), c_0_20]), c_0_21]), c_0_21]), c_0_21])).
% 0.59/0.75  cnf(c_0_55, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_46, c_0_20])).
% 0.59/0.75  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_47])).
% 0.59/0.75  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))|r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.59/0.75  cnf(c_0_58, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_50, c_0_20])).
% 0.59/0.75  cnf(c_0_59, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))=esk5_0|esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))=esk4_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.59/0.75  cnf(c_0_60, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.59/0.75  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))|r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_43])])).
% 0.59/0.75  cnf(c_0_62, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_55])).
% 0.59/0.75  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))|r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.59/0.75  cnf(c_0_64, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])]), c_0_42])).
% 0.59/0.75  cnf(c_0_65, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk5_0|r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_61])).
% 0.59/0.75  fof(c_0_66, plain, ![X40, X41, X42]:(((r2_hidden(X40,X42)|~r1_tarski(k2_tarski(X40,X41),X42))&(r2_hidden(X41,X42)|~r1_tarski(k2_tarski(X40,X41),X42)))&(~r2_hidden(X40,X42)|~r2_hidden(X41,X42)|r1_tarski(k2_tarski(X40,X41),X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.59/0.75  cnf(c_0_67, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_57])).
% 0.59/0.75  cnf(c_0_68, negated_conjecture, (esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk5_0|esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk4_0|r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_63])).
% 0.59/0.75  cnf(c_0_69, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_64]), c_0_40])]), c_0_42])).
% 0.59/0.75  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))|r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_65]), c_0_40]), c_0_60])]), c_0_54])).
% 0.59/0.75  cnf(c_0_71, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.59/0.75  cnf(c_0_72, negated_conjecture, (esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk4_0|r2_hidden(esk4_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.59/0.75  cnf(c_0_73, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.75  cnf(c_0_74, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk5_0|esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_70])).
% 0.59/0.75  fof(c_0_75, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.59/0.75  cnf(c_0_76, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_19]), c_0_21])).
% 0.59/0.75  cnf(c_0_77, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_72]), c_0_25]), c_0_49])).
% 0.59/0.75  cnf(c_0_78, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_73, c_0_20])).
% 0.59/0.75  cnf(c_0_79, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_74]), c_0_40]), c_0_60])]), c_0_54])).
% 0.59/0.75  cnf(c_0_80, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.59/0.75  cnf(c_0_81, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,esk4_0),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.59/0.75  cnf(c_0_82, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.75  cnf(c_0_83, negated_conjecture, (r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_77])]), c_0_54])).
% 0.59/0.75  cnf(c_0_84, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_80, c_0_20])).
% 0.59/0.75  cnf(c_0_85, negated_conjecture, (r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_81, c_0_77])).
% 0.59/0.75  cnf(c_0_86, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_19]), c_0_20]), c_0_21]), c_0_21])).
% 0.59/0.75  cnf(c_0_87, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_83])).
% 0.59/0.75  cnf(c_0_88, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.59/0.75  cnf(c_0_89, negated_conjecture, (r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,X1),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.59/0.75  cnf(c_0_90, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.59/0.75  cnf(c_0_91, negated_conjecture, (r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.59/0.75  cnf(c_0_92, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_91]), c_0_86]), ['proof']).
% 0.59/0.75  # SZS output end CNFRefutation
% 0.59/0.75  # Proof object total steps             : 93
% 0.59/0.75  # Proof object clause steps            : 72
% 0.59/0.75  # Proof object formula steps           : 21
% 0.59/0.75  # Proof object conjectures             : 38
% 0.59/0.75  # Proof object clause conjectures      : 35
% 0.59/0.75  # Proof object formula conjectures     : 3
% 0.59/0.75  # Proof object initial clauses used    : 21
% 0.59/0.75  # Proof object initial formulas used   : 10
% 0.59/0.75  # Proof object generating inferences   : 28
% 0.59/0.75  # Proof object simplifying inferences  : 79
% 0.59/0.75  # Training examples: 0 positive, 0 negative
% 0.59/0.75  # Parsed axioms                        : 11
% 0.59/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.75  # Initial clauses                      : 32
% 0.59/0.75  # Removed in clause preprocessing      : 4
% 0.59/0.75  # Initial clauses in saturation        : 28
% 0.59/0.75  # Processed clauses                    : 1410
% 0.59/0.75  # ...of these trivial                  : 19
% 0.59/0.75  # ...subsumed                          : 730
% 0.59/0.75  # ...remaining for further processing  : 661
% 0.59/0.75  # Other redundant clauses eliminated   : 1093
% 0.59/0.75  # Clauses deleted for lack of memory   : 0
% 0.59/0.75  # Backward-subsumed                    : 98
% 0.59/0.75  # Backward-rewritten                   : 187
% 0.59/0.75  # Generated clauses                    : 26687
% 0.59/0.75  # ...of the previous two non-trivial   : 24541
% 0.59/0.75  # Contextual simplify-reflections      : 22
% 0.59/0.75  # Paramodulations                      : 25552
% 0.59/0.75  # Factorizations                       : 39
% 0.59/0.75  # Equation resolutions                 : 1099
% 0.59/0.75  # Propositional unsat checks           : 0
% 0.59/0.75  #    Propositional check models        : 0
% 0.59/0.75  #    Propositional check unsatisfiable : 0
% 0.59/0.75  #    Propositional clauses             : 0
% 0.59/0.75  #    Propositional clauses after purity: 0
% 0.59/0.75  #    Propositional unsat core size     : 0
% 0.59/0.75  #    Propositional preprocessing time  : 0.000
% 0.59/0.75  #    Propositional encoding time       : 0.000
% 0.59/0.75  #    Propositional solver time         : 0.000
% 0.59/0.75  #    Success case prop preproc time    : 0.000
% 0.59/0.75  #    Success case prop encoding time   : 0.000
% 0.59/0.75  #    Success case prop solver time     : 0.000
% 0.59/0.75  # Current number of processed clauses  : 341
% 0.59/0.75  #    Positive orientable unit clauses  : 27
% 0.59/0.75  #    Positive unorientable unit clauses: 0
% 0.59/0.75  #    Negative unit clauses             : 16
% 0.59/0.75  #    Non-unit-clauses                  : 298
% 0.59/0.75  # Current number of unprocessed clauses: 22988
% 0.59/0.75  # ...number of literals in the above   : 135778
% 0.59/0.75  # Current number of archived formulas  : 0
% 0.59/0.75  # Current number of archived clauses   : 316
% 0.59/0.75  # Clause-clause subsumption calls (NU) : 30406
% 0.59/0.75  # Rec. Clause-clause subsumption calls : 10533
% 0.59/0.75  # Non-unit clause-clause subsumptions  : 753
% 0.59/0.75  # Unit Clause-clause subsumption calls : 1784
% 0.59/0.75  # Rewrite failures with RHS unbound    : 0
% 0.59/0.75  # BW rewrite match attempts            : 114
% 0.59/0.75  # BW rewrite match successes           : 13
% 0.59/0.75  # Condensation attempts                : 0
% 0.59/0.75  # Condensation successes               : 0
% 0.59/0.75  # Termbank termtop insertions          : 747061
% 0.59/0.75  
% 0.59/0.75  # -------------------------------------------------
% 0.59/0.75  # User time                : 0.390 s
% 0.59/0.75  # System time              : 0.019 s
% 0.59/0.75  # Total time               : 0.410 s
% 0.59/0.75  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
