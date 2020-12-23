%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 (5558 expanded)
%              Number of clauses        :   70 (2376 expanded)
%              Number of leaves         :    8 (1537 expanded)
%              Depth                    :   20
%              Number of atoms          :  209 (14489 expanded)
%              Number of equality atoms :  109 (9691 expanded)
%              Maximal formula depth    :   17 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X17
        | X20 = X18
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( esk2_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk2_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | esk2_3(X22,X23,X24) = X22
        | esk2_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0)
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk4_0)
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
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

cnf(c_0_16,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_17]),c_0_17]),c_0_21]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_25,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_30,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_17]),c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_17]),c_0_17]),c_0_21]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_37,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk4_0
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_38,c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])]),c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk4_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_42])]),c_0_36])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_48,c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_17]),c_0_21]),c_0_18]),c_0_18])).

cnf(c_0_56,plain,
    ( X1 = X2
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X2)
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_58,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_52]),c_0_41]),c_0_42])]),c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_41])]),c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56])]),c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_25])]),c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_24]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_20]),c_0_17]),c_0_17]),c_0_21]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0) = esk4_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_25])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk4_0
    | esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k1_xboole_0) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk4_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_73]),c_0_57]),c_0_60]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_75]),c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_80,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_77])])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_80]),c_0_41]),c_0_41])]),c_0_66]),c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_83]),c_0_41]),c_0_41])]),c_0_66]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_85]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:10:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.47  # and selection function SelectNegativeLiterals.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.027 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t74_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 0.20/0.47  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.47  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.47  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.47  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t74_zfmisc_1])).
% 0.20/0.47  fof(c_0_9, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X20,X19)|(X20=X17|X20=X18)|X19!=k2_tarski(X17,X18))&((X21!=X17|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))))&(((esk2_3(X22,X23,X24)!=X22|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23))&(esk2_3(X22,X23,X24)!=X23|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23)))&(r2_hidden(esk2_3(X22,X23,X24),X24)|(esk2_3(X22,X23,X24)=X22|esk2_3(X22,X23,X24)=X23)|X24=k2_tarski(X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.47  fof(c_0_10, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.47  fof(c_0_11, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.47  fof(c_0_12, negated_conjecture, (((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0))&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk4_0))&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.47  fof(c_0_13, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.47  fof(c_0_14, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.47  fof(c_0_15, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.47  cnf(c_0_16, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.47  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.47  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  cnf(c_0_22, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  cnf(c_0_23, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.47  cnf(c_0_24, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_17]), c_0_17]), c_0_21]), c_0_18]), c_0_18]), c_0_18])).
% 0.20/0.47  cnf(c_0_25, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.20/0.47  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_28, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  fof(c_0_30, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.47  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  cnf(c_0_32, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25])])).
% 0.20/0.47  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_17]), c_0_18])).
% 0.20/0.47  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_18])).
% 0.20/0.47  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_17]), c_0_17]), c_0_21]), c_0_18]), c_0_18]), c_0_18])).
% 0.20/0.47  cnf(c_0_37, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_21])).
% 0.20/0.47  cnf(c_0_38, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.47  cnf(c_0_39, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_31, c_0_21])).
% 0.20/0.47  cnf(c_0_40, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk4_0|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.47  cnf(c_0_41, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.20/0.47  cnf(c_0_42, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.20/0.47  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_25])])).
% 0.20/0.47  cnf(c_0_44, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.47  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_38, c_0_21])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])]), c_0_24])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_43])).
% 0.20/0.47  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_50, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.47  cnf(c_0_51, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  cnf(c_0_52, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk4_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_46])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_42])]), c_0_36])).
% 0.20/0.47  cnf(c_0_54, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_48, c_0_21])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_17]), c_0_21]), c_0_18]), c_0_18])).
% 0.20/0.47  cnf(c_0_56, plain, (X1=X2|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X2)|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_25])).
% 0.20/0.47  cnf(c_0_57, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 0.20/0.47  cnf(c_0_58, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_51, c_0_21])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_52]), c_0_41]), c_0_42])]), c_0_24])).
% 0.20/0.47  cnf(c_0_60, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_53]), c_0_41])]), c_0_36])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_54])).
% 0.20/0.47  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56])]), c_0_57])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_25])]), c_0_57])).
% 0.20/0.47  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_24]), c_0_60])).
% 0.20/0.47  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_20]), c_0_17]), c_0_17]), c_0_21]), c_0_18]), c_0_18]), c_0_18])).
% 0.20/0.47  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.47  cnf(c_0_68, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0)=esk4_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0)=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_64])).
% 0.20/0.47  cnf(c_0_69, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_65])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_25])])).
% 0.20/0.47  cnf(c_0_71, negated_conjecture, (~r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_63])).
% 0.20/0.47  cnf(c_0_72, negated_conjecture, (esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk4_0|esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_67])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k1_xboole_0)=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.47  cnf(c_0_74, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_69])).
% 0.20/0.47  cnf(c_0_75, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk4_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_70])).
% 0.20/0.47  cnf(c_0_76, negated_conjecture, (esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_73]), c_0_57]), c_0_60]), c_0_74])).
% 0.20/0.47  cnf(c_0_78, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|~r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_75]), c_0_66])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.20/0.47  cnf(c_0_80, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_77])])).
% 0.20/0.47  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_71, c_0_79])).
% 0.20/0.47  cnf(c_0_82, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_80]), c_0_41]), c_0_41])]), c_0_66]), c_0_81])).
% 0.20/0.47  cnf(c_0_83, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_82])).
% 0.20/0.47  cnf(c_0_84, negated_conjecture, (r2_hidden(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_83]), c_0_41]), c_0_41])]), c_0_66]), c_0_81])).
% 0.20/0.47  cnf(c_0_85, negated_conjecture, (esk4_0=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_84])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_85]), c_0_81]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 87
% 0.20/0.47  # Proof object clause steps            : 70
% 0.20/0.47  # Proof object formula steps           : 17
% 0.20/0.47  # Proof object conjectures             : 43
% 0.20/0.47  # Proof object clause conjectures      : 40
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 17
% 0.20/0.47  # Proof object initial formulas used   : 8
% 0.20/0.47  # Proof object generating inferences   : 31
% 0.20/0.47  # Proof object simplifying inferences  : 87
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 8
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 21
% 0.20/0.47  # Removed in clause preprocessing      : 4
% 0.20/0.47  # Initial clauses in saturation        : 17
% 0.20/0.47  # Processed clauses                    : 339
% 0.20/0.47  # ...of these trivial                  : 16
% 0.20/0.47  # ...subsumed                          : 138
% 0.20/0.47  # ...remaining for further processing  : 185
% 0.20/0.47  # Other redundant clauses eliminated   : 161
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 12
% 0.20/0.47  # Backward-rewritten                   : 82
% 0.20/0.47  # Generated clauses                    : 5910
% 0.20/0.47  # ...of the previous two non-trivial   : 5524
% 0.20/0.47  # Contextual simplify-reflections      : 3
% 0.20/0.47  # Paramodulations                      : 5731
% 0.20/0.47  # Factorizations                       : 18
% 0.20/0.47  # Equation resolutions                 : 161
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 66
% 0.20/0.47  #    Positive orientable unit clauses  : 7
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 2
% 0.20/0.47  #    Non-unit-clauses                  : 57
% 0.20/0.47  # Current number of unprocessed clauses: 5174
% 0.20/0.47  # ...number of literals in the above   : 23763
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 117
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 3785
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 2465
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 77
% 0.20/0.47  # Unit Clause-clause subsumption calls : 333
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 20
% 0.20/0.47  # BW rewrite match successes           : 8
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 130761
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.133 s
% 0.20/0.47  # System time              : 0.005 s
% 0.20/0.47  # Total time               : 0.138 s
% 0.20/0.47  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
