%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:03 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  107 (3627 expanded)
%              Number of clauses        :   86 (1519 expanded)
%              Number of leaves         :   10 (1019 expanded)
%              Depth                    :   19
%              Number of atoms          :  290 (9212 expanded)
%              Number of equality atoms :  130 (6272 expanded)
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

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t73_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X21,X20)
        | X21 = X18
        | X21 = X19
        | X20 != k2_tarski(X18,X19) )
      & ( X22 != X18
        | r2_hidden(X22,X20)
        | X20 != k2_tarski(X18,X19) )
      & ( X22 != X19
        | r2_hidden(X22,X20)
        | X20 != k2_tarski(X18,X19) )
      & ( esk2_3(X23,X24,X25) != X23
        | ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k2_tarski(X23,X24) )
      & ( esk2_3(X23,X24,X25) != X24
        | ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k2_tarski(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X25)
        | esk2_3(X23,X24,X25) = X23
        | esk2_3(X23,X24,X25) = X24
        | X25 = k2_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k1_enumset1(X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0)
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk4_0)
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_15,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_19]),c_0_19]),c_0_23]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_27,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_20])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_19]),c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_19]),c_0_19]),c_0_23]),c_0_20]),c_0_20]),c_0_20])).

fof(c_0_37,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,X35)
        | ~ r1_tarski(k2_tarski(X33,X34),X35) )
      & ( r2_hidden(X34,X35)
        | ~ r1_tarski(k2_tarski(X33,X34),X35) )
      & ( ~ r2_hidden(X33,X35)
        | ~ r2_hidden(X34,X35)
        | r1_tarski(k2_tarski(X33,X34),X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_38,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk4_0
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27])])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_42])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_19]),c_0_20])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk4_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_45]),c_0_41])]),c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | esk2_3(X1,X2,X3) = X1
    | esk2_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_52,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X1))
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_54,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_48]),c_0_40]),c_0_41])]),c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_49]),c_0_40])]),c_0_36])).

fof(c_0_57,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) != k1_xboole_0 )
      & ( r2_hidden(X37,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) != k1_xboole_0 )
      & ( ~ r2_hidden(X36,X38)
        | ~ r2_hidden(X37,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_22]),c_0_19]),c_0_19]),c_0_23]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_59,plain,
    ( esk2_3(X1,X2,X3) = X2
    | esk2_3(X1,X2,X3) = X1
    | X3 = k2_enumset1(X1,X1,X1,X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_19]),c_0_20])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_26]),c_0_56])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X3))
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_tarski(X1,X3),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk2_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( esk2_3(X1,X2,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = X1
    | esk2_3(X1,X2,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = X2
    | r2_hidden(esk2_3(X1,X2,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))
    | k2_enumset1(X1,X1,X1,X2) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_23])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | ~ r1_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_63])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_40])).

cnf(c_0_73,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X3),k3_xboole_0(k2_enumset1(X1,X1,X1,X3),X2)) = k1_xboole_0
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_19]),c_0_23]),c_0_20]),c_0_20])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,plain,
    ( X3 = k2_enumset1(X1,X1,X1,X2)
    | esk2_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_19]),c_0_20])).

cnf(c_0_76,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0
    | r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | k5_xboole_0(k2_enumset1(X3,X3,X3,X1),k3_xboole_0(k2_enumset1(X3,X3,X3,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_19]),c_0_23]),c_0_20]),c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,X1),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,X1),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0
    | r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_63])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_74,c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))
    | ~ r2_hidden(esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_58])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(k2_enumset1(X1,X1,X1,X2),X3)))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_40])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),X1)
    | r2_hidden(esk4_0,esk5_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_63])).

cnf(c_0_87,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_81,c_0_23])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_42]),c_0_42])]),c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_71])).

cnf(c_0_95,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk4_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk4_0
    | esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_100,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,X1),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,X1),esk5_0)) = k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_99]),c_0_58]),c_0_84])).

cnf(c_0_104,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_100]),c_0_100])])).

cnf(c_0_105,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_19]),c_0_23]),c_0_20]),c_0_20])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_104]),c_0_105]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:17:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.93  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.78/0.93  # and selection function SelectNegativeLiterals.
% 0.78/0.93  #
% 0.78/0.93  # Preprocessing time       : 0.027 s
% 0.78/0.93  # Presaturation interreduction done
% 0.78/0.93  
% 0.78/0.93  # Proof found!
% 0.78/0.93  # SZS status Theorem
% 0.78/0.93  # SZS output start CNFRefutation
% 0.78/0.93  fof(t74_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 0.78/0.93  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.78/0.93  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.78/0.93  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.78/0.93  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.78/0.93  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.78/0.93  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.78/0.93  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.78/0.93  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.78/0.93  fof(t73_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 0.78/0.93  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t74_zfmisc_1])).
% 0.78/0.93  fof(c_0_11, plain, ![X18, X19, X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X21,X20)|(X21=X18|X21=X19)|X20!=k2_tarski(X18,X19))&((X22!=X18|r2_hidden(X22,X20)|X20!=k2_tarski(X18,X19))&(X22!=X19|r2_hidden(X22,X20)|X20!=k2_tarski(X18,X19))))&(((esk2_3(X23,X24,X25)!=X23|~r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k2_tarski(X23,X24))&(esk2_3(X23,X24,X25)!=X24|~r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k2_tarski(X23,X24)))&(r2_hidden(esk2_3(X23,X24,X25),X25)|(esk2_3(X23,X24,X25)=X23|esk2_3(X23,X24,X25)=X24)|X25=k2_tarski(X23,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.78/0.93  fof(c_0_12, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.78/0.93  fof(c_0_13, plain, ![X30, X31, X32]:k2_enumset1(X30,X30,X31,X32)=k1_enumset1(X30,X31,X32), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.78/0.93  fof(c_0_14, negated_conjecture, (((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0))&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk4_0))&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.78/0.93  fof(c_0_15, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.78/0.93  fof(c_0_16, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.78/0.93  fof(c_0_17, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.78/0.93  cnf(c_0_18, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.93  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.78/0.93  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.93  cnf(c_0_21, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.93  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.93  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.93  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.93  cnf(c_0_25, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.78/0.93  cnf(c_0_26, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_19]), c_0_19]), c_0_23]), c_0_20]), c_0_20]), c_0_20])).
% 0.78/0.93  cnf(c_0_27, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.78/0.93  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.93  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.93  cnf(c_0_30, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.93  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.93  cnf(c_0_32, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.78/0.93  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 0.78/0.93  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_20])).
% 0.78/0.93  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_19]), c_0_20])).
% 0.78/0.93  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_19]), c_0_19]), c_0_23]), c_0_20]), c_0_20]), c_0_20])).
% 0.78/0.93  fof(c_0_37, plain, ![X33, X34, X35]:(((r2_hidden(X33,X35)|~r1_tarski(k2_tarski(X33,X34),X35))&(r2_hidden(X34,X35)|~r1_tarski(k2_tarski(X33,X34),X35)))&(~r2_hidden(X33,X35)|~r2_hidden(X34,X35)|r1_tarski(k2_tarski(X33,X34),X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.78/0.93  cnf(c_0_38, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_31, c_0_23])).
% 0.78/0.93  cnf(c_0_39, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk4_0|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.78/0.93  cnf(c_0_40, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.78/0.93  cnf(c_0_41, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.78/0.93  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27])])).
% 0.78/0.93  cnf(c_0_43, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.78/0.93  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])]), c_0_26])).
% 0.78/0.93  cnf(c_0_45, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_42])).
% 0.78/0.93  cnf(c_0_46, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_19]), c_0_20])).
% 0.78/0.93  cnf(c_0_47, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.93  cnf(c_0_48, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk4_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.78/0.93  cnf(c_0_49, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_45]), c_0_41])]), c_0_36])).
% 0.78/0.93  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.93  cnf(c_0_51, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|esk2_3(X1,X2,X3)=X1|esk2_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.93  fof(c_0_52, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.78/0.93  cnf(c_0_53, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X1))|~r2_hidden(X2,k2_enumset1(X3,X3,X3,X1))), inference(spm,[status(thm)],[c_0_46, c_0_41])).
% 0.78/0.93  cnf(c_0_54, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_47, c_0_23])).
% 0.78/0.93  cnf(c_0_55, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_48]), c_0_40]), c_0_41])]), c_0_26])).
% 0.78/0.93  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_49]), c_0_40])]), c_0_36])).
% 0.78/0.93  fof(c_0_57, plain, ![X36, X37, X38]:(((r2_hidden(X36,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)!=k1_xboole_0)&(r2_hidden(X37,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)!=k1_xboole_0))&(~r2_hidden(X36,X38)|~r2_hidden(X37,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).
% 0.78/0.93  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_22]), c_0_19]), c_0_19]), c_0_23]), c_0_20]), c_0_20]), c_0_20])).
% 0.78/0.93  cnf(c_0_59, plain, (esk2_3(X1,X2,X3)=X2|esk2_3(X1,X2,X3)=X1|X3=k2_enumset1(X1,X1,X1,X2)|r2_hidden(esk2_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_19]), c_0_20])).
% 0.78/0.93  cnf(c_0_60, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.93  cnf(c_0_61, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.78/0.93  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_42])).
% 0.78/0.93  cnf(c_0_63, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_26]), c_0_56])).
% 0.78/0.93  cnf(c_0_64, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X3))|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X3))), inference(spm,[status(thm)],[c_0_46, c_0_40])).
% 0.78/0.93  cnf(c_0_65, plain, (k4_xboole_0(k2_tarski(X1,X3),X2)=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.78/0.93  cnf(c_0_66, plain, (X3=k2_tarski(X1,X2)|esk2_3(X1,X2,X3)!=X2|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.93  cnf(c_0_67, negated_conjecture, (esk2_3(X1,X2,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=X1|esk2_3(X1,X2,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=X2|r2_hidden(esk2_3(X1,X2,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))|k2_enumset1(X1,X1,X1,X2)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.78/0.93  cnf(c_0_68, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_60, c_0_23])).
% 0.78/0.93  cnf(c_0_69, plain, (r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.78/0.93  cnf(c_0_70, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|~r1_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.78/0.93  cnf(c_0_71, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_63])).
% 0.78/0.93  cnf(c_0_72, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_64, c_0_40])).
% 0.78/0.93  cnf(c_0_73, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X3),k3_xboole_0(k2_enumset1(X1,X1,X1,X3),X2))=k1_xboole_0|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_19]), c_0_23]), c_0_20]), c_0_20])).
% 0.78/0.93  cnf(c_0_74, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.93  cnf(c_0_75, plain, (X3=k2_enumset1(X1,X1,X1,X2)|esk2_3(X1,X2,X3)!=X2|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_19]), c_0_20])).
% 0.78/0.93  cnf(c_0_76, negated_conjecture, (esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0|r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))), inference(er,[status(thm)],[c_0_67])).
% 0.78/0.93  cnf(c_0_77, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_68])).
% 0.78/0.93  cnf(c_0_78, plain, (r2_hidden(X1,X2)|k5_xboole_0(k2_enumset1(X3,X3,X3,X1),k3_xboole_0(k2_enumset1(X3,X3,X3,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_19]), c_0_23]), c_0_20]), c_0_20])).
% 0.78/0.93  cnf(c_0_79, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.78/0.93  cnf(c_0_80, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,X1),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,X1),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0|r2_hidden(esk4_0,esk5_0)|~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_73, c_0_63])).
% 0.78/0.93  cnf(c_0_81, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.93  cnf(c_0_82, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_74, c_0_23])).
% 0.78/0.93  cnf(c_0_83, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))|~r2_hidden(esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_58])).
% 0.78/0.93  cnf(c_0_84, plain, (r2_hidden(X1,k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(k2_enumset1(X1,X1,X1,X2),X3)))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_77, c_0_40])).
% 0.78/0.93  cnf(c_0_85, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),X1)|r2_hidden(esk4_0,esk5_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.78/0.93  cnf(c_0_86, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_80, c_0_63])).
% 0.78/0.93  cnf(c_0_87, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_81, c_0_23])).
% 0.78/0.93  cnf(c_0_88, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_82])).
% 0.78/0.93  cnf(c_0_89, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.78/0.93  cnf(c_0_90, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_42]), c_0_42])]), c_0_36])).
% 0.78/0.93  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.78/0.93  cnf(c_0_92, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_87])).
% 0.78/0.93  cnf(c_0_93, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.78/0.93  cnf(c_0_94, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_71])).
% 0.78/0.93  cnf(c_0_95, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk4_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_91])).
% 0.78/0.93  cnf(c_0_96, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0)), inference(spm,[status(thm)],[c_0_92, c_0_89])).
% 0.78/0.93  cnf(c_0_97, negated_conjecture, (esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk4_0|esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_93])).
% 0.78/0.93  cnf(c_0_98, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.78/0.93  cnf(c_0_99, negated_conjecture, (esk2_3(esk3_0,esk3_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0|r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 0.78/0.93  cnf(c_0_100, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 0.78/0.93  cnf(c_0_101, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.93  cnf(c_0_102, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,X1),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,X1),esk5_0))=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_98])).
% 0.78/0.93  cnf(c_0_103, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_99]), c_0_58]), c_0_84])).
% 0.78/0.93  cnf(c_0_104, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_100]), c_0_100])])).
% 0.78/0.93  cnf(c_0_105, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_19]), c_0_23]), c_0_20]), c_0_20])).
% 0.78/0.93  cnf(c_0_106, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_104]), c_0_105]), ['proof']).
% 0.78/0.93  # SZS output end CNFRefutation
% 0.78/0.93  # Proof object total steps             : 107
% 0.78/0.93  # Proof object clause steps            : 86
% 0.78/0.93  # Proof object formula steps           : 21
% 0.78/0.93  # Proof object conjectures             : 44
% 0.78/0.93  # Proof object clause conjectures      : 41
% 0.78/0.93  # Proof object formula conjectures     : 3
% 0.78/0.93  # Proof object initial clauses used    : 23
% 0.78/0.93  # Proof object initial formulas used   : 10
% 0.78/0.93  # Proof object generating inferences   : 39
% 0.78/0.93  # Proof object simplifying inferences  : 91
% 0.78/0.93  # Training examples: 0 positive, 0 negative
% 0.78/0.93  # Parsed axioms                        : 10
% 0.78/0.93  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.93  # Initial clauses                      : 29
% 0.78/0.93  # Removed in clause preprocessing      : 4
% 0.78/0.93  # Initial clauses in saturation        : 25
% 0.78/0.93  # Processed clauses                    : 1833
% 0.78/0.93  # ...of these trivial                  : 43
% 0.78/0.93  # ...subsumed                          : 1007
% 0.78/0.93  # ...remaining for further processing  : 783
% 0.78/0.93  # Other redundant clauses eliminated   : 767
% 0.78/0.93  # Clauses deleted for lack of memory   : 0
% 0.78/0.93  # Backward-subsumed                    : 204
% 0.78/0.93  # Backward-rewritten                   : 97
% 0.78/0.93  # Generated clauses                    : 38942
% 0.78/0.93  # ...of the previous two non-trivial   : 35915
% 0.78/0.93  # Contextual simplify-reflections      : 28
% 0.78/0.93  # Paramodulations                      : 38026
% 0.78/0.93  # Factorizations                       : 148
% 0.78/0.93  # Equation resolutions                 : 770
% 0.78/0.93  # Propositional unsat checks           : 0
% 0.78/0.93  #    Propositional check models        : 0
% 0.78/0.93  #    Propositional check unsatisfiable : 0
% 0.78/0.93  #    Propositional clauses             : 0
% 0.78/0.93  #    Propositional clauses after purity: 0
% 0.78/0.93  #    Propositional unsat core size     : 0
% 0.78/0.93  #    Propositional preprocessing time  : 0.000
% 0.78/0.93  #    Propositional encoding time       : 0.000
% 0.78/0.93  #    Propositional solver time         : 0.000
% 0.78/0.93  #    Success case prop preproc time    : 0.000
% 0.78/0.93  #    Success case prop encoding time   : 0.000
% 0.78/0.93  #    Success case prop solver time     : 0.000
% 0.78/0.93  # Current number of processed clauses  : 450
% 0.78/0.93  #    Positive orientable unit clauses  : 30
% 0.78/0.93  #    Positive unorientable unit clauses: 1
% 0.78/0.93  #    Negative unit clauses             : 10
% 0.78/0.93  #    Non-unit-clauses                  : 409
% 0.78/0.93  # Current number of unprocessed clauses: 33640
% 0.78/0.93  # ...number of literals in the above   : 222581
% 0.78/0.93  # Current number of archived formulas  : 0
% 0.78/0.93  # Current number of archived clauses   : 329
% 0.78/0.93  # Clause-clause subsumption calls (NU) : 38372
% 0.78/0.93  # Rec. Clause-clause subsumption calls : 14129
% 0.78/0.93  # Non-unit clause-clause subsumptions  : 1176
% 0.78/0.93  # Unit Clause-clause subsumption calls : 1576
% 0.78/0.93  # Rewrite failures with RHS unbound    : 0
% 0.78/0.93  # BW rewrite match attempts            : 121
% 0.78/0.93  # BW rewrite match successes           : 48
% 0.78/0.93  # Condensation attempts                : 0
% 0.78/0.93  # Condensation successes               : 0
% 0.78/0.93  # Termbank termtop insertions          : 1162639
% 0.78/0.93  
% 0.78/0.93  # -------------------------------------------------
% 0.78/0.93  # User time                : 0.578 s
% 0.78/0.93  # System time              : 0.021 s
% 0.78/0.93  # Total time               : 0.598 s
% 0.78/0.93  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
