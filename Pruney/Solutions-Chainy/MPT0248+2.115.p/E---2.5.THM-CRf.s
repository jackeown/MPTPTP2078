%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:55 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  123 (17830 expanded)
%              Number of clauses        :   88 (7561 expanded)
%              Number of leaves         :   17 (5054 expanded)
%              Depth                    :   21
%              Number of atoms          :  330 (31787 expanded)
%              Number of equality atoms :  153 (22033 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X68,X69] : k3_tarski(k2_tarski(X68,X69)) = k2_xboole_0(X68,X69) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X57,X58] : k1_enumset1(X57,X57,X58) = k2_tarski(X57,X58) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( r2_hidden(X32,X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X29)
        | r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk4_3(X34,X35,X36),X36)
        | ~ r2_hidden(esk4_3(X34,X35,X36),X34)
        | r2_hidden(esk4_3(X34,X35,X36),X35)
        | X36 = k4_xboole_0(X34,X35) )
      & ( r2_hidden(esk4_3(X34,X35,X36),X34)
        | r2_hidden(esk4_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) )
      & ( ~ r2_hidden(esk4_3(X34,X35,X36),X35)
        | r2_hidden(esk4_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_21,plain,(
    ! [X40,X41] : k4_xboole_0(X40,X41) = k5_xboole_0(X40,k3_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X66,X67] :
      ( ( ~ r1_tarski(X66,k1_tarski(X67))
        | X66 = k1_xboole_0
        | X66 = k1_tarski(X67) )
      & ( X66 != k1_xboole_0
        | r1_tarski(X66,k1_tarski(X67)) )
      & ( X66 != k1_tarski(X67)
        | r1_tarski(X66,k1_tarski(X67)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X56] : k2_tarski(X56,X56) = k1_tarski(X56) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X59,X60,X61] : k2_enumset1(X59,X59,X60,X61) = k1_enumset1(X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X62,X63,X64,X65] : k3_enumset1(X62,X62,X63,X64,X65) = k2_enumset1(X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,negated_conjecture,
    ( k1_tarski(esk7_0) = k2_xboole_0(esk8_0,esk9_0)
    & ( esk8_0 != k1_tarski(esk7_0)
      | esk9_0 != k1_tarski(esk7_0) )
    & ( esk8_0 != k1_xboole_0
      | esk9_0 != k1_tarski(esk7_0) )
    & ( esk8_0 != k1_tarski(esk7_0)
      | esk9_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X44,X45] : k3_xboole_0(X44,k2_xboole_0(X44,X45)) = X44 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_33,plain,(
    ! [X42,X43] :
      ( ~ r1_tarski(X42,X43)
      | k2_xboole_0(X42,X43) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k1_tarski(esk7_0) = k2_xboole_0(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X48] : k5_xboole_0(X48,X48) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | X1 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_28]),c_0_28]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( esk8_0 != k1_tarski(esk7_0)
    | esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k3_tarski(k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_35]),c_0_28]),c_0_40]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_50,plain,
    ( X3 = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_40]),c_0_36]),c_0_37])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_40]),c_0_36]),c_0_37])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_40]),c_0_36]),c_0_37])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_57,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk3_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk3_3(X25,X26,X27),X26)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X26)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_58,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | esk8_0 != k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_35]),c_0_28]),c_0_36]),c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( X1 = k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),esk8_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_60,plain,(
    ! [X38] :
      ( X38 = k1_xboole_0
      | r2_hidden(esk5_1(X38),X38) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_62,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_52]),c_0_53])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,esk9_0,esk8_0),esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,esk8_0),esk8_0)
    | esk9_0 != k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0)
    | r2_hidden(esk5_1(esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

fof(c_0_70,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0)
    | r2_hidden(esk5_1(esk9_0),k3_xboole_0(esk9_0,X1))
    | ~ r2_hidden(esk5_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_1(esk9_0),k3_xboole_0(esk9_0,esk9_0))
    | r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_69])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_3(X1,X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_72]),c_0_53]),c_0_53]),c_0_53]),c_0_67])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_78,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_73])).

cnf(c_0_79,plain,
    ( X3 = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_40]),c_0_36]),c_0_37])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk3_3(esk9_0,esk9_0,k1_xboole_0),esk9_0)
    | r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_67])).

cnf(c_0_81,plain,
    ( X1 = X2
    | r2_hidden(esk5_1(X2),X2)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_66])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_35]),c_0_35]),c_0_28]),c_0_28]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_83,negated_conjecture,
    ( k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = esk9_0
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | esk9_0 != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( esk8_0 != k1_tarski(esk7_0)
    | esk9_0 != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,k1_xboole_0)) = k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)
    | r2_hidden(esk5_1(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_66])).

cnf(c_0_88,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,k1_xboole_0)) = esk8_0
    | r2_hidden(esk3_3(esk9_0,esk9_0,k1_xboole_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_80])).

cnf(c_0_89,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_81]),c_0_67])).

fof(c_0_90,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ( ~ r2_hidden(X51,X50)
        | X51 = X49
        | X50 != k1_tarski(X49) )
      & ( X52 != X49
        | r2_hidden(X52,X50)
        | X50 != k1_tarski(X49) )
      & ( ~ r2_hidden(esk6_2(X53,X54),X54)
        | esk6_2(X53,X54) != X53
        | X54 = k1_tarski(X53) )
      & ( r2_hidden(esk6_2(X53,X54),X54)
        | esk6_2(X53,X54) = X53
        | X54 = k1_tarski(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_92,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk9_0
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)
    | ~ r1_tarski(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | esk9_0 != k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_35]),c_0_28]),c_0_36]),c_0_37])).

cnf(c_0_94,negated_conjecture,
    ( esk8_0 != k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)
    | esk9_0 != k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_35]),c_0_35]),c_0_28]),c_0_28]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_40]),c_0_36]),c_0_37])).

cnf(c_0_96,negated_conjecture,
    ( k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = esk8_0
    | r2_hidden(esk5_1(esk9_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_97,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(esk8_0,k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_100,negated_conjecture,
    ( X1 = esk9_0
    | X1 = k1_xboole_0
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)
    | r2_hidden(esk1_2(X1,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_73])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)
    | esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_83])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)
    | esk9_0 != esk8_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_83])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk5_1(esk9_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_96]),c_0_66])).

cnf(c_0_105,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_35]),c_0_28]),c_0_36]),c_0_37])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_99]),c_0_99]),c_0_99])]),c_0_101]),c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk5_1(esk9_0),k3_tarski(k3_enumset1(X1,X1,X1,X1,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk5_1(esk9_0),k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_49])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_113,negated_conjecture,
    ( esk1_2(esk8_0,esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( esk5_1(esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0)
    | ~ r2_hidden(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk7_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_104,c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])])).

cnf(c_0_118,negated_conjecture,
    ( k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = esk9_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_117]),c_0_49])).

cnf(c_0_119,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk9_0
    | ~ r1_tarski(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_118])])).

cnf(c_0_121,negated_conjecture,
    ( esk9_0 != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_118]),c_0_118])])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_117]),c_0_120]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:50:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.01/4.18  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 4.01/4.18  # and selection function SelectNegativeLiterals.
% 4.01/4.18  #
% 4.01/4.18  # Preprocessing time       : 0.030 s
% 4.01/4.18  # Presaturation interreduction done
% 4.01/4.18  
% 4.01/4.18  # Proof found!
% 4.01/4.18  # SZS status Theorem
% 4.01/4.18  # SZS output start CNFRefutation
% 4.01/4.18  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.01/4.18  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.01/4.18  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.01/4.18  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.01/4.18  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.01/4.18  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.01/4.18  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.01/4.18  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.01/4.18  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.01/4.18  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.01/4.18  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.01/4.18  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.01/4.18  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.01/4.18  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.01/4.18  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.01/4.18  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.01/4.18  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.01/4.18  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 4.01/4.18  fof(c_0_18, plain, ![X68, X69]:k3_tarski(k2_tarski(X68,X69))=k2_xboole_0(X68,X69), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 4.01/4.18  fof(c_0_19, plain, ![X57, X58]:k1_enumset1(X57,X57,X58)=k2_tarski(X57,X58), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.01/4.18  fof(c_0_20, plain, ![X29, X30, X31, X32, X33, X34, X35, X36]:((((r2_hidden(X32,X29)|~r2_hidden(X32,X31)|X31!=k4_xboole_0(X29,X30))&(~r2_hidden(X32,X30)|~r2_hidden(X32,X31)|X31!=k4_xboole_0(X29,X30)))&(~r2_hidden(X33,X29)|r2_hidden(X33,X30)|r2_hidden(X33,X31)|X31!=k4_xboole_0(X29,X30)))&((~r2_hidden(esk4_3(X34,X35,X36),X36)|(~r2_hidden(esk4_3(X34,X35,X36),X34)|r2_hidden(esk4_3(X34,X35,X36),X35))|X36=k4_xboole_0(X34,X35))&((r2_hidden(esk4_3(X34,X35,X36),X34)|r2_hidden(esk4_3(X34,X35,X36),X36)|X36=k4_xboole_0(X34,X35))&(~r2_hidden(esk4_3(X34,X35,X36),X35)|r2_hidden(esk4_3(X34,X35,X36),X36)|X36=k4_xboole_0(X34,X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 4.01/4.18  fof(c_0_21, plain, ![X40, X41]:k4_xboole_0(X40,X41)=k5_xboole_0(X40,k3_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 4.01/4.18  fof(c_0_22, plain, ![X66, X67]:((~r1_tarski(X66,k1_tarski(X67))|(X66=k1_xboole_0|X66=k1_tarski(X67)))&((X66!=k1_xboole_0|r1_tarski(X66,k1_tarski(X67)))&(X66!=k1_tarski(X67)|r1_tarski(X66,k1_tarski(X67))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 4.01/4.18  fof(c_0_23, plain, ![X56]:k2_tarski(X56,X56)=k1_tarski(X56), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.01/4.18  fof(c_0_24, plain, ![X59, X60, X61]:k2_enumset1(X59,X59,X60,X61)=k1_enumset1(X59,X60,X61), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.01/4.18  fof(c_0_25, plain, ![X62, X63, X64, X65]:k3_enumset1(X62,X62,X63,X64,X65)=k2_enumset1(X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 4.01/4.18  fof(c_0_26, negated_conjecture, (((k1_tarski(esk7_0)=k2_xboole_0(esk8_0,esk9_0)&(esk8_0!=k1_tarski(esk7_0)|esk9_0!=k1_tarski(esk7_0)))&(esk8_0!=k1_xboole_0|esk9_0!=k1_tarski(esk7_0)))&(esk8_0!=k1_tarski(esk7_0)|esk9_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 4.01/4.18  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.01/4.18  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.01/4.18  fof(c_0_29, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 4.01/4.18  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.01/4.18  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.01/4.18  fof(c_0_32, plain, ![X44, X45]:k3_xboole_0(X44,k2_xboole_0(X44,X45))=X44, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 4.01/4.18  fof(c_0_33, plain, ![X42, X43]:(~r1_tarski(X42,X43)|k2_xboole_0(X42,X43)=X43), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.01/4.18  cnf(c_0_34, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.01/4.18  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.01/4.18  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.01/4.18  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.01/4.18  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.01/4.18  cnf(c_0_39, negated_conjecture, (k1_tarski(esk7_0)=k2_xboole_0(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.01/4.18  cnf(c_0_40, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 4.01/4.18  cnf(c_0_41, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.01/4.18  cnf(c_0_42, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 4.01/4.18  cnf(c_0_43, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.01/4.18  fof(c_0_44, plain, ![X48]:k5_xboole_0(X48,X48)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 4.01/4.18  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.01/4.18  cnf(c_0_46, plain, (r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))|X1!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_28]), c_0_28]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 4.01/4.18  cnf(c_0_47, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_38, c_0_31])).
% 4.01/4.18  cnf(c_0_48, negated_conjecture, (esk8_0!=k1_tarski(esk7_0)|esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.01/4.18  cnf(c_0_49, negated_conjecture, (k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k3_tarski(k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_35]), c_0_28]), c_0_40]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 4.01/4.18  cnf(c_0_50, plain, (X3=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_40]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_51, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_42])).
% 4.01/4.18  cnf(c_0_52, plain, (k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_40]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_53, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 4.01/4.18  cnf(c_0_54, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_40]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_55, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_46])).
% 4.01/4.18  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_47])).
% 4.01/4.18  fof(c_0_57, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X23,X20)|~r2_hidden(X23,X22)|X22!=k3_xboole_0(X20,X21))&(r2_hidden(X23,X21)|~r2_hidden(X23,X22)|X22!=k3_xboole_0(X20,X21)))&(~r2_hidden(X24,X20)|~r2_hidden(X24,X21)|r2_hidden(X24,X22)|X22!=k3_xboole_0(X20,X21)))&((~r2_hidden(esk3_3(X25,X26,X27),X27)|(~r2_hidden(esk3_3(X25,X26,X27),X25)|~r2_hidden(esk3_3(X25,X26,X27),X26))|X27=k3_xboole_0(X25,X26))&((r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k3_xboole_0(X25,X26))&(r2_hidden(esk3_3(X25,X26,X27),X26)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k3_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 4.01/4.18  cnf(c_0_58, negated_conjecture, (esk9_0!=k1_xboole_0|esk8_0!=k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_35]), c_0_28]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_59, negated_conjecture, (X1=k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)|r2_hidden(esk2_3(esk8_0,esk9_0,X1),esk8_0)|r2_hidden(esk2_3(esk8_0,esk9_0,X1),esk9_0)|r2_hidden(esk2_3(esk8_0,esk9_0,X1),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 4.01/4.18  fof(c_0_60, plain, ![X38]:(X38=k1_xboole_0|r2_hidden(esk5_1(X38),X38)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 4.01/4.18  cnf(c_0_61, plain, (~r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 4.01/4.18  cnf(c_0_62, plain, (k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)))=k3_enumset1(X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 4.01/4.18  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_52]), c_0_53])).
% 4.01/4.18  cnf(c_0_64, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 4.01/4.18  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_3(esk8_0,esk9_0,esk8_0),esk9_0)|r2_hidden(esk2_3(esk8_0,esk9_0,esk8_0),esk8_0)|esk9_0!=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59])])).
% 4.01/4.18  cnf(c_0_66, plain, (X1=k1_xboole_0|r2_hidden(esk5_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 4.01/4.18  cnf(c_0_67, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 4.01/4.18  cnf(c_0_68, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_64])).
% 4.01/4.18  cnf(c_0_69, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0)|r2_hidden(esk5_1(esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 4.01/4.18  fof(c_0_70, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.01/4.18  cnf(c_0_71, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0)|r2_hidden(esk5_1(esk9_0),k3_xboole_0(esk9_0,X1))|~r2_hidden(esk5_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 4.01/4.18  cnf(c_0_72, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 4.01/4.18  cnf(c_0_73, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 4.01/4.18  cnf(c_0_74, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.01/4.18  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_1(esk9_0),k3_xboole_0(esk9_0,esk9_0))|r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_71, c_0_69])).
% 4.01/4.18  cnf(c_0_76, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_3(X1,X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_72]), c_0_53]), c_0_53]), c_0_53]), c_0_67])).
% 4.01/4.18  cnf(c_0_77, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.01/4.18  cnf(c_0_78, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_54, c_0_73])).
% 4.01/4.18  cnf(c_0_79, plain, (X3=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_40]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_80, negated_conjecture, (r2_hidden(esk3_3(esk9_0,esk9_0,k1_xboole_0),esk9_0)|r2_hidden(esk2_3(esk8_0,k1_xboole_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_67])).
% 4.01/4.18  cnf(c_0_81, plain, (X1=X2|r2_hidden(esk5_1(X2),X2)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_66, c_0_66])).
% 4.01/4.18  cnf(c_0_82, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_35]), c_0_35]), c_0_28]), c_0_28]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 4.01/4.18  cnf(c_0_83, negated_conjecture, (k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=esk9_0|r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_49, c_0_78])).
% 4.01/4.18  cnf(c_0_84, negated_conjecture, (esk8_0!=k1_xboole_0|esk9_0!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.01/4.18  cnf(c_0_85, negated_conjecture, (esk8_0!=k1_tarski(esk7_0)|esk9_0!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.01/4.18  cnf(c_0_86, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.01/4.18  cnf(c_0_87, negated_conjecture, (k3_tarski(k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,k1_xboole_0))=k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)|r2_hidden(esk5_1(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_66])).
% 4.01/4.18  cnf(c_0_88, negated_conjecture, (k3_tarski(k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,k1_xboole_0))=esk8_0|r2_hidden(esk3_3(esk9_0,esk9_0,k1_xboole_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_80])).
% 4.01/4.18  cnf(c_0_89, plain, (r2_hidden(esk5_1(X1),X1)|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_81]), c_0_67])).
% 4.01/4.18  fof(c_0_90, plain, ![X49, X50, X51, X52, X53, X54]:(((~r2_hidden(X51,X50)|X51=X49|X50!=k1_tarski(X49))&(X52!=X49|r2_hidden(X52,X50)|X50!=k1_tarski(X49)))&((~r2_hidden(esk6_2(X53,X54),X54)|esk6_2(X53,X54)!=X53|X54=k1_tarski(X53))&(r2_hidden(esk6_2(X53,X54),X54)|esk6_2(X53,X54)=X53|X54=k1_tarski(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 4.01/4.18  cnf(c_0_91, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 4.01/4.18  cnf(c_0_92, negated_conjecture, (X1=k1_xboole_0|X1=esk9_0|r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)|~r1_tarski(X1,esk9_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 4.01/4.18  cnf(c_0_93, negated_conjecture, (esk8_0!=k1_xboole_0|esk9_0!=k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_35]), c_0_28]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_94, negated_conjecture, (esk8_0!=k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)|esk9_0!=k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_35]), c_0_35]), c_0_28]), c_0_28]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 4.01/4.18  cnf(c_0_95, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_40]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_96, negated_conjecture, (k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=esk8_0|r2_hidden(esk5_1(esk9_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 4.01/4.18  cnf(c_0_97, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 4.01/4.18  cnf(c_0_98, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_91])).
% 4.01/4.18  cnf(c_0_99, negated_conjecture, (k3_xboole_0(esk8_0,k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))=esk8_0), inference(spm,[status(thm)],[c_0_52, c_0_49])).
% 4.01/4.18  cnf(c_0_100, negated_conjecture, (X1=esk9_0|X1=k1_xboole_0|r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)|r2_hidden(esk1_2(X1,esk9_0),X1)), inference(spm,[status(thm)],[c_0_92, c_0_73])).
% 4.01/4.18  cnf(c_0_101, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)|esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_83])).
% 4.01/4.18  cnf(c_0_102, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)|esk9_0!=esk8_0), inference(spm,[status(thm)],[c_0_94, c_0_83])).
% 4.01/4.18  cnf(c_0_103, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_95])).
% 4.01/4.18  cnf(c_0_104, negated_conjecture, (r2_hidden(esk5_1(esk9_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_96]), c_0_66])).
% 4.01/4.18  cnf(c_0_105, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_35]), c_0_28]), c_0_36]), c_0_37])).
% 4.01/4.18  cnf(c_0_106, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 4.01/4.18  cnf(c_0_107, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_99]), c_0_99]), c_0_99])]), c_0_101]), c_0_102])).
% 4.01/4.18  cnf(c_0_108, negated_conjecture, (r2_hidden(esk5_1(esk9_0),k3_tarski(k3_enumset1(X1,X1,X1,X1,esk9_0)))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 4.01/4.18  cnf(c_0_109, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_105])).
% 4.01/4.18  cnf(c_0_110, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 4.01/4.18  cnf(c_0_111, negated_conjecture, (r2_hidden(esk5_1(esk9_0),k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_108, c_0_49])).
% 4.01/4.18  cnf(c_0_112, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 4.01/4.18  cnf(c_0_113, negated_conjecture, (esk1_2(esk8_0,esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 4.01/4.18  cnf(c_0_114, negated_conjecture, (esk5_1(esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_109, c_0_111])).
% 4.01/4.18  cnf(c_0_115, negated_conjecture, (r1_tarski(esk8_0,esk9_0)|~r2_hidden(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 4.01/4.18  cnf(c_0_116, negated_conjecture, (r2_hidden(esk7_0,esk9_0)), inference(rw,[status(thm)],[c_0_104, c_0_114])).
% 4.01/4.18  cnf(c_0_117, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])])).
% 4.01/4.18  cnf(c_0_118, negated_conjecture, (k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=esk9_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_117]), c_0_49])).
% 4.01/4.18  cnf(c_0_119, negated_conjecture, (X1=k1_xboole_0|X1=esk9_0|~r1_tarski(X1,esk9_0)), inference(spm,[status(thm)],[c_0_82, c_0_118])).
% 4.01/4.18  cnf(c_0_120, negated_conjecture, (esk8_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_118])])).
% 4.01/4.18  cnf(c_0_121, negated_conjecture, (esk9_0!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_118]), c_0_118])])).
% 4.01/4.18  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_117]), c_0_120]), c_0_121]), ['proof']).
% 4.01/4.18  # SZS output end CNFRefutation
% 4.01/4.18  # Proof object total steps             : 123
% 4.01/4.18  # Proof object clause steps            : 88
% 4.01/4.18  # Proof object formula steps           : 35
% 4.01/4.18  # Proof object conjectures             : 42
% 4.01/4.18  # Proof object clause conjectures      : 39
% 4.01/4.18  # Proof object formula conjectures     : 3
% 4.01/4.18  # Proof object initial clauses used    : 27
% 4.01/4.18  # Proof object initial formulas used   : 17
% 4.01/4.18  # Proof object generating inferences   : 35
% 4.01/4.18  # Proof object simplifying inferences  : 99
% 4.01/4.18  # Training examples: 0 positive, 0 negative
% 4.01/4.18  # Parsed axioms                        : 18
% 4.01/4.18  # Removed by relevancy pruning/SinE    : 0
% 4.01/4.18  # Initial clauses                      : 44
% 4.01/4.18  # Removed in clause preprocessing      : 6
% 4.01/4.18  # Initial clauses in saturation        : 38
% 4.01/4.18  # Processed clauses                    : 9821
% 4.01/4.18  # ...of these trivial                  : 476
% 4.01/4.18  # ...subsumed                          : 7409
% 4.01/4.18  # ...remaining for further processing  : 1936
% 4.01/4.18  # Other redundant clauses eliminated   : 14308
% 4.01/4.18  # Clauses deleted for lack of memory   : 0
% 4.01/4.18  # Backward-subsumed                    : 133
% 4.01/4.18  # Backward-rewritten                   : 639
% 4.01/4.18  # Generated clauses                    : 504975
% 4.01/4.18  # ...of the previous two non-trivial   : 428363
% 4.01/4.18  # Contextual simplify-reflections      : 48
% 4.01/4.18  # Paramodulations                      : 490605
% 4.01/4.18  # Factorizations                       : 59
% 4.01/4.18  # Equation resolutions                 : 14308
% 4.01/4.18  # Propositional unsat checks           : 0
% 4.01/4.18  #    Propositional check models        : 0
% 4.01/4.18  #    Propositional check unsatisfiable : 0
% 4.01/4.18  #    Propositional clauses             : 0
% 4.01/4.18  #    Propositional clauses after purity: 0
% 4.01/4.18  #    Propositional unsat core size     : 0
% 4.01/4.18  #    Propositional preprocessing time  : 0.000
% 4.01/4.18  #    Propositional encoding time       : 0.000
% 4.01/4.18  #    Propositional solver time         : 0.000
% 4.01/4.18  #    Success case prop preproc time    : 0.000
% 4.01/4.18  #    Success case prop encoding time   : 0.000
% 4.01/4.18  #    Success case prop solver time     : 0.000
% 4.01/4.18  # Current number of processed clauses  : 1109
% 4.01/4.18  #    Positive orientable unit clauses  : 93
% 4.01/4.18  #    Positive unorientable unit clauses: 0
% 4.01/4.18  #    Negative unit clauses             : 4
% 4.01/4.18  #    Non-unit-clauses                  : 1012
% 4.01/4.18  # Current number of unprocessed clauses: 416764
% 4.01/4.18  # ...number of literals in the above   : 2223969
% 4.01/4.18  # Current number of archived formulas  : 0
% 4.01/4.18  # Current number of archived clauses   : 820
% 4.01/4.18  # Clause-clause subsumption calls (NU) : 284144
% 4.01/4.18  # Rec. Clause-clause subsumption calls : 131095
% 4.01/4.18  # Non-unit clause-clause subsumptions  : 7061
% 4.01/4.18  # Unit Clause-clause subsumption calls : 30653
% 4.01/4.18  # Rewrite failures with RHS unbound    : 0
% 4.01/4.18  # BW rewrite match attempts            : 370
% 4.01/4.18  # BW rewrite match successes           : 83
% 4.01/4.18  # Condensation attempts                : 0
% 4.01/4.18  # Condensation successes               : 0
% 4.01/4.18  # Termbank termtop insertions          : 11085848
% 4.01/4.19  
% 4.01/4.19  # -------------------------------------------------
% 4.01/4.19  # User time                : 3.672 s
% 4.01/4.19  # System time              : 0.182 s
% 4.01/4.19  # Total time               : 3.854 s
% 4.01/4.19  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
