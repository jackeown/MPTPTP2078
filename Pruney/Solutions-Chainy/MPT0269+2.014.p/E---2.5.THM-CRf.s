%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:29 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 308 expanded)
%              Number of clauses        :   41 ( 130 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 554 expanded)
%              Number of equality atoms :   79 ( 381 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t66_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
        & X1 != k1_xboole_0
        & X1 != k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_16,plain,(
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

fof(c_0_17,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
          & X1 != k1_xboole_0
          & X1 != k1_tarski(X2) ) ),
    inference(assume_negation,[status(cth)],[t66_zfmisc_1])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk4_0 != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_23,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_26,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X27] : k3_xboole_0(X27,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_34,plain,(
    ! [X30] : k5_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_35,plain,(
    ! [X19] :
      ( X19 = k1_xboole_0
      | r2_hidden(esk2_1(X19),X19) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_36,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X31
        | X32 != k1_tarski(X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k1_tarski(X31) )
      & ( ~ r2_hidden(esk3_2(X35,X36),X36)
        | esk3_2(X35,X36) != X35
        | X36 = k1_tarski(X35) )
      & ( r2_hidden(esk3_2(X35,X36),X36)
        | esk3_2(X35,X36) = X35
        | X36 = k1_tarski(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_20]),c_0_32])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X18)
        | r2_hidden(X16,X17)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X44,X45,X46] :
      ( ( r2_hidden(X44,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( r2_hidden(X45,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( ~ r2_hidden(X44,X46)
        | ~ r2_hidden(X45,X46)
        | r1_tarski(k2_tarski(X44,X45),X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_47,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k5_xboole_0(X1,esk4_0))
    | r2_hidden(esk2_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_31]),c_0_32])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_51])])).

fof(c_0_59,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(X23,X24) != k1_xboole_0
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | k4_xboole_0(X23,X24) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,esk2_1(esk4_0)),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( esk2_1(esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_63,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,esk5_0),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_61])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_20])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_49])).

cnf(c_0_68,negated_conjecture,
    ( esk4_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_49]),c_0_67])])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.42  # and selection function SelectNegativeLiterals.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.028 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.21/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.42  fof(t66_zfmisc_1, conjecture, ![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 0.21/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.42  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.42  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.42  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.42  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.42  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.21/0.42  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.21/0.42  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.42  fof(c_0_16, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.21/0.42  fof(c_0_17, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.42  fof(c_0_18, negated_conjecture, ~(![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t66_zfmisc_1])).
% 0.21/0.42  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  fof(c_0_21, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.42  fof(c_0_22, negated_conjecture, ((k4_xboole_0(esk4_0,k1_tarski(esk5_0))=k1_xboole_0&esk4_0!=k1_xboole_0)&esk4_0!=k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.21/0.42  fof(c_0_23, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.42  fof(c_0_24, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.42  fof(c_0_25, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.42  cnf(c_0_26, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.42  fof(c_0_27, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.42  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_29, negated_conjecture, (k4_xboole_0(esk4_0,k1_tarski(esk5_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.42  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.42  fof(c_0_33, plain, ![X27]:k3_xboole_0(X27,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.42  fof(c_0_34, plain, ![X30]:k5_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.42  fof(c_0_35, plain, ![X19]:(X19=k1_xboole_0|r2_hidden(esk2_1(X19),X19)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.42  fof(c_0_36, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|X33=X31|X32!=k1_tarski(X31))&(X34!=X31|r2_hidden(X34,X32)|X32!=k1_tarski(X31)))&((~r2_hidden(esk3_2(X35,X36),X36)|esk3_2(X35,X36)!=X35|X36=k1_tarski(X35))&(r2_hidden(esk3_2(X35,X36),X36)|esk3_2(X35,X36)=X35|X36=k1_tarski(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.42  cnf(c_0_37, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_26])).
% 0.21/0.42  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.42  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_20])).
% 0.21/0.42  cnf(c_0_40, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_20]), c_0_32])).
% 0.21/0.42  cnf(c_0_41, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.42  cnf(c_0_42, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.42  fof(c_0_43, plain, ![X16, X17, X18]:(((~r2_hidden(X16,X17)|~r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18)))&(r2_hidden(X16,X17)|r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18))))&((~r2_hidden(X16,X17)|r2_hidden(X16,X18)|r2_hidden(X16,k5_xboole_0(X17,X18)))&(~r2_hidden(X16,X18)|r2_hidden(X16,X17)|r2_hidden(X16,k5_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.21/0.42  cnf(c_0_44, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.42  fof(c_0_46, plain, ![X44, X45, X46]:(((r2_hidden(X44,X46)|~r1_tarski(k2_tarski(X44,X45),X46))&(r2_hidden(X45,X46)|~r1_tarski(k2_tarski(X44,X45),X46)))&(~r2_hidden(X44,X46)|~r2_hidden(X45,X46)|r1_tarski(k2_tarski(X44,X45),X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.21/0.42  cnf(c_0_47, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_48, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.42  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])).
% 0.21/0.42  cnf(c_0_50, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.42  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.42  cnf(c_0_52, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.42  cnf(c_0_53, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_30]), c_0_31]), c_0_32])).
% 0.21/0.42  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.42  cnf(c_0_55, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k5_xboole_0(X1,esk4_0))|r2_hidden(esk2_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.42  cnf(c_0_56, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_31]), c_0_32])).
% 0.21/0.42  cnf(c_0_57, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_53])).
% 0.21/0.42  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_51])])).
% 0.21/0.42  fof(c_0_59, plain, ![X23, X24]:((k4_xboole_0(X23,X24)!=k1_xboole_0|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|k4_xboole_0(X23,X24)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.42  cnf(c_0_60, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,esk2_1(esk4_0)),esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 0.21/0.42  cnf(c_0_61, negated_conjecture, (esk2_1(esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.42  cnf(c_0_62, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.42  fof(c_0_63, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.42  cnf(c_0_64, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,esk5_0),esk4_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.42  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_51, c_0_61])).
% 0.21/0.42  cnf(c_0_66, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_20])).
% 0.21/0.42  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_40, c_0_49])).
% 0.21/0.42  cnf(c_0_68, negated_conjecture, (esk4_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.42  cnf(c_0_70, negated_conjecture, (r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.42  cnf(c_0_71, negated_conjecture, (r1_tarski(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_49]), c_0_67])])).
% 0.21/0.42  cnf(c_0_72, negated_conjecture, (esk4_0!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_30]), c_0_31]), c_0_32])).
% 0.21/0.42  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), c_0_72]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 74
% 0.21/0.42  # Proof object clause steps            : 41
% 0.21/0.42  # Proof object formula steps           : 33
% 0.21/0.42  # Proof object conjectures             : 21
% 0.21/0.42  # Proof object clause conjectures      : 18
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 18
% 0.21/0.42  # Proof object initial formulas used   : 16
% 0.21/0.42  # Proof object generating inferences   : 11
% 0.21/0.42  # Proof object simplifying inferences  : 30
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 16
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 34
% 0.21/0.42  # Removed in clause preprocessing      : 4
% 0.21/0.42  # Initial clauses in saturation        : 30
% 0.21/0.42  # Processed clauses                    : 623
% 0.21/0.42  # ...of these trivial                  : 24
% 0.21/0.42  # ...subsumed                          : 435
% 0.21/0.42  # ...remaining for further processing  : 164
% 0.21/0.42  # Other redundant clauses eliminated   : 56
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 0
% 0.21/0.42  # Backward-rewritten                   : 26
% 0.21/0.42  # Generated clauses                    : 2991
% 0.21/0.42  # ...of the previous two non-trivial   : 2369
% 0.21/0.42  # Contextual simplify-reflections      : 0
% 0.21/0.42  # Paramodulations                      : 2936
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 56
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 102
% 0.21/0.42  #    Positive orientable unit clauses  : 21
% 0.21/0.42  #    Positive unorientable unit clauses: 1
% 0.21/0.42  #    Negative unit clauses             : 3
% 0.21/0.42  #    Non-unit-clauses                  : 77
% 0.21/0.42  # Current number of unprocessed clauses: 1756
% 0.21/0.42  # ...number of literals in the above   : 5397
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 59
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 3189
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 2798
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 310
% 0.21/0.42  # Unit Clause-clause subsumption calls : 167
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 60
% 0.21/0.42  # BW rewrite match successes           : 37
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 37562
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.070 s
% 0.21/0.42  # System time              : 0.003 s
% 0.21/0.42  # Total time               : 0.073 s
% 0.21/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
