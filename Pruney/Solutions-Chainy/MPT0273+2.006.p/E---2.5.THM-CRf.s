%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:56 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  114 (1797 expanded)
%              Number of clauses        :   83 ( 784 expanded)
%              Number of leaves         :   15 ( 498 expanded)
%              Depth                    :   19
%              Number of atoms          :  345 (4032 expanded)
%              Number of equality atoms :  160 (2545 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t59_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
        & r2_hidden(X2,X3)
        & X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
      <=> ( ~ r2_hidden(X1,X3)
          & ( r2_hidden(X2,X3)
            | X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_17,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k4_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,negated_conjecture,
    ( ( ~ r2_hidden(esk4_0,esk5_0)
      | r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) )
    & ( esk3_0 != esk4_0
      | r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) )
    & ( ~ r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0) )
    & ( r2_hidden(esk4_0,esk5_0)
      | esk3_0 = esk4_0
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_20,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X46,X47,X48,X49] : k3_enumset1(X46,X46,X47,X48,X49) = k2_enumset1(X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k3_xboole_0(X27,X28) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | esk3_0 = esk4_0
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_34,plain,(
    ! [X24,X25,X26] : k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X26,X25)) = k3_xboole_0(k5_xboole_0(X24,X26),X25) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 = esk3_0
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_30]),c_0_27]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_42,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X29
        | X33 = X30
        | X33 = X31
        | X32 != k1_enumset1(X29,X30,X31) )
      & ( X34 != X29
        | r2_hidden(X34,X32)
        | X32 != k1_enumset1(X29,X30,X31) )
      & ( X34 != X30
        | r2_hidden(X34,X32)
        | X32 != k1_enumset1(X29,X30,X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k1_enumset1(X29,X30,X31) )
      & ( esk2_4(X35,X36,X37,X38) != X35
        | ~ r2_hidden(esk2_4(X35,X36,X37,X38),X38)
        | X38 = k1_enumset1(X35,X36,X37) )
      & ( esk2_4(X35,X36,X37,X38) != X36
        | ~ r2_hidden(esk2_4(X35,X36,X37,X38),X38)
        | X38 = k1_enumset1(X35,X36,X37) )
      & ( esk2_4(X35,X36,X37,X38) != X37
        | ~ r2_hidden(esk2_4(X35,X36,X37,X38),X38)
        | X38 = k1_enumset1(X35,X36,X37) )
      & ( r2_hidden(esk2_4(X35,X36,X37,X38),X38)
        | esk2_4(X35,X36,X37,X38) = X35
        | esk2_4(X35,X36,X37,X38) = X36
        | esk2_4(X35,X36,X37,X38) = X37
        | X38 = k1_enumset1(X35,X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | esk3_0 != esk4_0
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_50,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X19)
        | r2_hidden(X17,X18)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_31]),c_0_32])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | esk4_0 != esk3_0
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_29]),c_0_30]),c_0_30]),c_0_27]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_48,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_31]),c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_39])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(X1,k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))
    | ~ r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X4,X1)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_64,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_45])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_67,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_63,c_0_27])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

fof(c_0_69,plain,(
    ! [X53,X54,X55] :
      ( k3_xboole_0(k2_tarski(X53,X54),X55) != k1_tarski(X53)
      | ~ r2_hidden(X54,X55)
      | X53 = X54 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_zfmisc_1])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_71,plain,(
    ! [X56,X57,X58] :
      ( ( r2_hidden(X58,X57)
        | k3_xboole_0(k2_tarski(X56,X58),X57) = k1_tarski(X56)
        | ~ r2_hidden(X56,X57) )
      & ( X56 != X58
        | k3_xboole_0(k2_tarski(X56,X58),X57) = k1_tarski(X56)
        | ~ r2_hidden(X56,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

cnf(c_0_72,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_73,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_31]),c_0_32])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( X1 = k3_xboole_0(X2,k5_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | r2_hidden(esk1_3(X2,X3,X1),X1) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,plain,
    ( X1 = X2
    | k3_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_31]),c_0_32])).

cnf(c_0_79,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_72,c_0_27])).

cnf(c_0_81,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_83,plain,
    ( X1 = X2
    | k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3) != k3_enumset1(X1,X1,X1,X1,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_29]),c_0_30]),c_0_30]),c_0_27]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_78])])).

cnf(c_0_88,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3) = k3_enumset1(X1,X1,X1,X1,X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_89,plain,
    ( X1 = k3_xboole_0(X2,k5_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X3)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_80,c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_49])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_84,c_0_57])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_39])).

cnf(c_0_95,plain,
    ( k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X1),X2) = k3_enumset1(X3,X3,X3,X3,X3)
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X1,X3),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_84,c_0_87])).

cnf(c_0_97,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) = k3_enumset1(X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_62])]),c_0_74])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_29]),c_0_30]),c_0_30]),c_0_27]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_45])).

cnf(c_0_102,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X1,X4),X5)) = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(X2,k5_xboole_0(k3_enumset1(X3,X3,X3,X1,X4),X5))
    | r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_39])).

cnf(c_0_106,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_92])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_99]),c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_45])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_57])]),c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])])).

cnf(c_0_112,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_111])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_57]),c_0_110])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.85/3.04  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.85/3.04  # and selection function SelectNegativeLiterals.
% 2.85/3.04  #
% 2.85/3.04  # Preprocessing time       : 0.028 s
% 2.85/3.04  # Presaturation interreduction done
% 2.85/3.04  
% 2.85/3.04  # Proof found!
% 2.85/3.04  # SZS status Theorem
% 2.85/3.04  # SZS output start CNFRefutation
% 2.85/3.04  fof(t70_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_zfmisc_1)).
% 2.85/3.04  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/3.04  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.85/3.04  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.85/3.04  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.85/3.04  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.85/3.04  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.85/3.04  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.85/3.04  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.85/3.04  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.85/3.04  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 2.85/3.04  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.85/3.04  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.85/3.04  fof(t59_zfmisc_1, axiom, ![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.85/3.04  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 2.85/3.04  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2)))), inference(assume_negation,[status(cth)],[t70_zfmisc_1])).
% 2.85/3.04  fof(c_0_16, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.85/3.04  fof(c_0_17, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.85/3.04  fof(c_0_18, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.85/3.04  fof(c_0_19, negated_conjecture, (((~r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0))&(esk3_0!=esk4_0|r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)))&((~r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0))&(r2_hidden(esk4_0,esk5_0)|esk3_0=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).
% 2.85/3.04  fof(c_0_20, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.85/3.04  fof(c_0_21, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.85/3.04  fof(c_0_22, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.85/3.04  fof(c_0_23, plain, ![X46, X47, X48, X49]:k3_enumset1(X46,X46,X47,X48,X49)=k2_enumset1(X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.85/3.04  fof(c_0_24, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k3_xboole_0(X27,X28)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.85/3.04  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.85/3.04  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.85/3.04  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.85/3.04  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|esk3_0=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.85/3.04  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.85/3.04  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.85/3.04  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.85/3.04  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.85/3.04  fof(c_0_33, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.85/3.04  fof(c_0_34, plain, ![X24, X25, X26]:k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X26,X25))=k3_xboole_0(k5_xboole_0(X24,X26),X25), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 2.85/3.04  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.85/3.04  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 2.85/3.04  cnf(c_0_37, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 2.85/3.04  cnf(c_0_38, negated_conjecture, (esk4_0=esk3_0|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_30]), c_0_27]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 2.85/3.04  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.85/3.04  cnf(c_0_40, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.85/3.04  cnf(c_0_41, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.85/3.04  fof(c_0_42, plain, ![X29, X30, X31, X32, X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X33,X32)|(X33=X29|X33=X30|X33=X31)|X32!=k1_enumset1(X29,X30,X31))&(((X34!=X29|r2_hidden(X34,X32)|X32!=k1_enumset1(X29,X30,X31))&(X34!=X30|r2_hidden(X34,X32)|X32!=k1_enumset1(X29,X30,X31)))&(X34!=X31|r2_hidden(X34,X32)|X32!=k1_enumset1(X29,X30,X31))))&((((esk2_4(X35,X36,X37,X38)!=X35|~r2_hidden(esk2_4(X35,X36,X37,X38),X38)|X38=k1_enumset1(X35,X36,X37))&(esk2_4(X35,X36,X37,X38)!=X36|~r2_hidden(esk2_4(X35,X36,X37,X38),X38)|X38=k1_enumset1(X35,X36,X37)))&(esk2_4(X35,X36,X37,X38)!=X37|~r2_hidden(esk2_4(X35,X36,X37,X38),X38)|X38=k1_enumset1(X35,X36,X37)))&(r2_hidden(esk2_4(X35,X36,X37,X38),X38)|(esk2_4(X35,X36,X37,X38)=X35|esk2_4(X35,X36,X37,X38)=X36|esk2_4(X35,X36,X37,X38)=X37)|X38=k1_enumset1(X35,X36,X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 2.85/3.04  cnf(c_0_43, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_37])).
% 2.85/3.04  cnf(c_0_44, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 2.85/3.04  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_39])).
% 2.85/3.04  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.85/3.04  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|esk3_0!=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.85/3.04  cnf(c_0_48, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 2.85/3.04  cnf(c_0_49, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 2.85/3.04  fof(c_0_50, plain, ![X17, X18, X19]:(((~r2_hidden(X17,X18)|~r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19)))&(r2_hidden(X17,X18)|r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19))))&((~r2_hidden(X17,X18)|r2_hidden(X17,X19)|r2_hidden(X17,k5_xboole_0(X18,X19)))&(~r2_hidden(X17,X19)|r2_hidden(X17,X18)|r2_hidden(X17,k5_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 2.85/3.04  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_31]), c_0_32])).
% 2.85/3.04  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.85/3.04  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|esk4_0!=esk3_0|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_29]), c_0_30]), c_0_30]), c_0_27]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 2.85/3.04  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_48, c_0_45])).
% 2.85/3.04  cnf(c_0_55, negated_conjecture, (k3_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_49])).
% 2.85/3.04  cnf(c_0_56, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.85/3.04  cnf(c_0_57, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).
% 2.85/3.04  cnf(c_0_58, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_31]), c_0_32])).
% 2.85/3.04  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[c_0_53, c_0_39])).
% 2.85/3.04  cnf(c_0_60, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)|~r2_hidden(X1,k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))|~r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 2.85/3.04  cnf(c_0_61, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X4,X1)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.85/3.04  cnf(c_0_62, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).
% 2.85/3.04  cnf(c_0_63, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.85/3.04  cnf(c_0_64, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.85/3.04  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[c_0_59, c_0_45])).
% 2.85/3.04  cnf(c_0_66, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 2.85/3.04  cnf(c_0_67, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_63, c_0_27])).
% 2.85/3.04  cnf(c_0_68, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 2.85/3.04  fof(c_0_69, plain, ![X53, X54, X55]:(k3_xboole_0(k2_tarski(X53,X54),X55)!=k1_tarski(X53)|~r2_hidden(X54,X55)|X53=X54), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_zfmisc_1])])).
% 2.85/3.04  cnf(c_0_70, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.85/3.04  fof(c_0_71, plain, ![X56, X57, X58]:((r2_hidden(X58,X57)|k3_xboole_0(k2_tarski(X56,X58),X57)=k1_tarski(X56)|~r2_hidden(X56,X57))&(X56!=X58|k3_xboole_0(k2_tarski(X56,X58),X57)=k1_tarski(X56)|~r2_hidden(X56,X57))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 2.85/3.04  cnf(c_0_72, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.85/3.04  cnf(c_0_73, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_31]), c_0_32])).
% 2.85/3.04  cnf(c_0_74, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.85/3.04  cnf(c_0_75, plain, (X1=k3_xboole_0(X2,k5_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X2)|r2_hidden(esk1_3(X2,X3,X1),X1)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 2.85/3.04  cnf(c_0_76, plain, (X1=X2|k3_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 2.85/3.04  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.85/3.04  cnf(c_0_78, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_31]), c_0_32])).
% 2.85/3.04  cnf(c_0_79, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.85/3.04  cnf(c_0_80, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_72, c_0_27])).
% 2.85/3.04  cnf(c_0_81, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_73])).
% 2.85/3.04  cnf(c_0_82, negated_conjecture, (r2_hidden(esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75])])).
% 2.85/3.04  cnf(c_0_83, plain, (X1=X2|k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3)!=k3_enumset1(X1,X1,X1,X1,X1)|~r2_hidden(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 2.85/3.04  cnf(c_0_84, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.85/3.04  cnf(c_0_85, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_29]), c_0_30]), c_0_30]), c_0_27]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 2.85/3.04  cnf(c_0_86, plain, (r2_hidden(X1,X2)|k3_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.85/3.04  cnf(c_0_87, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_78])])).
% 2.85/3.04  cnf(c_0_88, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3)=k3_enumset1(X1,X1,X1,X1,X1)|X1!=X2|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 2.85/3.04  cnf(c_0_89, plain, (X1=k3_xboole_0(X2,k5_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X3)|~r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),X2)), inference(rw,[status(thm)],[c_0_80, c_0_68])).
% 2.85/3.04  cnf(c_0_90, negated_conjecture, (esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 2.85/3.04  cnf(c_0_91, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_83, c_0_49])).
% 2.85/3.04  cnf(c_0_92, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_84, c_0_57])).
% 2.85/3.04  cnf(c_0_93, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.85/3.04  cnf(c_0_94, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_85, c_0_39])).
% 2.85/3.04  cnf(c_0_95, plain, (k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X1),X2)=k3_enumset1(X3,X3,X3,X3,X3)|r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 2.85/3.04  cnf(c_0_96, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X1,X3),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_84, c_0_87])).
% 2.85/3.04  cnf(c_0_97, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)=k3_enumset1(X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_88])).
% 2.85/3.04  cnf(c_0_98, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_62])]), c_0_74])).
% 2.85/3.04  cnf(c_0_99, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 2.85/3.04  cnf(c_0_100, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_29]), c_0_30]), c_0_30]), c_0_27]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 2.85/3.04  cnf(c_0_101, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_94, c_0_45])).
% 2.85/3.04  cnf(c_0_102, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X1,X4),X5))=k3_enumset1(X1,X1,X1,X1,X1)|r2_hidden(X2,k5_xboole_0(k3_enumset1(X3,X3,X3,X1,X4),X5))|r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 2.85/3.04  cnf(c_0_103, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 2.85/3.04  cnf(c_0_104, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_99])).
% 2.85/3.04  cnf(c_0_105, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_100, c_0_39])).
% 2.85/3.04  cnf(c_0_106, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.85/3.04  cnf(c_0_107, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_92])).
% 2.85/3.04  cnf(c_0_108, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_99]), c_0_104])).
% 2.85/3.04  cnf(c_0_109, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_105, c_0_45])).
% 2.85/3.04  cnf(c_0_110, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_57])]), c_0_108])).
% 2.85/3.04  cnf(c_0_111, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])])).
% 2.85/3.04  cnf(c_0_112, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_111])).
% 2.85/3.04  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_57]), c_0_110])]), ['proof']).
% 2.85/3.04  # SZS output end CNFRefutation
% 2.85/3.04  # Proof object total steps             : 114
% 2.85/3.04  # Proof object clause steps            : 83
% 2.85/3.04  # Proof object formula steps           : 31
% 2.85/3.04  # Proof object conjectures             : 36
% 2.85/3.04  # Proof object clause conjectures      : 33
% 2.85/3.04  # Proof object formula conjectures     : 3
% 2.85/3.04  # Proof object initial clauses used    : 26
% 2.85/3.04  # Proof object initial formulas used   : 15
% 2.85/3.04  # Proof object generating inferences   : 24
% 2.85/3.04  # Proof object simplifying inferences  : 109
% 2.85/3.04  # Training examples: 0 positive, 0 negative
% 2.85/3.04  # Parsed axioms                        : 17
% 2.85/3.04  # Removed by relevancy pruning/SinE    : 0
% 2.85/3.04  # Initial clauses                      : 38
% 2.85/3.04  # Removed in clause preprocessing      : 5
% 2.85/3.04  # Initial clauses in saturation        : 33
% 2.85/3.04  # Processed clauses                    : 7873
% 2.85/3.04  # ...of these trivial                  : 45
% 2.85/3.04  # ...subsumed                          : 6792
% 2.85/3.04  # ...remaining for further processing  : 1036
% 2.85/3.04  # Other redundant clauses eliminated   : 1244
% 2.85/3.04  # Clauses deleted for lack of memory   : 0
% 2.85/3.04  # Backward-subsumed                    : 81
% 2.85/3.04  # Backward-rewritten                   : 462
% 2.85/3.04  # Generated clauses                    : 217287
% 2.85/3.04  # ...of the previous two non-trivial   : 210055
% 2.85/3.04  # Contextual simplify-reflections      : 45
% 2.85/3.04  # Paramodulations                      : 215623
% 2.85/3.04  # Factorizations                       : 417
% 2.85/3.04  # Equation resolutions                 : 1250
% 2.85/3.04  # Propositional unsat checks           : 0
% 2.85/3.04  #    Propositional check models        : 0
% 2.85/3.04  #    Propositional check unsatisfiable : 0
% 2.85/3.04  #    Propositional clauses             : 0
% 2.85/3.04  #    Propositional clauses after purity: 0
% 2.85/3.04  #    Propositional unsat core size     : 0
% 2.85/3.04  #    Propositional preprocessing time  : 0.000
% 2.85/3.04  #    Propositional encoding time       : 0.000
% 2.85/3.04  #    Propositional solver time         : 0.000
% 2.85/3.04  #    Success case prop preproc time    : 0.000
% 2.85/3.04  #    Success case prop encoding time   : 0.000
% 2.85/3.04  #    Success case prop solver time     : 0.000
% 2.85/3.04  # Current number of processed clauses  : 451
% 2.85/3.04  #    Positive orientable unit clauses  : 35
% 2.85/3.04  #    Positive unorientable unit clauses: 6
% 2.85/3.04  #    Negative unit clauses             : 1
% 2.85/3.04  #    Non-unit-clauses                  : 409
% 2.85/3.04  # Current number of unprocessed clauses: 199589
% 2.85/3.04  # ...number of literals in the above   : 1180297
% 2.85/3.04  # Current number of archived formulas  : 0
% 2.85/3.04  # Current number of archived clauses   : 580
% 2.85/3.04  # Clause-clause subsumption calls (NU) : 135312
% 2.85/3.04  # Rec. Clause-clause subsumption calls : 78313
% 2.85/3.04  # Non-unit clause-clause subsumptions  : 3496
% 2.85/3.04  # Unit Clause-clause subsumption calls : 3779
% 2.85/3.04  # Rewrite failures with RHS unbound    : 1911
% 2.85/3.04  # BW rewrite match attempts            : 1106
% 2.85/3.04  # BW rewrite match successes           : 195
% 2.85/3.04  # Condensation attempts                : 0
% 2.85/3.04  # Condensation successes               : 0
% 2.85/3.04  # Termbank termtop insertions          : 6024118
% 2.85/3.06  
% 2.85/3.06  # -------------------------------------------------
% 2.85/3.06  # User time                : 2.622 s
% 2.85/3.06  # System time              : 0.096 s
% 2.85/3.06  # Total time               : 2.718 s
% 2.85/3.06  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
