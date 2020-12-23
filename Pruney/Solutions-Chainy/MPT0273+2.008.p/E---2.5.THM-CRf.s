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
% DateTime   : Thu Dec  3 10:42:56 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  106 (1647 expanded)
%              Number of clauses        :   77 ( 694 expanded)
%              Number of leaves         :   14 ( 468 expanded)
%              Depth                    :   19
%              Number of atoms          :  321 (3522 expanded)
%              Number of equality atoms :  150 (2365 expanded)
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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
      <=> ( ~ r2_hidden(X1,X3)
          & ( r2_hidden(X2,X3)
            | X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_zfmisc_1])).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_18,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X43,X44,X45,X46] : k3_enumset1(X43,X43,X44,X45,X46) = k2_enumset1(X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | esk3_0 = esk4_0
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X25,X24)) = k3_xboole_0(k5_xboole_0(X23,X25),X24) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_31,plain,(
    ! [X17] : k3_xboole_0(X17,X17) = X17 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_32,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( esk4_0 = esk3_0
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_26]),c_0_23]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X26
        | X30 = X27
        | X30 = X28
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( X31 != X26
        | r2_hidden(X31,X29)
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( X31 != X27
        | r2_hidden(X31,X29)
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( esk2_4(X32,X33,X34,X35) != X32
        | ~ r2_hidden(esk2_4(X32,X33,X34,X35),X35)
        | X35 = k1_enumset1(X32,X33,X34) )
      & ( esk2_4(X32,X33,X34,X35) != X33
        | ~ r2_hidden(esk2_4(X32,X33,X34,X35),X35)
        | X35 = k1_enumset1(X32,X33,X34) )
      & ( esk2_4(X32,X33,X34,X35) != X34
        | ~ r2_hidden(esk2_4(X32,X33,X34,X35),X35)
        | X35 = k1_enumset1(X32,X33,X34) )
      & ( r2_hidden(esk2_4(X32,X33,X34,X35),X35)
        | esk2_4(X32,X33,X34,X35) = X32
        | esk2_4(X32,X33,X34,X35) = X33
        | esk2_4(X32,X33,X34,X35) = X34
        | X35 = k1_enumset1(X32,X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | esk3_0 != esk4_0
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_45,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r2_hidden(X18,X19)
        | ~ r2_hidden(X18,X20)
        | ~ r2_hidden(X18,k5_xboole_0(X19,X20)) )
      & ( r2_hidden(X18,X19)
        | r2_hidden(X18,X20)
        | ~ r2_hidden(X18,k5_xboole_0(X19,X20)) )
      & ( ~ r2_hidden(X18,X19)
        | r2_hidden(X18,X20)
        | r2_hidden(X18,k5_xboole_0(X19,X20)) )
      & ( ~ r2_hidden(X18,X20)
        | r2_hidden(X18,X19)
        | r2_hidden(X18,k5_xboole_0(X19,X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | esk4_0 != esk3_0
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_25]),c_0_26]),c_0_26]),c_0_23]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(X1,k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))
    | ~ r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X1,X1,X1,X3,X4)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_56,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_51])])).

cnf(c_0_59,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_55,c_0_23])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

fof(c_0_61,plain,(
    ! [X50,X51,X52] :
      ( k3_xboole_0(k2_tarski(X50,X51),X52) != k1_tarski(X50)
      | ~ r2_hidden(X51,X52)
      | X50 = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_zfmisc_1])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_63,plain,(
    ! [X53,X54,X55] :
      ( ( r2_hidden(X55,X54)
        | k3_xboole_0(k2_tarski(X53,X55),X54) = k1_tarski(X53)
        | ~ r2_hidden(X53,X54) )
      & ( X53 != X55
        | k3_xboole_0(k2_tarski(X53,X55),X54) = k1_tarski(X53)
        | ~ r2_hidden(X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_27]),c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( X1 = k3_xboole_0(X2,k5_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | r2_hidden(esk1_3(X2,X3,X1),X1) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( X1 = X2
    | k3_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_27]),c_0_28])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_64,c_0_23])).

cnf(c_0_73,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_75,plain,
    ( X1 = X2
    | k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3) != k3_enumset1(X1,X1,X1,X1,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_69])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_25]),c_0_26]),c_0_26]),c_0_23]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3) = k3_enumset1(X1,X1,X1,X1,X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_81,plain,
    ( X1 = k3_xboole_0(X2,k5_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X3)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_60])).

cnf(c_0_82,negated_conjecture,
    ( esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_44])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_34])).

cnf(c_0_87,plain,
    ( k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X1),X2) = k3_enumset1(X3,X3,X3,X3,X3)
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_76,c_0_51])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) = k3_enumset1(X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_51])]),c_0_66])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_25]),c_0_26]),c_0_26]),c_0_23]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_86,c_0_40])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X1,X1,X1,X3,X4),X5)) = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(X2,k5_xboole_0(k3_enumset1(X1,X1,X1,X3,X4),X5))
    | r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_34])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_84])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_91]),c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_40])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_77])]),c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_51]),c_0_102])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:42 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 2.22/2.43  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.22/2.43  # and selection function SelectNegativeLiterals.
% 2.22/2.43  #
% 2.22/2.43  # Preprocessing time       : 0.028 s
% 2.22/2.43  # Presaturation interreduction done
% 2.22/2.43  
% 2.22/2.43  # Proof found!
% 2.22/2.43  # SZS status Theorem
% 2.22/2.43  # SZS output start CNFRefutation
% 2.22/2.43  fof(t70_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_zfmisc_1)).
% 2.22/2.43  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.22/2.43  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.22/2.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/2.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.22/2.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.22/2.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.22/2.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.22/2.43  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 2.22/2.43  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.22/2.43  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.22/2.43  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.22/2.43  fof(t59_zfmisc_1, axiom, ![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.22/2.43  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 2.22/2.43  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2)))), inference(assume_negation,[status(cth)],[t70_zfmisc_1])).
% 2.22/2.43  fof(c_0_15, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.22/2.43  fof(c_0_16, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.22/2.43  fof(c_0_17, negated_conjecture, (((~r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0))&(esk3_0!=esk4_0|r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)))&((~r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0))&(r2_hidden(esk4_0,esk5_0)|esk3_0=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 2.22/2.43  fof(c_0_18, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.22/2.43  fof(c_0_19, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.22/2.43  fof(c_0_20, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.22/2.43  fof(c_0_21, plain, ![X43, X44, X45, X46]:k3_enumset1(X43,X43,X44,X45,X46)=k2_enumset1(X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.22/2.43  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.22/2.43  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.22/2.43  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|esk3_0=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.22/2.43  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.22/2.43  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.22/2.43  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.22/2.43  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.22/2.43  fof(c_0_29, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.22/2.43  fof(c_0_30, plain, ![X23, X24, X25]:k5_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X25,X24))=k3_xboole_0(k5_xboole_0(X23,X25),X24), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 2.22/2.43  fof(c_0_31, plain, ![X17]:k3_xboole_0(X17,X17)=X17, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 2.22/2.43  cnf(c_0_32, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 2.22/2.43  cnf(c_0_33, negated_conjecture, (esk4_0=esk3_0|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_26]), c_0_23]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 2.22/2.43  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.22/2.43  cnf(c_0_35, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.22/2.43  cnf(c_0_36, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.22/2.43  fof(c_0_37, plain, ![X26, X27, X28, X29, X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X30,X29)|(X30=X26|X30=X27|X30=X28)|X29!=k1_enumset1(X26,X27,X28))&(((X31!=X26|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28))&(X31!=X27|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28)))&(X31!=X28|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28))))&((((esk2_4(X32,X33,X34,X35)!=X32|~r2_hidden(esk2_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34))&(esk2_4(X32,X33,X34,X35)!=X33|~r2_hidden(esk2_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34)))&(esk2_4(X32,X33,X34,X35)!=X34|~r2_hidden(esk2_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34)))&(r2_hidden(esk2_4(X32,X33,X34,X35),X35)|(esk2_4(X32,X33,X34,X35)=X32|esk2_4(X32,X33,X34,X35)=X33|esk2_4(X32,X33,X34,X35)=X34)|X35=k1_enumset1(X32,X33,X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 2.22/2.43  cnf(c_0_38, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_32])).
% 2.22/2.43  cnf(c_0_39, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 2.22/2.43  cnf(c_0_40, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_34])).
% 2.22/2.43  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.22/2.43  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|esk3_0!=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.22/2.43  cnf(c_0_43, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 2.22/2.43  cnf(c_0_44, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 2.22/2.43  fof(c_0_45, plain, ![X18, X19, X20]:(((~r2_hidden(X18,X19)|~r2_hidden(X18,X20)|~r2_hidden(X18,k5_xboole_0(X19,X20)))&(r2_hidden(X18,X19)|r2_hidden(X18,X20)|~r2_hidden(X18,k5_xboole_0(X19,X20))))&((~r2_hidden(X18,X19)|r2_hidden(X18,X20)|r2_hidden(X18,k5_xboole_0(X19,X20)))&(~r2_hidden(X18,X20)|r2_hidden(X18,X19)|r2_hidden(X18,k5_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 2.22/2.43  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_28])).
% 2.22/2.43  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|esk4_0!=esk3_0|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_25]), c_0_26]), c_0_26]), c_0_23]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 2.22/2.43  cnf(c_0_48, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_43, c_0_40])).
% 2.22/2.43  cnf(c_0_49, negated_conjecture, (k3_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_44])).
% 2.22/2.43  cnf(c_0_50, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.22/2.43  cnf(c_0_51, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 2.22/2.43  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[c_0_47, c_0_34])).
% 2.22/2.43  cnf(c_0_53, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)|~r2_hidden(X1,k5_xboole_0(k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))|~r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 2.22/2.43  cnf(c_0_54, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X1,X1,X1,X3,X4)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.22/2.43  cnf(c_0_55, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.22/2.43  cnf(c_0_56, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.22/2.43  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[c_0_52, c_0_40])).
% 2.22/2.43  cnf(c_0_58, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_51])])).
% 2.22/2.43  cnf(c_0_59, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_55, c_0_23])).
% 2.22/2.43  cnf(c_0_60, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 2.22/2.43  fof(c_0_61, plain, ![X50, X51, X52]:(k3_xboole_0(k2_tarski(X50,X51),X52)!=k1_tarski(X50)|~r2_hidden(X51,X52)|X50=X51), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_zfmisc_1])])).
% 2.22/2.43  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.22/2.43  fof(c_0_63, plain, ![X53, X54, X55]:((r2_hidden(X55,X54)|k3_xboole_0(k2_tarski(X53,X55),X54)=k1_tarski(X53)|~r2_hidden(X53,X54))&(X53!=X55|k3_xboole_0(k2_tarski(X53,X55),X54)=k1_tarski(X53)|~r2_hidden(X53,X54))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 2.22/2.43  cnf(c_0_64, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.22/2.43  cnf(c_0_65, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_27]), c_0_28])).
% 2.22/2.43  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 2.22/2.43  cnf(c_0_67, plain, (X1=k3_xboole_0(X2,k5_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X2)|r2_hidden(esk1_3(X2,X3,X1),X1)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 2.22/2.43  cnf(c_0_68, plain, (X1=X2|k3_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.22/2.43  cnf(c_0_69, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_27]), c_0_28])).
% 2.22/2.43  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.22/2.43  cnf(c_0_71, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.22/2.43  cnf(c_0_72, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_64, c_0_23])).
% 2.22/2.43  cnf(c_0_73, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_65])).
% 2.22/2.43  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67])])).
% 2.22/2.43  cnf(c_0_75, plain, (X1=X2|k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3)!=k3_enumset1(X1,X1,X1,X1,X1)|~r2_hidden(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 2.22/2.43  cnf(c_0_76, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.22/2.43  cnf(c_0_77, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_69])])).
% 2.22/2.43  cnf(c_0_78, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_25]), c_0_26]), c_0_26]), c_0_23]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 2.22/2.43  cnf(c_0_79, plain, (r2_hidden(X1,X2)|k3_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.22/2.43  cnf(c_0_80, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3)=k3_enumset1(X1,X1,X1,X1,X1)|X1!=X2|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 2.22/2.43  cnf(c_0_81, plain, (X1=k3_xboole_0(X2,k5_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X3)|~r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),X2)), inference(rw,[status(thm)],[c_0_72, c_0_60])).
% 2.22/2.43  cnf(c_0_82, negated_conjecture, (esk1_3(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 2.22/2.43  cnf(c_0_83, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_75, c_0_44])).
% 2.22/2.43  cnf(c_0_84, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 2.22/2.43  cnf(c_0_85, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.22/2.43  cnf(c_0_86, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_78, c_0_34])).
% 2.22/2.43  cnf(c_0_87, plain, (k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X1),X2)=k3_enumset1(X3,X3,X3,X3,X3)|r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 2.22/2.43  cnf(c_0_88, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_76, c_0_51])).
% 2.22/2.43  cnf(c_0_89, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)=k3_enumset1(X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_80])).
% 2.22/2.43  cnf(c_0_90, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_51])]), c_0_66])).
% 2.22/2.43  cnf(c_0_91, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 2.22/2.43  cnf(c_0_92, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_25]), c_0_26]), c_0_26]), c_0_23]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 2.22/2.43  cnf(c_0_93, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_86, c_0_40])).
% 2.22/2.43  cnf(c_0_94, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X1,X1,X1,X3,X4),X5))=k3_enumset1(X1,X1,X1,X1,X1)|r2_hidden(X2,k5_xboole_0(k3_enumset1(X1,X1,X1,X3,X4),X5))|r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 2.22/2.43  cnf(c_0_95, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 2.22/2.43  cnf(c_0_96, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk5_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_91])).
% 2.22/2.43  cnf(c_0_97, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_92, c_0_34])).
% 2.22/2.43  cnf(c_0_98, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.22/2.43  cnf(c_0_99, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_84])).
% 2.22/2.43  cnf(c_0_100, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_91]), c_0_96])).
% 2.22/2.43  cnf(c_0_101, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_97, c_0_40])).
% 2.22/2.43  cnf(c_0_102, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_77])]), c_0_100])).
% 2.22/2.43  cnf(c_0_103, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 2.22/2.43  cnf(c_0_104, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_103])).
% 2.22/2.43  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_51]), c_0_102])]), ['proof']).
% 2.22/2.43  # SZS output end CNFRefutation
% 2.22/2.43  # Proof object total steps             : 106
% 2.22/2.43  # Proof object clause steps            : 77
% 2.22/2.43  # Proof object formula steps           : 29
% 2.22/2.43  # Proof object conjectures             : 36
% 2.22/2.43  # Proof object clause conjectures      : 33
% 2.22/2.43  # Proof object formula conjectures     : 3
% 2.22/2.43  # Proof object initial clauses used    : 24
% 2.22/2.43  # Proof object initial formulas used   : 14
% 2.22/2.43  # Proof object generating inferences   : 23
% 2.22/2.43  # Proof object simplifying inferences  : 104
% 2.22/2.43  # Training examples: 0 positive, 0 negative
% 2.22/2.43  # Parsed axioms                        : 16
% 2.22/2.43  # Removed by relevancy pruning/SinE    : 0
% 2.22/2.43  # Initial clauses                      : 35
% 2.22/2.43  # Removed in clause preprocessing      : 5
% 2.22/2.43  # Initial clauses in saturation        : 30
% 2.22/2.43  # Processed clauses                    : 6630
% 2.22/2.43  # ...of these trivial                  : 45
% 2.22/2.43  # ...subsumed                          : 5714
% 2.22/2.43  # ...remaining for further processing  : 871
% 2.22/2.43  # Other redundant clauses eliminated   : 1191
% 2.22/2.43  # Clauses deleted for lack of memory   : 0
% 2.22/2.43  # Backward-subsumed                    : 69
% 2.22/2.43  # Backward-rewritten                   : 409
% 2.22/2.43  # Generated clauses                    : 168612
% 2.22/2.43  # ...of the previous two non-trivial   : 162921
% 2.22/2.43  # Contextual simplify-reflections      : 35
% 2.22/2.43  # Paramodulations                      : 167029
% 2.22/2.43  # Factorizations                       : 389
% 2.22/2.43  # Equation resolutions                 : 1197
% 2.22/2.43  # Propositional unsat checks           : 0
% 2.22/2.43  #    Propositional check models        : 0
% 2.22/2.43  #    Propositional check unsatisfiable : 0
% 2.22/2.43  #    Propositional clauses             : 0
% 2.22/2.43  #    Propositional clauses after purity: 0
% 2.22/2.43  #    Propositional unsat core size     : 0
% 2.22/2.43  #    Propositional preprocessing time  : 0.000
% 2.22/2.43  #    Propositional encoding time       : 0.000
% 2.22/2.43  #    Propositional solver time         : 0.000
% 2.22/2.43  #    Success case prop preproc time    : 0.000
% 2.22/2.43  #    Success case prop encoding time   : 0.000
% 2.22/2.43  #    Success case prop solver time     : 0.000
% 2.22/2.43  # Current number of processed clauses  : 355
% 2.22/2.43  #    Positive orientable unit clauses  : 34
% 2.22/2.43  #    Positive unorientable unit clauses: 6
% 2.22/2.43  #    Negative unit clauses             : 1
% 2.22/2.43  #    Non-unit-clauses                  : 314
% 2.22/2.43  # Current number of unprocessed clauses: 154026
% 2.22/2.43  # ...number of literals in the above   : 914107
% 2.22/2.43  # Current number of archived formulas  : 0
% 2.22/2.43  # Current number of archived clauses   : 513
% 2.22/2.43  # Clause-clause subsumption calls (NU) : 89181
% 2.22/2.43  # Rec. Clause-clause subsumption calls : 56821
% 2.22/2.43  # Non-unit clause-clause subsumptions  : 3031
% 2.22/2.43  # Unit Clause-clause subsumption calls : 3874
% 2.22/2.43  # Rewrite failures with RHS unbound    : 1863
% 2.22/2.43  # BW rewrite match attempts            : 1056
% 2.22/2.43  # BW rewrite match successes           : 187
% 2.22/2.43  # Condensation attempts                : 0
% 2.22/2.43  # Condensation successes               : 0
% 2.22/2.43  # Termbank termtop insertions          : 4449323
% 2.22/2.43  
% 2.22/2.43  # -------------------------------------------------
% 2.22/2.43  # User time                : 2.002 s
% 2.22/2.43  # System time              : 0.089 s
% 2.22/2.43  # Total time               : 2.092 s
% 2.22/2.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
