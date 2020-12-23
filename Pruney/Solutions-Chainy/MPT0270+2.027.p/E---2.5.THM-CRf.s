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
% DateTime   : Thu Dec  3 10:42:39 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 (1758 expanded)
%              Number of clauses        :   71 ( 795 expanded)
%              Number of leaves         :   13 ( 477 expanded)
%              Depth                    :   16
%              Number of atoms          :  247 (3516 expanded)
%              Number of equality atoms :  117 (1957 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
      <=> ~ r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t67_zfmisc_1])).

fof(c_0_14,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_tarski(esk3_0)
      | r2_hidden(esk3_0,esk4_0) )
    & ( k4_xboole_0(k1_tarski(esk3_0),esk4_0) = k1_tarski(esk3_0)
      | ~ r2_hidden(esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X43,X44] :
      ( ( k4_xboole_0(X43,k1_tarski(X44)) != X43
        | ~ r2_hidden(X44,X43) )
      & ( r2_hidden(X44,X43)
        | k4_xboole_0(X43,k1_tarski(X44)) = X43 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X21] : r1_tarski(k1_xboole_0,X21) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_23,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_24,plain,(
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

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | k4_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_28]),c_0_28])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_45,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
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

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk4_0))) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X3)
    | r2_hidden(esk1_3(X1,X3,X2),X1)
    | r2_hidden(esk1_3(X1,X3,X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_49])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_61,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,esk4_0),esk4_0)
    | r2_hidden(esk3_0,esk4_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,X1)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_50])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_41]),c_0_60])).

cnf(c_0_67,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_29])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,esk4_0),esk4_0)
    | r2_hidden(esk3_0,esk4_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(X1,esk4_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_39])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_3(X1,k2_enumset1(X2,X2,X2,X2),X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_49])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk3_0),esk4_0) = k1_tarski(esk3_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_57]),c_0_64]),c_0_65])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X2,k3_xboole_0(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_48])).

cnf(c_0_74,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_75,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_49])]),c_0_69])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_70,c_0_29])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_72]),c_0_73])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = X1
    | r2_hidden(esk1_3(X2,X3,k3_xboole_0(X1,k2_enumset1(X4,X4,X4,X4))),X2)
    | r2_hidden(X4,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_49]),c_0_66])).

cnf(c_0_81,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_82,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_39])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,X1,X2),X2)
    | r2_hidden(esk3_0,esk4_0)
    | k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X2) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_72])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1
    | r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_57]),c_0_64]),c_0_65])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_39]),c_0_83])]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_65])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_87]),c_0_69])).

cnf(c_0_90,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_91])])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_92,c_0_29])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_93])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_94])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.52  # and selection function SelectNegativeLiterals.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.027 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t67_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 0.19/0.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.52  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.52  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.52  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.52  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.52  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.52  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.52  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.52  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2)))), inference(assume_negation,[status(cth)],[t67_zfmisc_1])).
% 0.19/0.52  fof(c_0_14, negated_conjecture, ((k4_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk3_0)|r2_hidden(esk3_0,esk4_0))&(k4_xboole_0(k1_tarski(esk3_0),esk4_0)=k1_tarski(esk3_0)|~r2_hidden(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.52  fof(c_0_15, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.52  fof(c_0_16, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.52  fof(c_0_17, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.52  fof(c_0_18, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.52  fof(c_0_19, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.52  fof(c_0_20, plain, ![X43, X44]:((k4_xboole_0(X43,k1_tarski(X44))!=X43|~r2_hidden(X44,X43))&(r2_hidden(X44,X43)|k4_xboole_0(X43,k1_tarski(X44))=X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.19/0.52  fof(c_0_21, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.52  fof(c_0_22, plain, ![X21]:r1_tarski(k1_xboole_0,X21), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.52  fof(c_0_23, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.52  fof(c_0_24, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.52  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|k4_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.52  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.52  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.52  fof(c_0_30, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.52  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  cnf(c_0_32, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.52  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.52  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.52  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.52  cnf(c_0_40, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_28]), c_0_28])).
% 0.19/0.52  cnf(c_0_41, plain, (k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.52  cnf(c_0_42, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_43, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.52  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_35, c_0_28])).
% 0.19/0.52  cnf(c_0_45, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_28])).
% 0.19/0.52  cnf(c_0_46, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_37, c_0_28])).
% 0.19/0.52  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.52  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.52  cnf(c_0_49, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_42, c_0_28])).
% 0.19/0.52  cnf(c_0_50, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.52  cnf(c_0_51, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.52  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.52  fof(c_0_53, plain, ![X26, X27, X28, X29, X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X30,X29)|(X30=X26|X30=X27|X30=X28)|X29!=k1_enumset1(X26,X27,X28))&(((X31!=X26|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28))&(X31!=X27|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28)))&(X31!=X28|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28))))&((((esk2_4(X32,X33,X34,X35)!=X32|~r2_hidden(esk2_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34))&(esk2_4(X32,X33,X34,X35)!=X33|~r2_hidden(esk2_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34)))&(esk2_4(X32,X33,X34,X35)!=X34|~r2_hidden(esk2_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34)))&(r2_hidden(esk2_4(X32,X33,X34,X35),X35)|(esk2_4(X32,X33,X34,X35)=X32|esk2_4(X32,X33,X34,X35)=X33|esk2_4(X32,X33,X34,X35)=X34)|X35=k1_enumset1(X32,X33,X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.52  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk4_0)))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.52  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X3)|r2_hidden(esk1_3(X1,X3,X2),X1)|r2_hidden(esk1_3(X1,X3,X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_49])).
% 0.19/0.52  cnf(c_0_56, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.52  cnf(c_0_57, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 0.19/0.52  cnf(c_0_58, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_39])).
% 0.19/0.52  cnf(c_0_59, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_51, c_0_40])).
% 0.19/0.52  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_52, c_0_40])).
% 0.19/0.52  cnf(c_0_61, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.52  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(esk4_0,X1,esk4_0),esk4_0)|r2_hidden(esk3_0,esk4_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,X1))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.52  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.52  cnf(c_0_64, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_57])).
% 0.19/0.52  cnf(c_0_65, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_50])).
% 0.19/0.52  cnf(c_0_66, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_41]), c_0_60])).
% 0.19/0.52  cnf(c_0_67, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_29])).
% 0.19/0.52  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_3(esk4_0,X1,esk4_0),esk4_0)|r2_hidden(esk3_0,esk4_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(X1,esk4_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_39])).
% 0.19/0.52  cnf(c_0_69, plain, (r2_hidden(esk1_3(X1,k2_enumset1(X2,X2,X2,X2),X1),X1)|~r2_hidden(X2,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_49])])).
% 0.19/0.52  cnf(c_0_70, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.52  cnf(c_0_71, negated_conjecture, (k4_xboole_0(k1_tarski(esk3_0),esk4_0)=k1_tarski(esk3_0)|~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.52  cnf(c_0_72, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_57]), c_0_64]), c_0_65])).
% 0.19/0.52  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k5_xboole_0(X2,k3_xboole_0(X2,X2)))), inference(spm,[status(thm)],[c_0_66, c_0_48])).
% 0.19/0.52  cnf(c_0_74, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_75, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_67])).
% 0.19/0.52  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_49])]), c_0_69])).
% 0.19/0.52  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_70, c_0_29])).
% 0.19/0.52  cnf(c_0_78, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.52  cnf(c_0_79, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_72]), c_0_73])).
% 0.19/0.52  cnf(c_0_80, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=X1|r2_hidden(esk1_3(X2,X3,k3_xboole_0(X1,k2_enumset1(X4,X4,X4,X4))),X2)|r2_hidden(X4,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_49]), c_0_66])).
% 0.19/0.52  cnf(c_0_81, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_74, c_0_28])).
% 0.19/0.52  cnf(c_0_82, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.52  cnf(c_0_83, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])])).
% 0.19/0.52  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_78, c_0_39])).
% 0.19/0.52  cnf(c_0_85, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,X1,X2),X2)|r2_hidden(esk3_0,esk4_0)|k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X2)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_79, c_0_72])).
% 0.19/0.52  cnf(c_0_86, plain, (k5_xboole_0(X1,k1_xboole_0)=X1|r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_57]), c_0_64]), c_0_65])).
% 0.19/0.52  cnf(c_0_87, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_39]), c_0_83])]), c_0_84])).
% 0.19/0.52  cnf(c_0_88, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_65])).
% 0.19/0.52  cnf(c_0_89, negated_conjecture, (r2_hidden(esk1_3(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_87]), c_0_69])).
% 0.19/0.52  cnf(c_0_90, negated_conjecture, (X1=esk3_0|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_88])).
% 0.19/0.52  cnf(c_0_91, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.52  cnf(c_0_92, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.52  cnf(c_0_93, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_91])])).
% 0.19/0.52  cnf(c_0_94, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_92, c_0_29])).
% 0.19/0.52  cnf(c_0_95, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_93])).
% 0.19/0.52  cnf(c_0_96, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_94])])).
% 0.19/0.52  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_91])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 98
% 0.19/0.52  # Proof object clause steps            : 71
% 0.19/0.52  # Proof object formula steps           : 27
% 0.19/0.52  # Proof object conjectures             : 24
% 0.19/0.52  # Proof object clause conjectures      : 21
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 20
% 0.19/0.52  # Proof object initial formulas used   : 13
% 0.19/0.52  # Proof object generating inferences   : 29
% 0.19/0.52  # Proof object simplifying inferences  : 64
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 13
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 29
% 0.19/0.52  # Removed in clause preprocessing      : 4
% 0.19/0.52  # Initial clauses in saturation        : 25
% 0.19/0.52  # Processed clauses                    : 773
% 0.19/0.52  # ...of these trivial                  : 14
% 0.19/0.52  # ...subsumed                          : 519
% 0.19/0.52  # ...remaining for further processing  : 240
% 0.19/0.52  # Other redundant clauses eliminated   : 225
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 7
% 0.19/0.52  # Backward-rewritten                   : 53
% 0.19/0.52  # Generated clauses                    : 9479
% 0.19/0.52  # ...of the previous two non-trivial   : 8633
% 0.19/0.52  # Contextual simplify-reflections      : 13
% 0.19/0.52  # Paramodulations                      : 9245
% 0.19/0.52  # Factorizations                       : 12
% 0.19/0.52  # Equation resolutions                 : 225
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 147
% 0.19/0.52  #    Positive orientable unit clauses  : 25
% 0.19/0.52  #    Positive unorientable unit clauses: 1
% 0.19/0.52  #    Negative unit clauses             : 2
% 0.19/0.52  #    Non-unit-clauses                  : 119
% 0.19/0.52  # Current number of unprocessed clauses: 7808
% 0.19/0.52  # ...number of literals in the above   : 37454
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 88
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 11904
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 8071
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 369
% 0.19/0.52  # Unit Clause-clause subsumption calls : 154
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 30
% 0.19/0.52  # BW rewrite match successes           : 13
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 199386
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.176 s
% 0.19/0.52  # System time              : 0.009 s
% 0.19/0.52  # Total time               : 0.185 s
% 0.19/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
