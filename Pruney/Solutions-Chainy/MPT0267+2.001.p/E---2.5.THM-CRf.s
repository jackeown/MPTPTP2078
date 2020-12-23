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
% DateTime   : Thu Dec  3 10:42:15 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   70 (1206 expanded)
%              Number of clauses        :   39 ( 489 expanded)
%              Number of leaves         :   15 ( 346 expanded)
%              Depth                    :   12
%              Number of atoms          :  159 (2385 expanded)
%              Number of equality atoms :   55 ( 998 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

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

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
      <=> ( r2_hidden(X1,X2)
          & X1 != X3 ) ) ),
    inference(assume_negation,[status(cth)],[t64_zfmisc_1])).

fof(c_0_16,negated_conjecture,
    ( ( ~ r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))
      | ~ r2_hidden(esk4_0,esk5_0)
      | esk4_0 = esk6_0 )
    & ( r2_hidden(esk4_0,esk5_0)
      | r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))) )
    & ( esk4_0 != esk6_0
      | r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

fof(c_0_17,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X43,X44,X45,X46] : k3_enumset1(X43,X43,X44,X45,X46) = k2_enumset1(X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X47,X48,X49,X50,X51] : k4_enumset1(X47,X47,X48,X49,X50,X51) = k3_enumset1(X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X52,X53,X54,X55,X56,X57] : k5_enumset1(X52,X52,X53,X54,X55,X56,X57) = k4_enumset1(X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X15,X17)
        | ~ r2_hidden(X15,k5_xboole_0(X16,X17)) )
      & ( r2_hidden(X15,X16)
        | r2_hidden(X15,X17)
        | ~ r2_hidden(X15,k5_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X15,X16)
        | r2_hidden(X15,X17)
        | r2_hidden(X15,k5_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X15,X17)
        | r2_hidden(X15,X16)
        | r2_hidden(X15,k5_xboole_0(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_38,plain,(
    ! [X26,X27] : r1_tarski(k3_xboole_0(X26,X27),X26) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = esk6_0
    | ~ r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk4_0,X1)
    | ~ r1_tarski(k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = esk4_0
    | ~ r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_45,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X30
        | X31 != k1_tarski(X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_tarski(X30) )
      & ( ~ r2_hidden(esk3_2(X34,X35),X35)
        | esk3_2(X34,X35) != X34
        | X35 = k1_tarski(X34) )
      & ( r2_hidden(esk3_2(X34,X35),X35)
        | esk3_2(X34,X35) = X34
        | X35 = k1_tarski(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_46,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = esk4_0
    | ~ r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

fof(c_0_49,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_51,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = esk4_0
    | r2_hidden(esk4_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_26]),c_0_27]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_28])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_26]),c_0_27]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( esk6_0 = esk4_0
    | r2_hidden(esk4_0,X1)
    | ~ r1_tarski(k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_55])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_59])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))
    | esk6_0 != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_67]),c_0_67]),c_0_67]),c_0_67]),c_0_67]),c_0_67]),c_0_67])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.47/1.64  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 1.47/1.64  # and selection function GSelectMinInfpos.
% 1.47/1.64  #
% 1.47/1.64  # Preprocessing time       : 0.028 s
% 1.47/1.64  # Presaturation interreduction done
% 1.47/1.64  
% 1.47/1.64  # Proof found!
% 1.47/1.64  # SZS status Theorem
% 1.47/1.64  # SZS output start CNFRefutation
% 1.47/1.64  fof(t64_zfmisc_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.47/1.64  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.47/1.64  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.47/1.64  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.47/1.64  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.47/1.64  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.47/1.64  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.47/1.64  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.47/1.64  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 1.47/1.64  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.47/1.64  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.47/1.64  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.47/1.64  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.47/1.64  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.47/1.64  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.47/1.64  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t64_zfmisc_1])).
% 1.47/1.64  fof(c_0_16, negated_conjecture, ((~r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))|(~r2_hidden(esk4_0,esk5_0)|esk4_0=esk6_0))&((r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))))&(esk4_0!=esk6_0|r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 1.47/1.64  fof(c_0_17, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.47/1.64  fof(c_0_18, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.47/1.64  fof(c_0_19, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.47/1.64  fof(c_0_20, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.47/1.64  fof(c_0_21, plain, ![X43, X44, X45, X46]:k3_enumset1(X43,X43,X44,X45,X46)=k2_enumset1(X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.47/1.64  fof(c_0_22, plain, ![X47, X48, X49, X50, X51]:k4_enumset1(X47,X47,X48,X49,X50,X51)=k3_enumset1(X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.47/1.64  fof(c_0_23, plain, ![X52, X53, X54, X55, X56, X57]:k5_enumset1(X52,X52,X53,X54,X55,X56,X57)=k4_enumset1(X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.47/1.64  fof(c_0_24, plain, ![X15, X16, X17]:(((~r2_hidden(X15,X16)|~r2_hidden(X15,X17)|~r2_hidden(X15,k5_xboole_0(X16,X17)))&(r2_hidden(X15,X16)|r2_hidden(X15,X17)|~r2_hidden(X15,k5_xboole_0(X16,X17))))&((~r2_hidden(X15,X16)|r2_hidden(X15,X17)|r2_hidden(X15,k5_xboole_0(X16,X17)))&(~r2_hidden(X15,X17)|r2_hidden(X15,X16)|r2_hidden(X15,k5_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 1.47/1.64  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.47/1.64  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.47/1.64  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.47/1.64  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.47/1.64  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.47/1.64  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.47/1.64  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.47/1.64  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.47/1.64  fof(c_0_33, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.47/1.64  cnf(c_0_34, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.47/1.64  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 1.47/1.64  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.47/1.64  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.47/1.64  fof(c_0_38, plain, ![X26, X27]:r1_tarski(k3_xboole_0(X26,X27),X26), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.47/1.64  cnf(c_0_39, negated_conjecture, (esk4_0=esk6_0|~r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.47/1.64  cnf(c_0_40, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,X1)|~r1_tarski(k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.47/1.64  cnf(c_0_41, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.47/1.64  cnf(c_0_42, negated_conjecture, (esk6_0=esk4_0|~r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 1.47/1.64  cnf(c_0_43, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.47/1.64  cnf(c_0_44, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.47/1.64  fof(c_0_45, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|X32=X30|X31!=k1_tarski(X30))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_tarski(X30)))&((~r2_hidden(esk3_2(X34,X35),X35)|esk3_2(X34,X35)!=X34|X35=k1_tarski(X34))&(r2_hidden(esk3_2(X34,X35),X35)|esk3_2(X34,X35)=X34|X35=k1_tarski(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.47/1.64  fof(c_0_46, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 1.47/1.64  cnf(c_0_47, negated_conjecture, (esk6_0=esk4_0|~r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 1.47/1.64  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 1.47/1.64  fof(c_0_49, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.47/1.64  cnf(c_0_50, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.47/1.64  fof(c_0_51, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk2_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk2_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.47/1.64  cnf(c_0_52, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.47/1.64  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.47/1.64  cnf(c_0_54, negated_conjecture, (esk6_0=esk4_0|r2_hidden(esk4_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.47/1.64  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.47/1.64  cnf(c_0_56, plain, (X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_26]), c_0_27]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 1.47/1.64  cnf(c_0_57, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.47/1.64  cnf(c_0_58, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_52, c_0_28])).
% 1.47/1.64  cnf(c_0_59, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_26]), c_0_27]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 1.47/1.64  cnf(c_0_60, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.47/1.64  cnf(c_0_61, negated_conjecture, (esk6_0=esk4_0|r2_hidden(esk4_0,X1)|~r1_tarski(k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 1.47/1.64  cnf(c_0_62, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_41, c_0_55])).
% 1.47/1.64  cnf(c_0_63, plain, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_56])).
% 1.47/1.64  cnf(c_0_64, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.47/1.64  cnf(c_0_65, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_59])])).
% 1.47/1.64  cnf(c_0_66, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))|esk6_0!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 1.47/1.64  cnf(c_0_67, negated_conjecture, (esk6_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 1.47/1.64  cnf(c_0_68, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.47/1.64  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_67]), c_0_67]), c_0_67]), c_0_67]), c_0_67]), c_0_67]), c_0_67])]), c_0_68]), ['proof']).
% 1.47/1.64  # SZS output end CNFRefutation
% 1.47/1.64  # Proof object total steps             : 70
% 1.47/1.64  # Proof object clause steps            : 39
% 1.47/1.64  # Proof object formula steps           : 31
% 1.47/1.64  # Proof object conjectures             : 18
% 1.47/1.64  # Proof object clause conjectures      : 15
% 1.47/1.64  # Proof object formula conjectures     : 3
% 1.47/1.64  # Proof object initial clauses used    : 19
% 1.47/1.64  # Proof object initial formulas used   : 15
% 1.47/1.64  # Proof object generating inferences   : 10
% 1.47/1.64  # Proof object simplifying inferences  : 50
% 1.47/1.64  # Training examples: 0 positive, 0 negative
% 1.47/1.64  # Parsed axioms                        : 15
% 1.47/1.64  # Removed by relevancy pruning/SinE    : 0
% 1.47/1.64  # Initial clauses                      : 27
% 1.47/1.64  # Removed in clause preprocessing      : 7
% 1.47/1.64  # Initial clauses in saturation        : 20
% 1.47/1.64  # Processed clauses                    : 4132
% 1.47/1.64  # ...of these trivial                  : 73
% 1.47/1.64  # ...subsumed                          : 2877
% 1.47/1.64  # ...remaining for further processing  : 1182
% 1.47/1.64  # Other redundant clauses eliminated   : 18
% 1.47/1.64  # Clauses deleted for lack of memory   : 0
% 1.47/1.64  # Backward-subsumed                    : 14
% 1.47/1.64  # Backward-rewritten                   : 48
% 1.47/1.64  # Generated clauses                    : 73753
% 1.47/1.64  # ...of the previous two non-trivial   : 71283
% 1.47/1.64  # Contextual simplify-reflections      : 3
% 1.47/1.64  # Paramodulations                      : 73664
% 1.47/1.64  # Factorizations                       : 72
% 1.47/1.64  # Equation resolutions                 : 18
% 1.47/1.64  # Propositional unsat checks           : 0
% 1.47/1.64  #    Propositional check models        : 0
% 1.47/1.64  #    Propositional check unsatisfiable : 0
% 1.47/1.64  #    Propositional clauses             : 0
% 1.47/1.64  #    Propositional clauses after purity: 0
% 1.47/1.64  #    Propositional unsat core size     : 0
% 1.47/1.64  #    Propositional preprocessing time  : 0.000
% 1.47/1.64  #    Propositional encoding time       : 0.000
% 1.47/1.64  #    Propositional solver time         : 0.000
% 1.47/1.64  #    Success case prop preproc time    : 0.000
% 1.47/1.64  #    Success case prop encoding time   : 0.000
% 1.47/1.64  #    Success case prop solver time     : 0.000
% 1.47/1.64  # Current number of processed clauses  : 1098
% 1.47/1.64  #    Positive orientable unit clauses  : 102
% 1.47/1.64  #    Positive unorientable unit clauses: 1
% 1.47/1.64  #    Negative unit clauses             : 262
% 1.47/1.64  #    Non-unit-clauses                  : 733
% 1.47/1.64  # Current number of unprocessed clauses: 67060
% 1.47/1.64  # ...number of literals in the above   : 303736
% 1.47/1.64  # Current number of archived formulas  : 0
% 1.47/1.64  # Current number of archived clauses   : 89
% 1.47/1.64  # Clause-clause subsumption calls (NU) : 55418
% 1.47/1.64  # Rec. Clause-clause subsumption calls : 47343
% 1.47/1.64  # Non-unit clause-clause subsumptions  : 1125
% 1.47/1.64  # Unit Clause-clause subsumption calls : 15762
% 1.47/1.64  # Rewrite failures with RHS unbound    : 0
% 1.47/1.64  # BW rewrite match attempts            : 541
% 1.47/1.64  # BW rewrite match successes           : 24
% 1.47/1.64  # Condensation attempts                : 0
% 1.47/1.64  # Condensation successes               : 0
% 1.47/1.64  # Termbank termtop insertions          : 1750317
% 1.47/1.64  
% 1.47/1.64  # -------------------------------------------------
% 1.47/1.64  # User time                : 1.253 s
% 1.47/1.64  # System time              : 0.046 s
% 1.47/1.64  # Total time               : 1.299 s
% 1.47/1.64  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
