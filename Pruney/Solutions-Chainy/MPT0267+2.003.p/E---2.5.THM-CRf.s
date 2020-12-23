%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:16 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 (2922 expanded)
%              Number of clauses        :   43 (1144 expanded)
%              Number of leaves         :   17 ( 857 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 (5260 expanded)
%              Number of equality atoms :   61 (2390 expanded)
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

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

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

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
      <=> ( r2_hidden(X1,X2)
          & X1 != X3 ) ) ),
    inference(assume_negation,[status(cth)],[t64_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_19,plain,(
    ! [X19,X20] : r1_xboole_0(k3_xboole_0(X19,X20),k5_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_20,negated_conjecture,
    ( ( ~ r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))
      | ~ r2_hidden(esk3_0,esk4_0)
      | esk3_0 = esk5_0 )
    & ( r2_hidden(esk3_0,esk4_0)
      | r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))) )
    & ( esk3_0 != esk5_0
      | r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_21,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X46,X47,X48,X49,X50] : k4_enumset1(X46,X46,X47,X48,X49,X50) = k3_enumset1(X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k5_enumset1(X51,X51,X52,X53,X54,X55,X56) = k4_enumset1(X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63) = k5_enumset1(X57,X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_41,plain,(
    ! [X23,X24] : r1_tarski(k3_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_42,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_43,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r2_hidden(X10,X11)
        | ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X12)
        | r2_hidden(X10,X11)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k3_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 = esk5_0
    | ~ r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_54,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X31,X30)
        | X31 = X29
        | X30 != k1_tarski(X29) )
      & ( X32 != X29
        | r2_hidden(X32,X30)
        | X30 != k1_tarski(X29) )
      & ( ~ r2_hidden(esk2_2(X33,X34),X34)
        | esk2_2(X33,X34) != X33
        | X34 = k1_tarski(X33) )
      & ( r2_hidden(esk2_2(X33,X34),X34)
        | esk2_2(X33,X34) = X33
        | X34 = k1_tarski(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_58,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_59,plain,(
    ! [X27,X28] : r1_xboole_0(k4_xboole_0(X27,X28),X28) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_56])])).

cnf(c_0_62,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_32]),c_0_33]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))
    | esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk3_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(esk3_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_34])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_32]),c_0_33]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))
    | esk5_0 != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_69])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72])])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_75,c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.38  # and selection function GSelectMinInfpos.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t64_zfmisc_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.38  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.38  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.20/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t64_zfmisc_1])).
% 0.20/0.38  fof(c_0_18, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk1_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk1_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.38  fof(c_0_19, plain, ![X19, X20]:r1_xboole_0(k3_xboole_0(X19,X20),k5_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.20/0.38  fof(c_0_20, negated_conjecture, ((~r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))|(~r2_hidden(esk3_0,esk4_0)|esk3_0=esk5_0))&((r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0))))&(esk3_0!=esk5_0|r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_22, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  fof(c_0_24, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_25, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_26, plain, ![X46, X47, X48, X49, X50]:k4_enumset1(X46,X46,X47,X48,X49,X50)=k3_enumset1(X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_27, plain, ![X51, X52, X53, X54, X55, X56]:k5_enumset1(X51,X51,X52,X53,X54,X55,X56)=k4_enumset1(X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.38  fof(c_0_28, plain, ![X57, X58, X59, X60, X61, X62, X63]:k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63)=k5_enumset1(X57,X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.38  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_30, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  fof(c_0_40, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.38  fof(c_0_41, plain, ![X23, X24]:r1_tarski(k3_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.38  fof(c_0_42, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.38  fof(c_0_43, plain, ![X10, X11, X12]:(((~r2_hidden(X10,X11)|~r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12)))&(r2_hidden(X10,X11)|r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12))))&((~r2_hidden(X10,X11)|r2_hidden(X10,X12)|r2_hidden(X10,k5_xboole_0(X11,X12)))&(~r2_hidden(X10,X12)|r2_hidden(X10,X11)|r2_hidden(X10,k5_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.20/0.38  cnf(c_0_44, plain, (~r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.38  cnf(c_0_49, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k3_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_51, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (esk3_0=esk5_0|~r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))|~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_54, plain, ![X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X31,X30)|X31=X29|X30!=k1_tarski(X29))&(X32!=X29|r2_hidden(X32,X30)|X30!=k1_tarski(X29)))&((~r2_hidden(esk2_2(X33,X34),X34)|esk2_2(X33,X34)!=X33|X34=k1_tarski(X33))&(r2_hidden(esk2_2(X33,X34),X34)|esk2_2(X33,X34)=X33|X34=k1_tarski(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_55, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (esk5_0=esk3_0|~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_58, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.38  fof(c_0_59, plain, ![X27, X28]:r1_xboole_0(k4_xboole_0(X27,X28),X28), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1))|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (esk5_0=esk3_0|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_56])])).
% 0.20/0.38  cnf(c_0_62, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_32]), c_0_33]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_63, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  cnf(c_0_64, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(esk4_0,k1_tarski(esk5_0)))|esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_0,X1)|~r2_hidden(esk3_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (esk5_0=esk3_0|r2_hidden(esk3_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.20/0.38  cnf(c_0_68, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_62])).
% 0.20/0.38  cnf(c_0_69, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_63, c_0_34])).
% 0.20/0.38  cnf(c_0_70, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_32]), c_0_33]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))|esk5_0!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (esk5_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.20/0.38  cnf(c_0_73, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_29, c_0_69])).
% 0.20/0.38  cnf(c_0_74, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72])])).
% 0.20/0.38  cnf(c_0_76, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_75, c_0_76]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 78
% 0.20/0.38  # Proof object clause steps            : 43
% 0.20/0.38  # Proof object formula steps           : 35
% 0.20/0.38  # Proof object conjectures             : 19
% 0.20/0.38  # Proof object clause conjectures      : 16
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 21
% 0.20/0.38  # Proof object initial formulas used   : 17
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 59
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 17
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 27
% 0.20/0.38  # Removed in clause preprocessing      : 8
% 0.20/0.38  # Initial clauses in saturation        : 19
% 0.20/0.38  # Processed clauses                    : 149
% 0.20/0.38  # ...of these trivial                  : 7
% 0.20/0.38  # ...subsumed                          : 42
% 0.20/0.38  # ...remaining for further processing  : 100
% 0.20/0.38  # Other redundant clauses eliminated   : 4
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 8
% 0.20/0.38  # Backward-rewritten                   : 11
% 0.20/0.38  # Generated clauses                    : 374
% 0.20/0.38  # ...of the previous two non-trivial   : 330
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 370
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 4
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 59
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 18
% 0.20/0.38  #    Non-unit-clauses                  : 27
% 0.20/0.38  # Current number of unprocessed clauses: 214
% 0.20/0.38  # ...number of literals in the above   : 589
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 47
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 226
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 218
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.38  # Unit Clause-clause subsumption calls : 60
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 18
% 0.20/0.38  # BW rewrite match successes           : 12
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6067
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.036 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.042 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
