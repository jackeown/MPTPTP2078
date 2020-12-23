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
% DateTime   : Thu Dec  3 10:40:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  100 (1453 expanded)
%              Number of clauses        :   57 ( 567 expanded)
%              Number of leaves         :   21 ( 431 expanded)
%              Depth                    :   19
%              Number of atoms          :  179 (2060 expanded)
%              Number of equality atoms :  111 (1685 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t44_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_21,plain,(
    ! [X70,X71] : k3_tarski(k2_tarski(X70,X71)) = k2_xboole_0(X70,X71) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X46,X47,X48,X49] : k3_enumset1(X46,X46,X47,X48,X49) = k2_enumset1(X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X50,X51,X52,X53,X54] : k4_enumset1(X50,X50,X51,X52,X53,X54) = k3_enumset1(X50,X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X55,X56,X57,X58,X59,X60] : k5_enumset1(X55,X55,X56,X57,X58,X59,X60) = k4_enumset1(X55,X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X61,X62,X63,X64,X65,X66,X67] : k6_enumset1(X61,X61,X62,X63,X64,X65,X66,X67) = k5_enumset1(X61,X62,X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & esk5_0 != esk6_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_33,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_34,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_35,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X31
        | X34 = X32
        | X33 != k2_tarski(X31,X32) )
      & ( X35 != X31
        | r2_hidden(X35,X33)
        | X33 != k2_tarski(X31,X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k2_tarski(X31,X32) )
      & ( esk3_3(X36,X37,X38) != X36
        | ~ r2_hidden(esk3_3(X36,X37,X38),X38)
        | X38 = k2_tarski(X36,X37) )
      & ( esk3_3(X36,X37,X38) != X37
        | ~ r2_hidden(esk3_3(X36,X37,X38),X38)
        | X38 = k2_tarski(X36,X37) )
      & ( r2_hidden(esk3_3(X36,X37,X38),X38)
        | esk3_3(X36,X37,X38) = X36
        | esk3_3(X36,X37,X38) = X37
        | X38 = k2_tarski(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_26]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

fof(c_0_50,plain,(
    ! [X29,X30] : k3_xboole_0(X29,X30) = k5_xboole_0(k5_xboole_0(X29,X30),k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_51,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_55,plain,(
    ! [X20,X21] : r1_tarski(k4_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_56,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_26]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_37]),c_0_38]),c_0_39])).

fof(c_0_63,plain,(
    ! [X25,X26,X27] : k5_xboole_0(k5_xboole_0(X25,X26),X27) = k5_xboole_0(X25,k5_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_64,plain,(
    ! [X28] : k5_xboole_0(X28,X28) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_65,plain,(
    ! [X68,X69] :
      ( ( ~ r1_tarski(k1_tarski(X68),X69)
        | r2_hidden(X68,X69) )
      & ( ~ r2_hidden(X68,X69)
        | r1_tarski(k1_tarski(X68),X69) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_66,negated_conjecture,
    ( esk2_1(esk5_0) = X1
    | esk2_1(esk5_0) = X2
    | k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_70,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( esk2_1(esk5_0) = esk4_0 ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),X1) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_76,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_77,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_44]),c_0_26]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_72]),c_0_54])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_49])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_75])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_74]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_53])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk6_0,esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( X1 = esk4_0
    | X2 != esk5_0
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk2_1(k5_xboole_0(esk6_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( esk2_1(k5_xboole_0(esk6_0,esk5_0)) = esk4_0
    | k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = esk5_0
    | ~ r1_tarski(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk4_0,k5_xboole_0(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = esk5_0
    | ~ r1_tarski(esk5_0,k5_xboole_0(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_84]),c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0
    | r1_tarski(esk5_0,k5_xboole_0(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_90]),c_0_84])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0
    | k5_xboole_0(esk6_0,esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_74,c_0_80])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_69]),c_0_75]),c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_75]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.14/0.39  # and selection function SelectNegativeLiterals.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.14/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.39  fof(t44_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.14/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.14/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.39  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.14/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.14/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.14/0.39  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.14/0.39  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.14/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.14/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.39  fof(c_0_21, plain, ![X70, X71]:k3_tarski(k2_tarski(X70,X71))=k2_xboole_0(X70,X71), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.14/0.39  fof(c_0_22, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.39  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t44_zfmisc_1])).
% 0.14/0.39  fof(c_0_24, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.14/0.39  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  fof(c_0_27, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.39  fof(c_0_28, plain, ![X46, X47, X48, X49]:k3_enumset1(X46,X46,X47,X48,X49)=k2_enumset1(X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.39  fof(c_0_29, plain, ![X50, X51, X52, X53, X54]:k4_enumset1(X50,X50,X51,X52,X53,X54)=k3_enumset1(X50,X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.39  fof(c_0_30, plain, ![X55, X56, X57, X58, X59, X60]:k5_enumset1(X55,X55,X56,X57,X58,X59,X60)=k4_enumset1(X55,X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.39  fof(c_0_31, plain, ![X61, X62, X63, X64, X65, X66, X67]:k6_enumset1(X61,X61,X62,X63,X64,X65,X66,X67)=k5_enumset1(X61,X62,X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.39  fof(c_0_32, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&esk5_0!=esk6_0)&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.14/0.39  fof(c_0_33, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.39  fof(c_0_34, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.39  fof(c_0_35, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.39  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.39  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.39  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.39  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  cnf(c_0_44, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.39  fof(c_0_45, plain, ![X31, X32, X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X34,X33)|(X34=X31|X34=X32)|X33!=k2_tarski(X31,X32))&((X35!=X31|r2_hidden(X35,X33)|X33!=k2_tarski(X31,X32))&(X35!=X32|r2_hidden(X35,X33)|X33!=k2_tarski(X31,X32))))&(((esk3_3(X36,X37,X38)!=X36|~r2_hidden(esk3_3(X36,X37,X38),X38)|X38=k2_tarski(X36,X37))&(esk3_3(X36,X37,X38)!=X37|~r2_hidden(esk3_3(X36,X37,X38),X38)|X38=k2_tarski(X36,X37)))&(r2_hidden(esk3_3(X36,X37,X38),X38)|(esk3_3(X36,X37,X38)=X36|esk3_3(X36,X37,X38)=X37)|X38=k2_tarski(X36,X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.39  cnf(c_0_46, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  cnf(c_0_47, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_48, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_26]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.14/0.39  fof(c_0_50, plain, ![X29, X30]:k3_xboole_0(X29,X30)=k5_xboole_0(k5_xboole_0(X29,X30),k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.14/0.39  cnf(c_0_51, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.39  cnf(c_0_52, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  fof(c_0_55, plain, ![X20, X21]:r1_tarski(k4_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.14/0.39  fof(c_0_56, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.39  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.39  cnf(c_0_58, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_26]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (r2_hidden(esk2_1(esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.14/0.39  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.39  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.39  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.39  fof(c_0_63, plain, ![X25, X26, X27]:k5_xboole_0(k5_xboole_0(X25,X26),X27)=k5_xboole_0(X25,k5_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.14/0.39  fof(c_0_64, plain, ![X28]:k5_xboole_0(X28,X28)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.14/0.39  fof(c_0_65, plain, ![X68, X69]:((~r1_tarski(k1_tarski(X68),X69)|r2_hidden(X68,X69))&(~r2_hidden(X68,X69)|r1_tarski(k1_tarski(X68),X69))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.14/0.39  cnf(c_0_66, negated_conjecture, (esk2_1(esk5_0)=X1|esk2_1(esk5_0)=X2|k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.14/0.39  cnf(c_0_67, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_40]), c_0_41]), c_0_42])).
% 0.14/0.39  cnf(c_0_68, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.14/0.39  cnf(c_0_69, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.14/0.39  fof(c_0_70, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.14/0.39  cnf(c_0_71, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.14/0.39  cnf(c_0_72, negated_conjecture, (esk2_1(esk5_0)=esk4_0), inference(er,[status(thm)],[c_0_66])).
% 0.14/0.39  cnf(c_0_73, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),X1)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.14/0.39  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.14/0.39  cnf(c_0_75, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.14/0.39  fof(c_0_76, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.39  cnf(c_0_77, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_44]), c_0_26]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.14/0.39  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_72]), c_0_54])).
% 0.14/0.39  cnf(c_0_79, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_49])).
% 0.14/0.39  cnf(c_0_80, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_69]), c_0_75])).
% 0.14/0.39  cnf(c_0_81, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.14/0.39  cnf(c_0_82, negated_conjecture, (r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.14/0.39  cnf(c_0_83, negated_conjecture, (r1_tarski(k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_74]), c_0_80])).
% 0.14/0.39  cnf(c_0_84, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_53])])).
% 0.14/0.39  cnf(c_0_85, negated_conjecture, (r1_tarski(k5_xboole_0(esk6_0,esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.14/0.39  cnf(c_0_86, negated_conjecture, (X1=esk4_0|X2!=esk5_0|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_84])).
% 0.14/0.39  cnf(c_0_87, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0|r2_hidden(esk2_1(k5_xboole_0(esk6_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_85])).
% 0.14/0.39  cnf(c_0_88, negated_conjecture, (esk2_1(k5_xboole_0(esk6_0,esk5_0))=esk4_0|k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.14/0.39  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=esk5_0|~r1_tarski(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_81, c_0_83])).
% 0.14/0.39  cnf(c_0_90, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0|r2_hidden(esk4_0,k5_xboole_0(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_88])).
% 0.14/0.39  cnf(c_0_91, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=esk5_0|~r1_tarski(esk5_0,k5_xboole_0(esk6_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_84]), c_0_84])).
% 0.14/0.39  cnf(c_0_92, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0|r1_tarski(esk5_0,k5_xboole_0(esk6_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_90]), c_0_84])).
% 0.14/0.39  cnf(c_0_93, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_68])).
% 0.14/0.39  cnf(c_0_94, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0|k5_xboole_0(esk6_0,esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.14/0.39  cnf(c_0_95, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  cnf(c_0_96, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_74, c_0_80])).
% 0.14/0.39  cnf(c_0_97, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_69]), c_0_75]), c_0_95])).
% 0.14/0.39  cnf(c_0_98, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_75]), c_0_98]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 100
% 0.14/0.39  # Proof object clause steps            : 57
% 0.14/0.39  # Proof object formula steps           : 43
% 0.14/0.39  # Proof object conjectures             : 28
% 0.14/0.39  # Proof object clause conjectures      : 25
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 24
% 0.14/0.39  # Proof object initial formulas used   : 21
% 0.14/0.39  # Proof object generating inferences   : 21
% 0.14/0.39  # Proof object simplifying inferences  : 59
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 21
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 34
% 0.14/0.39  # Removed in clause preprocessing      : 10
% 0.14/0.39  # Initial clauses in saturation        : 24
% 0.14/0.39  # Processed clauses                    : 97
% 0.14/0.39  # ...of these trivial                  : 3
% 0.14/0.39  # ...subsumed                          : 14
% 0.14/0.39  # ...remaining for further processing  : 80
% 0.14/0.39  # Other redundant clauses eliminated   : 7
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 25
% 0.14/0.39  # Generated clauses                    : 308
% 0.14/0.39  # ...of the previous two non-trivial   : 255
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 293
% 0.14/0.39  # Factorizations                       : 1
% 0.14/0.39  # Equation resolutions                 : 14
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 51
% 0.14/0.39  #    Positive orientable unit clauses  : 17
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 3
% 0.14/0.39  #    Non-unit-clauses                  : 31
% 0.14/0.39  # Current number of unprocessed clauses: 176
% 0.14/0.39  # ...number of literals in the above   : 575
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 35
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 106
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 84
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 13
% 0.14/0.39  # Unit Clause-clause subsumption calls : 4
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 25
% 0.14/0.39  # BW rewrite match successes           : 6
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 5822
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.036 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.040 s
% 0.14/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
