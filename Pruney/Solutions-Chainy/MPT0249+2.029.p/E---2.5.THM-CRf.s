%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:02 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  136 (3232 expanded)
%              Number of clauses        :   91 (1302 expanded)
%              Number of leaves         :   22 ( 951 expanded)
%              Depth                    :   23
%              Number of atoms          :  252 (4120 expanded)
%              Number of equality atoms :  120 (3466 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_22,plain,(
    ! [X70,X71] : k3_tarski(k2_tarski(X70,X71)) = k2_xboole_0(X70,X71) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_26,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X48,X49,X50,X51] : k3_enumset1(X48,X48,X49,X50,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X52,X53,X54,X55,X56] : k4_enumset1(X52,X52,X53,X54,X55,X56) = k3_enumset1(X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X57,X58,X59,X60,X61,X62] : k5_enumset1(X57,X57,X58,X59,X60,X61,X62) = k4_enumset1(X57,X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X63,X64,X65,X66,X67,X68,X69] : k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69) = k5_enumset1(X63,X64,X65,X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_33,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & esk5_0 != esk6_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_34,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_35,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X37,X36)
        | X37 = X35
        | X36 != k1_tarski(X35) )
      & ( X38 != X35
        | r2_hidden(X38,X36)
        | X36 != k1_tarski(X35) )
      & ( ~ r2_hidden(esk3_2(X39,X40),X40)
        | esk3_2(X39,X40) != X39
        | X40 = k1_tarski(X39) )
      & ( r2_hidden(esk3_2(X39,X40),X40)
        | esk3_2(X39,X40) = X39
        | X40 = k1_tarski(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_37,plain,(
    ! [X19] :
      ( X19 = k1_xboole_0
      | r2_hidden(esk2_1(X19),X19) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_27]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_52,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_46]),c_0_27]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_57,plain,(
    ! [X33,X34] : k3_xboole_0(X33,X34) = k5_xboole_0(k5_xboole_0(X33,X34),k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

fof(c_0_61,plain,(
    ! [X15] : k3_xboole_0(X15,X15) = X15 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_63,plain,(
    ! [X14] : k2_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_64,plain,(
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

cnf(c_0_65,negated_conjecture,
    ( esk2_1(esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

fof(c_0_67,plain,(
    ! [X25,X26] : r1_tarski(k4_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_68,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_39]),c_0_40]),c_0_41])).

fof(c_0_71,plain,(
    ! [X32] : k5_xboole_0(X32,X32) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_65]),c_0_55])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( esk1_2(esk5_0,X1) = esk4_0
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_66])).

cnf(c_0_78,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_80,plain,(
    ! [X29,X30,X31] : k5_xboole_0(k5_xboole_0(X29,X30),X31) = k5_xboole_0(X29,k5_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_46]),c_0_27]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

fof(c_0_87,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_89,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_70]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ r2_hidden(esk4_0,k5_xboole_0(X2,k5_xboole_0(esk5_0,X1)))
    | ~ r2_hidden(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r1_tarski(esk5_0,k5_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_85])).

cnf(c_0_96,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),X1) ),
    inference(rw,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_82]),c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(esk5_0,X1) = esk5_0
    | r2_hidden(esk4_0,X1)
    | ~ r1_tarski(k5_xboole_0(esk5_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))),X2) ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_90])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_97,c_0_82])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))
    | ~ r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_51])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_101]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_97])).

cnf(c_0_108,negated_conjecture,
    ( k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = esk5_0
    | r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))) = k5_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_106,c_0_90])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = esk5_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_97])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k5_xboole_0(esk5_0,esk6_0)
    | r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_110]),c_0_111])).

cnf(c_0_113,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_114,plain,
    ( esk1_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = X1
    | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_115,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(X1,k5_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_112])).

cnf(c_0_116,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),k5_xboole_0(X2,X1))
    | r2_hidden(esk2_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_49])).

cnf(c_0_117,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_118,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( esk2_1(esk6_0) = esk4_0
    | r2_hidden(esk2_1(esk6_0),esk5_0)
    | r2_hidden(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0
    | ~ r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_54])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_74])).

cnf(c_0_122,negated_conjecture,
    ( esk2_1(esk6_0) = esk4_0
    | r2_hidden(esk2_1(esk6_0),X1)
    | r2_hidden(esk4_0,esk6_0)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121])])).

cnf(c_0_124,negated_conjecture,
    ( k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k1_xboole_0
    | r2_hidden(esk2_1(k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_105])).

cnf(c_0_125,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk2_1(X1),k5_xboole_0(X2,X1))
    | ~ r2_hidden(esk2_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_49])).

cnf(c_0_126,negated_conjecture,
    ( esk2_1(esk6_0) = esk4_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_54]),c_0_58])).

cnf(c_0_127,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( k5_xboole_0(esk5_0,esk6_0) = k1_xboole_0
    | r2_hidden(esk2_1(k5_xboole_0(esk5_0,esk6_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_123]),c_0_111]),c_0_123]),c_0_111])).

cnf(c_0_129,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k5_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_65]),c_0_55])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_126]),c_0_117])).

cnf(c_0_131,negated_conjecture,
    ( esk2_1(k5_xboole_0(esk5_0,esk6_0)) = esk4_0
    | k5_xboole_0(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k5_xboole_0(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_111])).

cnf(c_0_133,negated_conjecture,
    ( k5_xboole_0(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_131]),c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_133]),c_0_102]),c_0_134]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.92/1.13  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.92/1.13  # and selection function GSelectMinInfpos.
% 0.92/1.13  #
% 0.92/1.13  # Preprocessing time       : 0.027 s
% 0.92/1.13  # Presaturation interreduction done
% 0.92/1.13  
% 0.92/1.13  # Proof found!
% 0.92/1.13  # SZS status Theorem
% 0.92/1.13  # SZS output start CNFRefutation
% 0.92/1.13  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.92/1.13  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.92/1.13  fof(t44_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.92/1.13  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.92/1.13  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.92/1.14  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.92/1.14  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.92/1.14  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.92/1.14  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.92/1.14  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.92/1.14  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.92/1.14  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.92/1.14  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.92/1.14  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.92/1.14  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.92/1.14  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.92/1.14  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.92/1.14  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.92/1.14  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.92/1.14  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.92/1.14  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.92/1.14  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.92/1.14  fof(c_0_22, plain, ![X70, X71]:k3_tarski(k2_tarski(X70,X71))=k2_xboole_0(X70,X71), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.92/1.14  fof(c_0_23, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.92/1.14  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t44_zfmisc_1])).
% 0.92/1.14  fof(c_0_25, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.92/1.14  cnf(c_0_26, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.92/1.14  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.14  fof(c_0_28, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.92/1.14  fof(c_0_29, plain, ![X48, X49, X50, X51]:k3_enumset1(X48,X48,X49,X50,X51)=k2_enumset1(X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.92/1.14  fof(c_0_30, plain, ![X52, X53, X54, X55, X56]:k4_enumset1(X52,X52,X53,X54,X55,X56)=k3_enumset1(X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.92/1.14  fof(c_0_31, plain, ![X57, X58, X59, X60, X61, X62]:k5_enumset1(X57,X57,X58,X59,X60,X61,X62)=k4_enumset1(X57,X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.92/1.14  fof(c_0_32, plain, ![X63, X64, X65, X66, X67, X68, X69]:k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69)=k5_enumset1(X63,X64,X65,X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.92/1.14  fof(c_0_33, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&esk5_0!=esk6_0)&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.92/1.14  fof(c_0_34, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.92/1.14  fof(c_0_35, plain, ![X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X37,X36)|X37=X35|X36!=k1_tarski(X35))&(X38!=X35|r2_hidden(X38,X36)|X36!=k1_tarski(X35)))&((~r2_hidden(esk3_2(X39,X40),X40)|esk3_2(X39,X40)!=X39|X40=k1_tarski(X39))&(r2_hidden(esk3_2(X39,X40),X40)|esk3_2(X39,X40)=X39|X40=k1_tarski(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.92/1.14  fof(c_0_36, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.92/1.14  fof(c_0_37, plain, ![X19]:(X19=k1_xboole_0|r2_hidden(esk2_1(X19),X19)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.92/1.14  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.92/1.14  cnf(c_0_39, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.92/1.14  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.14  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.92/1.14  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.92/1.14  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.92/1.14  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.92/1.14  cnf(c_0_45, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.92/1.14  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.92/1.14  cnf(c_0_47, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.92/1.14  cnf(c_0_48, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.14  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.92/1.14  cnf(c_0_50, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.92/1.14  cnf(c_0_51, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_27]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.92/1.14  cnf(c_0_52, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_46]), c_0_27]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.92/1.14  cnf(c_0_53, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.92/1.14  cnf(c_0_54, negated_conjecture, (r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.92/1.14  cnf(c_0_55, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.92/1.14  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.14  fof(c_0_57, plain, ![X33, X34]:k3_xboole_0(X33,X34)=k5_xboole_0(k5_xboole_0(X33,X34),k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.92/1.14  cnf(c_0_58, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_52])).
% 0.92/1.14  cnf(c_0_59, negated_conjecture, (r2_hidden(esk2_1(esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.92/1.14  cnf(c_0_60, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_48, c_0_56])).
% 0.92/1.14  fof(c_0_61, plain, ![X15]:k3_xboole_0(X15,X15)=X15, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.92/1.14  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.92/1.14  fof(c_0_63, plain, ![X14]:k2_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.92/1.14  fof(c_0_64, plain, ![X16, X17, X18]:(((~r2_hidden(X16,X17)|~r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18)))&(r2_hidden(X16,X17)|r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18))))&((~r2_hidden(X16,X17)|r2_hidden(X16,X18)|r2_hidden(X16,k5_xboole_0(X17,X18)))&(~r2_hidden(X16,X18)|r2_hidden(X16,X17)|r2_hidden(X16,k5_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.92/1.14  cnf(c_0_65, negated_conjecture, (esk2_1(esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.92/1.14  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 0.92/1.14  fof(c_0_67, plain, ![X25, X26]:r1_tarski(k4_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.92/1.14  fof(c_0_68, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.92/1.14  cnf(c_0_69, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.92/1.14  cnf(c_0_70, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_39]), c_0_40]), c_0_41])).
% 0.92/1.14  fof(c_0_71, plain, ![X32]:k5_xboole_0(X32,X32)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.92/1.14  cnf(c_0_72, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.92/1.14  cnf(c_0_73, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.92/1.14  cnf(c_0_74, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_65]), c_0_55])).
% 0.92/1.14  cnf(c_0_75, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.92/1.14  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.14  cnf(c_0_77, negated_conjecture, (esk1_2(esk5_0,X1)=esk4_0|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_66])).
% 0.92/1.14  cnf(c_0_78, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.92/1.14  cnf(c_0_79, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.92/1.14  fof(c_0_80, plain, ![X29, X30, X31]:k5_xboole_0(k5_xboole_0(X29,X30),X31)=k5_xboole_0(X29,k5_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.92/1.14  cnf(c_0_81, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_42]), c_0_43]), c_0_44])).
% 0.92/1.14  cnf(c_0_82, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.92/1.14  cnf(c_0_83, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.92/1.14  cnf(c_0_84, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.92/1.14  cnf(c_0_85, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.92/1.14  cnf(c_0_86, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_46]), c_0_27]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.92/1.14  fof(c_0_87, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.92/1.14  cnf(c_0_88, negated_conjecture, (r1_tarski(esk5_0,X1)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.92/1.14  cnf(c_0_89, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_70]), c_0_42]), c_0_43]), c_0_44])).
% 0.92/1.14  cnf(c_0_90, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.92/1.14  cnf(c_0_91, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.92/1.14  cnf(c_0_92, negated_conjecture, (r2_hidden(esk4_0,X1)|~r2_hidden(esk4_0,k5_xboole_0(X2,k5_xboole_0(esk5_0,X1)))|~r2_hidden(esk4_0,X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.92/1.14  cnf(c_0_93, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).
% 0.92/1.14  cnf(c_0_94, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.92/1.14  cnf(c_0_95, negated_conjecture, (r2_hidden(esk4_0,X1)|r1_tarski(esk5_0,k5_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_88, c_0_85])).
% 0.92/1.14  cnf(c_0_96, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),X1)), inference(rw,[status(thm)],[c_0_89, c_0_90])).
% 0.92/1.14  cnf(c_0_97, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_82]), c_0_91])).
% 0.92/1.14  cnf(c_0_98, negated_conjecture, (r2_hidden(esk4_0,X1)|~r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.92/1.14  cnf(c_0_99, negated_conjecture, (k5_xboole_0(esk5_0,X1)=esk5_0|r2_hidden(esk4_0,X1)|~r1_tarski(k5_xboole_0(esk5_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.92/1.14  cnf(c_0_100, plain, (r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))),X2)), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.92/1.14  cnf(c_0_101, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_90])).
% 0.92/1.14  cnf(c_0_102, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_97, c_0_82])).
% 0.92/1.14  cnf(c_0_103, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))|~r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1))), inference(spm,[status(thm)],[c_0_98, c_0_97])).
% 0.92/1.14  cnf(c_0_104, negated_conjecture, (X1=esk5_0|r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_99, c_0_97])).
% 0.92/1.14  cnf(c_0_105, negated_conjecture, (r1_tarski(k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),esk5_0)), inference(spm,[status(thm)],[c_0_100, c_0_51])).
% 0.92/1.14  cnf(c_0_106, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_101]), c_0_102])).
% 0.92/1.14  cnf(c_0_107, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_97])).
% 0.92/1.14  cnf(c_0_108, negated_conjecture, (k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=esk5_0|r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.92/1.14  cnf(c_0_109, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1)))=k5_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_106, c_0_90])).
% 0.92/1.14  cnf(c_0_110, negated_conjecture, (k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=esk5_0|r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_97])).
% 0.92/1.14  cnf(c_0_111, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_97, c_0_106])).
% 0.92/1.14  cnf(c_0_112, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k5_xboole_0(esk5_0,esk6_0)|r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_110]), c_0_111])).
% 0.92/1.14  cnf(c_0_113, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.92/1.14  cnf(c_0_114, plain, (esk1_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=X1|r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.92/1.14  cnf(c_0_115, negated_conjecture, (X1=esk4_0|r2_hidden(esk4_0,esk6_0)|~r2_hidden(X1,k5_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_58, c_0_112])).
% 0.92/1.14  cnf(c_0_116, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),k5_xboole_0(X2,X1))|r2_hidden(esk2_1(X1),X2)), inference(spm,[status(thm)],[c_0_113, c_0_49])).
% 0.92/1.14  cnf(c_0_117, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.92/1.14  cnf(c_0_118, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_76, c_0_114])).
% 0.92/1.14  cnf(c_0_119, negated_conjecture, (esk2_1(esk6_0)=esk4_0|r2_hidden(esk2_1(esk6_0),esk5_0)|r2_hidden(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])).
% 0.92/1.14  cnf(c_0_120, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0|~r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_54])).
% 0.92/1.14  cnf(c_0_121, negated_conjecture, (r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_118, c_0_74])).
% 0.92/1.14  cnf(c_0_122, negated_conjecture, (esk2_1(esk6_0)=esk4_0|r2_hidden(esk2_1(esk6_0),X1)|r2_hidden(esk4_0,esk6_0)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_119])).
% 0.92/1.14  cnf(c_0_123, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_121])])).
% 0.92/1.14  cnf(c_0_124, negated_conjecture, (k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k1_xboole_0|r2_hidden(esk2_1(k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_105])).
% 0.92/1.14  cnf(c_0_125, plain, (X1=k1_xboole_0|~r2_hidden(esk2_1(X1),k5_xboole_0(X2,X1))|~r2_hidden(esk2_1(X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_49])).
% 0.92/1.14  cnf(c_0_126, negated_conjecture, (esk2_1(esk6_0)=esk4_0|r2_hidden(esk4_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_54]), c_0_58])).
% 0.92/1.14  cnf(c_0_127, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_123])).
% 0.92/1.14  cnf(c_0_128, negated_conjecture, (k5_xboole_0(esk5_0,esk6_0)=k1_xboole_0|r2_hidden(esk2_1(k5_xboole_0(esk5_0,esk6_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_123]), c_0_111]), c_0_123]), c_0_111])).
% 0.92/1.14  cnf(c_0_129, negated_conjecture, (~r2_hidden(esk4_0,k5_xboole_0(X1,esk5_0))|~r2_hidden(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_65]), c_0_55])).
% 0.92/1.14  cnf(c_0_130, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_126]), c_0_117])).
% 0.92/1.14  cnf(c_0_131, negated_conjecture, (esk2_1(k5_xboole_0(esk5_0,esk6_0))=esk4_0|k5_xboole_0(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.92/1.14  cnf(c_0_132, negated_conjecture, (~r2_hidden(esk4_0,k5_xboole_0(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_111])).
% 0.92/1.14  cnf(c_0_133, negated_conjecture, (k5_xboole_0(esk5_0,esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_131]), c_0_132])).
% 0.92/1.14  cnf(c_0_134, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.92/1.14  cnf(c_0_135, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_133]), c_0_102]), c_0_134]), ['proof']).
% 0.92/1.14  # SZS output end CNFRefutation
% 0.92/1.14  # Proof object total steps             : 136
% 0.92/1.14  # Proof object clause steps            : 91
% 0.92/1.14  # Proof object formula steps           : 45
% 0.92/1.14  # Proof object conjectures             : 43
% 0.92/1.14  # Proof object clause conjectures      : 40
% 0.92/1.14  # Proof object formula conjectures     : 3
% 0.92/1.14  # Proof object initial clauses used    : 30
% 0.92/1.14  # Proof object initial formulas used   : 22
% 0.92/1.14  # Proof object generating inferences   : 45
% 0.92/1.14  # Proof object simplifying inferences  : 80
% 0.92/1.14  # Training examples: 0 positive, 0 negative
% 0.92/1.14  # Parsed axioms                        : 22
% 0.92/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.14  # Initial clauses                      : 35
% 0.92/1.14  # Removed in clause preprocessing      : 10
% 0.92/1.14  # Initial clauses in saturation        : 25
% 0.92/1.14  # Processed clauses                    : 3732
% 0.92/1.14  # ...of these trivial                  : 36
% 0.92/1.14  # ...subsumed                          : 2961
% 0.92/1.14  # ...remaining for further processing  : 735
% 0.92/1.14  # Other redundant clauses eliminated   : 21
% 0.92/1.14  # Clauses deleted for lack of memory   : 0
% 0.92/1.14  # Backward-subsumed                    : 15
% 0.92/1.14  # Backward-rewritten                   : 185
% 0.92/1.14  # Generated clauses                    : 52021
% 0.92/1.14  # ...of the previous two non-trivial   : 48432
% 0.92/1.14  # Contextual simplify-reflections      : 1
% 0.92/1.14  # Paramodulations                      : 51914
% 0.92/1.14  # Factorizations                       : 87
% 0.92/1.14  # Equation resolutions                 : 21
% 0.92/1.14  # Propositional unsat checks           : 0
% 0.92/1.14  #    Propositional check models        : 0
% 0.92/1.14  #    Propositional check unsatisfiable : 0
% 0.92/1.14  #    Propositional clauses             : 0
% 0.92/1.14  #    Propositional clauses after purity: 0
% 0.92/1.14  #    Propositional unsat core size     : 0
% 0.92/1.14  #    Propositional preprocessing time  : 0.000
% 0.92/1.14  #    Propositional encoding time       : 0.000
% 0.92/1.14  #    Propositional solver time         : 0.000
% 0.92/1.14  #    Success case prop preproc time    : 0.000
% 0.92/1.14  #    Success case prop encoding time   : 0.000
% 0.92/1.14  #    Success case prop solver time     : 0.000
% 0.92/1.14  # Current number of processed clauses  : 507
% 0.92/1.14  #    Positive orientable unit clauses  : 36
% 0.92/1.14  #    Positive unorientable unit clauses: 3
% 0.92/1.14  #    Negative unit clauses             : 17
% 0.92/1.14  #    Non-unit-clauses                  : 451
% 0.92/1.14  # Current number of unprocessed clauses: 44537
% 0.92/1.14  # ...number of literals in the above   : 202939
% 0.92/1.14  # Current number of archived formulas  : 0
% 0.92/1.14  # Current number of archived clauses   : 234
% 0.92/1.14  # Clause-clause subsumption calls (NU) : 26766
% 0.92/1.14  # Rec. Clause-clause subsumption calls : 19793
% 0.92/1.14  # Non-unit clause-clause subsumptions  : 2491
% 0.92/1.14  # Unit Clause-clause subsumption calls : 320
% 0.92/1.14  # Rewrite failures with RHS unbound    : 0
% 0.92/1.14  # BW rewrite match attempts            : 303
% 0.92/1.14  # BW rewrite match successes           : 109
% 0.92/1.14  # Condensation attempts                : 0
% 0.92/1.14  # Condensation successes               : 0
% 0.92/1.14  # Termbank termtop insertions          : 1227175
% 0.92/1.14  
% 0.92/1.14  # -------------------------------------------------
% 0.92/1.14  # User time                : 0.768 s
% 0.92/1.14  # System time              : 0.027 s
% 0.92/1.14  # Total time               : 0.795 s
% 0.92/1.14  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
