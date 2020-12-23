%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 (2366 expanded)
%              Number of clauses        :   62 ( 897 expanded)
%              Number of leaves         :   27 ( 726 expanded)
%              Depth                    :   16
%              Number of atoms          :  201 (2697 expanded)
%              Number of equality atoms :  142 (2565 expanded)
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

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t44_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_27,plain,(
    ! [X139,X140] : k3_tarski(k2_tarski(X139,X140)) = k2_xboole_0(X139,X140) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X97,X98] : k1_enumset1(X97,X97,X98) = k2_tarski(X97,X98) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X42,X43] : k3_xboole_0(X42,X43) = k5_xboole_0(k5_xboole_0(X42,X43),k2_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X99,X100,X101] : k2_enumset1(X99,X99,X100,X101) = k1_enumset1(X99,X100,X101) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X102,X103,X104,X105] : k3_enumset1(X102,X102,X103,X104,X105) = k2_enumset1(X102,X103,X104,X105) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_34,plain,(
    ! [X22] : k3_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X106,X107,X108,X109,X110] : k4_enumset1(X106,X106,X107,X108,X109,X110) = k3_enumset1(X106,X107,X108,X109,X110) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X111,X112,X113,X114,X115,X116] : k5_enumset1(X111,X111,X112,X113,X114,X115,X116) = k4_enumset1(X111,X112,X113,X114,X115,X116) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X117,X118,X119,X120,X121,X122,X123] : k6_enumset1(X117,X117,X118,X119,X120,X121,X122,X123) = k5_enumset1(X117,X118,X119,X120,X121,X122,X123) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_42,plain,(
    ! [X21] : k2_xboole_0(X21,X21) = X21 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_43,plain,(
    ! [X25,X26] :
      ( ( k4_xboole_0(X25,X26) != k1_xboole_0
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | k4_xboole_0(X25,X26) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_44,plain,(
    ! [X27,X28] : k4_xboole_0(X27,X28) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X41] : k5_xboole_0(X41,X41) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_55,plain,(
    ! [X38,X39,X40] : k5_xboole_0(k5_xboole_0(X38,X39),X40) = k5_xboole_0(X38,k5_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_36]),c_0_37]),c_0_38]),c_0_47]),c_0_48]),c_0_49])).

fof(c_0_59,plain,(
    ! [X36,X37] : k2_xboole_0(X36,k2_xboole_0(X36,X37)) = k2_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_60,negated_conjecture,
    ( k1_tarski(esk7_0) = k2_xboole_0(esk8_0,esk9_0)
    & esk8_0 != esk9_0
    & esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

fof(c_0_61,plain,(
    ! [X96] : k2_tarski(X96,X96) = k1_tarski(X96) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k1_tarski(esk7_0) = k2_xboole_0(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_68,plain,(
    ! [X137,X138] :
      ( ( ~ r1_tarski(X137,k1_tarski(X138))
        | X137 = k1_xboole_0
        | X137 = k1_tarski(X138) )
      & ( X137 != k1_xboole_0
        | r1_tarski(X137,k1_tarski(X138)) )
      & ( X137 != k1_tarski(X138)
        | r1_tarski(X137,k1_tarski(X138)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_64])).

cnf(c_0_71,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_72,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_31]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

fof(c_0_73,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X18)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))) = k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

fof(c_0_77,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X46,X45)
        | X46 = X44
        | X45 != k1_tarski(X44) )
      & ( X47 != X44
        | r2_hidden(X47,X45)
        | X45 != k1_tarski(X44) )
      & ( ~ r2_hidden(esk3_2(X48,X49),X49)
        | esk3_2(X48,X49) != X48
        | X49 = k1_tarski(X48) )
      & ( r2_hidden(esk3_2(X48,X49),X49)
        | esk3_2(X48,X49) = X48
        | X49 = k1_tarski(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_67]),c_0_67]),c_0_31]),c_0_31]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_57])])).

cnf(c_0_81,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_82,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(k5_xboole_0(X2,X4),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_84,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

fof(c_0_85,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_86,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_67]),c_0_31]),c_0_37]),c_0_38]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_63])])).

cnf(c_0_88,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk9_0)) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_84])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_90,plain,(
    ! [X23] :
      ( X23 = k1_xboole_0
      | r2_hidden(esk2_1(X23),X23) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_91,plain,(
    ! [X135,X136] :
      ( ~ r2_hidden(X135,X136)
      | k3_xboole_0(X136,k1_tarski(X135)) = k1_tarski(X135) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_70])).

cnf(c_0_94,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_96,plain,(
    ! [X73,X74,X75,X76,X77,X78,X79] : k5_enumset1(X73,X74,X75,X76,X77,X78,X79) = k2_xboole_0(k4_enumset1(X73,X74,X75,X76,X77,X78),k1_tarski(X79)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_97,plain,(
    ! [X80,X81,X82,X83,X84,X85,X86,X87] : k6_enumset1(X80,X81,X82,X83,X84,X85,X86,X87) = k2_xboole_0(k4_enumset1(X80,X81,X82,X83,X84,X85),k2_tarski(X86,X87)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_84])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk2_1(esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

fof(c_0_101,plain,(
    ! [X51,X52,X53,X54] : k2_enumset1(X51,X52,X53,X54) = k2_enumset1(X54,X53,X52,X51) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

cnf(c_0_102,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_103,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_104,plain,
    ( k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_67]),c_0_67]),c_0_31]),c_0_31]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_105,negated_conjecture,
    ( esk2_1(esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_107,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_67]),c_0_31]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_108,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_31]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49])).

fof(c_0_109,plain,(
    ! [X35] : k5_xboole_0(X35,k1_xboole_0) = X35 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_104,c_0_63])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk7_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_105]),c_0_95])).

cnf(c_0_112,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_38]),c_0_38]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_113,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_84]),c_0_84]),c_0_112]),c_0_113]),c_0_113]),c_0_72]),c_0_84]),c_0_57]),c_0_114]),c_0_84]),c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:07:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.42  # and selection function GSelectMinInfpos.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.029 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.42  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.42  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.42  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.42  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.42  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.42  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.42  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.42  fof(t44_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.19/0.42  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.42  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.19/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.42  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.19/0.42  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.42  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.42  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.42  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.42  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.19/0.42  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 0.19/0.42  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.19/0.42  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.19/0.42  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.42  fof(c_0_27, plain, ![X139, X140]:k3_tarski(k2_tarski(X139,X140))=k2_xboole_0(X139,X140), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.42  fof(c_0_28, plain, ![X97, X98]:k1_enumset1(X97,X97,X98)=k2_tarski(X97,X98), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.42  fof(c_0_29, plain, ![X42, X43]:k3_xboole_0(X42,X43)=k5_xboole_0(k5_xboole_0(X42,X43),k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.42  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  fof(c_0_32, plain, ![X99, X100, X101]:k2_enumset1(X99,X99,X100,X101)=k1_enumset1(X99,X100,X101), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.42  fof(c_0_33, plain, ![X102, X103, X104, X105]:k3_enumset1(X102,X102,X103,X104,X105)=k2_enumset1(X102,X103,X104,X105), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.42  fof(c_0_34, plain, ![X22]:k3_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.42  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.42  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  fof(c_0_39, plain, ![X106, X107, X108, X109, X110]:k4_enumset1(X106,X106,X107,X108,X109,X110)=k3_enumset1(X106,X107,X108,X109,X110), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.42  fof(c_0_40, plain, ![X111, X112, X113, X114, X115, X116]:k5_enumset1(X111,X111,X112,X113,X114,X115,X116)=k4_enumset1(X111,X112,X113,X114,X115,X116), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.42  fof(c_0_41, plain, ![X117, X118, X119, X120, X121, X122, X123]:k6_enumset1(X117,X117,X118,X119,X120,X121,X122,X123)=k5_enumset1(X117,X118,X119,X120,X121,X122,X123), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.42  fof(c_0_42, plain, ![X21]:k2_xboole_0(X21,X21)=X21, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.42  fof(c_0_43, plain, ![X25, X26]:((k4_xboole_0(X25,X26)!=k1_xboole_0|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|k4_xboole_0(X25,X26)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.42  fof(c_0_44, plain, ![X27, X28]:k4_xboole_0(X27,X28)=k5_xboole_0(X27,k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.42  cnf(c_0_45, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.42  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.42  cnf(c_0_49, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  fof(c_0_50, plain, ![X41]:k5_xboole_0(X41,X41)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.42  cnf(c_0_51, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  fof(c_0_52, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t44_zfmisc_1])).
% 0.19/0.42  cnf(c_0_53, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.42  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.42  fof(c_0_55, plain, ![X38, X39, X40]:k5_xboole_0(k5_xboole_0(X38,X39),X40)=k5_xboole_0(X38,k5_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.42  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.19/0.42  cnf(c_0_57, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  cnf(c_0_58, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_36]), c_0_37]), c_0_38]), c_0_47]), c_0_48]), c_0_49])).
% 0.19/0.42  fof(c_0_59, plain, ![X36, X37]:k2_xboole_0(X36,k2_xboole_0(X36,X37))=k2_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.19/0.42  fof(c_0_60, negated_conjecture, (((k1_tarski(esk7_0)=k2_xboole_0(esk8_0,esk9_0)&esk8_0!=esk9_0)&esk8_0!=k1_xboole_0)&esk9_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 0.19/0.42  fof(c_0_61, plain, ![X96]:k2_tarski(X96,X96)=k1_tarski(X96), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.42  cnf(c_0_62, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.19/0.42  cnf(c_0_63, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.42  cnf(c_0_64, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.19/0.42  cnf(c_0_65, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (k1_tarski(esk7_0)=k2_xboole_0(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.42  cnf(c_0_67, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.42  fof(c_0_68, plain, ![X137, X138]:((~r1_tarski(X137,k1_tarski(X138))|(X137=k1_xboole_0|X137=k1_tarski(X138)))&((X137!=k1_xboole_0|r1_tarski(X137,k1_tarski(X138)))&(X137!=k1_tarski(X138)|r1_tarski(X137,k1_tarski(X138))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_69, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.42  cnf(c_0_70, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_57]), c_0_64])).
% 0.19/0.42  cnf(c_0_71, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_31]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49])).
% 0.19/0.42  fof(c_0_73, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k3_xboole_0(X12,X13))&(r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k3_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|~r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k3_xboole_0(X12,X13)))&((~r2_hidden(esk1_3(X17,X18,X19),X19)|(~r2_hidden(esk1_3(X17,X18,X19),X17)|~r2_hidden(esk1_3(X17,X18,X19),X18))|X19=k3_xboole_0(X17,X18))&((r2_hidden(esk1_3(X17,X18,X19),X17)|r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k3_xboole_0(X17,X18))&(r2_hidden(esk1_3(X17,X18,X19),X18)|r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k3_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_74, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.42  cnf(c_0_75, plain, (r1_tarski(X1,X2)|k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))=k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.42  fof(c_0_77, plain, ![X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X46,X45)|X46=X44|X45!=k1_tarski(X44))&(X47!=X44|r2_hidden(X47,X45)|X45!=k1_tarski(X44)))&((~r2_hidden(esk3_2(X48,X49),X49)|esk3_2(X48,X49)!=X48|X49=k1_tarski(X48))&(r2_hidden(esk3_2(X48,X49),X49)|esk3_2(X48,X49)=X48|X49=k1_tarski(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_78, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.42  cnf(c_0_79, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_67]), c_0_67]), c_0_31]), c_0_31]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (r1_tarski(esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_57])])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.42  cnf(c_0_82, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.42  cnf(c_0_83, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(k5_xboole_0(X2,X4),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.19/0.42  fof(c_0_85, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.42  cnf(c_0_86, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_67]), c_0_31]), c_0_37]), c_0_38]), c_0_47]), c_0_48]), c_0_49])).
% 0.19/0.42  cnf(c_0_87, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_63])])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk9_0))=esk8_0), inference(rw,[status(thm)],[c_0_72, c_0_84])).
% 0.19/0.42  cnf(c_0_89, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.42  fof(c_0_90, plain, ![X23]:(X23=k1_xboole_0|r2_hidden(esk2_1(X23),X23)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.42  fof(c_0_91, plain, ![X135, X136]:(~r2_hidden(X135,X136)|k3_xboole_0(X136,k1_tarski(X135))=k1_tarski(X135)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.19/0.42  cnf(c_0_92, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_86])).
% 0.19/0.42  cnf(c_0_93, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_70])).
% 0.19/0.42  cnf(c_0_94, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.42  fof(c_0_96, plain, ![X73, X74, X75, X76, X77, X78, X79]:k5_enumset1(X73,X74,X75,X76,X77,X78,X79)=k2_xboole_0(k4_enumset1(X73,X74,X75,X76,X77,X78),k1_tarski(X79)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 0.19/0.42  fof(c_0_97, plain, ![X80, X81, X82, X83, X84, X85, X86, X87]:k6_enumset1(X80,X81,X82,X83,X84,X85,X86,X87)=k2_xboole_0(k4_enumset1(X80,X81,X82,X83,X84,X85),k2_tarski(X86,X87)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.19/0.42  cnf(c_0_98, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.42  cnf(c_0_99, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_92, c_0_84])).
% 0.19/0.42  cnf(c_0_100, negated_conjecture, (r2_hidden(esk2_1(esk9_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.19/0.42  fof(c_0_101, plain, ![X51, X52, X53, X54]:k2_enumset1(X51,X52,X53,X54)=k2_enumset1(X54,X53,X52,X51), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.19/0.42  cnf(c_0_102, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.42  cnf(c_0_103, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.42  cnf(c_0_104, plain, (k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_67]), c_0_67]), c_0_31]), c_0_31]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 0.19/0.42  cnf(c_0_105, negated_conjecture, (esk2_1(esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.19/0.42  cnf(c_0_106, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.19/0.42  cnf(c_0_107, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_67]), c_0_31]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 0.19/0.42  cnf(c_0_108, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_31]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 0.19/0.42  fof(c_0_109, plain, ![X35]:k5_xboole_0(X35,k1_xboole_0)=X35, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.42  cnf(c_0_110, plain, (k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_104, c_0_63])).
% 0.19/0.42  cnf(c_0_111, negated_conjecture, (r2_hidden(esk7_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_105]), c_0_95])).
% 0.19/0.42  cnf(c_0_112, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_38]), c_0_38]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49])).
% 0.19/0.42  cnf(c_0_113, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_107, c_0_108])).
% 0.19/0.42  cnf(c_0_114, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.19/0.42  cnf(c_0_115, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.42  cnf(c_0_116, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_84]), c_0_84]), c_0_112]), c_0_113]), c_0_113]), c_0_72]), c_0_84]), c_0_57]), c_0_114]), c_0_84]), c_0_115]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 117
% 0.19/0.42  # Proof object clause steps            : 62
% 0.19/0.42  # Proof object formula steps           : 55
% 0.19/0.42  # Proof object conjectures             : 18
% 0.19/0.42  # Proof object clause conjectures      : 15
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 30
% 0.19/0.42  # Proof object initial formulas used   : 27
% 0.19/0.42  # Proof object generating inferences   : 10
% 0.19/0.42  # Proof object simplifying inferences  : 181
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 35
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 55
% 0.19/0.42  # Removed in clause preprocessing      : 10
% 0.19/0.42  # Initial clauses in saturation        : 45
% 0.19/0.42  # Processed clauses                    : 281
% 0.19/0.42  # ...of these trivial                  : 19
% 0.19/0.42  # ...subsumed                          : 69
% 0.19/0.42  # ...remaining for further processing  : 193
% 0.19/0.42  # Other redundant clauses eliminated   : 32
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 0
% 0.19/0.42  # Backward-rewritten                   : 23
% 0.19/0.42  # Generated clauses                    : 1657
% 0.19/0.42  # ...of the previous two non-trivial   : 1418
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 1621
% 0.19/0.42  # Factorizations                       : 5
% 0.19/0.42  # Equation resolutions                 : 32
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 114
% 0.19/0.42  #    Positive orientable unit clauses  : 36
% 0.19/0.42  #    Positive unorientable unit clauses: 3
% 0.19/0.42  #    Negative unit clauses             : 7
% 0.19/0.42  #    Non-unit-clauses                  : 68
% 0.19/0.42  # Current number of unprocessed clauses: 1222
% 0.19/0.42  # ...number of literals in the above   : 4036
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 78
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 360
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 196
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 25
% 0.19/0.42  # Unit Clause-clause subsumption calls : 130
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 237
% 0.19/0.42  # BW rewrite match successes           : 101
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 34087
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.076 s
% 0.19/0.42  # System time              : 0.006 s
% 0.19/0.42  # Total time               : 0.082 s
% 0.19/0.42  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
