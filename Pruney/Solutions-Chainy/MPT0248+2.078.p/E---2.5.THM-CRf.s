%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:49 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  141 (11175 expanded)
%              Number of clauses        :   84 (4150 expanded)
%              Number of leaves         :   28 (3492 expanded)
%              Depth                    :   20
%              Number of atoms          :  257 (12323 expanded)
%              Number of equality atoms :  190 (12070 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

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

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_28,plain,(
    ! [X147,X148] : k3_tarski(k2_tarski(X147,X148)) = k2_xboole_0(X147,X148) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X105,X106] : k1_enumset1(X105,X105,X106) = k2_tarski(X105,X106) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X51,X52] : k3_xboole_0(X51,X52) = k5_xboole_0(k5_xboole_0(X51,X52),k2_xboole_0(X51,X52)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X107,X108,X109] : k2_enumset1(X107,X107,X108,X109) = k1_enumset1(X107,X108,X109) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X110,X111,X112,X113] : k3_enumset1(X110,X110,X111,X112,X113) = k2_enumset1(X110,X111,X112,X113) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X31] : k3_xboole_0(X31,X31) = X31 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X114,X115,X116,X117,X118] : k4_enumset1(X114,X114,X115,X116,X117,X118) = k3_enumset1(X114,X115,X116,X117,X118) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_41,plain,(
    ! [X119,X120,X121,X122,X123,X124] : k5_enumset1(X119,X119,X120,X121,X122,X123,X124) = k4_enumset1(X119,X120,X121,X122,X123,X124) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_42,plain,(
    ! [X125,X126,X127,X128,X129,X130,X131] : k6_enumset1(X125,X125,X126,X127,X128,X129,X130,X131) = k5_enumset1(X125,X126,X127,X128,X129,X130,X131) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_43,plain,(
    ! [X30] : k2_xboole_0(X30,X30) = X30 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_44,plain,(
    ! [X42,X43] : k2_xboole_0(X42,k4_xboole_0(X43,X42)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_45,plain,(
    ! [X36,X37] : k4_xboole_0(X36,X37) = k5_xboole_0(X36,k3_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X50] : k5_xboole_0(X50,X50) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_55,plain,(
    ! [X47,X48,X49] : k5_xboole_0(k5_xboole_0(X47,X48),X49) = k5_xboole_0(X47,k5_xboole_0(X48,X49)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_37]),c_0_38]),c_0_39]),c_0_48]),c_0_49]),c_0_50])).

fof(c_0_59,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

cnf(c_0_60,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_37]),c_0_37]),c_0_54]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

fof(c_0_63,negated_conjecture,
    ( k1_tarski(esk8_0) = k2_xboole_0(esk9_0,esk10_0)
    & ( esk9_0 != k1_tarski(esk8_0)
      | esk10_0 != k1_tarski(esk8_0) )
    & ( esk9_0 != k1_xboole_0
      | esk10_0 != k1_tarski(esk8_0) )
    & ( esk9_0 != k1_tarski(esk8_0)
      | esk10_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).

fof(c_0_64,plain,(
    ! [X104] : k2_tarski(X104,X104) = k1_tarski(X104) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_65,plain,(
    ! [X60,X61,X62,X63] : k2_enumset1(X60,X61,X62,X63) = k2_enumset1(X63,X62,X61,X60) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_66,plain,(
    ! [X34,X35] :
      ( ( k4_xboole_0(X34,X35) != k1_xboole_0
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | k4_xboole_0(X34,X35) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_67,plain,(
    ! [X45,X46] : k2_xboole_0(X45,k2_xboole_0(X45,X46)) = k2_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_68,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k1_tarski(esk8_0) = k2_xboole_0(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_73,plain,(
    ! [X82,X83,X84,X85,X86,X87] : k4_enumset1(X82,X83,X84,X85,X86,X87) = k2_xboole_0(k3_enumset1(X82,X83,X84,X85,X86),k1_tarski(X87)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_74,plain,(
    ! [X88,X89,X90,X91,X92,X93,X94,X95] : k6_enumset1(X88,X89,X90,X91,X92,X93,X94,X95) = k2_xboole_0(k3_enumset1(X88,X89,X90,X91,X92),k1_enumset1(X93,X94,X95)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_32]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_79,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_39]),c_0_39]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_80,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_54]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_83,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_84,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,k5_xboole_0(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))) = k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0,esk10_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_85,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_71]),c_0_32]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_86,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50])).

fof(c_0_87,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X14)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X18)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k2_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X19)
        | r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X18)
        | X19 = k2_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_88,plain,(
    ! [X53,X54,X55,X56,X57,X58] :
      ( ( ~ r2_hidden(X55,X54)
        | X55 = X53
        | X54 != k1_tarski(X53) )
      & ( X56 != X53
        | r2_hidden(X56,X54)
        | X54 != k1_tarski(X53) )
      & ( ~ r2_hidden(esk4_2(X57,X58),X58)
        | esk4_2(X57,X58) != X57
        | X58 = k1_tarski(X57) )
      & ( r2_hidden(esk4_2(X57,X58),X58)
        | esk4_2(X57,X58) = X57
        | X58 = k1_tarski(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_89,plain,(
    ! [X149,X150] :
      ( ( k4_xboole_0(k1_tarski(X149),k1_tarski(X150)) != k1_tarski(X149)
        | X149 != X150 )
      & ( X149 = X150
        | k4_xboole_0(k1_tarski(X149),k1_tarski(X150)) = k1_tarski(X149) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_90,plain,(
    ! [X145,X146] :
      ( ( ~ r1_tarski(X145,k1_tarski(X146))
        | X145 = k1_xboole_0
        | X145 = k1_tarski(X146) )
      & ( X145 != k1_xboole_0
        | r1_tarski(X145,k1_tarski(X146)) )
      & ( X145 != k1_tarski(X146)
        | r1_tarski(X145,k1_tarski(X146)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_61])).

cnf(c_0_92,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0,esk10_0,esk10_0)))) = k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0,esk10_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_95,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_97,plain,(
    ! [X44] : k5_xboole_0(X44,k1_xboole_0) = X44 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_69])).

cnf(c_0_100,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_78]),c_0_93]),c_0_78])).

fof(c_0_101,plain,(
    ! [X143,X144] :
      ( ~ r2_hidden(X143,X144)
      | k3_xboole_0(X144,k1_tarski(X143)) = k1_tarski(X143) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_37]),c_0_38]),c_0_39]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_103,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_71]),c_0_32]),c_0_38]),c_0_39]),c_0_48]),c_0_49]),c_0_50])).

fof(c_0_104,plain,(
    ! [X32] :
      ( X32 = k1_xboole_0
      | r2_hidden(esk3_1(X32),X32) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_105,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_71]),c_0_71]),c_0_71]),c_0_32]),c_0_32]),c_0_32]),c_0_54]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_107,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_78])).

cnf(c_0_108,negated_conjecture,
    ( esk9_0 != k1_tarski(esk8_0)
    | esk10_0 != k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_109,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_71]),c_0_71]),c_0_32]),c_0_32]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_57])])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_113,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_115,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_61])]),c_0_58]),c_0_57]),c_0_106]),c_0_57])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_107]),c_0_57])])).

cnf(c_0_117,negated_conjecture,
    ( esk9_0 != k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)
    | esk10_0 != k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_71]),c_0_71]),c_0_32]),c_0_32]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_118,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = esk10_0
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_119,plain,
    ( k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_71]),c_0_71]),c_0_32]),c_0_32]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_78])).

cnf(c_0_121,plain,
    ( esk3_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( esk9_0 != k1_tarski(esk8_0)
    | esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_123,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = esk9_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_116])).

cnf(c_0_124,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk10_0 != esk9_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_125,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_119,c_0_61])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0)
    | r2_hidden(esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_114]),c_0_121]),c_0_121]),c_0_115])).

cnf(c_0_127,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | esk10_0 != k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_128,negated_conjecture,
    ( esk10_0 != k1_xboole_0
    | esk9_0 != k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_71]),c_0_32]),c_0_38]),c_0_39]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_129,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_118]),c_0_124])).

cnf(c_0_130,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = esk10_0
    | r2_hidden(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_100]),c_0_57]),c_0_106])).

cnf(c_0_131,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | esk10_0 != k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_71]),c_0_32]),c_0_38]),c_0_39]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_132,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_123])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0)
    | esk10_0 != esk9_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) != esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132])])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk8_0,k1_xboole_0)
    | esk10_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_132]),c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_118,c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_107]),c_0_57]),c_0_79]),c_0_79])).

cnf(c_0_138,negated_conjecture,
    ( r2_hidden(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136])])).

cnf(c_0_139,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_93]),c_0_107]),c_0_93])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_138]),c_0_139]),c_0_57]),c_0_62]),c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:30:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.18/0.47  # and selection function GSelectMinInfpos.
% 0.18/0.47  #
% 0.18/0.47  # Preprocessing time       : 0.031 s
% 0.18/0.47  # Presaturation interreduction done
% 0.18/0.47  
% 0.18/0.47  # Proof found!
% 0.18/0.47  # SZS status Theorem
% 0.18/0.47  # SZS output start CNFRefutation
% 0.18/0.47  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.18/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.47  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.18/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.47  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.18/0.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.47  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.47  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.18/0.47  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.18/0.47  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.18/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.47  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.18/0.47  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.18/0.47  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.18/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.47  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.18/0.47  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.47  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.18/0.47  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.18/0.47  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 0.18/0.47  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.18/0.47  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.47  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.18/0.47  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.18/0.47  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.18/0.47  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.18/0.47  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.18/0.47  fof(c_0_28, plain, ![X147, X148]:k3_tarski(k2_tarski(X147,X148))=k2_xboole_0(X147,X148), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.18/0.47  fof(c_0_29, plain, ![X105, X106]:k1_enumset1(X105,X105,X106)=k2_tarski(X105,X106), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.47  fof(c_0_30, plain, ![X51, X52]:k3_xboole_0(X51,X52)=k5_xboole_0(k5_xboole_0(X51,X52),k2_xboole_0(X51,X52)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.18/0.47  cnf(c_0_31, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.47  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.47  fof(c_0_33, plain, ![X107, X108, X109]:k2_enumset1(X107,X107,X108,X109)=k1_enumset1(X107,X108,X109), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.47  fof(c_0_34, plain, ![X110, X111, X112, X113]:k3_enumset1(X110,X110,X111,X112,X113)=k2_enumset1(X110,X111,X112,X113), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.47  fof(c_0_35, plain, ![X31]:k3_xboole_0(X31,X31)=X31, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.18/0.47  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.47  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.47  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.47  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.47  fof(c_0_40, plain, ![X114, X115, X116, X117, X118]:k4_enumset1(X114,X114,X115,X116,X117,X118)=k3_enumset1(X114,X115,X116,X117,X118), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.47  fof(c_0_41, plain, ![X119, X120, X121, X122, X123, X124]:k5_enumset1(X119,X119,X120,X121,X122,X123,X124)=k4_enumset1(X119,X120,X121,X122,X123,X124), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.47  fof(c_0_42, plain, ![X125, X126, X127, X128, X129, X130, X131]:k6_enumset1(X125,X125,X126,X127,X128,X129,X130,X131)=k5_enumset1(X125,X126,X127,X128,X129,X130,X131), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.18/0.47  fof(c_0_43, plain, ![X30]:k2_xboole_0(X30,X30)=X30, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.18/0.47  fof(c_0_44, plain, ![X42, X43]:k2_xboole_0(X42,k4_xboole_0(X43,X42))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.18/0.47  fof(c_0_45, plain, ![X36, X37]:k4_xboole_0(X36,X37)=k5_xboole_0(X36,k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.47  cnf(c_0_46, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.47  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])).
% 0.18/0.47  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.47  cnf(c_0_49, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.47  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.47  fof(c_0_51, plain, ![X50]:k5_xboole_0(X50,X50)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.18/0.47  cnf(c_0_52, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.47  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.47  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.47  fof(c_0_55, plain, ![X47, X48, X49]:k5_xboole_0(k5_xboole_0(X47,X48),X49)=k5_xboole_0(X47,k5_xboole_0(X48,X49)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.18/0.47  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.47  cnf(c_0_57, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.47  cnf(c_0_58, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_37]), c_0_38]), c_0_39]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.47  fof(c_0_59, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.18/0.47  cnf(c_0_60, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_37]), c_0_37]), c_0_54]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_61, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.47  cnf(c_0_62, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.18/0.47  fof(c_0_63, negated_conjecture, (((k1_tarski(esk8_0)=k2_xboole_0(esk9_0,esk10_0)&(esk9_0!=k1_tarski(esk8_0)|esk10_0!=k1_tarski(esk8_0)))&(esk9_0!=k1_xboole_0|esk10_0!=k1_tarski(esk8_0)))&(esk9_0!=k1_tarski(esk8_0)|esk10_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).
% 0.18/0.47  fof(c_0_64, plain, ![X104]:k2_tarski(X104,X104)=k1_tarski(X104), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.47  fof(c_0_65, plain, ![X60, X61, X62, X63]:k2_enumset1(X60,X61,X62,X63)=k2_enumset1(X63,X62,X61,X60), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.18/0.47  fof(c_0_66, plain, ![X34, X35]:((k4_xboole_0(X34,X35)!=k1_xboole_0|r1_tarski(X34,X35))&(~r1_tarski(X34,X35)|k4_xboole_0(X34,X35)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.47  fof(c_0_67, plain, ![X45, X46]:k2_xboole_0(X45,k2_xboole_0(X45,X46))=k2_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.18/0.47  cnf(c_0_68, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.47  cnf(c_0_69, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_57]), c_0_62])).
% 0.18/0.47  cnf(c_0_70, negated_conjecture, (k1_tarski(esk8_0)=k2_xboole_0(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.47  cnf(c_0_71, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.18/0.47  cnf(c_0_72, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.18/0.47  fof(c_0_73, plain, ![X82, X83, X84, X85, X86, X87]:k4_enumset1(X82,X83,X84,X85,X86,X87)=k2_xboole_0(k3_enumset1(X82,X83,X84,X85,X86),k1_tarski(X87)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.18/0.47  fof(c_0_74, plain, ![X88, X89, X90, X91, X92, X93, X94, X95]:k6_enumset1(X88,X89,X90,X91,X92,X93,X94,X95)=k2_xboole_0(k3_enumset1(X88,X89,X90,X91,X92),k1_enumset1(X93,X94,X95)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.18/0.47  cnf(c_0_75, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.47  cnf(c_0_76, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.47  cnf(c_0_77, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.47  cnf(c_0_78, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_32]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_79, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_39]), c_0_39]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_80, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.18/0.47  cnf(c_0_81, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.18/0.47  cnf(c_0_82, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_54]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.47  cnf(c_0_83, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_84, negated_conjecture, (k3_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,k5_xboole_0(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))))=k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0,esk10_0,esk10_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.18/0.47  cnf(c_0_85, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_71]), c_0_32]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_86, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.18/0.47  fof(c_0_87, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X15,X14)|(r2_hidden(X15,X12)|r2_hidden(X15,X13))|X14!=k2_xboole_0(X12,X13))&((~r2_hidden(X16,X12)|r2_hidden(X16,X14)|X14!=k2_xboole_0(X12,X13))&(~r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k2_xboole_0(X12,X13))))&(((~r2_hidden(esk1_3(X17,X18,X19),X17)|~r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k2_xboole_0(X17,X18))&(~r2_hidden(esk1_3(X17,X18,X19),X18)|~r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k2_xboole_0(X17,X18)))&(r2_hidden(esk1_3(X17,X18,X19),X19)|(r2_hidden(esk1_3(X17,X18,X19),X17)|r2_hidden(esk1_3(X17,X18,X19),X18))|X19=k2_xboole_0(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.18/0.47  fof(c_0_88, plain, ![X53, X54, X55, X56, X57, X58]:(((~r2_hidden(X55,X54)|X55=X53|X54!=k1_tarski(X53))&(X56!=X53|r2_hidden(X56,X54)|X54!=k1_tarski(X53)))&((~r2_hidden(esk4_2(X57,X58),X58)|esk4_2(X57,X58)!=X57|X58=k1_tarski(X57))&(r2_hidden(esk4_2(X57,X58),X58)|esk4_2(X57,X58)=X57|X58=k1_tarski(X57)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.47  fof(c_0_89, plain, ![X149, X150]:((k4_xboole_0(k1_tarski(X149),k1_tarski(X150))!=k1_tarski(X149)|X149!=X150)&(X149=X150|k4_xboole_0(k1_tarski(X149),k1_tarski(X150))=k1_tarski(X149))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.18/0.47  fof(c_0_90, plain, ![X145, X146]:((~r1_tarski(X145,k1_tarski(X146))|(X145=k1_xboole_0|X145=k1_tarski(X146)))&((X145!=k1_xboole_0|r1_tarski(X145,k1_tarski(X146)))&(X145!=k1_tarski(X146)|r1_tarski(X145,k1_tarski(X146))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.18/0.47  cnf(c_0_91, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_61])).
% 0.18/0.47  cnf(c_0_92, negated_conjecture, (k3_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0,esk10_0,esk10_0))))=k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk10_0,esk10_0,esk10_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.18/0.47  cnf(c_0_93, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6)=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.18/0.47  cnf(c_0_94, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.18/0.47  cnf(c_0_95, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.18/0.47  cnf(c_0_96, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.18/0.47  fof(c_0_97, plain, ![X44]:k5_xboole_0(X44,k1_xboole_0)=X44, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.18/0.47  cnf(c_0_98, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.18/0.47  cnf(c_0_99, plain, (r1_tarski(X1,X2)|k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_91, c_0_69])).
% 0.18/0.47  cnf(c_0_100, negated_conjecture, (k3_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_78]), c_0_93]), c_0_78])).
% 0.18/0.47  fof(c_0_101, plain, ![X143, X144]:(~r2_hidden(X143,X144)|k3_xboole_0(X144,k1_tarski(X143))=k1_tarski(X143)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.18/0.47  cnf(c_0_102, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_37]), c_0_38]), c_0_39]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.47  cnf(c_0_103, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_71]), c_0_32]), c_0_38]), c_0_39]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.47  fof(c_0_104, plain, ![X32]:(X32=k1_xboole_0|r2_hidden(esk3_1(X32),X32)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.18/0.47  cnf(c_0_105, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_71]), c_0_71]), c_0_71]), c_0_32]), c_0_32]), c_0_32]), c_0_54]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_106, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.18/0.47  cnf(c_0_107, negated_conjecture, (k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_83, c_0_78])).
% 0.18/0.47  cnf(c_0_108, negated_conjecture, (esk9_0!=k1_tarski(esk8_0)|esk10_0!=k1_tarski(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.47  cnf(c_0_109, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_71]), c_0_71]), c_0_32]), c_0_32]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_110, negated_conjecture, (r1_tarski(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_57])])).
% 0.18/0.47  cnf(c_0_111, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.18/0.47  cnf(c_0_112, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_102])).
% 0.18/0.47  cnf(c_0_113, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_103])).
% 0.18/0.47  cnf(c_0_114, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.18/0.47  cnf(c_0_115, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_61])]), c_0_58]), c_0_57]), c_0_106]), c_0_57])).
% 0.18/0.47  cnf(c_0_116, negated_conjecture, (r1_tarski(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_107]), c_0_57])])).
% 0.18/0.47  cnf(c_0_117, negated_conjecture, (esk9_0!=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)|esk10_0!=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_71]), c_0_71]), c_0_32]), c_0_32]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_118, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=esk10_0|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.18/0.47  cnf(c_0_119, plain, (k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_71]), c_0_71]), c_0_32]), c_0_32]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.18/0.47  cnf(c_0_120, negated_conjecture, (r2_hidden(X1,esk10_0)|r2_hidden(X1,esk9_0)|~r2_hidden(X1,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_112, c_0_78])).
% 0.18/0.47  cnf(c_0_121, plain, (esk3_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.18/0.47  cnf(c_0_122, negated_conjecture, (esk9_0!=k1_tarski(esk8_0)|esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.47  cnf(c_0_123, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=esk9_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_109, c_0_116])).
% 0.18/0.47  cnf(c_0_124, negated_conjecture, (esk10_0=k1_xboole_0|esk10_0!=esk9_0), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.18/0.47  cnf(c_0_125, plain, (k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_119, c_0_61])).
% 0.18/0.47  cnf(c_0_126, negated_conjecture, (r2_hidden(esk8_0,esk9_0)|r2_hidden(esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_114]), c_0_121]), c_0_121]), c_0_115])).
% 0.18/0.47  cnf(c_0_127, negated_conjecture, (esk9_0!=k1_xboole_0|esk10_0!=k1_tarski(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.47  cnf(c_0_128, negated_conjecture, (esk10_0!=k1_xboole_0|esk9_0!=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_71]), c_0_32]), c_0_38]), c_0_39]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.47  cnf(c_0_129, negated_conjecture, (esk10_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_118]), c_0_124])).
% 0.18/0.47  cnf(c_0_130, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=esk10_0|r2_hidden(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_100]), c_0_57]), c_0_106])).
% 0.18/0.47  cnf(c_0_131, negated_conjecture, (esk9_0!=k1_xboole_0|esk10_0!=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_71]), c_0_32]), c_0_38]), c_0_39]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.47  cnf(c_0_132, negated_conjecture, (esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_123])).
% 0.18/0.47  cnf(c_0_133, negated_conjecture, (r2_hidden(esk8_0,esk9_0)|esk10_0!=esk9_0), inference(spm,[status(thm)],[c_0_117, c_0_130])).
% 0.18/0.47  cnf(c_0_134, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)!=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_132])])).
% 0.18/0.47  cnf(c_0_135, negated_conjecture, (r2_hidden(esk8_0,k1_xboole_0)|esk10_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_132]), c_0_132])).
% 0.18/0.47  cnf(c_0_136, negated_conjecture, (esk10_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_118, c_0_134])).
% 0.18/0.47  cnf(c_0_137, negated_conjecture, (k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_107]), c_0_57]), c_0_79]), c_0_79])).
% 0.18/0.47  cnf(c_0_138, negated_conjecture, (r2_hidden(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136])])).
% 0.18/0.47  cnf(c_0_139, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_93]), c_0_107]), c_0_93])).
% 0.18/0.47  cnf(c_0_140, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_138]), c_0_139]), c_0_57]), c_0_62]), c_0_115]), ['proof']).
% 0.18/0.47  # SZS output end CNFRefutation
% 0.18/0.47  # Proof object total steps             : 141
% 0.18/0.47  # Proof object clause steps            : 84
% 0.18/0.47  # Proof object formula steps           : 57
% 0.18/0.47  # Proof object conjectures             : 33
% 0.18/0.47  # Proof object clause conjectures      : 30
% 0.18/0.47  # Proof object formula conjectures     : 3
% 0.18/0.47  # Proof object initial clauses used    : 31
% 0.18/0.47  # Proof object initial formulas used   : 28
% 0.18/0.47  # Proof object generating inferences   : 18
% 0.18/0.47  # Proof object simplifying inferences  : 308
% 0.18/0.47  # Training examples: 0 positive, 0 negative
% 0.18/0.47  # Parsed axioms                        : 36
% 0.18/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.47  # Initial clauses                      : 61
% 0.18/0.47  # Removed in clause preprocessing      : 10
% 0.18/0.47  # Initial clauses in saturation        : 51
% 0.18/0.47  # Processed clauses                    : 469
% 0.18/0.47  # ...of these trivial                  : 6
% 0.18/0.47  # ...subsumed                          : 164
% 0.18/0.47  # ...remaining for further processing  : 299
% 0.18/0.47  # Other redundant clauses eliminated   : 34
% 0.18/0.47  # Clauses deleted for lack of memory   : 0
% 0.18/0.47  # Backward-subsumed                    : 4
% 0.18/0.47  # Backward-rewritten                   : 146
% 0.18/0.47  # Generated clauses                    : 3544
% 0.18/0.47  # ...of the previous two non-trivial   : 3196
% 0.18/0.47  # Contextual simplify-reflections      : 3
% 0.18/0.47  # Paramodulations                      : 3501
% 0.18/0.47  # Factorizations                       : 9
% 0.18/0.47  # Equation resolutions                 : 34
% 0.18/0.47  # Propositional unsat checks           : 0
% 0.18/0.47  #    Propositional check models        : 0
% 0.18/0.47  #    Propositional check unsatisfiable : 0
% 0.18/0.47  #    Propositional clauses             : 0
% 0.18/0.47  #    Propositional clauses after purity: 0
% 0.18/0.47  #    Propositional unsat core size     : 0
% 0.18/0.47  #    Propositional preprocessing time  : 0.000
% 0.18/0.47  #    Propositional encoding time       : 0.000
% 0.18/0.47  #    Propositional solver time         : 0.000
% 0.18/0.47  #    Success case prop preproc time    : 0.000
% 0.18/0.47  #    Success case prop encoding time   : 0.000
% 0.18/0.47  #    Success case prop solver time     : 0.000
% 0.18/0.47  # Current number of processed clauses  : 83
% 0.18/0.47  #    Positive orientable unit clauses  : 25
% 0.18/0.47  #    Positive unorientable unit clauses: 5
% 0.18/0.47  #    Negative unit clauses             : 3
% 0.18/0.47  #    Non-unit-clauses                  : 50
% 0.18/0.47  # Current number of unprocessed clauses: 2824
% 0.18/0.47  # ...number of literals in the above   : 10353
% 0.18/0.47  # Current number of archived formulas  : 0
% 0.18/0.47  # Current number of archived clauses   : 212
% 0.18/0.47  # Clause-clause subsumption calls (NU) : 3341
% 0.18/0.47  # Rec. Clause-clause subsumption calls : 1826
% 0.18/0.47  # Non-unit clause-clause subsumptions  : 144
% 0.18/0.47  # Unit Clause-clause subsumption calls : 298
% 0.18/0.47  # Rewrite failures with RHS unbound    : 0
% 0.18/0.47  # BW rewrite match attempts            : 290
% 0.18/0.47  # BW rewrite match successes           : 155
% 0.18/0.47  # Condensation attempts                : 0
% 0.18/0.47  # Condensation successes               : 0
% 0.18/0.47  # Termbank termtop insertions          : 72803
% 0.18/0.47  
% 0.18/0.47  # -------------------------------------------------
% 0.18/0.47  # User time                : 0.128 s
% 0.18/0.47  # System time              : 0.005 s
% 0.18/0.47  # Total time               : 0.133 s
% 0.18/0.47  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
