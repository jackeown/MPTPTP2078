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
% DateTime   : Thu Dec  3 10:38:15 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 (13770 expanded)
%              Number of clauses        :   48 (4959 expanded)
%              Number of leaves         :   19 (4382 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 (13933 expanded)
%              Number of equality atoms :  100 (13921 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t21_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_xboole_0
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t136_enumset1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != X2
        & X1 != X3
        & k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1)) != k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(c_0_19,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_xboole_0
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t21_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] : k6_enumset1(X27,X28,X29,X30,X31,X32,X33,X34) = k2_xboole_0(k5_enumset1(X27,X28,X29,X30,X31,X32,X33),k1_tarski(X34)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_23,plain,(
    ! [X35] : k2_tarski(X35,X35) = k1_tarski(X35) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X36,X37] : k1_enumset1(X36,X36,X37) = k2_tarski(X36,X37) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X41,X42,X43,X44] : k3_enumset1(X41,X41,X42,X43,X44) = k2_enumset1(X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X45,X46,X47,X48,X49] : k4_enumset1(X45,X45,X46,X47,X48,X49) = k3_enumset1(X45,X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X50,X51,X52,X53,X54,X55] : k5_enumset1(X50,X50,X51,X52,X53,X54,X55) = k4_enumset1(X50,X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X56,X57,X58,X59,X60,X61,X62] : k6_enumset1(X56,X56,X57,X58,X59,X60,X61,X62) = k5_enumset1(X56,X57,X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_xboole_0
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_33,plain,(
    ! [X20,X21,X22,X23] : k2_enumset1(X20,X21,X22,X23) = k2_enumset1(X23,X22,X21,X20) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_34,plain,(
    ! [X13] : k5_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_35,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_47,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X14,X15),X16) = k5_xboole_0(X14,k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_48,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_26]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

fof(c_0_54,plain,(
    ! [X65,X66] :
      ( ( k4_xboole_0(k1_tarski(X65),X66) != k1_xboole_0
        | r2_hidden(X65,X66) )
      & ( ~ r2_hidden(X65,X66)
        | k4_xboole_0(k1_tarski(X65),X66) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_49]),c_0_53])).

fof(c_0_59,plain,(
    ! [X63,X64] :
      ( ( k4_xboole_0(k1_tarski(X63),X64) != k1_tarski(X63)
        | ~ r2_hidden(X63,X64) )
      & ( r2_hidden(X63,X64)
        | k4_xboole_0(k1_tarski(X63),X64) = k1_tarski(X63) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_58]),c_0_51])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_37]),c_0_38]),c_0_26]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_61])).

fof(c_0_66,plain,(
    ! [X24,X25,X26] :
      ( X24 = X25
      | X24 = X26
      | k4_xboole_0(k1_enumset1(X24,X25,X26),k1_tarski(X24)) = k2_tarski(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_enumset1])])).

cnf(c_0_67,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk2_0) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_62])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_26]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_56])])).

cnf(c_0_70,plain,
    ( X1 = X2
    | X1 = X3
    | k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1)) = k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_62]),c_0_51])).

cnf(c_0_72,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk2_0,X1) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_67]),c_0_51])).

cnf(c_0_73,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_65]),c_0_56])).

cnf(c_0_74,plain,
    ( X1 = X3
    | X1 = X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_37]),c_0_38]),c_0_38]),c_0_26]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3) = k6_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_71]),c_0_51])).

cnf(c_0_76,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_72]),c_0_51])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_58])).

cnf(c_0_78,plain,
    ( X1 = X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3,X4) = k6_enumset1(esk1_0,esk2_0,esk2_0,esk2_0,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_75]),c_0_51])).

cnf(c_0_80,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3) = k6_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_76]),c_0_51])).

cnf(c_0_81,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk1_0) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_77]),c_0_49])).

cnf(c_0_82,negated_conjecture,
    ( esk2_0 = X1
    | k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X1),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X1),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_75]),c_0_76]),c_0_75]),c_0_76]),c_0_80]),c_0_76]),c_0_72]),c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk1_0,X1) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_81]),c_0_51])).

cnf(c_0_84,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_79]),c_0_80]),c_0_76]),c_0_72]),c_0_67]),c_0_80]),c_0_76]),c_0_72]),c_0_67]),c_0_80]),c_0_76]),c_0_72]),c_0_67])).

cnf(c_0_85,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_81]),c_0_81]),c_0_84]),c_0_56])]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:08:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.21/0.44  # and selection function GSelectMinInfpos.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.026 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.44  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.44  fof(t21_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_xboole_0=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 0.21/0.44  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 0.21/0.44  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.44  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.44  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.44  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.44  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.44  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.44  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.44  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.21/0.44  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.44  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.21/0.44  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.44  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.21/0.44  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.21/0.44  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.21/0.44  fof(t136_enumset1, axiom, ![X1, X2, X3]:~(((X1!=X2&X1!=X3)&k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1))!=k2_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 0.21/0.44  fof(c_0_19, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.44  fof(c_0_20, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.44  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_xboole_0=>X1=X2)), inference(assume_negation,[status(cth)],[t21_zfmisc_1])).
% 0.21/0.44  fof(c_0_22, plain, ![X27, X28, X29, X30, X31, X32, X33, X34]:k6_enumset1(X27,X28,X29,X30,X31,X32,X33,X34)=k2_xboole_0(k5_enumset1(X27,X28,X29,X30,X31,X32,X33),k1_tarski(X34)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.21/0.44  fof(c_0_23, plain, ![X35]:k2_tarski(X35,X35)=k1_tarski(X35), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.44  fof(c_0_24, plain, ![X36, X37]:k1_enumset1(X36,X36,X37)=k2_tarski(X36,X37), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.44  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.44  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.44  fof(c_0_27, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.44  fof(c_0_28, plain, ![X41, X42, X43, X44]:k3_enumset1(X41,X41,X42,X43,X44)=k2_enumset1(X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.44  fof(c_0_29, plain, ![X45, X46, X47, X48, X49]:k4_enumset1(X45,X45,X46,X47,X48,X49)=k3_enumset1(X45,X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.44  fof(c_0_30, plain, ![X50, X51, X52, X53, X54, X55]:k5_enumset1(X50,X50,X51,X52,X53,X54,X55)=k4_enumset1(X50,X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.44  fof(c_0_31, plain, ![X56, X57, X58, X59, X60, X61, X62]:k6_enumset1(X56,X56,X57,X58,X59,X60,X61,X62)=k5_enumset1(X56,X57,X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.44  fof(c_0_32, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_xboole_0&esk1_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.21/0.44  fof(c_0_33, plain, ![X20, X21, X22, X23]:k2_enumset1(X20,X21,X22,X23)=k2_enumset1(X23,X22,X21,X20), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.21/0.44  fof(c_0_34, plain, ![X13]:k5_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.44  fof(c_0_35, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.21/0.44  cnf(c_0_36, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.44  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.44  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.44  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.44  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.44  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.44  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.44  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.44  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.44  cnf(c_0_46, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.44  fof(c_0_47, plain, ![X14, X15, X16]:k5_xboole_0(k5_xboole_0(X14,X15),X16)=k5_xboole_0(X14,k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.44  fof(c_0_48, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.21/0.44  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.44  cnf(c_0_50, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.44  cnf(c_0_51, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.21/0.44  cnf(c_0_52, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_26]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44])).
% 0.21/0.44  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.21/0.44  fof(c_0_54, plain, ![X65, X66]:((k4_xboole_0(k1_tarski(X65),X66)!=k1_xboole_0|r2_hidden(X65,X66))&(~r2_hidden(X65,X66)|k4_xboole_0(k1_tarski(X65),X66)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.21/0.44  cnf(c_0_55, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.44  cnf(c_0_56, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.44  cnf(c_0_57, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.44  cnf(c_0_58, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_49]), c_0_53])).
% 0.21/0.44  fof(c_0_59, plain, ![X63, X64]:((k4_xboole_0(k1_tarski(X63),X64)!=k1_tarski(X63)|~r2_hidden(X63,X64))&(r2_hidden(X63,X64)|k4_xboole_0(k1_tarski(X63),X64)=k1_tarski(X63))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.21/0.44  cnf(c_0_60, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.44  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.21/0.44  cnf(c_0_62, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_58]), c_0_51])).
% 0.21/0.44  cnf(c_0_63, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.44  cnf(c_0_64, plain, (r2_hidden(X1,X2)|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_37]), c_0_38]), c_0_26]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.21/0.44  cnf(c_0_65, plain, (k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_51, c_0_61])).
% 0.21/0.44  fof(c_0_66, plain, ![X24, X25, X26]:(X24=X25|X24=X26|k4_xboole_0(k1_enumset1(X24,X25,X26),k1_tarski(X24))=k2_tarski(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_enumset1])])).
% 0.21/0.44  cnf(c_0_67, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk2_0)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_58, c_0_62])).
% 0.21/0.44  cnf(c_0_68, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_26]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44])).
% 0.21/0.44  cnf(c_0_69, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_56])])).
% 0.21/0.44  cnf(c_0_70, plain, (X1=X2|X1=X3|k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1))=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.44  cnf(c_0_71, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_62]), c_0_51])).
% 0.21/0.44  cnf(c_0_72, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_67]), c_0_51])).
% 0.21/0.44  cnf(c_0_73, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_65]), c_0_56])).
% 0.21/0.44  cnf(c_0_74, plain, (X1=X3|X1=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_37]), c_0_38]), c_0_38]), c_0_26]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.21/0.44  cnf(c_0_75, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3)=k6_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_71]), c_0_51])).
% 0.21/0.44  cnf(c_0_76, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_72]), c_0_51])).
% 0.21/0.44  cnf(c_0_77, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_52, c_0_58])).
% 0.21/0.44  cnf(c_0_78, plain, (X1=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.44  cnf(c_0_79, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3,X4)=k6_enumset1(esk1_0,esk2_0,esk2_0,esk2_0,X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_75]), c_0_51])).
% 0.21/0.44  cnf(c_0_80, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3)=k6_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_76]), c_0_51])).
% 0.21/0.44  cnf(c_0_81, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk1_0)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_77]), c_0_49])).
% 0.21/0.44  cnf(c_0_82, negated_conjecture, (esk2_0=X1|k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X1),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1,X1),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_75]), c_0_76]), c_0_75]), c_0_76]), c_0_80]), c_0_76]), c_0_72]), c_0_67])).
% 0.21/0.44  cnf(c_0_83, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,esk1_0,X1)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_81]), c_0_51])).
% 0.21/0.44  cnf(c_0_84, negated_conjecture, (k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_79]), c_0_80]), c_0_76]), c_0_72]), c_0_67]), c_0_80]), c_0_76]), c_0_72]), c_0_67]), c_0_80]), c_0_76]), c_0_72]), c_0_67])).
% 0.21/0.44  cnf(c_0_85, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.44  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_81]), c_0_81]), c_0_84]), c_0_56])]), c_0_85]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 87
% 0.21/0.44  # Proof object clause steps            : 48
% 0.21/0.44  # Proof object formula steps           : 39
% 0.21/0.44  # Proof object conjectures             : 21
% 0.21/0.44  # Proof object clause conjectures      : 18
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 20
% 0.21/0.44  # Proof object initial formulas used   : 19
% 0.21/0.44  # Proof object generating inferences   : 19
% 0.21/0.44  # Proof object simplifying inferences  : 145
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 19
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 22
% 0.21/0.44  # Removed in clause preprocessing      : 9
% 0.21/0.44  # Initial clauses in saturation        : 13
% 0.21/0.44  # Processed clauses                    : 431
% 0.21/0.44  # ...of these trivial                  : 83
% 0.21/0.44  # ...subsumed                          : 258
% 0.21/0.44  # ...remaining for further processing  : 90
% 0.21/0.45  # Other redundant clauses eliminated   : 0
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 1
% 0.21/0.45  # Backward-rewritten                   : 8
% 0.21/0.45  # Generated clauses                    : 1886
% 0.21/0.45  # ...of the previous two non-trivial   : 1663
% 0.21/0.45  # Contextual simplify-reflections      : 0
% 0.21/0.45  # Paramodulations                      : 1886
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 0
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 68
% 0.21/0.45  #    Positive orientable unit clauses  : 27
% 0.21/0.45  #    Positive unorientable unit clauses: 6
% 0.21/0.45  #    Negative unit clauses             : 4
% 0.21/0.45  #    Non-unit-clauses                  : 31
% 0.21/0.45  # Current number of unprocessed clauses: 1239
% 0.21/0.45  # ...number of literals in the above   : 3423
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 31
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 358
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 291
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 104
% 0.21/0.45  # Unit Clause-clause subsumption calls : 82
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 182
% 0.21/0.45  # BW rewrite match successes           : 105
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 34804
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.099 s
% 0.21/0.45  # System time              : 0.005 s
% 0.21/0.45  # Total time               : 0.104 s
% 0.21/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
