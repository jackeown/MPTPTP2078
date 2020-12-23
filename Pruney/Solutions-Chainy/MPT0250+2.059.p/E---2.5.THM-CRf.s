%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:15 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  145 (18736 expanded)
%              Number of clauses        :   96 (7780 expanded)
%              Number of leaves         :   24 (5477 expanded)
%              Depth                    :   19
%              Number of atoms          :  161 (18755 expanded)
%              Number of equality atoms :  135 (18723 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t80_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t101_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t94_enumset1,axiom,(
    ! [X1] : k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(l29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(c_0_24,plain,(
    ! [X73,X74] : k3_tarski(k2_tarski(X73,X74)) = k2_xboole_0(X73,X74) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X45,X46] : k1_enumset1(X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X20] : k2_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X50,X51,X52,X53] : k3_enumset1(X50,X50,X51,X52,X53) = k2_enumset1(X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X65,X66,X67,X68,X69] : k5_enumset1(X65,X65,X65,X66,X67,X68,X69) = k3_enumset1(X65,X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t80_enumset1])).

fof(c_0_32,plain,(
    ! [X54,X55,X56,X57,X58,X59,X60] : k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60) = k5_enumset1(X54,X55,X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_33,plain,(
    ! [X61,X62,X63,X64] : k4_enumset1(X61,X61,X61,X62,X63,X64) = k2_enumset1(X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_34,plain,(
    ! [X27,X28] : k2_xboole_0(X27,X28) = k5_xboole_0(X27,k4_xboole_0(X28,X27)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_35,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X26] : k4_xboole_0(k1_xboole_0,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_46,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_47,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_49,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_37]),c_0_44]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_52,plain,(
    ! [X21] : k3_xboole_0(X21,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_53,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_44])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_44]),c_0_44])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

fof(c_0_59,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_60,plain,(
    ! [X17,X18,X19] : k3_xboole_0(k3_xboole_0(X17,X18),X19) = k3_xboole_0(X17,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

fof(c_0_62,plain,(
    ! [X12,X13] : k5_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t101_xboole_1])).

fof(c_0_63,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k4_enumset1(X32,X33,X34,X35,X36,X37) = k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_64,plain,(
    ! [X70] : k5_enumset1(X70,X70,X70,X70,X70,X70,X70) = k1_tarski(X70) ),
    inference(variable_rename,[status(thm)],[t94_enumset1])).

fof(c_0_65,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] : k5_enumset1(X38,X39,X40,X41,X42,X43,X44) = k2_xboole_0(k3_enumset1(X38,X39,X40,X41,X42),k2_tarski(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

fof(c_0_66,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | X23 = k2_xboole_0(X22,k4_xboole_0(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_67,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X16,X15)) = k3_xboole_0(k5_xboole_0(X14,X16),X15) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_68,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_61]),c_0_57]),c_0_58])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_73,plain,(
    ! [X29,X30,X31] : k1_enumset1(X29,X30,X31) = k1_enumset1(X31,X30,X29) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

cnf(c_0_74,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_79,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk1_0),esk2_0),esk2_0)
    & ~ r2_hidden(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_69])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_37]),c_0_44]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_83,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_84,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_37]),c_0_38]),c_0_75]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_85,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_28]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_86,plain,
    ( X2 = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_37]),c_0_44]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_71]),c_0_69])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk1_0),esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_80])).

cnf(c_0_90,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_69])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_69])).

cnf(c_0_92,plain,
    ( k5_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,k3_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_48]),c_0_48]),c_0_69]),c_0_70])).

cnf(c_0_93,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_94,plain,
    ( k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6))) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_48]),c_0_48])).

cnf(c_0_95,plain,
    ( k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X7))) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_48]),c_0_48])).

cnf(c_0_96,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_71]),c_0_69])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_61,c_0_71])).

cnf(c_0_98,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_86,c_0_48])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_69])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_37]),c_0_38]),c_0_75]),c_0_75]),c_0_75]),c_0_39]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_89]),c_0_91])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_71]),c_0_69])).

cnf(c_0_103,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_80]),c_0_58])).

cnf(c_0_104,plain,
    ( k4_enumset1(X1,X1,X1,X1,X2,X3) = k4_enumset1(X3,X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_48]),c_0_48])).

cnf(c_0_105,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_90]),c_0_78]),c_0_97]),c_0_80]),c_0_87]),c_0_70]),c_0_81])).

cnf(c_0_107,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) = k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_101]),c_0_102])).

cnf(c_0_110,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,plain,
    ( k4_enumset1(X1,X1,X1,X1,X2,X3) = k4_enumset1(X1,X1,X1,X2,X3,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_105])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(k5_xboole_0(X2,X1),X3))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_106]),c_0_80]),c_0_70])).

cnf(c_0_113,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_106]),c_0_58])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_107]),c_0_70]),c_0_69]),c_0_81]),c_0_106]),c_0_58])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))),esk2_0) ),
    inference(rw,[status(thm)],[c_0_108,c_0_54])).

cnf(c_0_116,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_69])).

cnf(c_0_117,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_99]),c_0_99]),c_0_99]),c_0_81])).

cnf(c_0_118,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X2))))) = k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_106]),c_0_89]),c_0_70]),c_0_109])).

cnf(c_0_119,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_54]),c_0_80]),c_0_58]),c_0_58])).

cnf(c_0_120,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2))) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X3,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_70])).

cnf(c_0_121,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_112,c_0_91])).

cnf(c_0_122,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))),esk2_0) ),
    inference(rw,[status(thm)],[c_0_115,c_0_99])).

cnf(c_0_124,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(k5_xboole_0(X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_81]),c_0_116]),c_0_69])).

cnf(c_0_125,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_117]),c_0_69]),c_0_70])).

cnf(c_0_126,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_70]),c_0_70])).

cnf(c_0_127,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X2))))) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_128,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(k5_xboole_0(X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_90]),c_0_78]),c_0_69])).

fof(c_0_129,plain,(
    ! [X71,X72] :
      ( k3_xboole_0(X71,k1_tarski(X72)) != k1_tarski(X72)
      | r2_hidden(X72,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).

cnf(c_0_130,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X4,k5_xboole_0(X4,X2))) = k3_xboole_0(X1,k3_xboole_0(X4,k5_xboole_0(X4,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_58])).

cnf(c_0_131,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))) = k3_xboole_0(esk2_0,k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_69]),c_0_124]),c_0_69])).

cnf(c_0_132,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X2))) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_125]),c_0_58]),c_0_70])).

cnf(c_0_133,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_81]),c_0_70]),c_0_126]),c_0_91])).

cnf(c_0_134,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_135,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_136,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(X1,k5_xboole_0(X1,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_70]),c_0_121])).

cnf(c_0_137,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133]),c_0_134])).

cnf(c_0_138,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_75]),c_0_75]),c_0_41]),c_0_41])).

cnf(c_0_139,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_136]),c_0_137])).

cnf(c_0_140,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_137]),c_0_99]),c_0_117])).

cnf(c_0_141,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1)) != k4_enumset1(X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_48]),c_0_48])).

cnf(c_0_142,negated_conjecture,
    ( k3_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_139]),c_0_58]),c_0_140]),c_0_69])).

cnf(c_0_143,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_144,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_143]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 2.76/3.01  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.76/3.01  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.76/3.01  #
% 2.76/3.01  # Preprocessing time       : 0.027 s
% 2.76/3.01  # Presaturation interreduction done
% 2.76/3.01  
% 2.76/3.01  # Proof found!
% 2.76/3.01  # SZS status Theorem
% 2.76/3.01  # SZS output start CNFRefutation
% 2.76/3.01  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.76/3.01  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.76/3.01  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.76/3.01  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.76/3.01  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.76/3.01  fof(t80_enumset1, axiom, ![X1, X2, X3, X4, X5]:k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 2.76/3.01  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.76/3.01  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 2.76/3.01  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.76/3.01  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.76/3.01  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.76/3.01  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.76/3.01  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.76/3.01  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.76/3.01  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.76/3.01  fof(t101_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 2.76/3.01  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.76/3.01  fof(t94_enumset1, axiom, ![X1]:k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_enumset1)).
% 2.76/3.01  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.76/3.01  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.76/3.01  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 2.76/3.01  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.76/3.01  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 2.76/3.01  fof(l29_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.76/3.01  fof(c_0_24, plain, ![X73, X74]:k3_tarski(k2_tarski(X73,X74))=k2_xboole_0(X73,X74), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 2.76/3.01  fof(c_0_25, plain, ![X45, X46]:k1_enumset1(X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.76/3.01  fof(c_0_26, plain, ![X20]:k2_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t1_boole])).
% 2.76/3.01  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.76/3.01  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.76/3.01  fof(c_0_29, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.76/3.01  fof(c_0_30, plain, ![X50, X51, X52, X53]:k3_enumset1(X50,X50,X51,X52,X53)=k2_enumset1(X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.76/3.01  fof(c_0_31, plain, ![X65, X66, X67, X68, X69]:k5_enumset1(X65,X65,X65,X66,X67,X68,X69)=k3_enumset1(X65,X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t80_enumset1])).
% 2.76/3.01  fof(c_0_32, plain, ![X54, X55, X56, X57, X58, X59, X60]:k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60)=k5_enumset1(X54,X55,X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 2.76/3.01  fof(c_0_33, plain, ![X61, X62, X63, X64]:k4_enumset1(X61,X61,X61,X62,X63,X64)=k2_enumset1(X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 2.76/3.01  fof(c_0_34, plain, ![X27, X28]:k2_xboole_0(X27,X28)=k5_xboole_0(X27,k4_xboole_0(X28,X27)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.76/3.01  fof(c_0_35, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.76/3.01  cnf(c_0_36, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.76/3.01  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 2.76/3.01  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.76/3.01  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.76/3.01  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.76/3.01  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.76/3.01  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.76/3.01  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.76/3.01  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.76/3.01  fof(c_0_45, plain, ![X26]:k4_xboole_0(k1_xboole_0,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 2.76/3.01  fof(c_0_46, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.76/3.01  cnf(c_0_47, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 2.76/3.01  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_39]), c_0_40]), c_0_41])).
% 2.76/3.01  cnf(c_0_49, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_37]), c_0_44]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 2.76/3.01  cnf(c_0_50, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.76/3.01  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.76/3.01  fof(c_0_52, plain, ![X21]:k3_xboole_0(X21,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 2.76/3.01  cnf(c_0_53, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 2.76/3.01  cnf(c_0_54, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_49, c_0_48])).
% 2.76/3.01  cnf(c_0_55, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_44])).
% 2.76/3.01  cnf(c_0_56, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_44]), c_0_44])).
% 2.76/3.01  cnf(c_0_57, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 2.76/3.01  cnf(c_0_58, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 2.76/3.01  fof(c_0_59, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.76/3.01  fof(c_0_60, plain, ![X17, X18, X19]:k3_xboole_0(k3_xboole_0(X17,X18),X19)=k3_xboole_0(X17,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 2.76/3.01  cnf(c_0_61, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 2.76/3.01  fof(c_0_62, plain, ![X12, X13]:k5_xboole_0(X12,X13)=k4_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t101_xboole_1])).
% 2.76/3.01  fof(c_0_63, plain, ![X32, X33, X34, X35, X36, X37]:k4_enumset1(X32,X33,X34,X35,X36,X37)=k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k1_tarski(X37)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 2.76/3.01  fof(c_0_64, plain, ![X70]:k5_enumset1(X70,X70,X70,X70,X70,X70,X70)=k1_tarski(X70), inference(variable_rename,[status(thm)],[t94_enumset1])).
% 2.76/3.01  fof(c_0_65, plain, ![X38, X39, X40, X41, X42, X43, X44]:k5_enumset1(X38,X39,X40,X41,X42,X43,X44)=k2_xboole_0(k3_enumset1(X38,X39,X40,X41,X42),k2_tarski(X43,X44)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 2.76/3.01  fof(c_0_66, plain, ![X22, X23]:(~r1_tarski(X22,X23)|X23=k2_xboole_0(X22,k4_xboole_0(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 2.76/3.01  fof(c_0_67, plain, ![X14, X15, X16]:k5_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X16,X15))=k3_xboole_0(k5_xboole_0(X14,X16),X15), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 2.76/3.01  fof(c_0_68, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 2.76/3.01  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.76/3.01  cnf(c_0_70, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 2.76/3.01  cnf(c_0_71, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_61]), c_0_57]), c_0_58])).
% 2.76/3.01  cnf(c_0_72, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 2.76/3.01  fof(c_0_73, plain, ![X29, X30, X31]:k1_enumset1(X29,X30,X31)=k1_enumset1(X31,X30,X29), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 2.76/3.01  cnf(c_0_74, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.76/3.01  cnf(c_0_75, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.76/3.01  cnf(c_0_76, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 2.76/3.01  cnf(c_0_77, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 2.76/3.01  cnf(c_0_78, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 2.76/3.01  fof(c_0_79, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk1_0),esk2_0),esk2_0)&~r2_hidden(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).
% 2.76/3.01  cnf(c_0_80, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_69])).
% 2.76/3.01  cnf(c_0_81, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.76/3.01  cnf(c_0_82, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_37]), c_0_44]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 2.76/3.01  cnf(c_0_83, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.76/3.01  cnf(c_0_84, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_37]), c_0_38]), c_0_75]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 2.76/3.01  cnf(c_0_85, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_28]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 2.76/3.01  cnf(c_0_86, plain, (X2=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_37]), c_0_44]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 2.76/3.01  cnf(c_0_87, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_71]), c_0_69])).
% 2.76/3.01  cnf(c_0_88, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk1_0),esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 2.76/3.01  cnf(c_0_89, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))=k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_78, c_0_80])).
% 2.76/3.01  cnf(c_0_90, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_81, c_0_69])).
% 2.76/3.01  cnf(c_0_91, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_70, c_0_69])).
% 2.76/3.01  cnf(c_0_92, plain, (k5_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,k3_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_48]), c_0_48]), c_0_69]), c_0_70])).
% 2.76/3.01  cnf(c_0_93, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 2.76/3.01  cnf(c_0_94, plain, (k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6)))=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_48]), c_0_48])).
% 2.76/3.01  cnf(c_0_95, plain, (k3_tarski(k4_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X7)))=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_48]), c_0_48])).
% 2.76/3.01  cnf(c_0_96, plain, (k5_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(X2,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_71]), c_0_69])).
% 2.76/3.01  cnf(c_0_97, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_61, c_0_71])).
% 2.76/3.01  cnf(c_0_98, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_86, c_0_48])).
% 2.76/3.01  cnf(c_0_99, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_87, c_0_69])).
% 2.76/3.01  cnf(c_0_100, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_37]), c_0_38]), c_0_75]), c_0_75]), c_0_75]), c_0_39]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 2.76/3.01  cnf(c_0_101, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2))=k3_xboole_0(k5_xboole_0(k1_xboole_0,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_89]), c_0_91])).
% 2.76/3.01  cnf(c_0_102, plain, (k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_71]), c_0_69])).
% 2.76/3.01  cnf(c_0_103, plain, (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_80]), c_0_58])).
% 2.76/3.01  cnf(c_0_104, plain, (k4_enumset1(X1,X1,X1,X1,X2,X3)=k4_enumset1(X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_48]), c_0_48])).
% 2.76/3.01  cnf(c_0_105, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 2.76/3.01  cnf(c_0_106, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_90]), c_0_78]), c_0_97]), c_0_80]), c_0_87]), c_0_70]), c_0_81])).
% 2.76/3.01  cnf(c_0_107, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 2.76/3.01  cnf(c_0_108, negated_conjecture, (r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48])).
% 2.76/3.01  cnf(c_0_109, plain, (k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)=k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_101]), c_0_102])).
% 2.76/3.01  cnf(c_0_110, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,k1_xboole_0,k1_xboole_0))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 2.76/3.01  cnf(c_0_111, plain, (k4_enumset1(X1,X1,X1,X1,X2,X3)=k4_enumset1(X1,X1,X1,X2,X3,X3)), inference(spm,[status(thm)],[c_0_48, c_0_105])).
% 2.76/3.01  cnf(c_0_112, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(k5_xboole_0(X2,X1),X3)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_106]), c_0_80]), c_0_70])).
% 2.76/3.01  cnf(c_0_113, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_106]), c_0_58])).
% 2.76/3.01  cnf(c_0_114, plain, (k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_107]), c_0_70]), c_0_69]), c_0_81]), c_0_106]), c_0_58])).
% 2.76/3.01  cnf(c_0_115, negated_conjecture, (r1_tarski(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))),esk2_0)), inference(rw,[status(thm)],[c_0_108, c_0_54])).
% 2.76/3.01  cnf(c_0_116, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_78, c_0_69])).
% 2.76/3.01  cnf(c_0_117, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_99]), c_0_99]), c_0_99]), c_0_81])).
% 2.76/3.01  cnf(c_0_118, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X2)))))=k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_106]), c_0_89]), c_0_70]), c_0_109])).
% 2.76/3.01  cnf(c_0_119, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_54]), c_0_80]), c_0_58]), c_0_58])).
% 2.76/3.01  cnf(c_0_120, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)))=k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X3,X4)),X2)), inference(spm,[status(thm)],[c_0_78, c_0_70])).
% 2.76/3.01  cnf(c_0_121, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_112, c_0_91])).
% 2.76/3.01  cnf(c_0_122, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 2.76/3.01  cnf(c_0_123, negated_conjecture, (r1_tarski(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))),esk2_0)), inference(rw,[status(thm)],[c_0_115, c_0_99])).
% 2.76/3.01  cnf(c_0_124, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(k5_xboole_0(X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_81]), c_0_116]), c_0_69])).
% 2.76/3.01  cnf(c_0_125, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_117]), c_0_69]), c_0_70])).
% 2.76/3.01  cnf(c_0_126, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_70]), c_0_70])).
% 2.76/3.01  cnf(c_0_127, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X2)))))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_118, c_0_119])).
% 2.76/3.01  cnf(c_0_128, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(k5_xboole_0(X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_90]), c_0_78]), c_0_69])).
% 2.76/3.01  fof(c_0_129, plain, ![X71, X72]:(k3_xboole_0(X71,k1_tarski(X72))!=k1_tarski(X72)|r2_hidden(X72,X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).
% 2.76/3.01  cnf(c_0_130, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X4,k5_xboole_0(X4,X2)))=k3_xboole_0(X1,k3_xboole_0(X4,k5_xboole_0(X4,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_58])).
% 2.76/3.01  cnf(c_0_131, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))=k3_xboole_0(esk2_0,k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_69]), c_0_124]), c_0_69])).
% 2.76/3.01  cnf(c_0_132, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X2)))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_125]), c_0_58]), c_0_70])).
% 2.76/3.01  cnf(c_0_133, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3)))=k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_81]), c_0_70]), c_0_126]), c_0_91])).
% 2.76/3.01  cnf(c_0_134, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_127, c_0_128])).
% 2.76/3.01  cnf(c_0_135, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 2.76/3.01  cnf(c_0_136, negated_conjecture, (k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(X1,k5_xboole_0(X1,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_70]), c_0_121])).
% 2.76/3.01  cnf(c_0_137, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_133]), c_0_134])).
% 2.76/3.01  cnf(c_0_138, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_75]), c_0_75]), c_0_41]), c_0_41])).
% 2.76/3.01  cnf(c_0_139, negated_conjecture, (k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_136]), c_0_137])).
% 2.76/3.01  cnf(c_0_140, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_137]), c_0_99]), c_0_117])).
% 2.76/3.01  cnf(c_0_141, plain, (r2_hidden(X1,X2)|k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1))!=k4_enumset1(X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_48]), c_0_48])).
% 2.76/3.01  cnf(c_0_142, negated_conjecture, (k3_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_139]), c_0_58]), c_0_140]), c_0_69])).
% 2.76/3.01  cnf(c_0_143, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 2.76/3.01  cnf(c_0_144, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_143]), ['proof']).
% 2.76/3.01  # SZS output end CNFRefutation
% 2.76/3.01  # Proof object total steps             : 145
% 2.76/3.01  # Proof object clause steps            : 96
% 2.76/3.01  # Proof object formula steps           : 49
% 2.76/3.01  # Proof object conjectures             : 14
% 2.76/3.01  # Proof object clause conjectures      : 11
% 2.76/3.01  # Proof object formula conjectures     : 3
% 2.76/3.01  # Proof object initial clauses used    : 25
% 2.76/3.01  # Proof object initial formulas used   : 24
% 2.76/3.01  # Proof object generating inferences   : 39
% 2.76/3.01  # Proof object simplifying inferences  : 190
% 2.76/3.01  # Training examples: 0 positive, 0 negative
% 2.76/3.01  # Parsed axioms                        : 24
% 2.76/3.01  # Removed by relevancy pruning/SinE    : 0
% 2.76/3.01  # Initial clauses                      : 25
% 2.76/3.01  # Removed in clause preprocessing      : 8
% 2.76/3.01  # Initial clauses in saturation        : 17
% 2.76/3.01  # Processed clauses                    : 10144
% 2.76/3.01  # ...of these trivial                  : 727
% 2.76/3.01  # ...subsumed                          : 8608
% 2.76/3.01  # ...remaining for further processing  : 809
% 2.76/3.01  # Other redundant clauses eliminated   : 0
% 2.76/3.01  # Clauses deleted for lack of memory   : 0
% 2.76/3.01  # Backward-subsumed                    : 24
% 2.76/3.01  # Backward-rewritten                   : 124
% 2.76/3.01  # Generated clauses                    : 268752
% 2.76/3.01  # ...of the previous two non-trivial   : 236761
% 2.76/3.01  # Contextual simplify-reflections      : 0
% 2.76/3.01  # Paramodulations                      : 268752
% 2.76/3.01  # Factorizations                       : 0
% 2.76/3.01  # Equation resolutions                 : 0
% 2.76/3.01  # Propositional unsat checks           : 0
% 2.76/3.01  #    Propositional check models        : 0
% 2.76/3.01  #    Propositional check unsatisfiable : 0
% 2.76/3.01  #    Propositional clauses             : 0
% 2.76/3.01  #    Propositional clauses after purity: 0
% 2.76/3.01  #    Propositional unsat core size     : 0
% 2.76/3.01  #    Propositional preprocessing time  : 0.000
% 2.76/3.01  #    Propositional encoding time       : 0.000
% 2.76/3.01  #    Propositional solver time         : 0.000
% 2.76/3.01  #    Success case prop preproc time    : 0.000
% 2.76/3.01  #    Success case prop encoding time   : 0.000
% 2.76/3.01  #    Success case prop solver time     : 0.000
% 2.76/3.01  # Current number of processed clauses  : 644
% 2.76/3.01  #    Positive orientable unit clauses  : 231
% 2.76/3.01  #    Positive unorientable unit clauses: 45
% 2.76/3.01  #    Negative unit clauses             : 1
% 2.76/3.01  #    Non-unit-clauses                  : 367
% 2.76/3.01  # Current number of unprocessed clauses: 225491
% 2.76/3.01  # ...number of literals in the above   : 340872
% 2.76/3.01  # Current number of archived formulas  : 0
% 2.76/3.01  # Current number of archived clauses   : 173
% 2.76/3.01  # Clause-clause subsumption calls (NU) : 96910
% 2.76/3.01  # Rec. Clause-clause subsumption calls : 82919
% 2.76/3.01  # Non-unit clause-clause subsumptions  : 7620
% 2.76/3.01  # Unit Clause-clause subsumption calls : 2063
% 2.76/3.01  # Rewrite failures with RHS unbound    : 0
% 2.76/3.01  # BW rewrite match attempts            : 10578
% 2.76/3.01  # BW rewrite match successes           : 683
% 2.76/3.01  # Condensation attempts                : 0
% 2.76/3.01  # Condensation successes               : 0
% 2.76/3.01  # Termbank termtop insertions          : 5889298
% 2.86/3.02  
% 2.86/3.02  # -------------------------------------------------
% 2.86/3.02  # User time                : 2.536 s
% 2.86/3.02  # System time              : 0.144 s
% 2.86/3.02  # Total time               : 2.680 s
% 2.86/3.02  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
