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
% DateTime   : Thu Dec  3 10:59:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 (25209 expanded)
%              Number of clauses        :   64 (9642 expanded)
%              Number of leaves         :   20 (7783 expanded)
%              Depth                    :   17
%              Number of atoms          :  107 (25211 expanded)
%              Number of equality atoms :  106 (25210 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t133_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).

fof(t132_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(t100_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_20,plain,(
    ! [X80,X81] : k3_tarski(k2_tarski(X80,X81)) = k2_xboole_0(X80,X81) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X60,X61] : k1_enumset1(X60,X60,X61) = k2_tarski(X60,X61) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k5_enumset1(X44,X45,X46,X47,X48,X49,X50) = k2_xboole_0(k3_enumset1(X44,X45,X46,X47,X48),k2_tarski(X49,X50)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X62,X63,X64] : k2_enumset1(X62,X62,X63,X64) = k1_enumset1(X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X65,X66,X67,X68] : k3_enumset1(X65,X65,X66,X67,X68) = k2_enumset1(X65,X66,X67,X68) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X69,X70,X71,X72,X73] : k4_enumset1(X69,X69,X70,X71,X72,X73) = k3_enumset1(X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X74,X75,X76,X77,X78,X79] : k5_enumset1(X74,X74,X75,X76,X77,X78,X79) = k4_enumset1(X74,X75,X76,X77,X78,X79) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_30,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57,X58] : k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) = k2_xboole_0(k4_enumset1(X51,X52,X53,X54,X55,X56),k2_tarski(X57,X58)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

fof(c_0_31,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42,X43] : k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) = k2_xboole_0(k5_enumset1(X35,X36,X37,X38,X39,X40,X41),k2_tarski(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t133_enumset1])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_24]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_42,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_24]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_44,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_24]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

fof(c_0_45,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33,X34] : k7_enumset1(X26,X27,X28,X29,X30,X31,X32,X33,X34) = k2_xboole_0(k4_enumset1(X26,X27,X28,X29,X30,X31),k1_enumset1(X32,X33,X34)) ),
    inference(variable_rename,[status(thm)],[t132_enumset1])).

fof(c_0_46,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X1,X1,X1,X2,X3,X4,X5))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X8),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X9),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_44,c_0_42])).

fof(c_0_50,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22] : k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

cnf(c_0_51,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_57,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_24]),c_0_24]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_58,plain,
    ( k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_33]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_56,c_0_42])).

cnf(c_0_61,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X2,X2,X2,X2,X1,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_57]),c_0_49]),c_0_58]),c_0_58])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X2,X3,X4))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_59,c_0_42])).

fof(c_0_63,plain,(
    ! [X23,X24,X25] : k1_enumset1(X23,X24,X25) = k1_enumset1(X24,X25,X23) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

cnf(c_0_64,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X5,X5,X6,X7) = k5_enumset1(X2,X1,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_58])).

cnf(c_0_65,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_66,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X2,X3,X3,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_58,c_0_64])).

cnf(c_0_67,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X2,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_68,plain,
    ( k5_enumset1(X1,X1,X2,X2,X2,X3,X4) = k5_enumset1(X2,X2,X2,X2,X1,X3,X4) ),
    inference(spm,[status(thm)],[c_0_61,c_0_66])).

cnf(c_0_69,plain,
    ( k7_enumset1(X1,X2,X2,X2,X3,X4,X5,X6,X7) = k5_enumset1(X2,X1,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_66]),c_0_62]),c_0_64])).

cnf(c_0_70,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_57])).

fof(c_0_71,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

cnf(c_0_72,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X5,X6) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_68]),c_0_60]),c_0_69]),c_0_58])).

cnf(c_0_73,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_70])).

fof(c_0_74,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).

fof(c_0_75,plain,(
    ! [X59] : k2_tarski(X59,X59) = k1_tarski(X59) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_76,plain,(
    ! [X89,X90,X91] : k3_mcart_1(X89,X90,X91) = k4_tarski(k4_tarski(X89,X90),X91) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_77,plain,(
    ! [X92,X93,X94] : k3_zfmisc_1(X92,X93,X94) = k2_zfmisc_1(k2_zfmisc_1(X92,X93),X94) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_78,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X2,X3) = k5_enumset1(X2,X2,X2,X2,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_72])).

cnf(c_0_79,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X2,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_72])).

fof(c_0_80,plain,(
    ! [X82,X83,X84,X85] : k2_zfmisc_1(k2_tarski(X82,X83),k2_tarski(X84,X85)) = k2_enumset1(k4_tarski(X82,X84),k4_tarski(X82,X85),k4_tarski(X83,X84),k4_tarski(X83,X85)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

fof(c_0_81,plain,(
    ! [X86,X87,X88] :
      ( k2_zfmisc_1(k1_tarski(X86),k2_tarski(X87,X88)) = k2_tarski(k4_tarski(X86,X87),k4_tarski(X86,X88))
      & k2_zfmisc_1(k2_tarski(X86,X87),k1_tarski(X88)) = k2_tarski(k4_tarski(X86,X88),k4_tarski(X87,X88)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_82,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X3,X3,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_72])).

cnf(c_0_87,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X5,X6,X6,X7) = k5_enumset1(X2,X1,X3,X4,X6,X7,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_78]),c_0_62]),c_0_64])).

cnf(c_0_88,plain,
    ( k7_enumset1(X1,X1,X2,X1,X3,X4,X5,X6,X7) = k5_enumset1(X2,X1,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_79]),c_0_62]),c_0_69])).

cnf(c_0_89,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X7,X8) = k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_49,c_0_60])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X9,X8),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(spm,[status(thm)],[c_0_49,c_0_67])).

cnf(c_0_91,plain,
    ( k5_enumset1(X1,X1,X2,X1,X3,X4,X5) = k5_enumset1(X2,X2,X2,X1,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_70]),c_0_60]),c_0_58]),c_0_58])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_93,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k5_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_24]),c_0_24]),c_0_24]),c_0_34]),c_0_34]),c_0_34]),c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_85]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_95,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X7,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_86]),c_0_62]),c_0_64]),c_0_87])).

cnf(c_0_96,plain,
    ( k7_enumset1(X1,X2,X1,X3,X4,X5,X6,X6,X7) = k5_enumset1(X2,X1,X3,X4,X5,X6,X7) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_97,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X7) = k7_enumset1(X1,X2,X3,X4,X5,X6,X8,X8,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_70]),c_0_60])).

cnf(c_0_98,plain,
    ( k7_enumset1(X1,X2,X1,X3,X4,X5,X6,X7,X6) = k5_enumset1(X2,X1,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_60]),c_0_58])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X4)) = k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_24]),c_0_24]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_100,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) = k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_83]),c_0_24]),c_0_24]),c_0_24]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_101,negated_conjecture,
    ( k5_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0)) != k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X7,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_103,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)),k5_enumset1(X4,X4,X4,X4,X4,X4,X5)) = k5_enumset1(k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X5),k4_tarski(k4_tarski(X2,X3),X4),k4_tarski(k4_tarski(X2,X3),X5)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_103])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:30:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.59  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.59  #
% 0.20/0.59  # Preprocessing time       : 0.027 s
% 0.20/0.59  # Presaturation interreduction done
% 0.20/0.59  
% 0.20/0.59  # Proof found!
% 0.20/0.59  # SZS status Theorem
% 0.20/0.59  # SZS output start CNFRefutation
% 0.20/0.59  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.59  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.59  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 0.20/0.59  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.59  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.59  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.59  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.59  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.59  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.20/0.59  fof(t133_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_enumset1)).
% 0.20/0.59  fof(t132_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_enumset1)).
% 0.20/0.59  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.59  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 0.20/0.59  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 0.20/0.59  fof(t44_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 0.20/0.59  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.59  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.59  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.59  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.20/0.59  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.20/0.59  fof(c_0_20, plain, ![X80, X81]:k3_tarski(k2_tarski(X80,X81))=k2_xboole_0(X80,X81), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.59  fof(c_0_21, plain, ![X60, X61]:k1_enumset1(X60,X60,X61)=k2_tarski(X60,X61), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.59  fof(c_0_22, plain, ![X44, X45, X46, X47, X48, X49, X50]:k5_enumset1(X44,X45,X46,X47,X48,X49,X50)=k2_xboole_0(k3_enumset1(X44,X45,X46,X47,X48),k2_tarski(X49,X50)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.20/0.59  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.59  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.59  fof(c_0_25, plain, ![X62, X63, X64]:k2_enumset1(X62,X62,X63,X64)=k1_enumset1(X62,X63,X64), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.59  fof(c_0_26, plain, ![X65, X66, X67, X68]:k3_enumset1(X65,X65,X66,X67,X68)=k2_enumset1(X65,X66,X67,X68), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.59  fof(c_0_27, plain, ![X69, X70, X71, X72, X73]:k4_enumset1(X69,X69,X70,X71,X72,X73)=k3_enumset1(X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.59  fof(c_0_28, plain, ![X74, X75, X76, X77, X78, X79]:k5_enumset1(X74,X74,X75,X76,X77,X78,X79)=k4_enumset1(X74,X75,X76,X77,X78,X79), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.59  fof(c_0_29, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(X10,k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.59  fof(c_0_30, plain, ![X51, X52, X53, X54, X55, X56, X57, X58]:k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)=k2_xboole_0(k4_enumset1(X51,X52,X53,X54,X55,X56),k2_tarski(X57,X58)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.20/0.59  fof(c_0_31, plain, ![X35, X36, X37, X38, X39, X40, X41, X42, X43]:k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)=k2_xboole_0(k5_enumset1(X35,X36,X37,X38,X39,X40,X41),k2_tarski(X42,X43)), inference(variable_rename,[status(thm)],[t133_enumset1])).
% 0.20/0.59  cnf(c_0_32, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.59  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.59  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.59  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.59  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.59  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.59  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.59  cnf(c_0_39, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.59  cnf(c_0_40, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.59  cnf(c_0_41, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_24]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_42, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.20/0.59  cnf(c_0_43, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_24]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_44, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_24]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.20/0.59  fof(c_0_45, plain, ![X26, X27, X28, X29, X30, X31, X32, X33, X34]:k7_enumset1(X26,X27,X28,X29,X30,X31,X32,X33,X34)=k2_xboole_0(k4_enumset1(X26,X27,X28,X29,X30,X31),k1_enumset1(X32,X33,X34)), inference(variable_rename,[status(thm)],[t132_enumset1])).
% 0.20/0.59  fof(c_0_46, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_tarski(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.59  cnf(c_0_47, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X1,X1,X1,X2,X3,X4,X5)))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.59  cnf(c_0_48, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X8),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_43, c_0_42])).
% 0.20/0.59  cnf(c_0_49, plain, (k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X9),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_44, c_0_42])).
% 0.20/0.59  fof(c_0_50, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22]:k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 0.20/0.59  cnf(c_0_51, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.59  cnf(c_0_52, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.59  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.59  cnf(c_0_54, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.59  cnf(c_0_55, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.59  cnf(c_0_56, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_57, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k5_enumset1(X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_24]), c_0_24]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_58, plain, (k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.59  cnf(c_0_59, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_33]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_60, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_56, c_0_42])).
% 0.20/0.59  cnf(c_0_61, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X2,X2,X2,X2,X1,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_57]), c_0_49]), c_0_58]), c_0_58])).
% 0.20/0.59  cnf(c_0_62, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_59, c_0_42])).
% 0.20/0.59  fof(c_0_63, plain, ![X23, X24, X25]:k1_enumset1(X23,X24,X25)=k1_enumset1(X24,X25,X23), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.20/0.59  cnf(c_0_64, plain, (k7_enumset1(X1,X2,X3,X4,X5,X5,X5,X6,X7)=k5_enumset1(X2,X1,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_58])).
% 0.20/0.59  cnf(c_0_65, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.59  cnf(c_0_66, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_enumset1(X1,X2,X3,X3,X3,X4,X5)), inference(spm,[status(thm)],[c_0_58, c_0_64])).
% 0.20/0.59  cnf(c_0_67, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k5_enumset1(X2,X2,X2,X2,X2,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_68, plain, (k5_enumset1(X1,X1,X2,X2,X2,X3,X4)=k5_enumset1(X2,X2,X2,X2,X1,X3,X4)), inference(spm,[status(thm)],[c_0_61, c_0_66])).
% 0.20/0.59  cnf(c_0_69, plain, (k7_enumset1(X1,X2,X2,X2,X3,X4,X5,X6,X7)=k5_enumset1(X2,X1,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_66]), c_0_62]), c_0_64])).
% 0.20/0.59  cnf(c_0_70, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k5_enumset1(X2,X2,X2,X2,X2,X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_57])).
% 0.20/0.59  fof(c_0_71, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5))), inference(assume_negation,[status(cth)],[t44_mcart_1])).
% 0.20/0.59  cnf(c_0_72, plain, (k5_enumset1(X1,X2,X3,X4,X5,X5,X6)=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_68]), c_0_60]), c_0_69]), c_0_58])).
% 0.20/0.59  cnf(c_0_73, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X2)=k5_enumset1(X1,X1,X1,X1,X1,X2,X1)), inference(spm,[status(thm)],[c_0_67, c_0_70])).
% 0.20/0.59  fof(c_0_74, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).
% 0.20/0.59  fof(c_0_75, plain, ![X59]:k2_tarski(X59,X59)=k1_tarski(X59), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.59  fof(c_0_76, plain, ![X89, X90, X91]:k3_mcart_1(X89,X90,X91)=k4_tarski(k4_tarski(X89,X90),X91), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.59  fof(c_0_77, plain, ![X92, X93, X94]:k3_zfmisc_1(X92,X93,X94)=k2_zfmisc_1(k2_zfmisc_1(X92,X93),X94), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.59  cnf(c_0_78, plain, (k5_enumset1(X1,X1,X1,X1,X2,X2,X3)=k5_enumset1(X2,X2,X2,X2,X2,X3,X1)), inference(spm,[status(thm)],[c_0_67, c_0_72])).
% 0.20/0.59  cnf(c_0_79, plain, (k5_enumset1(X1,X1,X1,X1,X2,X2,X2)=k5_enumset1(X1,X1,X1,X1,X1,X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_72])).
% 0.20/0.59  fof(c_0_80, plain, ![X82, X83, X84, X85]:k2_zfmisc_1(k2_tarski(X82,X83),k2_tarski(X84,X85))=k2_enumset1(k4_tarski(X82,X84),k4_tarski(X82,X85),k4_tarski(X83,X84),k4_tarski(X83,X85)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 0.20/0.59  fof(c_0_81, plain, ![X86, X87, X88]:(k2_zfmisc_1(k1_tarski(X86),k2_tarski(X87,X88))=k2_tarski(k4_tarski(X86,X87),k4_tarski(X86,X88))&k2_zfmisc_1(k2_tarski(X86,X87),k1_tarski(X88))=k2_tarski(k4_tarski(X86,X88),k4_tarski(X87,X88))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.20/0.59  cnf(c_0_82, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.59  cnf(c_0_83, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.59  cnf(c_0_84, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.59  cnf(c_0_85, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.59  cnf(c_0_86, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k5_enumset1(X2,X2,X2,X2,X3,X3,X1)), inference(spm,[status(thm)],[c_0_67, c_0_72])).
% 0.20/0.59  cnf(c_0_87, plain, (k7_enumset1(X1,X2,X3,X4,X5,X5,X6,X6,X7)=k5_enumset1(X2,X1,X3,X4,X6,X7,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_78]), c_0_62]), c_0_64])).
% 0.20/0.59  cnf(c_0_88, plain, (k7_enumset1(X1,X1,X2,X1,X3,X4,X5,X6,X7)=k5_enumset1(X2,X1,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_79]), c_0_62]), c_0_69])).
% 0.20/0.59  cnf(c_0_89, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X7,X8)=k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_49, c_0_60])).
% 0.20/0.59  cnf(c_0_90, plain, (k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X9,X8),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(spm,[status(thm)],[c_0_49, c_0_67])).
% 0.20/0.59  cnf(c_0_91, plain, (k5_enumset1(X1,X1,X2,X1,X3,X4,X5)=k5_enumset1(X2,X2,X2,X1,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_70]), c_0_60]), c_0_58]), c_0_58])).
% 0.20/0.59  cnf(c_0_92, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.59  cnf(c_0_93, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.59  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k5_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_24]), c_0_24]), c_0_24]), c_0_34]), c_0_34]), c_0_34]), c_0_84]), c_0_84]), c_0_84]), c_0_84]), c_0_85]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_95, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X7,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_86]), c_0_62]), c_0_64]), c_0_87])).
% 0.20/0.59  cnf(c_0_96, plain, (k7_enumset1(X1,X2,X1,X3,X4,X5,X6,X6,X7)=k5_enumset1(X2,X1,X3,X4,X5,X6,X7)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.59  cnf(c_0_97, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X7)=k7_enumset1(X1,X2,X3,X4,X5,X6,X8,X8,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_70]), c_0_60])).
% 0.20/0.59  cnf(c_0_98, plain, (k7_enumset1(X1,X2,X1,X3,X4,X5,X6,X7,X6)=k5_enumset1(X2,X1,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_60]), c_0_58])).
% 0.20/0.59  cnf(c_0_99, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X4))=k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_24]), c_0_24]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_100, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3))=k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_83]), c_0_24]), c_0_24]), c_0_24]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.20/0.59  cnf(c_0_101, negated_conjecture, (k5_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0))!=k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.20/0.59  cnf(c_0_102, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X7,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.20/0.59  cnf(c_0_103, plain, (k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)),k5_enumset1(X4,X4,X4,X4,X4,X4,X5))=k5_enumset1(k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X5),k4_tarski(k4_tarski(X2,X3),X4),k4_tarski(k4_tarski(X2,X3),X5))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.20/0.59  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_103])]), ['proof']).
% 0.20/0.59  # SZS output end CNFRefutation
% 0.20/0.59  # Proof object total steps             : 105
% 0.20/0.59  # Proof object clause steps            : 64
% 0.20/0.59  # Proof object formula steps           : 41
% 0.20/0.59  # Proof object conjectures             : 7
% 0.20/0.59  # Proof object clause conjectures      : 4
% 0.20/0.59  # Proof object formula conjectures     : 3
% 0.20/0.59  # Proof object initial clauses used    : 20
% 0.20/0.59  # Proof object initial formulas used   : 20
% 0.20/0.59  # Proof object generating inferences   : 23
% 0.20/0.59  # Proof object simplifying inferences  : 189
% 0.20/0.59  # Training examples: 0 positive, 0 negative
% 0.20/0.59  # Parsed axioms                        : 20
% 0.20/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.59  # Initial clauses                      : 21
% 0.20/0.59  # Removed in clause preprocessing      : 9
% 0.20/0.59  # Initial clauses in saturation        : 12
% 0.20/0.59  # Processed clauses                    : 1144
% 0.20/0.59  # ...of these trivial                  : 155
% 0.20/0.59  # ...subsumed                          : 732
% 0.20/0.59  # ...remaining for further processing  : 257
% 0.20/0.59  # Other redundant clauses eliminated   : 0
% 0.20/0.59  # Clauses deleted for lack of memory   : 0
% 0.20/0.59  # Backward-subsumed                    : 13
% 0.20/0.59  # Backward-rewritten                   : 7
% 0.20/0.59  # Generated clauses                    : 42326
% 0.20/0.59  # ...of the previous two non-trivial   : 25134
% 0.20/0.59  # Contextual simplify-reflections      : 0
% 0.20/0.59  # Paramodulations                      : 42326
% 0.20/0.59  # Factorizations                       : 0
% 0.20/0.59  # Equation resolutions                 : 0
% 0.20/0.59  # Propositional unsat checks           : 0
% 0.20/0.59  #    Propositional check models        : 0
% 0.20/0.59  #    Propositional check unsatisfiable : 0
% 0.20/0.59  #    Propositional clauses             : 0
% 0.20/0.59  #    Propositional clauses after purity: 0
% 0.20/0.59  #    Propositional unsat core size     : 0
% 0.20/0.59  #    Propositional preprocessing time  : 0.000
% 0.20/0.59  #    Propositional encoding time       : 0.000
% 0.20/0.59  #    Propositional solver time         : 0.000
% 0.20/0.59  #    Success case prop preproc time    : 0.000
% 0.20/0.59  #    Success case prop encoding time   : 0.000
% 0.20/0.59  #    Success case prop solver time     : 0.000
% 0.20/0.59  # Current number of processed clauses  : 225
% 0.20/0.59  #    Positive orientable unit clauses  : 126
% 0.20/0.59  #    Positive unorientable unit clauses: 99
% 0.20/0.59  #    Negative unit clauses             : 0
% 0.20/0.59  #    Non-unit-clauses                  : 0
% 0.20/0.59  # Current number of unprocessed clauses: 23913
% 0.20/0.59  # ...number of literals in the above   : 23913
% 0.20/0.59  # Current number of archived formulas  : 0
% 0.20/0.59  # Current number of archived clauses   : 41
% 0.20/0.59  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.59  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.59  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.59  # Unit Clause-clause subsumption calls : 4869
% 0.20/0.59  # Rewrite failures with RHS unbound    : 0
% 0.20/0.59  # BW rewrite match attempts            : 21095
% 0.20/0.59  # BW rewrite match successes           : 7987
% 0.20/0.59  # Condensation attempts                : 0
% 0.20/0.59  # Condensation successes               : 0
% 0.20/0.59  # Termbank termtop insertions          : 364339
% 0.20/0.59  
% 0.20/0.59  # -------------------------------------------------
% 0.20/0.59  # User time                : 0.246 s
% 0.20/0.59  # System time              : 0.013 s
% 0.20/0.59  # Total time               : 0.259 s
% 0.20/0.59  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
