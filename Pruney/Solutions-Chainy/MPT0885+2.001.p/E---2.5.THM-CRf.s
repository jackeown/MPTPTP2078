%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:47 EST 2020

% Result     : Theorem 0.94s
% Output     : CNFRefutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :  105 (5527 expanded)
%              Number of clauses        :   60 (2074 expanded)
%              Number of leaves         :   22 (1726 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 (5529 expanded)
%              Number of equality atoms :  106 (5528 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(t133_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(t100_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(t132_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(t45_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_22,plain,(
    ! [X97,X98] : k3_tarski(k2_tarski(X97,X98)) = k2_xboole_0(X97,X98) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X77,X78] : k1_enumset1(X77,X77,X78) = k2_tarski(X77,X78) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59] : k5_enumset1(X53,X54,X55,X56,X57,X58,X59) = k2_xboole_0(k1_tarski(X53),k4_enumset1(X54,X55,X56,X57,X58,X59)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_25,plain,(
    ! [X76] : k2_tarski(X76,X76) = k1_tarski(X76) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_26,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X79,X80,X81] : k2_enumset1(X79,X79,X80,X81) = k1_enumset1(X79,X80,X81) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X82,X83,X84,X85] : k3_enumset1(X82,X82,X83,X84,X85) = k2_enumset1(X82,X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X86,X87,X88,X89,X90] : k4_enumset1(X86,X86,X87,X88,X89,X90) = k3_enumset1(X86,X87,X88,X89,X90) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X91,X92,X93,X94,X95,X96] : k5_enumset1(X91,X91,X92,X93,X94,X95,X96) = k4_enumset1(X91,X92,X93,X94,X95,X96) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_33,plain,(
    ! [X60,X61,X62,X63,X64,X65,X66,X67] : k6_enumset1(X60,X61,X62,X63,X64,X65,X66,X67) = k2_xboole_0(k2_tarski(X60,X61),k4_enumset1(X62,X63,X64,X65,X66,X67)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_44,plain,(
    ! [X68,X69,X70,X71,X72,X73,X74,X75] : k6_enumset1(X68,X69,X70,X71,X72,X73,X74,X75) = k2_xboole_0(k4_enumset1(X68,X69,X70,X71,X72,X73),k2_tarski(X74,X75)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

fof(c_0_45,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50,X51,X52] : k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) = k2_xboole_0(k5_enumset1(X44,X45,X46,X47,X48,X49,X50),k2_tarski(X51,X52)) ),
    inference(variable_rename,[status(thm)],[t133_enumset1])).

fof(c_0_46,plain,(
    ! [X23,X24,X25] : k1_enumset1(X23,X24,X25) = k1_enumset1(X24,X25,X23) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X3,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_27]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_48,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X4,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_27]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33,X34] : k7_enumset1(X26,X27,X28,X29,X30,X31,X32,X33,X34) = k2_xboole_0(k3_enumset1(X26,X27,X28,X29,X30),k2_enumset1(X31,X32,X33,X34)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

cnf(c_0_54,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_57,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_27]),c_0_27]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_27]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_59,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_27]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

fof(c_0_60,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42,X43] : k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43) = k2_xboole_0(k4_enumset1(X35,X36,X37,X38,X39,X40),k1_enumset1(X41,X42,X43)) ),
    inference(variable_rename,[status(thm)],[t132_enumset1])).

cnf(c_0_61,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X2,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k6_enumset1(X1,X2,X3,X3,X3,X3,X3,X4) = k6_enumset1(X1,X2,X4,X4,X4,X4,X4,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_56])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X8),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X9),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_59,c_0_48])).

fof(c_0_67,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22] : k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

cnf(c_0_68,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_36]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_70,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_57])).

cnf(c_0_71,plain,
    ( k5_enumset1(X1,X2,X2,X2,X2,X2,X3) = k5_enumset1(X1,X3,X3,X3,X3,X3,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_63])).

cnf(c_0_72,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_74,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t45_mcart_1])).

cnf(c_0_75,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X2,X3,X4,X5))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_69,c_0_48])).

cnf(c_0_77,plain,
    ( k5_enumset1(X1,X2,X2,X2,X2,X2,X1) = k5_enumset1(X2,X2,X2,X2,X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(spm,[status(thm)],[c_0_63,c_0_72])).

cnf(c_0_79,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_36]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_48])).

fof(c_0_81,plain,(
    ! [X99,X100,X101,X102] : k2_zfmisc_1(k2_tarski(X99,X100),k2_tarski(X101,X102)) = k2_enumset1(k4_tarski(X99,X101),k4_tarski(X99,X102),k4_tarski(X100,X101),k4_tarski(X100,X102)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

fof(c_0_82,plain,(
    ! [X103,X104,X105] :
      ( k2_zfmisc_1(k1_tarski(X103),k2_tarski(X104,X105)) = k2_tarski(k4_tarski(X103,X104),k4_tarski(X103,X105))
      & k2_zfmisc_1(k2_tarski(X103,X104),k1_tarski(X105)) = k2_tarski(k4_tarski(X103,X105),k4_tarski(X104,X105)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_83,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).

fof(c_0_84,plain,(
    ! [X106,X107,X108] : k3_mcart_1(X106,X107,X108) = k4_tarski(k4_tarski(X106,X107),X108) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_85,plain,(
    ! [X109,X110,X111] : k3_zfmisc_1(X109,X110,X111) = k2_zfmisc_1(k2_zfmisc_1(X109,X110),X111) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_75,c_0_48])).

cnf(c_0_87,plain,
    ( k5_enumset1(X1,X2,X2,X2,X3,X4,X5) = k5_enumset1(X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_56]),c_0_63]),c_0_78])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X2,X3,X4))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_79,c_0_48])).

cnf(c_0_89,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X7,X8,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_56]),c_0_66])).

cnf(c_0_90,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_91,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X5,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_78])).

cnf(c_0_96,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X2,X1,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_56])).

cnf(c_0_97,plain,
    ( k6_enumset1(X1,X2,X3,X3,X4,X5,X6,X7) = k5_enumset1(X3,X4,X5,X6,X7,X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_89])).

cnf(c_0_98,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X4)) = k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_27]),c_0_27]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_35]),c_0_27]),c_0_27]),c_0_27]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k5_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_35]),c_0_27]),c_0_27]),c_0_27]),c_0_37]),c_0_37]),c_0_37]),c_0_93]),c_0_93]),c_0_93]),c_0_93]),c_0_94]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_101,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X7,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_62]),c_0_88]),c_0_95]),c_0_95])).

cnf(c_0_102,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X7,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_97])).

cnf(c_0_103,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)),k5_enumset1(X4,X4,X4,X4,X4,X4,X5)) = k5_enumset1(k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X5),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X5)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_103])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.94/1.11  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.94/1.11  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.94/1.11  #
% 0.94/1.11  # Preprocessing time       : 0.027 s
% 0.94/1.11  # Presaturation interreduction done
% 0.94/1.11  
% 0.94/1.11  # Proof found!
% 0.94/1.11  # SZS status Theorem
% 0.94/1.11  # SZS output start CNFRefutation
% 0.94/1.11  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.94/1.11  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.94/1.11  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 0.94/1.11  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.94/1.11  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.94/1.11  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.94/1.11  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.94/1.11  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.94/1.11  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.94/1.11  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 0.94/1.11  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.94/1.11  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 0.94/1.11  fof(t133_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_enumset1)).
% 0.94/1.11  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 0.94/1.11  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 0.94/1.11  fof(t132_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 0.94/1.11  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 0.94/1.11  fof(t45_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_mcart_1)).
% 0.94/1.11  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.94/1.11  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.94/1.11  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.94/1.11  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.94/1.11  fof(c_0_22, plain, ![X97, X98]:k3_tarski(k2_tarski(X97,X98))=k2_xboole_0(X97,X98), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.94/1.11  fof(c_0_23, plain, ![X77, X78]:k1_enumset1(X77,X77,X78)=k2_tarski(X77,X78), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.94/1.11  fof(c_0_24, plain, ![X53, X54, X55, X56, X57, X58, X59]:k5_enumset1(X53,X54,X55,X56,X57,X58,X59)=k2_xboole_0(k1_tarski(X53),k4_enumset1(X54,X55,X56,X57,X58,X59)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.94/1.11  fof(c_0_25, plain, ![X76]:k2_tarski(X76,X76)=k1_tarski(X76), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.94/1.11  cnf(c_0_26, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.94/1.11  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.94/1.11  fof(c_0_28, plain, ![X79, X80, X81]:k2_enumset1(X79,X79,X80,X81)=k1_enumset1(X79,X80,X81), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.94/1.11  fof(c_0_29, plain, ![X82, X83, X84, X85]:k3_enumset1(X82,X82,X83,X84,X85)=k2_enumset1(X82,X83,X84,X85), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.94/1.11  fof(c_0_30, plain, ![X86, X87, X88, X89, X90]:k4_enumset1(X86,X86,X87,X88,X89,X90)=k3_enumset1(X86,X87,X88,X89,X90), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.94/1.11  fof(c_0_31, plain, ![X91, X92, X93, X94, X95, X96]:k5_enumset1(X91,X91,X92,X93,X94,X95,X96)=k4_enumset1(X91,X92,X93,X94,X95,X96), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.94/1.11  fof(c_0_32, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(X10,k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.94/1.11  fof(c_0_33, plain, ![X60, X61, X62, X63, X64, X65, X66, X67]:k6_enumset1(X60,X61,X62,X63,X64,X65,X66,X67)=k2_xboole_0(k2_tarski(X60,X61),k4_enumset1(X62,X63,X64,X65,X66,X67)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.94/1.11  cnf(c_0_34, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.94/1.11  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.94/1.11  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.94/1.11  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.94/1.11  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.94/1.11  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.94/1.11  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.94/1.11  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.94/1.11  cnf(c_0_42, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.94/1.11  fof(c_0_43, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_tarski(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.94/1.11  fof(c_0_44, plain, ![X68, X69, X70, X71, X72, X73, X74, X75]:k6_enumset1(X68,X69,X70,X71,X72,X73,X74,X75)=k2_xboole_0(k4_enumset1(X68,X69,X70,X71,X72,X73),k2_tarski(X74,X75)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.94/1.11  fof(c_0_45, plain, ![X44, X45, X46, X47, X48, X49, X50, X51, X52]:k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)=k2_xboole_0(k5_enumset1(X44,X45,X46,X47,X48,X49,X50),k2_tarski(X51,X52)), inference(variable_rename,[status(thm)],[t133_enumset1])).
% 0.94/1.11  fof(c_0_46, plain, ![X23, X24, X25]:k1_enumset1(X23,X24,X25)=k1_enumset1(X24,X25,X23), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.94/1.11  cnf(c_0_47, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X3,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_27]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_48, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.94/1.11  cnf(c_0_49, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X4,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_27]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.94/1.11  cnf(c_0_51, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.94/1.11  cnf(c_0_52, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.94/1.11  fof(c_0_53, plain, ![X26, X27, X28, X29, X30, X31, X32, X33, X34]:k7_enumset1(X26,X27,X28,X29,X30,X31,X32,X33,X34)=k2_xboole_0(k3_enumset1(X26,X27,X28,X29,X30),k2_enumset1(X31,X32,X33,X34)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.94/1.11  cnf(c_0_54, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.94/1.11  cnf(c_0_55, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.94/1.11  cnf(c_0_56, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_49, c_0_48])).
% 0.94/1.11  cnf(c_0_57, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k5_enumset1(X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_27]), c_0_27]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_58, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_27]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_59, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_27]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.94/1.11  fof(c_0_60, plain, ![X35, X36, X37, X38, X39, X40, X41, X42, X43]:k7_enumset1(X35,X36,X37,X38,X39,X40,X41,X42,X43)=k2_xboole_0(k4_enumset1(X35,X36,X37,X38,X39,X40),k1_enumset1(X41,X42,X43)), inference(variable_rename,[status(thm)],[t132_enumset1])).
% 0.94/1.11  cnf(c_0_61, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.94/1.11  cnf(c_0_62, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k5_enumset1(X2,X2,X2,X2,X2,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_63, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.94/1.11  cnf(c_0_64, plain, (k6_enumset1(X1,X2,X3,X3,X3,X3,X3,X4)=k6_enumset1(X1,X2,X4,X4,X4,X4,X4,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_56])).
% 0.94/1.11  cnf(c_0_65, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X8),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_58, c_0_48])).
% 0.94/1.11  cnf(c_0_66, plain, (k5_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X9),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_59, c_0_48])).
% 0.94/1.11  fof(c_0_67, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22]:k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 0.94/1.11  cnf(c_0_68, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.94/1.11  cnf(c_0_69, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_36]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_70, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k5_enumset1(X2,X2,X2,X2,X2,X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_57])).
% 0.94/1.11  cnf(c_0_71, plain, (k5_enumset1(X1,X2,X2,X2,X2,X2,X3)=k5_enumset1(X1,X3,X3,X3,X3,X3,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_63])).
% 0.94/1.11  cnf(c_0_72, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.94/1.11  cnf(c_0_73, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.94/1.11  fof(c_0_74, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))), inference(assume_negation,[status(cth)],[t45_mcart_1])).
% 0.94/1.11  cnf(c_0_75, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_76, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X2,X3,X4,X5)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_69, c_0_48])).
% 0.94/1.11  cnf(c_0_77, plain, (k5_enumset1(X1,X2,X2,X2,X2,X2,X1)=k5_enumset1(X2,X2,X2,X2,X2,X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.94/1.11  cnf(c_0_78, plain, (k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(spm,[status(thm)],[c_0_63, c_0_72])).
% 0.94/1.11  cnf(c_0_79, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_36]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_80, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_48])).
% 0.94/1.11  fof(c_0_81, plain, ![X99, X100, X101, X102]:k2_zfmisc_1(k2_tarski(X99,X100),k2_tarski(X101,X102))=k2_enumset1(k4_tarski(X99,X101),k4_tarski(X99,X102),k4_tarski(X100,X101),k4_tarski(X100,X102)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 0.94/1.11  fof(c_0_82, plain, ![X103, X104, X105]:(k2_zfmisc_1(k1_tarski(X103),k2_tarski(X104,X105))=k2_tarski(k4_tarski(X103,X104),k4_tarski(X103,X105))&k2_zfmisc_1(k2_tarski(X103,X104),k1_tarski(X105))=k2_tarski(k4_tarski(X103,X105),k4_tarski(X104,X105))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.94/1.11  fof(c_0_83, negated_conjecture, k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).
% 0.94/1.11  fof(c_0_84, plain, ![X106, X107, X108]:k3_mcart_1(X106,X107,X108)=k4_tarski(k4_tarski(X106,X107),X108), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.94/1.11  fof(c_0_85, plain, ![X109, X110, X111]:k3_zfmisc_1(X109,X110,X111)=k2_zfmisc_1(k2_zfmisc_1(X109,X110),X111), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.94/1.11  cnf(c_0_86, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_75, c_0_48])).
% 0.94/1.11  cnf(c_0_87, plain, (k5_enumset1(X1,X2,X2,X2,X3,X4,X5)=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_56]), c_0_63]), c_0_78])).
% 0.94/1.11  cnf(c_0_88, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_79, c_0_48])).
% 0.94/1.11  cnf(c_0_89, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X7,X8,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_56]), c_0_66])).
% 0.94/1.11  cnf(c_0_90, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.94/1.11  cnf(c_0_91, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.94/1.11  cnf(c_0_92, negated_conjecture, (k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.94/1.11  cnf(c_0_93, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.94/1.11  cnf(c_0_94, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.94/1.11  cnf(c_0_95, plain, (k7_enumset1(X1,X2,X3,X4,X5,X5,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_78])).
% 0.94/1.11  cnf(c_0_96, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X2,X1,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_56])).
% 0.94/1.11  cnf(c_0_97, plain, (k6_enumset1(X1,X2,X3,X3,X4,X5,X6,X7)=k5_enumset1(X3,X4,X5,X6,X7,X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_89])).
% 0.94/1.11  cnf(c_0_98, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X4))=k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_27]), c_0_27]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_99, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3))=k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_35]), c_0_27]), c_0_27]), c_0_27]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_100, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k5_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_35]), c_0_27]), c_0_27]), c_0_27]), c_0_37]), c_0_37]), c_0_37]), c_0_93]), c_0_93]), c_0_93]), c_0_93]), c_0_94]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.94/1.11  cnf(c_0_101, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X7,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_62]), c_0_88]), c_0_95]), c_0_95])).
% 0.94/1.11  cnf(c_0_102, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X7,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_97])).
% 0.94/1.11  cnf(c_0_103, plain, (k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)),k5_enumset1(X4,X4,X4,X4,X4,X4,X5))=k5_enumset1(k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X4),k4_tarski(k4_tarski(X1,X2),X5),k4_tarski(k4_tarski(X1,X3),X4),k4_tarski(k4_tarski(X1,X3),X5))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.94/1.11  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_103])]), ['proof']).
% 0.94/1.11  # SZS output end CNFRefutation
% 0.94/1.11  # Proof object total steps             : 105
% 0.94/1.11  # Proof object clause steps            : 60
% 0.94/1.11  # Proof object formula steps           : 45
% 0.94/1.11  # Proof object conjectures             : 6
% 0.94/1.11  # Proof object clause conjectures      : 3
% 0.94/1.11  # Proof object formula conjectures     : 3
% 0.94/1.11  # Proof object initial clauses used    : 22
% 0.94/1.11  # Proof object initial formulas used   : 22
% 0.94/1.11  # Proof object generating inferences   : 14
% 0.94/1.11  # Proof object simplifying inferences  : 222
% 0.94/1.11  # Training examples: 0 positive, 0 negative
% 0.94/1.11  # Parsed axioms                        : 22
% 0.94/1.11  # Removed by relevancy pruning/SinE    : 0
% 0.94/1.11  # Initial clauses                      : 23
% 0.94/1.11  # Removed in clause preprocessing      : 9
% 0.94/1.11  # Initial clauses in saturation        : 14
% 0.94/1.11  # Processed clauses                    : 2976
% 0.94/1.11  # ...of these trivial                  : 140
% 0.94/1.11  # ...subsumed                          : 2311
% 0.94/1.11  # ...remaining for further processing  : 525
% 0.94/1.11  # Other redundant clauses eliminated   : 0
% 0.94/1.11  # Clauses deleted for lack of memory   : 0
% 0.94/1.11  # Backward-subsumed                    : 25
% 0.94/1.11  # Backward-rewritten                   : 29
% 0.94/1.11  # Generated clauses                    : 147105
% 0.94/1.11  # ...of the previous two non-trivial   : 107521
% 0.94/1.11  # Contextual simplify-reflections      : 0
% 0.94/1.11  # Paramodulations                      : 147105
% 0.94/1.11  # Factorizations                       : 0
% 0.94/1.11  # Equation resolutions                 : 0
% 0.94/1.11  # Propositional unsat checks           : 0
% 0.94/1.11  #    Propositional check models        : 0
% 0.94/1.11  #    Propositional check unsatisfiable : 0
% 0.94/1.11  #    Propositional clauses             : 0
% 0.94/1.11  #    Propositional clauses after purity: 0
% 0.94/1.11  #    Propositional unsat core size     : 0
% 0.94/1.11  #    Propositional preprocessing time  : 0.000
% 0.94/1.11  #    Propositional encoding time       : 0.000
% 0.94/1.11  #    Propositional solver time         : 0.000
% 0.94/1.11  #    Success case prop preproc time    : 0.000
% 0.94/1.11  #    Success case prop encoding time   : 0.000
% 0.94/1.11  #    Success case prop solver time     : 0.000
% 0.94/1.11  # Current number of processed clauses  : 457
% 0.94/1.11  #    Positive orientable unit clauses  : 238
% 0.94/1.11  #    Positive unorientable unit clauses: 219
% 0.94/1.11  #    Negative unit clauses             : 0
% 0.94/1.11  #    Non-unit-clauses                  : 0
% 0.94/1.11  # Current number of unprocessed clauses: 104159
% 0.94/1.11  # ...number of literals in the above   : 104159
% 0.94/1.11  # Current number of archived formulas  : 0
% 0.94/1.11  # Current number of archived clauses   : 77
% 0.94/1.11  # Clause-clause subsumption calls (NU) : 0
% 0.94/1.11  # Rec. Clause-clause subsumption calls : 0
% 0.94/1.11  # Non-unit clause-clause subsumptions  : 0
% 0.94/1.11  # Unit Clause-clause subsumption calls : 23615
% 0.94/1.11  # Rewrite failures with RHS unbound    : 0
% 0.94/1.11  # BW rewrite match attempts            : 87837
% 0.94/1.11  # BW rewrite match successes           : 24014
% 0.94/1.11  # Condensation attempts                : 0
% 0.94/1.11  # Condensation successes               : 0
% 0.94/1.11  # Termbank termtop insertions          : 1008325
% 0.94/1.11  
% 0.94/1.11  # -------------------------------------------------
% 0.94/1.11  # User time                : 0.738 s
% 0.94/1.11  # System time              : 0.030 s
% 0.94/1.11  # Total time               : 0.768 s
% 0.94/1.11  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
