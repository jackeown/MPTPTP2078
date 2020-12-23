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
% DateTime   : Thu Dec  3 10:37:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 (4115 expanded)
%              Number of clauses        :   47 (1495 expanded)
%              Number of leaves         :   19 (1304 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 (4208 expanded)
%              Number of equality atoms :  122 (4184 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(t132_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(t133_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_19,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44,X45,X46] : k7_enumset1(X38,X39,X40,X41,X42,X43,X44,X45,X46) = k2_xboole_0(k4_enumset1(X38,X39,X40,X41,X42,X43),k1_enumset1(X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[t132_enumset1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X76,X77,X78] : k2_enumset1(X76,X76,X77,X78) = k1_enumset1(X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X79,X80,X81,X82] : k3_enumset1(X79,X79,X80,X81,X82) = k2_enumset1(X79,X80,X81,X82) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X83,X84,X85,X86,X87] : k4_enumset1(X83,X83,X84,X85,X86,X87) = k3_enumset1(X83,X84,X85,X86,X87) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X88,X89,X90,X91,X92,X93] : k5_enumset1(X88,X88,X89,X90,X91,X92,X93) = k4_enumset1(X88,X89,X90,X91,X92,X93) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X94,X95,X96,X97,X98,X99,X100] : k6_enumset1(X94,X94,X95,X96,X97,X98,X99,X100) = k5_enumset1(X94,X95,X96,X97,X98,X99,X100) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_31,plain,(
    ! [X73] : k2_tarski(X73,X73) = k1_tarski(X73) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X74,X75] : k1_enumset1(X74,X74,X75) = k2_tarski(X74,X75) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_33,plain,(
    ! [X65,X66,X67,X68,X69,X70,X71,X72] : k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) = k2_xboole_0(k5_enumset1(X65,X66,X67,X68,X69,X70,X71),k1_tarski(X72)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_34,plain,(
    ! [X56,X57,X58,X59,X60,X61,X62,X63,X64] : k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) = k2_xboole_0(k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63),k1_tarski(X64)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_35,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_45,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_46,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_49,plain,(
    ! [X34,X35,X36,X37] : k2_enumset1(X34,X35,X36,X37) = k2_enumset1(X37,X36,X35,X34) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_50,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54,X55] : k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55) = k2_xboole_0(k5_enumset1(X47,X48,X49,X50,X51,X52,X53),k2_tarski(X54,X55)) ),
    inference(variable_rename,[status(thm)],[t133_enumset1])).

cnf(c_0_51,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_43]),c_0_44]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_56,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_43]),c_0_44]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_57,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_59,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X16
        | X20 = X17
        | X20 = X18
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( X21 != X16
        | r2_hidden(X21,X19)
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( esk1_4(X22,X23,X24,X25) != X22
        | ~ r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | X25 = k1_enumset1(X22,X23,X24) )
      & ( esk1_4(X22,X23,X24,X25) != X23
        | ~ r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | X25 = k1_enumset1(X22,X23,X24) )
      & ( esk1_4(X22,X23,X24,X25) != X24
        | ~ r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | X25 = k1_enumset1(X22,X23,X24) )
      & ( r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | esk1_4(X22,X23,X24,X25) = X22
        | esk1_4(X22,X23,X24,X25) = X23
        | esk1_4(X22,X23,X24,X25) = X24
        | X25 = k1_enumset1(X22,X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_60,negated_conjecture,
    ( k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk3_0) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_61,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_63,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_44]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_61]),c_0_62]),c_0_65])).

fof(c_0_70,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X27
        | X28 != k1_tarski(X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k1_tarski(X27) )
      & ( ~ r2_hidden(esk2_2(X31,X32),X32)
        | esk2_2(X31,X32) != X31
        | X32 = k1_tarski(X31) )
      & ( r2_hidden(esk2_2(X31,X32),X32)
        | esk2_2(X31,X32) = X31
        | X32 = k1_tarski(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_68]),c_0_53]),c_0_54]),c_0_61]),c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1,X1,X1) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_69]),c_0_51]),c_0_61]),c_0_61])).

cnf(c_0_74,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X4) ),
    inference(spm,[status(thm)],[c_0_71,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0,X1) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_72]),c_0_51]),c_0_61]),c_0_61]),c_0_73])).

cnf(c_0_77,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_43]),c_0_44]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_80,negated_conjecture,
    ( X1 = esk4_0
    | X2 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0,esk4_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_61]),c_0_62]),c_0_65])).

cnf(c_0_84,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,esk4_0) != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_76]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:48:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.39  # and selection function SelectNegativeLiterals.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.39  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 0.20/0.39  fof(t132_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 0.20/0.39  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 0.20/0.39  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.39  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.20/0.39  fof(t133_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_enumset1)).
% 0.20/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.39  fof(c_0_19, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(X14,k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.39  fof(c_0_20, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.39  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 0.20/0.39  fof(c_0_22, plain, ![X38, X39, X40, X41, X42, X43, X44, X45, X46]:k7_enumset1(X38,X39,X40,X41,X42,X43,X44,X45,X46)=k2_xboole_0(k4_enumset1(X38,X39,X40,X41,X42,X43),k1_enumset1(X44,X45,X46)), inference(variable_rename,[status(thm)],[t132_enumset1])).
% 0.20/0.39  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_25, plain, ![X76, X77, X78]:k2_enumset1(X76,X76,X77,X78)=k1_enumset1(X76,X77,X78), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_26, plain, ![X79, X80, X81, X82]:k3_enumset1(X79,X79,X80,X81,X82)=k2_enumset1(X79,X80,X81,X82), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.39  fof(c_0_27, plain, ![X83, X84, X85, X86, X87]:k4_enumset1(X83,X83,X84,X85,X86,X87)=k3_enumset1(X83,X84,X85,X86,X87), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.39  fof(c_0_28, plain, ![X88, X89, X90, X91, X92, X93]:k5_enumset1(X88,X88,X89,X90,X91,X92,X93)=k4_enumset1(X88,X89,X90,X91,X92,X93), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.39  fof(c_0_29, plain, ![X94, X95, X96, X97, X98, X99, X100]:k6_enumset1(X94,X94,X95,X96,X97,X98,X99,X100)=k5_enumset1(X94,X95,X96,X97,X98,X99,X100), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.39  fof(c_0_30, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.39  fof(c_0_31, plain, ![X73]:k2_tarski(X73,X73)=k1_tarski(X73), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  fof(c_0_32, plain, ![X74, X75]:k1_enumset1(X74,X74,X75)=k2_tarski(X74,X75), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_33, plain, ![X65, X66, X67, X68, X69, X70, X71, X72]:k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)=k2_xboole_0(k5_enumset1(X65,X66,X67,X68,X69,X70,X71),k1_tarski(X72)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.20/0.39  fof(c_0_34, plain, ![X56, X57, X58, X59, X60, X61, X62, X63, X64]:k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)=k2_xboole_0(k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63),k1_tarski(X64)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.20/0.39  cnf(c_0_35, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.39  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.39  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  fof(c_0_45, plain, ![X13]:k5_xboole_0(X13,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.39  fof(c_0_46, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.39  cnf(c_0_47, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_48, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  fof(c_0_49, plain, ![X34, X35, X36, X37]:k2_enumset1(X34,X35,X36,X37)=k2_enumset1(X37,X36,X35,X34), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.20/0.39  fof(c_0_50, plain, ![X47, X48, X49, X50, X51, X52, X53, X54, X55]:k7_enumset1(X47,X48,X49,X50,X51,X52,X53,X54,X55)=k2_xboole_0(k5_enumset1(X47,X48,X49,X50,X51,X52,X53),k2_tarski(X54,X55)), inference(variable_rename,[status(thm)],[t133_enumset1])).
% 0.20/0.39  cnf(c_0_51, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X9),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41])).
% 0.20/0.39  cnf(c_0_53, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_55, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_43]), c_0_44]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.20/0.39  cnf(c_0_56, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_43]), c_0_44]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.20/0.39  cnf(c_0_57, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  cnf(c_0_58, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  fof(c_0_59, plain, ![X16, X17, X18, X19, X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X20,X19)|(X20=X16|X20=X17|X20=X18)|X19!=k1_enumset1(X16,X17,X18))&(((X21!=X16|r2_hidden(X21,X19)|X19!=k1_enumset1(X16,X17,X18))&(X21!=X17|r2_hidden(X21,X19)|X19!=k1_enumset1(X16,X17,X18)))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_enumset1(X16,X17,X18))))&((((esk1_4(X22,X23,X24,X25)!=X22|~r2_hidden(esk1_4(X22,X23,X24,X25),X25)|X25=k1_enumset1(X22,X23,X24))&(esk1_4(X22,X23,X24,X25)!=X23|~r2_hidden(esk1_4(X22,X23,X24,X25),X25)|X25=k1_enumset1(X22,X23,X24)))&(esk1_4(X22,X23,X24,X25)!=X24|~r2_hidden(esk1_4(X22,X23,X24,X25),X25)|X25=k1_enumset1(X22,X23,X24)))&(r2_hidden(esk1_4(X22,X23,X24,X25),X25)|(esk1_4(X22,X23,X24,X25)=X22|esk1_4(X22,X23,X24,X25)=X23|esk1_4(X22,X23,X24,X25)=X24)|X25=k1_enumset1(X22,X23,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk3_0)=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.39  cnf(c_0_61, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.39  cnf(c_0_62, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.20/0.39  cnf(c_0_63, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_44]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.20/0.39  cnf(c_0_64, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0)=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.39  cnf(c_0_67, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_52, c_0_65])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_61]), c_0_62]), c_0_65])).
% 0.20/0.39  fof(c_0_70, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X29,X28)|X29=X27|X28!=k1_tarski(X27))&(X30!=X27|r2_hidden(X30,X28)|X28!=k1_tarski(X27)))&((~r2_hidden(esk2_2(X31,X32),X32)|esk2_2(X31,X32)!=X31|X32=k1_tarski(X31))&(r2_hidden(esk2_2(X31,X32),X32)|esk2_2(X31,X32)=X31|X32=k1_tarski(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_71, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_68]), c_0_53]), c_0_54]), c_0_61]), c_0_62])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1,X1,X1)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_69]), c_0_51]), c_0_61]), c_0_61])).
% 0.20/0.39  cnf(c_0_74, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.39  cnf(c_0_75, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X4)), inference(spm,[status(thm)],[c_0_71, c_0_62])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0,X1)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_72]), c_0_51]), c_0_61]), c_0_61]), c_0_73])).
% 0.20/0.39  cnf(c_0_77, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_43]), c_0_44]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (r2_hidden(esk3_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0)=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (X1=esk4_0|X2!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_77, c_0_65])).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,esk4_0))), inference(er,[status(thm)],[c_0_78])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk4_0,esk4_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_61]), c_0_62]), c_0_65])).
% 0.20/0.39  cnf(c_0_84, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk3_0,esk4_0)!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_76]), c_0_84]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 86
% 0.20/0.39  # Proof object clause steps            : 47
% 0.20/0.39  # Proof object formula steps           : 39
% 0.20/0.39  # Proof object conjectures             : 21
% 0.20/0.39  # Proof object clause conjectures      : 18
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 20
% 0.20/0.39  # Proof object initial formulas used   : 19
% 0.20/0.39  # Proof object generating inferences   : 11
% 0.20/0.39  # Proof object simplifying inferences  : 130
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 19
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 30
% 0.20/0.39  # Removed in clause preprocessing      : 9
% 0.20/0.39  # Initial clauses in saturation        : 21
% 0.20/0.39  # Processed clauses                    : 91
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 36
% 0.20/0.39  # ...remaining for further processing  : 53
% 0.20/0.39  # Other redundant clauses eliminated   : 82
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 10
% 0.20/0.39  # Generated clauses                    : 887
% 0.20/0.39  # ...of the previous two non-trivial   : 786
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 785
% 0.20/0.39  # Factorizations                       : 8
% 0.20/0.39  # Equation resolutions                 : 94
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 39
% 0.20/0.39  #    Positive orientable unit clauses  : 12
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 24
% 0.20/0.39  # Current number of unprocessed clauses: 711
% 0.20/0.39  # ...number of literals in the above   : 3732
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 19
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 284
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 252
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 36
% 0.20/0.39  # Unit Clause-clause subsumption calls : 1
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 63
% 0.20/0.39  # BW rewrite match successes           : 17
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 16079
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.057 s
% 0.20/0.39  # System time              : 0.001 s
% 0.20/0.39  # Total time               : 0.058 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
