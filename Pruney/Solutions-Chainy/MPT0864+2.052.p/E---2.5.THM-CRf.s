%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:25 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 404 expanded)
%              Number of clauses        :   44 ( 161 expanded)
%              Number of leaves         :   18 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  182 ( 742 expanded)
%              Number of equality atoms :  125 ( 598 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(c_0_18,plain,(
    ! [X79,X80,X81,X82,X83,X84,X85,X86,X87,X88,X89,X90,X91,X92,X93,X94] :
      ( ( ~ r2_hidden(X86,X85)
        | X86 = X79
        | X86 = X80
        | X86 = X81
        | X86 = X82
        | X86 = X83
        | X86 = X84
        | X85 != k4_enumset1(X79,X80,X81,X82,X83,X84) )
      & ( X87 != X79
        | r2_hidden(X87,X85)
        | X85 != k4_enumset1(X79,X80,X81,X82,X83,X84) )
      & ( X87 != X80
        | r2_hidden(X87,X85)
        | X85 != k4_enumset1(X79,X80,X81,X82,X83,X84) )
      & ( X87 != X81
        | r2_hidden(X87,X85)
        | X85 != k4_enumset1(X79,X80,X81,X82,X83,X84) )
      & ( X87 != X82
        | r2_hidden(X87,X85)
        | X85 != k4_enumset1(X79,X80,X81,X82,X83,X84) )
      & ( X87 != X83
        | r2_hidden(X87,X85)
        | X85 != k4_enumset1(X79,X80,X81,X82,X83,X84) )
      & ( X87 != X84
        | r2_hidden(X87,X85)
        | X85 != k4_enumset1(X79,X80,X81,X82,X83,X84) )
      & ( esk2_7(X88,X89,X90,X91,X92,X93,X94) != X88
        | ~ r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)
        | X94 = k4_enumset1(X88,X89,X90,X91,X92,X93) )
      & ( esk2_7(X88,X89,X90,X91,X92,X93,X94) != X89
        | ~ r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)
        | X94 = k4_enumset1(X88,X89,X90,X91,X92,X93) )
      & ( esk2_7(X88,X89,X90,X91,X92,X93,X94) != X90
        | ~ r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)
        | X94 = k4_enumset1(X88,X89,X90,X91,X92,X93) )
      & ( esk2_7(X88,X89,X90,X91,X92,X93,X94) != X91
        | ~ r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)
        | X94 = k4_enumset1(X88,X89,X90,X91,X92,X93) )
      & ( esk2_7(X88,X89,X90,X91,X92,X93,X94) != X92
        | ~ r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)
        | X94 = k4_enumset1(X88,X89,X90,X91,X92,X93) )
      & ( esk2_7(X88,X89,X90,X91,X92,X93,X94) != X93
        | ~ r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)
        | X94 = k4_enumset1(X88,X89,X90,X91,X92,X93) )
      & ( r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)
        | esk2_7(X88,X89,X90,X91,X92,X93,X94) = X88
        | esk2_7(X88,X89,X90,X91,X92,X93,X94) = X89
        | esk2_7(X88,X89,X90,X91,X92,X93,X94) = X90
        | esk2_7(X88,X89,X90,X91,X92,X93,X94) = X91
        | esk2_7(X88,X89,X90,X91,X92,X93,X94) = X92
        | esk2_7(X88,X89,X90,X91,X92,X93,X94) = X93
        | X94 = k4_enumset1(X88,X89,X90,X91,X92,X93) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_19,plain,(
    ! [X54,X55,X56,X57,X58,X59] : k5_enumset1(X54,X54,X55,X56,X57,X58,X59) = k4_enumset1(X54,X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X60,X61,X62,X63,X64,X65,X66] : k6_enumset1(X60,X60,X61,X62,X63,X64,X65,X66) = k5_enumset1(X60,X61,X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X96,X97] :
      ( k1_mcart_1(k4_tarski(X96,X97)) = X96
      & k2_mcart_1(k4_tarski(X96,X97)) = X97 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_26,negated_conjecture,
    ( esk3_0 = k4_tarski(esk4_0,esk5_0)
    & ( esk3_0 = k1_mcart_1(esk3_0)
      | esk3_0 = k2_mcart_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = k4_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X71,X72,X73,X74] :
      ( ( r2_hidden(X71,X73)
        | ~ r2_hidden(k4_tarski(X71,X72),k2_zfmisc_1(X73,X74)) )
      & ( r2_hidden(X72,X74)
        | ~ r2_hidden(k4_tarski(X71,X72),k2_zfmisc_1(X73,X74)) )
      & ( ~ r2_hidden(X71,X73)
        | ~ r2_hidden(X72,X74)
        | r2_hidden(k4_tarski(X71,X72),k2_zfmisc_1(X73,X74)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk3_0)
    | esk3_0 = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k1_mcart_1(esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_35,plain,(
    ! [X69,X70] : k3_tarski(k2_tarski(X69,X70)) = k2_xboole_0(X69,X70) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_36,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k2_mcart_1(esk3_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k2_mcart_1(esk3_0) = esk3_0
    | esk4_0 = esk3_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,plain,(
    ! [X77,X78] : k2_xboole_0(k1_tarski(X77),X78) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_42,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_43,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_46,plain,(
    ! [X45,X46,X47,X48] : k3_enumset1(X45,X45,X46,X47,X48) = k2_enumset1(X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_47,plain,(
    ! [X49,X50,X51,X52,X53] : k4_enumset1(X49,X49,X50,X51,X52,X53) = k3_enumset1(X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_48,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_49,plain,(
    ! [X67,X68] :
      ( ( ~ r1_tarski(k1_tarski(X67),X68)
        | r2_hidden(X67,X68) )
      & ( ~ r2_hidden(X67,X68)
        | r1_tarski(k1_tarski(X67),X68) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1),X8))
    | ~ r2_hidden(X2,X8) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk5_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1),k6_enumset1(X8,X8,X8,X9,X10,X11,X12,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( k4_tarski(esk4_0,esk3_0) = esk3_0
    | esk4_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_51])).

cnf(c_0_62,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_44]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_63,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_23]),c_0_24])).

fof(c_0_64,plain,(
    ! [X12] : k4_xboole_0(k1_xboole_0,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_65,plain,(
    ! [X13] : k5_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_66,plain,(
    ! [X75,X76] :
      ( ( ~ r1_tarski(X75,k2_zfmisc_1(X75,X76))
        | X75 = k1_xboole_0 )
      & ( ~ r1_tarski(X75,k2_zfmisc_1(X76,X75))
        | X75 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_67,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_53]),c_0_44]),c_0_55]),c_0_56]),c_0_57]),c_0_23]),c_0_24])).

cnf(c_0_68,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_29])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = esk3_0
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk3_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:19:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.45/3.64  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 3.45/3.64  # and selection function SelectNegativeLiterals.
% 3.45/3.64  #
% 3.45/3.64  # Preprocessing time       : 0.030 s
% 3.45/3.64  
% 3.45/3.64  # Proof found!
% 3.45/3.64  # SZS status Theorem
% 3.45/3.64  # SZS output start CNFRefutation
% 3.45/3.64  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.45/3.64  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.45/3.64  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.45/3.64  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.45/3.64  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.45/3.64  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.45/3.64  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.45/3.64  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.45/3.64  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.45/3.64  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.45/3.64  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.45/3.64  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.45/3.64  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.45/3.64  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.45/3.64  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.45/3.64  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.45/3.64  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.45/3.64  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.45/3.64  fof(c_0_18, plain, ![X79, X80, X81, X82, X83, X84, X85, X86, X87, X88, X89, X90, X91, X92, X93, X94]:(((~r2_hidden(X86,X85)|(X86=X79|X86=X80|X86=X81|X86=X82|X86=X83|X86=X84)|X85!=k4_enumset1(X79,X80,X81,X82,X83,X84))&((((((X87!=X79|r2_hidden(X87,X85)|X85!=k4_enumset1(X79,X80,X81,X82,X83,X84))&(X87!=X80|r2_hidden(X87,X85)|X85!=k4_enumset1(X79,X80,X81,X82,X83,X84)))&(X87!=X81|r2_hidden(X87,X85)|X85!=k4_enumset1(X79,X80,X81,X82,X83,X84)))&(X87!=X82|r2_hidden(X87,X85)|X85!=k4_enumset1(X79,X80,X81,X82,X83,X84)))&(X87!=X83|r2_hidden(X87,X85)|X85!=k4_enumset1(X79,X80,X81,X82,X83,X84)))&(X87!=X84|r2_hidden(X87,X85)|X85!=k4_enumset1(X79,X80,X81,X82,X83,X84))))&(((((((esk2_7(X88,X89,X90,X91,X92,X93,X94)!=X88|~r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)|X94=k4_enumset1(X88,X89,X90,X91,X92,X93))&(esk2_7(X88,X89,X90,X91,X92,X93,X94)!=X89|~r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)|X94=k4_enumset1(X88,X89,X90,X91,X92,X93)))&(esk2_7(X88,X89,X90,X91,X92,X93,X94)!=X90|~r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)|X94=k4_enumset1(X88,X89,X90,X91,X92,X93)))&(esk2_7(X88,X89,X90,X91,X92,X93,X94)!=X91|~r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)|X94=k4_enumset1(X88,X89,X90,X91,X92,X93)))&(esk2_7(X88,X89,X90,X91,X92,X93,X94)!=X92|~r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)|X94=k4_enumset1(X88,X89,X90,X91,X92,X93)))&(esk2_7(X88,X89,X90,X91,X92,X93,X94)!=X93|~r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)|X94=k4_enumset1(X88,X89,X90,X91,X92,X93)))&(r2_hidden(esk2_7(X88,X89,X90,X91,X92,X93,X94),X94)|(esk2_7(X88,X89,X90,X91,X92,X93,X94)=X88|esk2_7(X88,X89,X90,X91,X92,X93,X94)=X89|esk2_7(X88,X89,X90,X91,X92,X93,X94)=X90|esk2_7(X88,X89,X90,X91,X92,X93,X94)=X91|esk2_7(X88,X89,X90,X91,X92,X93,X94)=X92|esk2_7(X88,X89,X90,X91,X92,X93,X94)=X93)|X94=k4_enumset1(X88,X89,X90,X91,X92,X93)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 3.45/3.64  fof(c_0_19, plain, ![X54, X55, X56, X57, X58, X59]:k5_enumset1(X54,X54,X55,X56,X57,X58,X59)=k4_enumset1(X54,X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 3.45/3.64  fof(c_0_20, plain, ![X60, X61, X62, X63, X64, X65, X66]:k6_enumset1(X60,X60,X61,X62,X63,X64,X65,X66)=k5_enumset1(X60,X61,X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 3.45/3.64  fof(c_0_21, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 3.45/3.64  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.45/3.64  cnf(c_0_23, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.45/3.64  cnf(c_0_24, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.45/3.64  fof(c_0_25, plain, ![X96, X97]:(k1_mcart_1(k4_tarski(X96,X97))=X96&k2_mcart_1(k4_tarski(X96,X97))=X97), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 3.45/3.64  fof(c_0_26, negated_conjecture, (esk3_0=k4_tarski(esk4_0,esk5_0)&(esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 3.45/3.64  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 3.45/3.64  cnf(c_0_28, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.45/3.64  cnf(c_0_29, negated_conjecture, (esk3_0=k4_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.45/3.64  fof(c_0_30, plain, ![X71, X72, X73, X74]:(((r2_hidden(X71,X73)|~r2_hidden(k4_tarski(X71,X72),k2_zfmisc_1(X73,X74)))&(r2_hidden(X72,X74)|~r2_hidden(k4_tarski(X71,X72),k2_zfmisc_1(X73,X74))))&(~r2_hidden(X71,X73)|~r2_hidden(X72,X74)|r2_hidden(k4_tarski(X71,X72),k2_zfmisc_1(X73,X74)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 3.45/3.64  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1)), inference(er,[status(thm)],[c_0_27])).
% 3.45/3.64  cnf(c_0_32, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.45/3.64  cnf(c_0_33, negated_conjecture, (esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.45/3.64  cnf(c_0_34, negated_conjecture, (k1_mcart_1(esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 3.45/3.64  fof(c_0_35, plain, ![X69, X70]:k3_tarski(k2_tarski(X69,X70))=k2_xboole_0(X69,X70), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 3.45/3.64  fof(c_0_36, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.45/3.64  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.45/3.64  cnf(c_0_38, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[c_0_31])).
% 3.45/3.64  cnf(c_0_39, negated_conjecture, (k2_mcart_1(esk3_0)=esk5_0), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 3.45/3.64  cnf(c_0_40, negated_conjecture, (k2_mcart_1(esk3_0)=esk3_0|esk4_0=esk3_0), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 3.45/3.64  fof(c_0_41, plain, ![X77, X78]:k2_xboole_0(k1_tarski(X77),X78)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 3.45/3.64  fof(c_0_42, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 3.45/3.64  cnf(c_0_43, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.45/3.64  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.45/3.64  fof(c_0_45, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.45/3.64  fof(c_0_46, plain, ![X45, X46, X47, X48]:k3_enumset1(X45,X45,X46,X47,X48)=k2_enumset1(X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 3.45/3.64  fof(c_0_47, plain, ![X49, X50, X51, X52, X53]:k4_enumset1(X49,X49,X50,X51,X52,X53)=k3_enumset1(X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 3.45/3.64  fof(c_0_48, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(X14,k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 3.45/3.64  fof(c_0_49, plain, ![X67, X68]:((~r1_tarski(k1_tarski(X67),X68)|r2_hidden(X67,X68))&(~r2_hidden(X67,X68)|r1_tarski(k1_tarski(X67),X68))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 3.45/3.64  cnf(c_0_50, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1),X8))|~r2_hidden(X2,X8)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.45/3.64  cnf(c_0_51, negated_conjecture, (esk4_0=esk3_0|esk5_0=esk3_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 3.45/3.64  cnf(c_0_52, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.45/3.64  cnf(c_0_53, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.45/3.64  cnf(c_0_54, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 3.45/3.64  cnf(c_0_55, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.45/3.64  cnf(c_0_56, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.45/3.64  cnf(c_0_57, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 3.45/3.64  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 3.45/3.64  cnf(c_0_59, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 3.45/3.64  cnf(c_0_60, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1),k6_enumset1(X8,X8,X8,X9,X10,X11,X12,X2)))), inference(spm,[status(thm)],[c_0_50, c_0_38])).
% 3.45/3.64  cnf(c_0_61, negated_conjecture, (k4_tarski(esk4_0,esk3_0)=esk3_0|esk4_0=esk3_0), inference(spm,[status(thm)],[c_0_29, c_0_51])).
% 3.45/3.64  cnf(c_0_62, plain, (k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_44]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 3.45/3.64  cnf(c_0_63, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_23]), c_0_24])).
% 3.45/3.64  fof(c_0_64, plain, ![X12]:k4_xboole_0(k1_xboole_0,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 3.45/3.64  fof(c_0_65, plain, ![X13]:k5_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t5_boole])).
% 3.45/3.64  fof(c_0_66, plain, ![X75, X76]:((~r1_tarski(X75,k2_zfmisc_1(X75,X76))|X75=k1_xboole_0)&(~r1_tarski(X75,k2_zfmisc_1(X76,X75))|X75=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 3.45/3.64  cnf(c_0_67, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_53]), c_0_44]), c_0_55]), c_0_56]), c_0_57]), c_0_23]), c_0_24])).
% 3.45/3.64  cnf(c_0_68, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk3_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 3.45/3.64  cnf(c_0_69, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 3.45/3.64  cnf(c_0_70, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 3.45/3.64  cnf(c_0_71, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 3.45/3.64  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk5_0)))), inference(spm,[status(thm)],[c_0_60, c_0_29])).
% 3.45/3.64  cnf(c_0_73, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.45/3.64  cnf(c_0_74, negated_conjecture, (esk4_0=esk3_0|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk3_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 3.45/3.64  cnf(c_0_75, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 3.45/3.64  cnf(c_0_76, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk4_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk5_0)))), inference(spm,[status(thm)],[c_0_67, c_0_72])).
% 3.45/3.64  cnf(c_0_77, negated_conjecture, (esk4_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 3.45/3.64  cnf(c_0_78, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.45/3.64  cnf(c_0_79, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,esk3_0),k6_enumset1(X6,X6,X6,X7,X8,X9,X10,esk5_0)))), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 3.45/3.64  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_75]), ['proof']).
% 3.45/3.64  # SZS output end CNFRefutation
% 3.45/3.64  # Proof object total steps             : 81
% 3.45/3.64  # Proof object clause steps            : 44
% 3.45/3.64  # Proof object formula steps           : 37
% 3.45/3.64  # Proof object conjectures             : 17
% 3.45/3.64  # Proof object clause conjectures      : 14
% 3.45/3.64  # Proof object formula conjectures     : 3
% 3.45/3.64  # Proof object initial clauses used    : 21
% 3.45/3.64  # Proof object initial formulas used   : 18
% 3.45/3.64  # Proof object generating inferences   : 14
% 3.45/3.64  # Proof object simplifying inferences  : 51
% 3.45/3.64  # Training examples: 0 positive, 0 negative
% 3.45/3.64  # Parsed axioms                        : 19
% 3.45/3.64  # Removed by relevancy pruning/SinE    : 0
% 3.45/3.64  # Initial clauses                      : 57
% 3.45/3.64  # Removed in clause preprocessing      : 8
% 3.45/3.64  # Initial clauses in saturation        : 49
% 3.45/3.64  # Processed clauses                    : 424
% 3.45/3.64  # ...of these trivial                  : 1
% 3.45/3.64  # ...subsumed                          : 88
% 3.45/3.64  # ...remaining for further processing  : 335
% 3.45/3.64  # Other redundant clauses eliminated   : 435
% 3.45/3.64  # Clauses deleted for lack of memory   : 0
% 3.45/3.64  # Backward-subsumed                    : 0
% 3.45/3.64  # Backward-rewritten                   : 62
% 3.45/3.64  # Generated clauses                    : 15125
% 3.45/3.64  # ...of the previous two non-trivial   : 14513
% 3.45/3.64  # Contextual simplify-reflections      : 0
% 3.45/3.64  # Paramodulations                      : 14573
% 3.45/3.64  # Factorizations                       : 74
% 3.45/3.64  # Equation resolutions                 : 478
% 3.45/3.64  # Propositional unsat checks           : 0
% 3.45/3.64  #    Propositional check models        : 0
% 3.45/3.64  #    Propositional check unsatisfiable : 0
% 3.45/3.64  #    Propositional clauses             : 0
% 3.45/3.64  #    Propositional clauses after purity: 0
% 3.45/3.64  #    Propositional unsat core size     : 0
% 3.45/3.64  #    Propositional preprocessing time  : 0.000
% 3.45/3.64  #    Propositional encoding time       : 0.000
% 3.45/3.64  #    Propositional solver time         : 0.000
% 3.45/3.64  #    Success case prop preproc time    : 0.000
% 3.45/3.64  #    Success case prop encoding time   : 0.000
% 3.45/3.64  #    Success case prop solver time     : 0.000
% 3.45/3.64  # Current number of processed clauses  : 258
% 3.45/3.64  #    Positive orientable unit clauses  : 42
% 3.45/3.64  #    Positive unorientable unit clauses: 0
% 3.45/3.64  #    Negative unit clauses             : 2
% 3.45/3.64  #    Non-unit-clauses                  : 214
% 3.45/3.64  # Current number of unprocessed clauses: 14137
% 3.45/3.64  # ...number of literals in the above   : 120269
% 3.45/3.64  # Current number of archived formulas  : 0
% 3.45/3.64  # Current number of archived clauses   : 70
% 3.45/3.64  # Clause-clause subsumption calls (NU) : 18426
% 3.45/3.64  # Rec. Clause-clause subsumption calls : 11355
% 3.45/3.64  # Non-unit clause-clause subsumptions  : 88
% 3.45/3.64  # Unit Clause-clause subsumption calls : 743
% 3.45/3.64  # Rewrite failures with RHS unbound    : 0
% 3.45/3.64  # BW rewrite match attempts            : 114
% 3.45/3.64  # BW rewrite match successes           : 2
% 3.45/3.64  # Condensation attempts                : 0
% 3.45/3.64  # Condensation successes               : 0
% 3.45/3.64  # Termbank termtop insertions          : 405194
% 3.45/3.64  
% 3.45/3.64  # -------------------------------------------------
% 3.45/3.64  # User time                : 3.290 s
% 3.45/3.64  # System time              : 0.014 s
% 3.45/3.64  # Total time               : 3.304 s
% 3.45/3.64  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
