%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 142 expanded)
%              Number of clauses        :   28 (  54 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  174 ( 258 expanded)
%              Number of equality atoms :  132 ( 213 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d7_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( X10 = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X11 != X1
              & X11 != X2
              & X11 != X3
              & X11 != X4
              & X11 != X5
              & X11 != X6
              & X11 != X7
              & X11 != X8
              & X11 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t24_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(X23,k4_xboole_0(X24,X23)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_18,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k1_tarski(esk4_0))
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X64] : k2_tarski(X64,X64) = k1_tarski(X64) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X65,X66] : k1_enumset1(X65,X65,X66) = k2_tarski(X65,X66) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X67,X68,X69] : k2_enumset1(X67,X67,X68,X69) = k1_enumset1(X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X70,X71,X72,X73] : k3_enumset1(X70,X70,X71,X72,X73) = k2_enumset1(X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X74,X75,X76,X77,X78] : k4_enumset1(X74,X74,X75,X76,X77,X78) = k3_enumset1(X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X79,X80,X81,X82,X83,X84] : k5_enumset1(X79,X79,X80,X81,X82,X83,X84) = k4_enumset1(X79,X80,X81,X82,X83,X84) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X85,X86,X87,X88,X89,X90,X91] : k6_enumset1(X85,X85,X86,X87,X88,X89,X90,X91) = k5_enumset1(X85,X86,X87,X88,X89,X90,X91) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_27,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X25
        | X26 != k1_tarski(X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k1_tarski(X25) )
      & ( ~ r2_hidden(esk1_2(X29,X30),X30)
        | esk1_2(X29,X30) != X29
        | X30 = k1_tarski(X29) )
      & ( r2_hidden(esk1_2(X29,X30),X30)
        | esk1_2(X29,X30) = X29
        | X30 = k1_tarski(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_28,plain,(
    ! [X55,X56,X57,X58,X59,X60,X61,X62,X63] : k7_enumset1(X55,X56,X57,X58,X59,X60,X61,X62,X63) = k2_xboole_0(k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62),k1_tarski(X63)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

fof(c_0_45,plain,(
    ! [X22] : k5_xboole_0(X22,X22) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_46,plain,(
    ! [X21] : k5_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_47,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X32
        | X42 = X33
        | X42 = X34
        | X42 = X35
        | X42 = X36
        | X42 = X37
        | X42 = X38
        | X42 = X39
        | X42 = X40
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X32
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X33
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X34
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X35
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X36
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X37
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X38
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X39
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X44
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X45
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X46
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X47
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X48
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X49
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X50
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X51
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X52
        | ~ r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X44
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X45
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X46
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X47
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X48
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X49
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X50
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X51
        | esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X52
        | X53 = k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_48,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_49,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_33]),c_0_34]),c_0_42]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.38  # and selection function SelectNegativeLiterals.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t24_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 0.20/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.38  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 0.20/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.38  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 0.20/0.38  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2)), inference(assume_negation,[status(cth)],[t24_zfmisc_1])).
% 0.20/0.38  fof(c_0_17, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(X23,k4_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.38  fof(c_0_18, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),k1_tarski(esk4_0))&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.38  fof(c_0_20, plain, ![X64]:k2_tarski(X64,X64)=k1_tarski(X64), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_21, plain, ![X65, X66]:k1_enumset1(X65,X65,X66)=k2_tarski(X65,X66), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_22, plain, ![X67, X68, X69]:k2_enumset1(X67,X67,X68,X69)=k1_enumset1(X67,X68,X69), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X70, X71, X72, X73]:k3_enumset1(X70,X70,X71,X72,X73)=k2_enumset1(X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_24, plain, ![X74, X75, X76, X77, X78]:k4_enumset1(X74,X74,X75,X76,X77,X78)=k3_enumset1(X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_25, plain, ![X79, X80, X81, X82, X83, X84]:k5_enumset1(X79,X79,X80,X81,X82,X83,X84)=k4_enumset1(X79,X80,X81,X82,X83,X84), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.38  fof(c_0_26, plain, ![X85, X86, X87, X88, X89, X90, X91]:k6_enumset1(X85,X85,X86,X87,X88,X89,X90,X91)=k5_enumset1(X85,X86,X87,X88,X89,X90,X91), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.38  fof(c_0_27, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|X27=X25|X26!=k1_tarski(X25))&(X28!=X25|r2_hidden(X28,X26)|X26!=k1_tarski(X25)))&((~r2_hidden(esk1_2(X29,X30),X30)|esk1_2(X29,X30)!=X29|X30=k1_tarski(X29))&(r2_hidden(esk1_2(X29,X30),X30)|esk1_2(X29,X30)=X29|X30=k1_tarski(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.38  fof(c_0_28, plain, ![X55, X56, X57, X58, X59, X60, X61, X62, X63]:k7_enumset1(X55,X56,X57,X58,X59,X60,X61,X62,X63)=k2_xboole_0(k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62),k1_tarski(X63)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.20/0.38  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_31, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_40, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_41, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.38  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.20/0.38  fof(c_0_45, plain, ![X22]:k5_xboole_0(X22,X22)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.38  fof(c_0_46, plain, ![X21]:k5_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.38  fof(c_0_47, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53]:(((~r2_hidden(X42,X41)|(X42=X32|X42=X33|X42=X34|X42=X35|X42=X36|X42=X37|X42=X38|X42=X39|X42=X40)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40))&(((((((((X43!=X32|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40))&(X43!=X33|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X34|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X35|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X36|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X37|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X38|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X39|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)))&(X43!=X40|r2_hidden(X43,X41)|X41!=k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40))))&((((((((((esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X44|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X45|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X46|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X47|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X48|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X49|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X50|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X51|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X52|~r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(r2_hidden(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|(esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X44|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X45|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X46|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X47|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X48|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X49|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X50|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X51|esk2_10(X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X52)|X53=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.20/0.38  cnf(c_0_48, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_49, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_33]), c_0_34]), c_0_42]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.38  cnf(c_0_51, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_52, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_54, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])).
% 0.20/0.38  cnf(c_0_56, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X1)), inference(er,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k7_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.38  cnf(c_0_58, plain, (r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1))), inference(er,[status(thm)],[c_0_56])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 61
% 0.20/0.38  # Proof object clause steps            : 28
% 0.20/0.38  # Proof object formula steps           : 33
% 0.20/0.38  # Proof object conjectures             : 10
% 0.20/0.38  # Proof object clause conjectures      : 7
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 16
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 39
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 19
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 42
% 0.20/0.38  # Removed in clause preprocessing      : 9
% 0.20/0.38  # Initial clauses in saturation        : 33
% 0.20/0.38  # Processed clauses                    : 67
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 62
% 0.20/0.38  # Other redundant clauses eliminated   : 13
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 176
% 0.20/0.38  # ...of the previous two non-trivial   : 160
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 147
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 29
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 49
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 34
% 0.20/0.38  # Current number of unprocessed clauses: 121
% 0.20/0.38  # ...number of literals in the above   : 497
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 12
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 256
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 222
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.38  # Unit Clause-clause subsumption calls : 2
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 8
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4558
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.036 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
