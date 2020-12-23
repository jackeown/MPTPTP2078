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
% DateTime   : Thu Dec  3 10:39:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 558 expanded)
%              Number of clauses        :   36 ( 207 expanded)
%              Number of leaves         :   18 ( 173 expanded)
%              Depth                    :   10
%              Number of atoms          :  205 ( 720 expanded)
%              Number of equality atoms :  160 ( 653 expanded)
%              Maximal formula depth    :   52 (   5 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(t129_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

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

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))
    & esk3_0 != esk5_0
    & esk3_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X108,X109] : k1_enumset1(X108,X108,X109) = k2_tarski(X108,X109) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X110,X111,X112] : k2_enumset1(X110,X110,X111,X112) = k1_enumset1(X110,X111,X112) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X113,X114,X115,X116] : k3_enumset1(X113,X113,X114,X115,X116) = k2_enumset1(X113,X114,X115,X116) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X117,X118,X119,X120,X121] : k4_enumset1(X117,X117,X118,X119,X120,X121) = k3_enumset1(X117,X118,X119,X120,X121) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X122,X123,X124,X125,X126,X127] : k5_enumset1(X122,X122,X123,X124,X125,X126,X127) = k4_enumset1(X122,X123,X124,X125,X126,X127) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X128,X129,X130,X131,X132,X133,X134] : k6_enumset1(X128,X128,X129,X130,X131,X132,X133,X134) = k5_enumset1(X128,X129,X130,X131,X132,X133,X134) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X73,X74,X75,X76,X77,X78,X79,X80,X81] : k7_enumset1(X73,X74,X75,X76,X77,X78,X79,X80,X81) = k2_xboole_0(k1_enumset1(X73,X74,X75),k4_enumset1(X76,X77,X78,X79,X80,X81)) ),
    inference(variable_rename,[status(thm)],[t129_enumset1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,plain,(
    ! [X99,X100,X101,X102,X103,X104,X105,X106] : k6_enumset1(X99,X100,X101,X102,X103,X104,X105,X106) = k2_xboole_0(k5_enumset1(X99,X100,X101,X102,X103,X104,X105),k1_tarski(X106)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_40,plain,(
    ! [X107] : k2_tarski(X107,X107) = k1_tarski(X107) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X82,X83,X84,X85,X86,X87,X88,X89,X90] : k7_enumset1(X82,X83,X84,X85,X86,X87,X88,X89,X90) = k2_xboole_0(k6_enumset1(X82,X83,X84,X85,X86,X87,X88,X89),k1_tarski(X90)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_42,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

fof(c_0_46,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_47,plain,(
    ! [X16] : k5_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_51,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X20
        | X23 = X21
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( esk1_3(X25,X26,X27) != X25
        | ~ r2_hidden(esk1_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( esk1_3(X25,X26,X27) != X26
        | ~ r2_hidden(esk1_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( r2_hidden(esk1_3(X25,X26,X27),X27)
        | esk1_3(X25,X26,X27) = X25
        | esk1_3(X25,X26,X27) = X26
        | X27 = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_52,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X29
        | X39 = X30
        | X39 = X31
        | X39 = X32
        | X39 = X33
        | X39 = X34
        | X39 = X35
        | X39 = X36
        | X39 = X37
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X29
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X30
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X31
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X32
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X33
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X34
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X35
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X36
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X41
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X42
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X43
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X44
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X45
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X46
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X47
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X48
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X49
        | ~ r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X41
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X42
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X43
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X44
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X45
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X46
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X47
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X48
        | esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X49
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_53,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_33]),c_0_43]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_58,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_49]),c_0_33]),c_0_43]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_59,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X2,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k7_enumset1(esk5_0,esk5_0,esk6_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_62,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X1,X10) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k7_enumset1(esk5_0,esk5_0,esk6_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( X1 = esk6_0
    | X1 = esk5_0
    | X2 != k7_enumset1(esk5_0,esk5_0,esk6_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | X1 != k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( X1 = esk5_0
    | X1 = esk6_0
    | X2 != k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_66,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk3_0,k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:13:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.14/0.38  # and selection function SelectNegativeLiterals.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.031 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 0.14/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.14/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.38  fof(t129_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 0.14/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.14/0.38  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 0.14/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.14/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.14/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.38  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 0.14/0.38  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 0.14/0.38  fof(c_0_19, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.14/0.38  fof(c_0_20, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.38  fof(c_0_21, negated_conjecture, ((r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))&esk3_0!=esk5_0)&esk3_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.14/0.38  fof(c_0_22, plain, ![X108, X109]:k1_enumset1(X108,X108,X109)=k2_tarski(X108,X109), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_23, plain, ![X110, X111, X112]:k2_enumset1(X110,X110,X111,X112)=k1_enumset1(X110,X111,X112), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_24, plain, ![X113, X114, X115, X116]:k3_enumset1(X113,X113,X114,X115,X116)=k2_enumset1(X113,X114,X115,X116), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.38  fof(c_0_25, plain, ![X117, X118, X119, X120, X121]:k4_enumset1(X117,X117,X118,X119,X120,X121)=k3_enumset1(X117,X118,X119,X120,X121), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.38  fof(c_0_26, plain, ![X122, X123, X124, X125, X126, X127]:k5_enumset1(X122,X122,X123,X124,X125,X126,X127)=k4_enumset1(X122,X123,X124,X125,X126,X127), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.38  fof(c_0_27, plain, ![X128, X129, X130, X131, X132, X133, X134]:k6_enumset1(X128,X128,X129,X130,X131,X132,X133,X134)=k5_enumset1(X128,X129,X130,X131,X132,X133,X134), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.38  fof(c_0_28, plain, ![X73, X74, X75, X76, X77, X78, X79, X80, X81]:k7_enumset1(X73,X74,X75,X76,X77,X78,X79,X80,X81)=k2_xboole_0(k1_enumset1(X73,X74,X75),k4_enumset1(X76,X77,X78,X79,X80,X81)), inference(variable_rename,[status(thm)],[t129_enumset1])).
% 0.14/0.38  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  fof(c_0_31, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  fof(c_0_39, plain, ![X99, X100, X101, X102, X103, X104, X105, X106]:k6_enumset1(X99,X100,X101,X102,X103,X104,X105,X106)=k2_xboole_0(k5_enumset1(X99,X100,X101,X102,X103,X104,X105),k1_tarski(X106)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.14/0.38  fof(c_0_40, plain, ![X107]:k2_tarski(X107,X107)=k1_tarski(X107), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_41, plain, ![X82, X83, X84, X85, X86, X87, X88, X89, X90]:k7_enumset1(X82,X83,X84,X85,X86,X87,X88,X89,X90)=k2_xboole_0(k6_enumset1(X82,X83,X84,X85,X86,X87,X88,X89),k1_tarski(X90)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.14/0.38  cnf(c_0_42, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.14/0.38  fof(c_0_46, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.14/0.38  fof(c_0_47, plain, ![X16]:k5_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.14/0.38  cnf(c_0_48, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_50, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  fof(c_0_51, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X23,X22)|(X23=X20|X23=X21)|X22!=k2_tarski(X20,X21))&((X24!=X20|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))))&(((esk1_3(X25,X26,X27)!=X25|~r2_hidden(esk1_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26))&(esk1_3(X25,X26,X27)!=X26|~r2_hidden(esk1_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26)))&(r2_hidden(esk1_3(X25,X26,X27),X27)|(esk1_3(X25,X26,X27)=X25|esk1_3(X25,X26,X27)=X26)|X27=k2_tarski(X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.38  fof(c_0_52, plain, ![X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X39,X38)|(X39=X29|X39=X30|X39=X31|X39=X32|X39=X33|X39=X34|X39=X35|X39=X36|X39=X37)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37))&(((((((((X40!=X29|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37))&(X40!=X30|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X31|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X32|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X33|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X34|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X35|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X36|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X37|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37))))&((((((((((esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X41|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X42|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X43|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X44|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X45|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X46|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X47|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X48|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X49|~r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(r2_hidden(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|(esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X41|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X42|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X43|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X44|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X45|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X46|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X47|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X48|esk2_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X49)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.14/0.38  cnf(c_0_53, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.38  cnf(c_0_55, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.38  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.38  cnf(c_0_57, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_33]), c_0_43]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.14/0.38  cnf(c_0_58, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_49]), c_0_33]), c_0_43]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.14/0.38  cnf(c_0_59, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.38  cnf(c_0_60, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X2,X11)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k7_enumset1(esk5_0,esk5_0,esk6_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])).
% 0.14/0.38  cnf(c_0_62, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.14/0.38  cnf(c_0_63, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.14/0.38  cnf(c_0_64, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X1,X10)), inference(er,[status(thm)],[c_0_60])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (k7_enumset1(esk5_0,esk5_0,esk6_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.14/0.38  cnf(c_0_66, negated_conjecture, (X1=esk6_0|X1=esk5_0|X2!=k7_enumset1(esk5_0,esk5_0,esk6_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_61])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_0,X1)|X1!=k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (X1=esk5_0|X1=esk6_0|X2!=k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_66, c_0_65])).
% 0.14/0.38  cnf(c_0_69, negated_conjecture, (r2_hidden(esk3_0,k7_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(er,[status(thm)],[c_0_67])).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 73
% 0.14/0.38  # Proof object clause steps            : 36
% 0.14/0.38  # Proof object formula steps           : 37
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 20
% 0.14/0.38  # Proof object initial formulas used   : 18
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 70
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 23
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 49
% 0.14/0.38  # Removed in clause preprocessing      : 9
% 0.14/0.38  # Initial clauses in saturation        : 40
% 0.14/0.38  # Processed clauses                    : 91
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 17
% 0.14/0.38  # ...remaining for further processing  : 73
% 0.14/0.38  # Other redundant clauses eliminated   : 18
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 9
% 0.14/0.38  # Generated clauses                    : 428
% 0.14/0.38  # ...of the previous two non-trivial   : 367
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 388
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 40
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 52
% 0.14/0.38  #    Positive orientable unit clauses  : 12
% 0.14/0.38  #    Positive unorientable unit clauses: 4
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 34
% 0.14/0.38  # Current number of unprocessed clauses: 312
% 0.14/0.38  # ...number of literals in the above   : 911
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 19
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 294
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 292
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 17
% 0.14/0.38  # Unit Clause-clause subsumption calls : 13
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 75
% 0.14/0.38  # BW rewrite match successes           : 48
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 7117
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.040 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.046 s
% 0.14/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
