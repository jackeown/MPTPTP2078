%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 964 expanded)
%              Number of clauses        :   45 ( 350 expanded)
%              Number of leaves         :   22 ( 306 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 (1084 expanded)
%              Number of equality atoms :  125 ( 996 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

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

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_22,plain,(
    ! [X99,X100] : k3_tarski(k2_tarski(X99,X100)) = k2_xboole_0(X99,X100) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X70,X71] : k1_enumset1(X70,X70,X71) = k2_tarski(X70,X71) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
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
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X41
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X42
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X43
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X44
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X45
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X46
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X47
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X48
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) != X49
        | ~ r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) )
      & ( r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X41
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X42
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X43
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X44
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X45
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X46
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X47
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X48
        | esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50) = X49
        | X50 = k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X25,X26] : k2_xboole_0(X25,X26) = k5_xboole_0(k5_xboole_0(X25,X26),k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X72,X73,X74] : k2_enumset1(X72,X72,X73,X74) = k1_enumset1(X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X75,X76,X77,X78] : k3_enumset1(X75,X75,X76,X77,X78) = k2_enumset1(X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X79,X80,X81,X82,X83] : k4_enumset1(X79,X79,X80,X81,X82,X83) = k3_enumset1(X79,X80,X81,X82,X83) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X84,X85,X86,X87,X88,X89] : k5_enumset1(X84,X84,X85,X86,X87,X88,X89) = k4_enumset1(X84,X85,X86,X87,X88,X89) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_33,plain,(
    ! [X90,X91,X92,X93,X94,X95,X96] : k6_enumset1(X90,X90,X91,X92,X93,X94,X95,X96) = k5_enumset1(X90,X91,X92,X93,X94,X95,X96) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_34,plain,(
    ! [X97,X98] :
      ( ~ r2_hidden(X97,X98)
      | r1_tarski(X97,k3_tarski(X98)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58,X59] : k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) = k2_xboole_0(k2_enumset1(X52,X53,X54,X55),k2_enumset1(X56,X57,X58,X59)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_37,plain,(
    ! [X60,X61,X62,X63,X64,X65,X66,X67,X68] : k7_enumset1(X60,X61,X62,X63,X64,X65,X66,X67,X68) = k2_xboole_0(k3_enumset1(X60,X61,X62,X63,X64),k2_enumset1(X65,X66,X67,X68)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

fof(c_0_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_39,plain,(
    ! [X69] : k2_tarski(X69,X69) = k1_tarski(X69) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_47,plain,(
    ! [X22,X23,X24] : k5_xboole_0(k5_xboole_0(X22,X23),X24) = k5_xboole_0(X22,k5_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_48,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | ~ r2_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_57,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_58,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k3_tarski(k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_41]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_61,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_41]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

fof(c_0_62,plain,(
    ! [X27,X28] : k2_xboole_0(X27,X28) = k5_xboole_0(X27,k4_xboole_0(X28,X27)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_63,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_64,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_28]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_66,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( ~ r2_xboole_0(k3_tarski(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)),X9) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_72,plain,(
    ! [X101,X102,X103] :
      ( ( r2_hidden(X101,X103)
        | ~ r1_tarski(k2_tarski(X101,X102),X103) )
      & ( r2_hidden(X102,X103)
        | ~ r1_tarski(k2_tarski(X101,X102),X103) )
      & ( ~ r2_hidden(X101,X103)
        | ~ r2_hidden(X102,X103)
        | r1_tarski(k2_tarski(X101,X102),X103) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_74,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | ~ r2_xboole_0(X14,X15) )
      & ( X14 != X15
        | ~ r2_xboole_0(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | X14 = X15
        | r2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_76,plain,
    ( ~ r2_xboole_0(k3_tarski(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),X8) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_41]),c_0_71]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_80,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_69]),c_0_69])).

cnf(c_0_82,plain,
    ( ~ r2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_28]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k7_enumset1(X3,X3,X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_69])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.13/0.39  # and selection function GSelectMinInfpos.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 0.13/0.39  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 0.13/0.39  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.39  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.13/0.39  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 0.13/0.39  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.13/0.39  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.13/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.39  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.13/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.39  fof(c_0_22, plain, ![X99, X100]:k3_tarski(k2_tarski(X99,X100))=k2_xboole_0(X99,X100), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.39  fof(c_0_23, plain, ![X70, X71]:k1_enumset1(X70,X70,X71)=k2_tarski(X70,X71), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_24, plain, ![X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X39,X38)|(X39=X29|X39=X30|X39=X31|X39=X32|X39=X33|X39=X34|X39=X35|X39=X36|X39=X37)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37))&(((((((((X40!=X29|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37))&(X40!=X30|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X31|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X32|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X33|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X34|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X35|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X36|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37)))&(X40!=X37|r2_hidden(X40,X38)|X38!=k7_enumset1(X29,X30,X31,X32,X33,X34,X35,X36,X37))))&((((((((((esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X41|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X42|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X43|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X44|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X45|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X46|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X47|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X48|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)!=X49|~r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))&(r2_hidden(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50),X50)|(esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X41|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X42|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X43|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X44|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X45|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X46|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X47|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X48|esk1_10(X41,X42,X43,X44,X45,X46,X47,X48,X49,X50)=X49)|X50=k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.13/0.39  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 0.13/0.39  fof(c_0_26, plain, ![X25, X26]:k2_xboole_0(X25,X26)=k5_xboole_0(k5_xboole_0(X25,X26),k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.39  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  fof(c_0_29, plain, ![X72, X73, X74]:k2_enumset1(X72,X72,X73,X74)=k1_enumset1(X72,X73,X74), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_30, plain, ![X75, X76, X77, X78]:k3_enumset1(X75,X75,X76,X77,X78)=k2_enumset1(X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_31, plain, ![X79, X80, X81, X82, X83]:k4_enumset1(X79,X79,X80,X81,X82,X83)=k3_enumset1(X79,X80,X81,X82,X83), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.39  fof(c_0_32, plain, ![X84, X85, X86, X87, X88, X89]:k5_enumset1(X84,X84,X85,X86,X87,X88,X89)=k4_enumset1(X84,X85,X86,X87,X88,X89), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.39  fof(c_0_33, plain, ![X90, X91, X92, X93, X94, X95, X96]:k6_enumset1(X90,X90,X91,X92,X93,X94,X95,X96)=k5_enumset1(X90,X91,X92,X93,X94,X95,X96), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.39  fof(c_0_34, plain, ![X97, X98]:(~r2_hidden(X97,X98)|r1_tarski(X97,k3_tarski(X98))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.13/0.39  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X11,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  fof(c_0_36, plain, ![X52, X53, X54, X55, X56, X57, X58, X59]:k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)=k2_xboole_0(k2_enumset1(X52,X53,X54,X55),k2_enumset1(X56,X57,X58,X59)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.13/0.39  fof(c_0_37, plain, ![X60, X61, X62, X63, X64, X65, X66, X67, X68]:k7_enumset1(X60,X61,X62,X63,X64,X65,X66,X67,X68)=k2_xboole_0(k3_enumset1(X60,X61,X62,X63,X64),k2_enumset1(X65,X66,X67,X68)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.13/0.39  fof(c_0_38, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0)&~r2_hidden(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.39  fof(c_0_39, plain, ![X69]:k2_tarski(X69,X69)=k1_tarski(X69), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.39  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  fof(c_0_47, plain, ![X22, X23, X24]:k5_xboole_0(k5_xboole_0(X22,X23),X24)=k5_xboole_0(X22,k5_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.13/0.39  fof(c_0_48, plain, ![X18, X19]:(~r1_tarski(X18,X19)|~r2_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.13/0.39  cnf(c_0_49, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_50, plain, (r2_hidden(X1,k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.13/0.39  cnf(c_0_51, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_52, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk2_0),esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  cnf(c_0_54, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  cnf(c_0_55, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.13/0.39  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.39  fof(c_0_57, plain, ![X12, X13]:k3_xboole_0(X12,X13)=k3_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.39  cnf(c_0_58, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  cnf(c_0_59, plain, (r1_tarski(X1,k3_tarski(k7_enumset1(X2,X3,X4,X5,X6,X7,X8,X9,X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_60, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_41]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.13/0.39  cnf(c_0_61, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_41]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.13/0.39  fof(c_0_62, plain, ![X27, X28]:k2_xboole_0(X27,X28)=k5_xboole_0(X27,k4_xboole_0(X28,X27)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.39  fof(c_0_63, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  fof(c_0_64, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_28]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.13/0.39  cnf(c_0_66, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  cnf(c_0_67, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.39  cnf(c_0_68, plain, (~r2_xboole_0(k3_tarski(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)),X9)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.39  cnf(c_0_69, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.39  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.39  cnf(c_0_71, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.39  fof(c_0_72, plain, ![X101, X102, X103]:(((r2_hidden(X101,X103)|~r1_tarski(k2_tarski(X101,X102),X103))&(r2_hidden(X102,X103)|~r1_tarski(k2_tarski(X101,X102),X103)))&(~r2_hidden(X101,X103)|~r2_hidden(X102,X103)|r1_tarski(k2_tarski(X101,X102),X103))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.13/0.39  cnf(c_0_73, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.39  fof(c_0_74, plain, ![X14, X15]:(((r1_tarski(X14,X15)|~r2_xboole_0(X14,X15))&(X14!=X15|~r2_xboole_0(X14,X15)))&(~r1_tarski(X14,X15)|X14=X15|r2_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (r1_tarski(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.13/0.39  cnf(c_0_76, plain, (~r2_xboole_0(k3_tarski(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),X8)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.39  cnf(c_0_77, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_41]), c_0_71]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.13/0.39  cnf(c_0_78, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.39  cnf(c_0_79, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.13/0.39  cnf(c_0_80, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (r1_tarski(k5_xboole_0(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_69]), c_0_69])).
% 0.13/0.39  cnf(c_0_82, plain, (~r2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.13/0.39  cnf(c_0_83, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_28]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.13/0.39  cnf(c_0_84, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_79, c_0_77])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (k5_xboole_0(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.13/0.39  cnf(c_0_86, plain, (r2_hidden(X1,X2)|~r1_tarski(k7_enumset1(X3,X3,X3,X3,X3,X3,X3,X3,X1),X2)), inference(spm,[status(thm)],[c_0_83, c_0_69])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (r1_tarski(k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.13/0.39  cnf(c_0_88, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 90
% 0.13/0.39  # Proof object clause steps            : 45
% 0.13/0.39  # Proof object formula steps           : 45
% 0.13/0.39  # Proof object conjectures             : 11
% 0.13/0.39  # Proof object clause conjectures      : 8
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 23
% 0.13/0.39  # Proof object initial formulas used   : 22
% 0.13/0.39  # Proof object generating inferences   : 9
% 0.13/0.39  # Proof object simplifying inferences  : 117
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 22
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 46
% 0.13/0.39  # Removed in clause preprocessing      : 9
% 0.13/0.39  # Initial clauses in saturation        : 37
% 0.13/0.39  # Processed clauses                    : 221
% 0.13/0.39  # ...of these trivial                  : 6
% 0.13/0.39  # ...subsumed                          : 67
% 0.13/0.39  # ...remaining for further processing  : 148
% 0.13/0.39  # Other redundant clauses eliminated   : 20
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 6
% 0.13/0.39  # Generated clauses                    : 445
% 0.13/0.39  # ...of the previous two non-trivial   : 415
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 434
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 20
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 94
% 0.13/0.39  #    Positive orientable unit clauses  : 35
% 0.13/0.39  #    Positive unorientable unit clauses: 4
% 0.13/0.39  #    Negative unit clauses             : 35
% 0.13/0.39  #    Non-unit-clauses                  : 20
% 0.13/0.39  # Current number of unprocessed clauses: 266
% 0.13/0.39  # ...number of literals in the above   : 344
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 52
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 161
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 159
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.39  # Unit Clause-clause subsumption calls : 213
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 187
% 0.13/0.39  # BW rewrite match successes           : 26
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 7634
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.038 s
% 0.13/0.39  # System time              : 0.006 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
