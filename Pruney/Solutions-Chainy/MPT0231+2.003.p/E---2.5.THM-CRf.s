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
% DateTime   : Thu Dec  3 10:38:48 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 629 expanded)
%              Number of clauses        :   36 ( 240 expanded)
%              Number of leaves         :   15 ( 193 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 ( 879 expanded)
%              Number of equality atoms :  146 ( 788 expanded)
%              Maximal formula depth    :   57 (   5 average)
%              Maximal clause size      :   84 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(t135_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = k2_xboole_0(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X10)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_enumset1)).

fof(t128_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).

fof(t26_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => X1 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d8_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11] :
      ( X11 = k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
    <=> ! [X12] :
          ( r2_hidden(X12,X11)
        <=> ~ ( X12 != X1
              & X12 != X2
              & X12 != X3
              & X12 != X4
              & X12 != X5
              & X12 != X6
              & X12 != X7
              & X12 != X8
              & X12 != X9
              & X12 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_enumset1)).

fof(c_0_15,plain,(
    ! [X92,X93,X94,X95,X96,X97,X98,X99] : k6_enumset1(X92,X93,X94,X95,X96,X97,X98,X99) = k2_xboole_0(k1_tarski(X92),k5_enumset1(X93,X94,X95,X96,X97,X98,X99)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_16,plain,(
    ! [X100] : k2_tarski(X100,X100) = k1_tarski(X100) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X116,X117] : k2_enumset1(X116,X116,X116,X117) = k2_tarski(X116,X117) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_18,plain,(
    ! [X101,X102,X103,X104] : k3_enumset1(X101,X101,X102,X103,X104) = k2_enumset1(X101,X102,X103,X104) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X105,X106,X107,X108,X109] : k4_enumset1(X105,X105,X106,X107,X108,X109) = k3_enumset1(X105,X106,X107,X108,X109) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X110,X111,X112,X113,X114,X115] : k5_enumset1(X110,X110,X111,X112,X113,X114,X115) = k4_enumset1(X110,X111,X112,X113,X114,X115) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X55,X56,X57,X58,X59,X60,X61,X62,X63] : k7_enumset1(X55,X56,X57,X58,X59,X60,X61,X62,X63) = k2_xboole_0(k1_tarski(X55),k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

cnf(c_0_22,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X82,X83,X84,X85,X86,X87,X88,X89,X90,X91] : k8_enumset1(X82,X83,X84,X85,X86,X87,X88,X89,X90,X91) = k2_xboole_0(k7_enumset1(X82,X83,X84,X85,X86,X87,X88,X89,X90),k1_tarski(X91)) ),
    inference(variable_rename,[status(thm)],[t135_enumset1])).

cnf(c_0_29,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

fof(c_0_31,plain,(
    ! [X64,X65,X66,X67,X68,X69,X70,X71,X72] : k7_enumset1(X64,X65,X66,X67,X68,X69,X70,X71,X72) = k2_xboole_0(k2_tarski(X64,X65),k5_enumset1(X66,X67,X68,X69,X70,X71,X72)) ),
    inference(variable_rename,[status(thm)],[t128_enumset1])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t26_zfmisc_1])).

fof(c_0_33,plain,(
    ! [X73,X74,X75,X76,X77,X78,X79,X80,X81] : k7_enumset1(X73,X74,X75,X76,X77,X78,X79,X80,X81) = k2_xboole_0(k6_enumset1(X73,X74,X75,X76,X77,X78,X79,X80),k1_tarski(X81)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_34,plain,
    ( k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = k2_xboole_0(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X10)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_30])).

cnf(c_0_36,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X20,X21,X22] : k2_xboole_0(k2_xboole_0(X20,X21),X22) = k2_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_38,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_39,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))),k5_enumset1(X10,X10,X10,X10,X10,X10,X10)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_35])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_35])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X23
        | X24 != k1_tarski(X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_tarski(X23) )
      & ( ~ r2_hidden(esk1_2(X27,X28),X28)
        | esk1_2(X27,X28) != X27
        | X28 = k1_tarski(X27) )
      & ( r2_hidden(esk1_2(X27,X28),X28)
        | esk1_2(X27,X28) = X27
        | X28 = k1_tarski(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))) = k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_30]),c_0_35])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k2_xboole_0(k5_enumset1(X3,X4,X5,X6,X7,X8,X9),k5_enumset1(X10,X10,X10,X10,X10,X10,X10))) = k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) = k8_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_41]),c_0_42]),c_0_47])).

fof(c_0_52,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53] :
      ( ( ~ r2_hidden(X41,X40)
        | X41 = X30
        | X41 = X31
        | X41 = X32
        | X41 = X33
        | X41 = X34
        | X41 = X35
        | X41 = X36
        | X41 = X37
        | X41 = X38
        | X41 = X39
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X30
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X31
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X32
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X33
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X34
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X35
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X36
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X37
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X38
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( X42 != X39
        | r2_hidden(X42,X40)
        | X40 != k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X43
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X44
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X45
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X46
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X47
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X48
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X49
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X50
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X51
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) != X52
        | ~ r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X43
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X44
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X45
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X46
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X47
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X48
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X49
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X50
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X51
        | esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53) = X52
        | X53 = k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_enumset1])])])])])])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k8_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k8_enumset1(X4,X5,X2,X6,X7,X8,X9,X10,X11,X12) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( X1 = esk5_0
    | X2 != k8_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | X2 != k8_enumset1(X3,X4,X1,X5,X6,X7,X8,X9,X10,X11) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,k8_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k8_enumset1(X2,X3,X1,X4,X5,X6,X7,X8,X9,X10)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k8_enumset1(X4,X2,X5,X6,X7,X8,X9,X10,X11,X12) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | X2 != k8_enumset1(X3,X1,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,k8_enumset1(esk3_0,esk3_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_61])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k8_enumset1(X2,X1,X3,X4,X5,X6,X7,X8,X9,X10)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.44  # and selection function SelectNegativeLiterals.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.029 s
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 0.19/0.44  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.44  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.44  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.44  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.44  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.44  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 0.19/0.44  fof(t135_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)=k2_xboole_0(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X10)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_enumset1)).
% 0.19/0.44  fof(t128_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_enumset1)).
% 0.19/0.44  fof(t26_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 0.19/0.44  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 0.19/0.44  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.44  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.44  fof(d8_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11]:(X11=k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)<=>![X12]:(r2_hidden(X12,X11)<=>~((((((((((X12!=X1&X12!=X2)&X12!=X3)&X12!=X4)&X12!=X5)&X12!=X6)&X12!=X7)&X12!=X8)&X12!=X9)&X12!=X10)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_enumset1)).
% 0.19/0.44  fof(c_0_15, plain, ![X92, X93, X94, X95, X96, X97, X98, X99]:k6_enumset1(X92,X93,X94,X95,X96,X97,X98,X99)=k2_xboole_0(k1_tarski(X92),k5_enumset1(X93,X94,X95,X96,X97,X98,X99)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.19/0.44  fof(c_0_16, plain, ![X100]:k2_tarski(X100,X100)=k1_tarski(X100), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.44  fof(c_0_17, plain, ![X116, X117]:k2_enumset1(X116,X116,X116,X117)=k2_tarski(X116,X117), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.44  fof(c_0_18, plain, ![X101, X102, X103, X104]:k3_enumset1(X101,X101,X102,X103,X104)=k2_enumset1(X101,X102,X103,X104), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.44  fof(c_0_19, plain, ![X105, X106, X107, X108, X109]:k4_enumset1(X105,X105,X106,X107,X108,X109)=k3_enumset1(X105,X106,X107,X108,X109), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.44  fof(c_0_20, plain, ![X110, X111, X112, X113, X114, X115]:k5_enumset1(X110,X110,X111,X112,X113,X114,X115)=k4_enumset1(X110,X111,X112,X113,X114,X115), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.44  fof(c_0_21, plain, ![X55, X56, X57, X58, X59, X60, X61, X62, X63]:k7_enumset1(X55,X56,X57,X58,X59,X60,X61,X62,X63)=k2_xboole_0(k1_tarski(X55),k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 0.19/0.44  cnf(c_0_22, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_26, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_27, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  fof(c_0_28, plain, ![X82, X83, X84, X85, X86, X87, X88, X89, X90, X91]:k8_enumset1(X82,X83,X84,X85,X86,X87,X88,X89,X90,X91)=k2_xboole_0(k7_enumset1(X82,X83,X84,X85,X86,X87,X88,X89,X90),k1_tarski(X91)), inference(variable_rename,[status(thm)],[t135_enumset1])).
% 0.19/0.44  cnf(c_0_29, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_30, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.44  fof(c_0_31, plain, ![X64, X65, X66, X67, X68, X69, X70, X71, X72]:k7_enumset1(X64,X65,X66,X67,X68,X69,X70,X71,X72)=k2_xboole_0(k2_tarski(X64,X65),k5_enumset1(X66,X67,X68,X69,X70,X71,X72)), inference(variable_rename,[status(thm)],[t128_enumset1])).
% 0.19/0.44  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3)), inference(assume_negation,[status(cth)],[t26_zfmisc_1])).
% 0.19/0.44  fof(c_0_33, plain, ![X73, X74, X75, X76, X77, X78, X79, X80, X81]:k7_enumset1(X73,X74,X75,X76,X77,X78,X79,X80,X81)=k2_xboole_0(k6_enumset1(X73,X74,X75,X76,X77,X78,X79,X80),k1_tarski(X81)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.19/0.44  cnf(c_0_34, plain, (k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)=k2_xboole_0(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X10))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_35, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_30])).
% 0.19/0.44  cnf(c_0_36, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  fof(c_0_37, plain, ![X20, X21, X22]:k2_xboole_0(k2_xboole_0(X20,X21),X22)=k2_xboole_0(X20,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.44  fof(c_0_38, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.19/0.44  cnf(c_0_39, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.44  cnf(c_0_40, plain, (k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)=k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))),k5_enumset1(X10,X10,X10,X10,X10,X10,X10))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_35])).
% 0.19/0.44  cnf(c_0_41, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)))=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_35])).
% 0.19/0.44  cnf(c_0_42, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.44  fof(c_0_43, plain, ![X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X25,X24)|X25=X23|X24!=k1_tarski(X23))&(X26!=X23|r2_hidden(X26,X24)|X24!=k1_tarski(X23)))&((~r2_hidden(esk1_2(X27,X28),X28)|esk1_2(X27,X28)!=X27|X28=k1_tarski(X27))&(r2_hidden(esk1_2(X27,X28),X28)|esk1_2(X27,X28)=X27|X28=k1_tarski(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.44  fof(c_0_44, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.44  cnf(c_0_46, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)))=k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_30]), c_0_35])).
% 0.19/0.44  cnf(c_0_47, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k2_xboole_0(k5_enumset1(X3,X4,X5,X6,X7,X8,X9),k5_enumset1(X10,X10,X10,X10,X10,X10,X10)))=k8_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.19/0.44  cnf(c_0_48, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.44  cnf(c_0_50, negated_conjecture, (r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.19/0.44  cnf(c_0_51, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))=k8_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_41]), c_0_42]), c_0_47])).
% 0.19/0.44  fof(c_0_52, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53]:(((~r2_hidden(X41,X40)|(X41=X30|X41=X31|X41=X32|X41=X33|X41=X34|X41=X35|X41=X36|X41=X37|X41=X38|X41=X39)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39))&((((((((((X42!=X30|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39))&(X42!=X31|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X32|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X33|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X34|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X35|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X36|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X37|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X38|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39)))&(X42!=X39|r2_hidden(X42,X40)|X40!=k8_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38,X39))))&(((((((((((esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X43|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X44|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X45|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X46|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X47|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X48|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X49|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X50|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X51|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)!=X52|~r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(r2_hidden(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53),X53)|(esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X43|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X44|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X45|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X46|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X47|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X48|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X49|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X50|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X51|esk2_11(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53)=X52)|X53=k8_enumset1(X43,X44,X45,X46,X47,X48,X49,X50,X51,X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_enumset1])])])])])])).
% 0.19/0.44  cnf(c_0_53, plain, (X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k8_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.44  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k8_enumset1(X4,X5,X2,X6,X7,X8,X9,X10,X11,X12)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (X1=esk5_0|X2!=k8_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.44  cnf(c_0_57, plain, (r2_hidden(X1,X2)|X2!=k8_enumset1(X3,X4,X1,X5,X6,X7,X8,X9,X10,X11)), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,k8_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(er,[status(thm)],[c_0_56])).
% 0.19/0.44  cnf(c_0_59, plain, (r2_hidden(X1,k8_enumset1(X2,X3,X1,X4,X5,X6,X7,X8,X9,X10))), inference(er,[status(thm)],[c_0_57])).
% 0.19/0.44  cnf(c_0_60, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k8_enumset1(X4,X2,X5,X6,X7,X8,X9,X10,X11,X12)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.44  cnf(c_0_62, plain, (r2_hidden(X1,X2)|X2!=k8_enumset1(X3,X1,X4,X5,X6,X7,X8,X9,X10,X11)), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,k8_enumset1(esk3_0,esk3_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_58, c_0_61])).
% 0.19/0.44  cnf(c_0_64, plain, (r2_hidden(X1,k8_enumset1(X2,X1,X3,X4,X5,X6,X7,X8,X9,X10))), inference(er,[status(thm)],[c_0_62])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 67
% 0.19/0.44  # Proof object clause steps            : 36
% 0.19/0.44  # Proof object formula steps           : 31
% 0.19/0.44  # Proof object conjectures             : 12
% 0.19/0.44  # Proof object clause conjectures      : 9
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 17
% 0.19/0.44  # Proof object initial formulas used   : 15
% 0.19/0.44  # Proof object generating inferences   : 7
% 0.19/0.44  # Proof object simplifying inferences  : 53
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 18
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 43
% 0.19/0.44  # Removed in clause preprocessing      : 7
% 0.19/0.44  # Initial clauses in saturation        : 36
% 0.19/0.44  # Processed clauses                    : 304
% 0.19/0.44  # ...of these trivial                  : 36
% 0.19/0.44  # ...subsumed                          : 112
% 0.19/0.44  # ...remaining for further processing  : 156
% 0.19/0.44  # Other redundant clauses eliminated   : 108
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 6
% 0.19/0.44  # Backward-rewritten                   : 45
% 0.19/0.44  # Generated clauses                    : 2524
% 0.19/0.44  # ...of the previous two non-trivial   : 2316
% 0.19/0.44  # Contextual simplify-reflections      : 0
% 0.19/0.44  # Paramodulations                      : 2376
% 0.19/0.44  # Factorizations                       : 8
% 0.19/0.44  # Equation resolutions                 : 140
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 94
% 0.19/0.44  #    Positive orientable unit clauses  : 26
% 0.19/0.44  #    Positive unorientable unit clauses: 5
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 62
% 0.19/0.44  # Current number of unprocessed clauses: 1992
% 0.19/0.44  # ...number of literals in the above   : 10053
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 58
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 871
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 798
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 81
% 0.19/0.44  # Unit Clause-clause subsumption calls : 21
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 153
% 0.19/0.44  # BW rewrite match successes           : 41
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 46859
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.093 s
% 0.19/0.44  # System time              : 0.013 s
% 0.19/0.44  # Total time               : 0.106 s
% 0.19/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
